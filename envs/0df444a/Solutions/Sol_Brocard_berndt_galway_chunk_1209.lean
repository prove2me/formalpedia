-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1209
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T01:46:33.348736+00:00
-- url     : https://prove2.me/submissions/b798f310-ad47-46fb-a1df-f81d7333caf6

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 217266187 ≤ n < 217446043 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 217267437 1250 217266187 217266221
    0x2040221010b04120f05101401050f03060c2209020309150c0a090306020903211308011103130f050312060a0501050c151008060c0d0606050a0203041514030f040303 72
    0x428000a00c1d81c101c0340303513001458072140105500c1808802c11200f80a800040d005003c130040b4020b045030254801e12815005012480c2110194903010884034032401c6440c9145091a17441c03560980407440b540150034010046580201d5107803454002180b03d038014900410800040310112840c804000305802100c030418400069041d0b401848101240e0300000096103e610200002e800e0500788582104d110f4021a0703e2543c80100201509603210880d5500d0800d03a6640001401ea03101050688507034003040001540003c6d01e030001040700d03400b5418507000c1c010b4640d2203d282d6031003100c03000c0d5500c010703900700801440c001200c02c01410080c40e08600740840d002500342e0702e0002c0e410b5211201c1040c00002d0900d0041100e41c002003201e00200e40300c505041c003800d0b8488e403002c482a0071180c140407000c28028003c0080720054605035000318a01480c0136054160004243c54180030412241c141001000307840c0061802030308449a82c83c80750900d4940982100d01100c0a00000e80c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 217268687 1250 217267437 217267439
    0x6090803070f03050a1106070306080105071b1401140a060f05010c020603060d02061c05090705030109050d0c051f020c0c0f0f0f1305070f0224041202010902040221010b04 75
    0x1000c041c9007100b407641c10f013050341d03c444d0511400e40d60110200b011481134800c070020041c0450341354201008880c2c54200030001500d6803481120440000b520381d0001c424042d8002001030160701c030b0701c03540211300300c0006041e5644c1d42c0c900ca1848410344034840ca40362a91801e002c0c2800d00003140f401000c007400e1221050909501140c0180001000d5510514042c044c84065494481c12200b860a000038040c00031004469800024101943d1240191160741c201140a080510416991582010041681e44902d08088400000c030200c100c3d454000c0d100d1000c1100500742c904031860314a08809a2640c4642408030300d04003004645a2161200c420214216220302d40500c1e0000703030503035002807252000700200341c020011004444400d4074050400c1220366005540c4c0005010a901f41c030210144c3d400320300b9103140e02103c0d00c80e00340c0840e00400c0000d1648021030343c1220081c0000308141c211500001c0880e005207109056100c00310520707200351051a0544c0d409815450070841c00c2c1 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 217269937 1250 217268687 217268693
    0x40b0f0411150a0305010b12010308031909230c0a050d03020106080a0809090906060f06030727060e0111070303030905030d1112060306090c0103180b0c040609080307 73
    0x11110141401051555550200e814806540c00556006402601e80b0220554106020342240d003e008514006131410340045001d100e00b02c1101e038100b2001c00c296440c0e07401e40d02e82542e6503001902c4001e5810710404000c4010240303000c0c01358641e005202e4210f10500008400d00040c0903407040350800d420001e901e036129038601d49100c1c150382d001e03511900c194620740707401c2c0c1c010070454000207814481d00c1d507114200000701000384000d100644600101d512450180b50fa03c0303c00303450003036014262144100080c00c144000e55802407031403601e00195440101e5640108440816840b03000e0741120f810700406403c0384001403103440a18107030741403164042e105034580456000041c100340d1901600e8040c00420801e56440d0100000208429070021601e261168800320900e40e0407516880064040d02c0c011908a101d00911809080d040d849100114000d005401c80480000c0f00f507600300000c0356800c41c0725441180302c6e01c205035803070341025000b0300bd841d02e0ba8415612a40304021407000 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 217271187 1250 217269937 217269953
    0xa030e0303090a03112806030c0c1a13060c1d0a0302030a02040203041112030d0c03020a080a050702070b0f0702030c0306240d021c020405010b03010b0702130209040e0d020d03020304 80
    0x301d81e0400c50303a00200a0f4200000c0390b59085c0405d0079190501e40c3c1880140c211b0001050007140c5064804000c10301c0600720590302c0c08020076024221080c006961140c1c041d003c68610b921030250009040105032507601c510842d00c810801d0740c00213503002d03038082184200746040a65a14200c4d8401d1b0a03901c1c4d0780c0001d03910007040e40001d018035004804102005648242c0c0c04c14094002c040143d0356800c55a801d503a0740001c448041d89a044c2241540f09502a01c01c690306075003d6034540510b580c400c00c8840103440041d05080440c402c4c400d0004200684202418425240750496035a80301c90340101860102103400c1c051094202604cc0400000080d0080302e400003594100d02c1010320590002d120780c1617101c4083d40003040e450290140f078540c42d0400c20514400c450401a40c0d0f01c64203a081072380000d020b10518100700b001183c0143c43c141d130440301d42c0030308078101510704007583c1d0109003542c1c5c900076041c41591150030780781d5500340c06014801000704180b40441c00c0d481d158070390080b = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 217272437 1250 217271187 217271189
    0x5060405030a020d0203070801050f0405070609120609030c080a030609050a0204061e09050d140d0f05090618060706050103120c03020304060809030c0105270708070608061f020a030e0303090a 84
    0x104c58481c940035001103484c14080e0070300402016000b00594030342a02510340c0381d0011901104c49019000000c201180140f000742e050380c0e05003000840740240c07540c80e48002c0105100940500c01a5444403001684680007801c400503d640c020172220303d0722443c00c00340e420152003018200e0041c48140501d980c014002e50101c141c980545005c0151000306617084402500403e40150940a612051122004000d41011a20b10442c0c0e9542090300702120003100060b0030800007542003104c6607080c6032103406001c03004011204c00000c00f241d64006552580000303c101e41c525100c0c001042400310021248180c01a142009044909140d4000b5102e02c502d004001c1480a110046038044008109903590010050020485424102c50602c801c4844812906203101c185114000c06140440c900d8100c4250390024010241000419950050b000385040d421880c108510000310b0f0240c9202c100840381900684500000c500307009000384c40d0104158000e41c410004080071b5100e284402e0 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 217273687 1250 217272437 217272439
    0xe030f091201091110020c1807171305160e040f0c0e070c0210050708030a2a0f08010b120402011d0301020403061e0615050a05190c0c05060405030a02 66
    0x680d9512400300014005a54044122640c0d840e200b40e04040043d824030340c1c1e9525000319145d01c0000b00f1104104c0c0e84001507820070703801c440e003000b041c4602d0341d458003456080403403800c1c500311010140965070311814040340c001c134641c000c00910200380b1000344460034107400804680145142007900e8104803440103807000303111500c450007076000c1c04103211516018001200300300d610780c1807521005100803030301c56060344a4005200b03c014050b0003501122079490344112004e0941d40c8540481e0000c050104100d44020780c034005800c00c0c280001d5040d40101d01ba9140c520040f903d11800410840051b0000303400d00d82d08110175a03031080c00350001c8c1da026909181c2103a54001c0003142090702e02513200080d4240d030011501008014003600445400640d04491a518a00101c403c2095a44d113200d0ba5104100d00d281074541c50744140000c0c00002080e003451450400072001203240c0c000303d0605c0c0f50006501030000b600700800b940b40d140c000d000480d4594101820580080d40350306d6010350003 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 217274937 1250 217273687 217273717
    0x910050c0a080f0d050c030901050105032404060e0a230703150b03071a041a07121409090f0105030c0d0201140901091206020903060a090f031407060f020c100e03 71
    0x344080d9490901198003a400813801405142064400d01c2001d401c143c911960382c2d401d000000c00c450400082000e20700a421030320780c40c0010340620303205036000c000c1c000399035140e00d501101c080c2c404100200c411140c800c1c208843c040303c02161300009080c08107103c4110390005041080464000300c4c02c441080d00c1003000054251030400007a107054030300c2d0302080245904600c4242c2030b100c420040c00c00c8074000e44104006c0d03402c80c0107460951080345002400b1016100c0c0908040b481104034006400d0804285490042c03d400084d106810807201808124541001440706040500c1501c0841c0c40685503602c0c00c264690010342641098a02106801c1011400e40e442e0b83c40740b0900340041008071001022001c490030b110b0042e50080c030b195802449840c0120b0b00020661296209054100f50b920358100c081e55812034078900d20036400d4a60b80b10901007600811300510400c07100021161006030b4410088141600300200d02c2007904540e071070300209a459020100480e01010044070306 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 217276187 1250 217274937 217274947
    0xc0a1412092707180b030c03130312140103060e21030a020f0712030b06030f010315091407060206130503090d022701030c0b0a0e01030509011d030910050c0a08 70
    0x19448405010031010300703641494500744034039640c000062281345062401d074080c40b00e40b24813804041d4401a18010440c0104000040f920f10801420006640c03082c0b8108812140b1003501d070b415181c8500750b074030000060100400c104a00d41c41a0940203012101624208002c90102e1032401c0c5409122400e0140000020310003a80075811103600302c0f48101c0c0c1d11b84620090800900e013030441400b5002007032900ca1040400d10303020b0300780c0e44288035401507191641c1c2155500c080c6003070703081c8070303401c0551311200c0a40c00038113040540c50410003035900500800e850103000034500384d405010781c01180790520808000c1800071003140c03000d120580305500c03422903d2001c80c0080c01c04603441e42d0080b864110f4900703295040c3c407419048034040c0100c440d0082d240c070130844031480346119510100f506003401d00380790f50003500082e5010203007030700006100c0c00c0585181d001002e882c20961007908000780c000d04620b04000d8003200c0c002a8a4468182110400215541c80c2a0b4078081c00c18070300411 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 217277437 1250 217276187 217276219
    0x20d0c06060f06081e1b0702060d020712080c0a020a0b040507090903020f070b0f09090a0e030f1e0703020606090a0207120906110c0f04020715020c0a141209 69
    0x80c0c0050603031506815210b550b5010080c41d0100984031040300383d190034480b070b6040e105600518007030310b403144050301111b8003661080321503400494100d80050050014501040c142d101034003541740a080d490003e9910100c0013080804000c1a8120040707040c025250560340c0000c1075040076910000540c81341d207840c14030501d881003a5105200c4c044c2010060800c040d408946900c00f01c4d80f20044035a450b499150b071000500072151034105120b010305c0562060b2030405045900100b00c01d500103400030000040c10b065a004110242d02c411000440e90700c400843c8112455022405a50f1801c008650750025100e01b40075000324403545c060070110354040728ed941100d0701c2540c819030200304c500302c011740540081042e110b80b802246c0030740c91103581c14801162103804050300824140c1c003484036000b00030007908094019102051480e02c8101d6030341d2603200400c5259035020080c80c4168051030310100c040f0841101e10b66940065842130301c008180d0b810348082d42012503044850400c219 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 217278687 1250 217277437 217277441
    0x191203020c0402180108010e06031b04020d060308030105010e0604150509030316050d1205070f35180f03070605040f1209171504020f040603050304030602130906030201020d0c06 78
    0x60301c080d845407000074a41030700040c0b031158681d4240c0a0f03c4100480c0c0e650b403900081c1002c112036464040d0000311038252103206c513031080780c48200010401810500c00140420459645801c202c488640001c0107000c2c940e000304c071100c50f060080f01c800e4075090521021a108141300d40740c10341400804200041e50703650901c1074401c204038a40030044461254200315a54010784843c038404a1101c0c43da20000c0031046c066148658002e0300ca442e40d015034250112105141c4d038142c114103242c1c054403095485440742c0d40e012800724200c80c507c61414041d54840b407181d0040503081c2d050740701d0003154100383d80101c242d41c0c60315000381000403d5030f11410300c840140740381003008041034041000807040741c0e08405050252182100c1185603190442c240650358041d0032110f0320003155030000100103152040100d01c80210203480450060f51b60364815255400c00d80046a0140d0007080040c0c981001c0b00b800b00080c100040709009951641d00043c3d1200e1440c5840001c2100040d09001404140e07 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 217279937 1250 217278687 217278703
    0x90906151201140103090f120509040e0105091c0215070e040905010507020f07141201020705030c07030302100b0109060503100b0c010b01020601090e060601080714040308090f19120302 81
    0x3544a059803040035840620903a50309000b16258654083c41e0300c03005500c24401e0240407581701308013404601c071548804602c03c2000301d0f4507081100410030903003151102c1c0542c3c00c0000b940c8001042c01c0c1094100f05062000c005c400b0036001e0707241061346113142da00007521400082a24002070107a141d03050b0840700359000450b181d07041401c1007104801c121055005c80e01c1802c540c0d09885020148805854682c03c01e881144103c0c2901e800303040040c50496020000200c0e80000180303404034540d151411354020700c0e820403594120100410501d90140031100c51280c100c001040801d91406c0042d002c581d02d40a0881017000200000d001c024008140a01910540d11710589982603041c4031b030f0107030501d414141e005003d000000a0081c2c080e004007060040d80c1e401815865235680700440300c018000305a1000c01c18030b22070f44031400741114001c2015500807800c881d90b4803100018860351008128886000d500c0c41c24560090300d00b40351510090310641c01242070900c0f03c07030908074541166 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 217281187 1250 217279937 217279969
    0xa0f020109061404110a0e010b09030c09070905100819050408070212100e0106080601030209040c12050d09060215010312170f01141002370b0a0b0301060605090906 72
    0x2e8803d00342030319588030300761a200754403500c0c00030901e40e90501844506c60980c468030040980f000c005000050720701028010400e4050700701c0710000d00601c00503107018000e40b955804a500b050040c0840d007801e0200003140d14690400040d03034202041903080302c81c4a10014032905544c0c4000c10100840c400c01c40301d5581d002400070800003402c0007050748a59940c400e0a904a00d4800507001c104c00600807007044811110107070026030300e10340078011307002001082154807031032072000801c50010041540400b01e020310014141c0c8507503031002510b01080380d0051025940a00c4072062070a001d070601906482d8881503003031800c0010b80c0290b9610119940f480c070740c3c01455003005001e52115030701504039000507040e181075221503800d010300720130440c22640042c2c000040500d0310805440744c0250360182d50034902d90445403801b400c0701805c80c290085603046540f90070b014085149000f00e0b01105000c40003040092301d4844081e20340d10a50002034080c07070303a6000240840c3e5030b07441f141c0c1e041a4 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 217282437 1250 217281187 217281191
    0xb011209060e06060109030201020a060b0f10030b090c070b0612120c1609110324120a0201090e07090303030509030405030a08040806070e01120e011b050c01200a0f02010906 76
    0x4151030a1005080380402c006040e229450018459611540c0d9040441c1d406030098003c10440382c9540c40541148100c0320303041002010703005015100c2022507807081840740c3d03000407003c10000411500800c060303e250103442e400e02203d03010410b4800c1c80303500002d0440d80440341414035889030f400d1100880014424030804562149003400124244030001c7c07015030001e00035525094080d08464107640045005501440002c420b18044602c030895440884014070500a4120014403d614031050103005504029080402c40d60414503041c00b41c400e8034895400e40c941444000c11103540c5100140030151100040340322510241b0803640984006801da0359504250b0820748115400b41c40b41281c075105080004001c43c0c0304120144c030031141652058000041e0340d03010070103040d0340050200295a155401a01d2480021480300290320644807a5110030301c0503451390031504445445e81c1c48201440c0e1443c4024100000c8998800707075800d0041c003020017407400b01d00512074540000d281c94 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 217283687 1250 217282437 217282451
    0x21b0304080705030c0a03030e010f1407060225080a050d0f1503170c0607031a1801080709061805180703050304030b0105030f0a0b07020102070f060b010f020d0c060b0112 75
    0xc0c1c40030074440c040e00d400b64202c49800300c0e45400c0c0f1404003498400900043c040018091545d80b00b501d11034200031051501580001203030140202c030358000031049400c04e500040313801c3d070510039910200c00104502220f10740340c90240c440d002140301d030841c01c01c1048000201181d082601d94030031003101140b901d0410540282c408481d5944803203000640e5100c4122880d10380607001141200c00d0600c4520250916444e29401a000340c505481100404410404440020b40700c055580d01d009440d4041441c0d80d5241005450a0506d90b0304000c6405040031810310510b50b1203100c40300301044014000030b0503614000d441c000c6c1d040c41c2c201d1603c02d0003509000801e001e0b0010140c402c1e030340150210456641d890341003640d01d036013198810395181c0000c190303038010804d001280e82c0d01603558000503250101ca541c3c2c820b07030050541001c65a013941c134000982656070103910030660540300d0004120000100783c0160041841c024000d011a881c1c2c0031581182c3d10850350240b10390310841090011b1 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 217284937 1250 217283687 217283699
    0x1b040801020d0e0a0f030806130c081501030903080c0c0703050a06090c0e060916021c090e132004090213020c010e1234030c06140402060409021b0304 66
    0x10354000d1400d242c440f410310310b0381c840300d4001099251140e075109481d0b040c00e940e44d550559140000400a503803000c000e00d00c003085d40c00c4d2402030030500100c658a14456240c0f41080e5204a98201d8a2604051604214070300007900441815085010702c625941c0747e4000d894410b140800907000204240143c0001100b00110f640040351441d1190192843c010b40700d583d00041c1440841d6116030000b4140e0110343c204d00328482e48084a190362040c1c03000c0001c601d00000750344074026401c00005111003010881c40c4041070388113400c50002003003051202c217140c030b40621031a010040a8107003c0c0706078071280c040e5100d038001c8604540c0900b000c116034906003107120003900000c0c0c0021003942409482c52901d000800e2980c1e118140c80c0c0558288844c1c58070f6010115516001c3d13003010395544280c02c00f08075025051220461080e942e5180f007141304e191660646181501030000581c0040a200040e0303268016603050300c088103c01a240d900b4000018004c65000e141c2ea10b282c08001808146 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 217286187 1250 217284937 217284941
    0x5180d0203070312030e12070f050f010507050d0e030307050405010f1205130203150930040b031902040f060507030309061407020c061602040b061e090f031501030b1b040801 76
    0xc0c18207a1700c0422000052401458640310240800384800030200002400070702040c2c3c1080c01c040c0688110b8100580001800c2c0c01c403130043c3d619201103140492500c0b80f46019010b40c000c00c2800c2809503045007403021000d4080d024a00a031814000d4622914901d42e03c60f540015001402d19801d00203402c2c01003a9202d02092100c4c164000d0203480e4030103041445464030307140a030724114010102780060040742141c05038151015a041a00c0c11905640306c441000548003810f40000029600c0c281030080e0151082000000203866005220400400340312080d1201260300311304001d546d45003075290440c01031142c00f00080c080b81c80c2c5000f541c0c15080c7c001070780e84119029021500d8650b401c60800c011740c05081c90005000313409010a8005041c282c00c0024062009005503003803503003c101140000038002c10201d40300c031010800701c0301c51904501740441140240c1c080c0c80c28411220b17019401043c1400301901c4509044041800c505402400c56a03007101460181e417290307114208140 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 217287437 1250 217286187 217286213
    0x10911060a1224060203030601020c130e0f0c2e0309030e03010e0c01030605040b060405061e0a1e0c030c0605060a2d051903030807120906090b010f0605180d02030703 73
    0x2500408070f100401c2040c0000110b900518058004210b0100b031001005412540c0b404220040c5880e54200600304000f003040d00040344d50304014210801c2c500f000e0002445200480861140264070b080d02c0101500110a1502e031162034042414005410240e81070719100850a41561a0507a190051800803a82c000a004240d905214260392201084256054103600503030103482000104414a4024000c08803031381d0080c00410081090004105550004070400700410703030041c0410403802d031150005031120b403241403828098605440c002c1c580c0b946440010300c103e0f990700100d03180e5910a02e41800511039004070081d006403200702c901300c8c2100d0201c1801d4850070300402003141d142c0300712528405041d8641d010206881c6850884616601030011018040c003260840ca0310031a03401070001d010302901012031025240d24043c04c0103078050740040c0691200300400d01500e83d000c01220a0032115a0810483c40c01c440b0000e203c5d4000c0d100002d60600c65000000108451201031074 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 217288687 1250 217287437 217287491
    0xe0c1207120e03030c090105070c0f2615040b090a050d170901050112081303081b1c080105011409040606030b0307090207020105040e1807090518010911060a12 70
    0x2009120b401c002c0c0a03560301044c3d500c005040001c0c0401c038000e501c602c010b0a040360180403000d01595446082c210030034103135008800e024401a13943e4010502c8074180050825407400106071002003180014601e04024100408056207100801c0035030508000030341c04140c11406440d120030001c400036041c01c504540b0070804120314070009200c2841842198101c1b070905a03c00080c0f06030350b07030f03001050303000302b4100381d407080309100c0400401c031840d01409000100720901d40710702c5500d460f00e601d02041c404460f00c4807030762401032100d615880310900d41180c5007030900103108418030b40c610503540504504290041d2603c03500155481c8d06400000c4000e1050f420703a4250ba46031a540410b91184480113400b05604001c00c00400b0740791310b203c5512030a0500c0700200008010100b905007107496101a4130310303450701b083c0088401c1103200385110380c0b030010003002030030041d607a901041004081c2803841040081100a4143d0040c0141660b01c488070904204641040c0901070045c00c00c1c2a1315 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 217289937 1250 217288687 217288691
    0xc0111150114040606020f0d051b190c0e0402010905040e0f0303040c03020a1203090b0f040810050609070c110f0d02090702070e0f010e0f040606080709020714030708040e0c120712 79
    0x58100e001191f1810a000c0c4980a410800102d4030709442903030200007400070b403d5a045039017000750020b00002c4004440744040543d91a4a41400a9040b00c2504501c1c10540c20301c080c00b0041c0e810502c8001110810f54011443c1d459401900c2d00348a01c030044029240400000c00040006054652040d28400c0300c3c1d41000c142c86801407804044000c2c2e004011411600041c8001145400505603d04a9803d07140c80c00e81c5480029003092074003044101540e48500c180f14030f80ca40a00c156a01500c9480d00644c031003040c0c4c8420956000c1007441d280141184c426410705a1204804d0040c0c807500034100c1d540ba81000c10b8000d5840e80c3e544250030002c0d0608011840803904122041d04031000f0584210050f1201c1030b40d9a10322001402c00c5031110303620301000800f1013050103502c0003441107440042c2c8803100341c102202030b50410240100342e604104452400505803009490994810b01c0f0521081c0d80c81c0c00408001d8402c19082d0301d5148180c41c1004a15035000703c40076030481c011101 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 217291187 1250 217289937 217289939
    0xc02040b03010c030b2b0b0637090e150903040e04080a0207051e0405100f0b1b150c0706020c1203010305010b0108251e0804030914030c01111501140406 67
    0x2000341d007508401544802281c180620801150001c94940d802c0302c0010f2816400c15201c035500144c4c0c900501c1c0c02d06276500d40c4003902030b07041700028032100107028100701400b5410020811035180c0084020030360a0507503034004030741034003010415603001d0322001b44a50120f0a06040002e020380088a200b00180300d0801302060501b00814205464000040801180135880041101619008000703030510b00c0402c8001130300d2248a01c404c802080e841c0300050f5104222041d42d0100c040420411a10780c0c0a4900314000080d51080182d000d51288001520382c00c0c6480c14101920a0030204050741c4155070000b4500c0b401d42c00254100c83c422002000100421001920300e00000c480c5083c620061465191000d0a442100c26801400746041c03141038506840c0c0690b1194000c40703100c0000e0101f0108000c0540060005c0060241c442c0c0003e0340d0510040041ea8035880040a1810442140e10742080c1e00700410038045881c1d16400d4140e101c1d83c440441c130044d0260464001d01c15410a00 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 217292437 1250 217291187 217291219
    0x140903040e0103060504030e13052d0708061c0803160c0f02010e0d230d08160e0a0e040b041502160b0705090a03080301090606080106050a0c02040b03010c030b 70
    0x4110303400c4848020798014140e00c0d5840c0e100040c8401807081d0280120000c3e140b64aa889011500500807040c1c40090141410401641d00258000002c0806c4c003440c0c034107640840c0001115580140507181486d0907540d5200490b0010201000c00820b0040703400d10f0608003c0500b0145110f000c41044026520103480c2080b2001d020302100030385401401c00310715000d5482104c0c80750b16504050310620390b0351200e070394000d0621345071b490300c0810b800f010720905900c1109101c3d0480891081ca07040c100340c1013180c86080070582030042e1000f4099a40c2c1c1078101d64842c01c114000500d654410501c40c2d14081c104a024080100c60441d80c611481d0080007a0307504034403d803285241c10b10068114134100d6902c101100c50040c1114050103810310801c485a51000303001c0c80034602c20385a0b10340382d52525191105642d0181c00420178081d00740010f000007680138041d110384401c2403520a0f003d00e142d001141c000c083d103080c004d801d5403c1220b03400c0c0903a05134000000103082900e03090301210300c0c40b0f = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 217293687 1250 217292437 217292443
    0x130c111f050a0203040812040201021f090b15060307030506190612050a0c090b03040c050901060c0b090304142103130314060103020109030b04151406040b040b0609010c030302091002011409 83
    0x5074000c1c41b00ca000d101414806202d0810302d0b91042c4180100c4591182020350070103843c0c00c220780d020000b07803600f040038204064108025040211030030a5070444022000050032404000c00c980704150359080042c0480d950715400000b901c0c1e00c401d0290803181c07628401045034a50b006031100791410440401c40d421007600c40c445401c11541e407084405030500324802080c5c0e2007d0320540e4510305088000c40d8550b107500c1080d00802a07a1603509200c4800d141c91802d03101d00800a15098000f48802c00c22a1810f440c400c842c0c60080b2503107142c2070700400028226010b04034840d9014440468095180308001c072100701540d000300030280a29004942c000d035242000d00000740021061082000040c045030941c6400502c00e0059214000c00c1140e1207007107920208802c000e818a880c1840381b0f605142c42788546018050310284041004140170607000e1098001050400190785002c00c240b5100383d042c0d813000c06000300174028046c200b84000340a015401c86c12120f034101080070501042c800 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 217294937 1250 217293687 217293691
    0xe100807170f07080c10091a03130606030311121306031107060504080304020f040212071110050903072f010f050f0a030603060e0c130c111f050a0203 66
    0x99004160301401c28881101800000d100103085224071400002604801e01040e0301038110b90700203000e2444c2403010000d2241c5031031406020f000100b20148500c8420701c1c000900100400329a40c0d5039200c118441c02c40503841d03c0d01901040c54401c0100070194000a9400020840e4003150500300105042040a200301841480e00280100b0108078090203a004070804880d00101d4608110341a1502e40c02d480013141c2c100c460385000810041140740030080e820b10500c0698003107040070004074007503141035005882d403030904c100c104c80004a42001c00542e81d41c0c000c088420320841c10051410355aa030410300c82103580c0d580301083c0901d40d12800100050300c840d91090761b10103960a8005444590181381d2240030010104004106842040002d1280c0e000694002484030b15500f440021603003402121131058009071815821960340b41402d040d200151000026400da1130141500c00101c00c48a803450790080e001502e01607010704420485000d800c10b0280559030314071440d8400ca12003 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 217296187 1250 217294937 217294949
    0x614070e031b040507051306020309040531080c0f0604020f091605091f020c0f06090a0b090d050703030206071b03080a0509010e0303150a0f050a05100c0204020d060e10 74
    0x4a0144a03918680b541005805c500c450800629054241598800420158020703030090b910000740d1141d141414868268880282c209402c0705d40040110040180070390000e19806070348540340e000c1030000c05801c80e10391480c4802100c02c6500783c03211440c0c4440048509a10a28840690700141d041c12070010b4403507600d15100317299150140c0f105407010b82005c40301ca0741005000f07a003801030040b415043c03a102c860a800030410400888100b044008094480034050801407100348455256040c80005071a0300101854845003070034040344511242680c0034100303208000c0e00100b49900815a5400350220380e481400b51000e0581400807074000780d41c02000614407100052800c0040d80c01641c10201d1003002054211000280600e986c0007070ba54048a200d0307a1501042c10318124420800a000f0958010081072910000942e420894400c05008085002c02c0841c80e610a138040d03c080ca80c000c000315141d1885a918500506032402858100d0101c6808100c900030316000240071150 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 217297437 1250 217296187 217296223
    0x31503020922020d060e101a040c02010b04060f0612020405090a0e0f0d0e1e06040302040b1801270e100e0c060408010c030b0a03050c100c0614070e03 66
    0x490b05240c2208840720040c0004003840040d000e0010f070f40343c42c0c0310f5940501407070000c1041d424000340d290070581c0c1c81e160704203501d141002a102600700e401e4180782c0404121400200d14140e00b106038050805210960360061070170502044c0701511080440035501d0303030340e540c58040450700c11210407031203940990f42d409105440040c110184680280c442c0424580507140074201d4614400e103040b00b0401598003064071060b0701281e40c03c0002d85880360341c20400380301d9041c40090020400910135030001034040c03619441e0808007601c81da0001044000780203070071080740d82c1d40d100440d020420392020b420084146098030b0341c94010341c080c80c204090b20101800500c403d11102400511200a0a41030b030b0040080e880850b94445c409480104606400825501c0b60864000c003243c00c07075850144203c044c18014030100d03900043c0d00354036410540d140d12a98420030019551041c900e840200310340c2c18131780120055068001280d0080f007243c2c942c040f00c1e841c0c20003003684035503620507000e038480 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 217298687 1250 217297437 217297441
    0x2070317120612120702010903020d0308010611150f1003080a0302030a0609020c0627030703270609170102090603040f0c1a09060304020402090909030301030b01060509090c0d0605040e010603030315030209 90
    0x10329134401440403a00c141085410705039264041020360104020030303000b007403d01d401001999000b8108041c081d542c140a004408001248070590400250900400002c80c4001819207003a0b00360003400345801100e044e0300d906a02e01c000f170195008a074617018080c202400000c03890098002e0769200c00100e0f0280525580b003c00410299900d15070245290b4408101284442014801030407901d019035640203050800b01c2094040d0508640c42d00c002c44504401004031550140681080c0d94000549600310542100c8e540c0c003a0154180c0103501c1003000080c841080588041c0320304c881e102d03004901c2c1d800c0c1d03900101c1c0040715480a82014140c0304104001040c03414034010b69206100500042c00d00e1254000b090000c04216200c801560000005000344214100f8080c01404580b5029103000190340108840d0b01d00540403495801001c80c2803510422181c11600181802600801114440c0e807443e07406454140b01c1580820715011485c801c4104800143d400d494010b00584915 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 217299937 1250 217298687 217298713
    0x70e0103110d060b040f090c0503060709060f1e0e03061f05010c020303071203020c0f0601061409040b090f1503010e1203060d060218010e0405090a1202070317120612 73
    0x2440601e1040f80c180340e0364810000345580f1441110071003900484000344c00c100c54506082ca003450b0703800003842540544200720b441580030303810381c0c00c0d14514074155418840340710080e03500341a0804500c5a400c001204040400e50200301003541c040224210303101611400491035444041311055011100075040a1001354000c035103504045201804491400601c0e80340c0d49007802d0342c00b81840010fa000100b42f070035800b00700a070000030000324010b00f4155250900203008000c56420b000c44001c00030654031202d6880b903202c0030400102070460560740c5400007041c10f400204880180003010760300b60011050034140314001c0424101d100504401da81510a00d0064100130081584040640c0038000040d5a070300181000b400c01c41c102c5045204500d00251021f170800340320a0090380742c00104014800300240e0300d0102500700c00c6901184940fa81c0407401e16815820160401c1c094215402503204504001d10203000312080903091038803420f08100340180211104c20090748403032180d03020 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 217301187 1250 217299937 217299949
    0x604030e040b1f020f0102030f180f03040302090a02041203020a020102100b0616061806140114060d092909121201030305030601051c0c1d0607030c1106031305070e010311 75
    0x200040d41d0046512448510b082a1b003641d00840b140c0303222101c00c0c1c0c14001044110000f07860011444406410f01c900d104544170350303070f020714440a4443c51a80c00400c8044103207078100d502514034403a40c107180c400141030183d40c503003159000300c0c0103105140800003a240e9510a0b4134405800405032440c010040198880800b40742c0415242543c2d1080c40036099091110b00482e05849a91f0110b80b8002810004040c00c1050f8880ca6882c1e0b08581c150120b80e440808481c4500b1090500180c88141801c0440c1800085d440340c00c0794650040018401008200700c00744250b2120007100d1a001c60b0002d140c8450064040c80d805000301c4c03100500010b03015102950b80203d0601d00345007002c0c0c0b40c001e5003245079003007446207075410b607180051690703a41d1102101c8810220040f80700c091060356008110b040c45450006010080d40880c07003006c10948014418403032000400c9262642010b200c408440e13200064222860311a25600003006640c0c10f00481c100d94202c004200b02000b40c206100c8 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 217302437 1250 217301187 217301239
    0x80912061512010e0105011d0124050a020a08031e0a18020d11060403030804060b04090206040b090604030b010305030415020f06070f020a05060c03010602010f09150b0604170604030e040b 82
    0xc07143d504c411001d10700e0b88007441458000e28003113600c11050f125511610078460b2042e00701c0d82c408a6003200894100c2ca8002011002c40340520b01240c0e5400782040480c100314000100412440780001840460380b081401520000104803070026540c0390750040c6400ca4803881180044580c0b241c5000015140c01c3c51141001405486991207407002200020a60380c003a03041203010a0040f814401408042c0c850010000c0064408001c6c0a5458000416a01540c404d01000120006800c2041d1716102d0a0303500a55001e06118130650b124030300a51280c105000300802095500c800c03800303584c40022542c200075145009442d1645801a00311800c2e01819a500107511845100c0400100c013003044610690180b0701482c1c895061003002820343d03031403911420300c5905006110004c1072800780034047c0e00c1301110001403000c004102045c02405103a10079030307014210007003000d100312000c22400c2c42940f103a5100205c1902620070401103132040c1010a8014441240d000300c003400300e0340084 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 217303687 1250 217302437 217302469
    0x61d06030c0103110412060f0c08190f110409020d110f0d0b010507020303130501112a0a1203030203070201110f071113020703020f0601060906051909120809120615 72
    0x1313161039100d400f500d44150158408681c4c7e40e6440c5c12811400c5018030480041d00e50f1454210213900384500c1c150500240c4a00081910307607580d0400c4280002a80b2200c03400d101840fa4035102ca9a4034551002508880c0140c0600ca0810111000d059052012998401404503149090440742d80000f801070501c9a00c0768103200b8100045000341e0b80400c044c00b0b100c902e0800200c0000e081000040040030801c1e038401c1280e100c2505250480e10013511030004580701c64045904121210000e098800e55602142507a404003846506041c1c0c107400943c45040c10b034000707010038656550050101d1141e65003885101c0011b1120000060058500d06003040000b0694900c060600b03000383e040340d002401c00c03000741c0d2001400740b1510906100550043c0b5150600c070101601d4020054110f100d1010144407411500950700ca009000b248040058203034600d4819400303c4600d44050540e1040c09601d100b058071100d520009000000d100e0b100d182210051415038034600203010b445c2840d0101c0c0 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 217304937 1250 217303687 217303721
    0x5032205070909110a05040203011401030b0d1b140a120f0c0b03090c15030408030117030706020d0c120c02031c06032012030a0c0b0a090b0a061d06030c0103 69
    0x618a02d01e806845401801086050340128001041120030783c141c0d405140124010f000400c00e40d540c814910324946020f0901245007550f500005140343c80000009014070320410a0120240d02ca1071214196091180000c1c03032980c80c20104440b0340214862016a41200c8003064001116201c007106503521480c0c89104c010b807510042c4100350803c507240381e5240c1c0014880700d99032a0202c903080303607140c0402d1424a1410316850310b1081e0700c0140620000050041c9031075108130400c104548082e50442c00443d100d224403402c01340600401c40e810000100c0c1d0b45840c000e814800d1140b1161081d040d0000c51504420326140d45030ba0440100c05203070144d540c9400000b04590039141b40b444211019806103c006050401040441e0039400c000c40c3e40c424405040100c1e00040c07200401600721391342003156600d0040800103800d403400c004060014841c188082608541c02003400c1d102040d0074511401602035032a04441070488407194140c0c03101107140c3d1694026446804501e0802e100 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 217306187 1250 217304937 217304939
    0xc14090406020c0f0a050309010e0405040807110112020a020703121815141801180b030f040f051b090a021201090c0e1f09050a15030e0c040e030909070503220507 71
    0x5041c5c10001c8241c002e031826080052542520341e4880415024404100e40c104104d007440e84400c252405205c03c020400c04002090318116800340c11248003c0c4040d50040d5501d20301500c000391680c06c14070048400003102203074204181d01038107070640070010031a42c04513000d1414422002c4034400d030168409020790446001e0240c6048401402c02c40c03400d6024024440c0c824000506d02c80e000c6442c22401c01e12890203201182d10074040b40c1e0082c2247d00a05156283c034144103113001d5481100038014400c80d80c0c2c0452801c80c0380100e009500c011031b019019a0b9031401c04c202a8480c2c45e6240b4a111845001031045074817590010000440c10710307210114a1000021441d4040c074100c81c40c58030000c080c1084c103015400894480680800d45120a00c81c1c03138005c040c101d42200295840c10305413520060807202c0400c014030111851300402c14085064111181e51310b0b41c0c00143d40c4c50107204810b0000c0c0c1d2407801401141c2c0511800841016141143d04044401c0b651034502141c01d4001d0303001c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 217307437 1250 217306187 217306213
    0x40308041b0b0705070e06060406030506010e0405010306050901060b03060a23041e05150f01030b040f0615020609060702210c070e06031506010905010e0307030215070c14090406020c 80
    0x6034000d03042090380b407591404581085481e1001c143e02680c440090413040100a403540001e0703400f12019410041460340710100142d643e6014404800c3e001885d18000205004540d04410700450003074008001e01c980b603014513180740c4804c49410788c100d140e82800b04044218501d0100c0d800c0c1c09110100d0151554000103800c0d603603240054500d8582c40ca03a9000801c016106180d00705180500348015039124401003445210760000080c14140d40300400d14154841e90000e04200c1081601009000d4503030895010107001d13104400c0040c8150000200c420a0008240b401500c0c140c0040000c0582c00c3da0b04007812407094500241e1b106d05014100f5000b00c100400e2001c1c1c541d5100150442c0b030304100741403401c41d92001100c4616103501c02d00003a46d820094040c1612001c0c03800f58200f85600c008a440d2010351b40c23000350800c20804680c10707a00c01500141405900c00c2d4a074114140c5d47d0007265203590500305005500c80400000b1600094160b030080c030507940035005481c80181c500d0 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 217308687 1250 217307437 217307483
    0x150212090d060209030d0e011713141f02042111060922060e0a09121202040314030403060e061e060d0f050c28090c05040f03030c050d110604030804 65
    0xe00240400c06a402c0801f0941c0c10211900461072403058034020f03850440610042d070895400058400070302440b800c400c50800f4131a04548440c0705403101e01141221014900a50240c0304540d00c10001c0441049480c00c007048160300c96800032894580764042c4c10030000e8960080b0b50b899032106480100447c045a5025071001d200c80305030f000240b043c600042d0103071108000b440c02c0c40e124a0038519500003036a80c43c110b14001050314151a4010030002018024402c981014203e880b50f030701d030001c080c44000000d000b524482c09091000c5407140440075a21001503a00b4140d0b8940d0071074503040b14072111072041d4090300083c8440c00900064441b848400002002a00c0c40d03000601d00e0745031802c0c50141140004030fa078540e2001c0c500c030324481d5039095595026403440300d603ca400400709584076209a4001c1c040f44030640c4080c5541c2d01e00070341103819042d401c84150140c1100111000c5c000c40031080c400e18114081e180c203540703642c2c04450380724004000320350f0301a141408901c4400c0e00 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 217309937 1250 217308687 217308703
    0x30a05092b08090915060a081803040305060907060f0c030c02040605090c030402030d05040f060c050a2a090203070c1e0611090111010501050d080d0f15150212090d06020903 76
    0x140b0200d0350b1150302c00180900b907100100b5003c0da008000300d0120f8191901c3d0101d41380c50b00d03d4541110152200220000c0351803411084043c01d100225003c000d21102084245c0689045021580d08543d6030388262064041c0503c448041a035050012020a00847c5004801c52004100180302606ca50000d0050101035881002c0784401004200860500304a00024400c550500b14242884c10101c400785105500030f031000c00c4090215601041004c2101a00041e40080d60038440b04a090244022000b000070303880000c4046100000c3c802564800c40c2d01800d10385d590741c4520121a290341d07000222001c1c4003d0742c1c811441155021036414816000d44415494a0f503640b04000d034001400710a1074000344500d030b4503180c01081140c3d101c0880414190b03100044548611074040010000c0151040450080d401d1255074800981d5001459080c0c41c0100620018110360480890f696a02d0a489100d1001c0402c202081860b0040700401081d1099401600d03001c224004207051440b0 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 217311187 1250 217309937 217309943
    0x106050a020f0a20040e0717010b0306040609120503040809060912011103481603050d050c0315010e06090301091b050d0b0c0a0c02100917030a05092b 66
    0xd02e1902c08004040211901c508041141c0a10242d0100007035243ca031003141c4036000c9880c200c0700c8c0f08080d041302900b0096560380001d05841240c94079003001d401070204000c04540080e080816407524902446c15680115042003a5600700004a420702c40b56038030002141d50300014040c040108100240a04010714034051b580781c0d120b00b0880d295248842502d0028106061041030072410941c0705c007000141740023419005042c0d12000101e80001d4843c007448000000030741000f200a0641040044c58581216182040f45903200c402d041c001e03000c103859400080c0150600c0d0399a561007402d2243e00c40f500201301318070740201180040d085a180040854a40c0c521200a40d11225004d490740001d20307081d50040c010100ba652034542a840083c425040000b020402c000030714443d2102c10866640a004001c00d00b040c104080c00010091283e1030340701601200003160100b022045e20b91100c00c58880c40d081c2410201002142c603130401194000040f0740d0102d440d02001c541d99581c007140 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 217312437 1250 217311187 217311203
    0x31c05180f010c031a061e0c0d0c020117010e0610050f04080705040b01050c0316170a030203040501060f260c04090c1406040b0315040603080a02010f1a090106050a020f0a 75
    0x602404060140c546003c4000c4d40303a01c41c02100784968840004941404019400308000c0c120600c072900316501451032101c45909c070321300003e4545030b0401c0300003d07803a000741c030740f944544440d222044541d40240110170000d10082c010990b681020341e0444021200390078014100306d5401841ea03001c0e001903006014590207420200103e080500c941d0400b44028603010785080c1c403518010740e6a115200201002509002e0b0b50741c1481a09282c01c01410031207018580c1d1001c811000a019420035078044e03d055180000009902d540f08030264100c88042004020300d903034962901e00541d070580c170f1390401400340950544240e680c038072030000c08600c1001e862251904251254541114411095009074003c00050003040513030b100781ea90001c051042285044484d0020a010f17140d942d00007000f42c00040790b8500580c1c0c064220070309140c5081c00c208130501d07420000f2080c540c510440640c000ca90403005008680c840c0d8018204100f00d80116001340c01145c00c0b00f490424250400e5405e04 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 217313687 1250 217312437 217312451
    0xc2103060315090c0b0309121204061811040209030a0c0b07030206010602060105150a020307050d0e0f040516030209190f0f06050a0906110c06030906070f02031c05180f01 75
    0x100b0841e00c0200c100350b44004200600c500d0b542c0b04568003d41c000c28502c2203022001506807002000200c56a481110b01e003520348900500e900b9107480d007a41d00b12421403c04841d0020340c003801500041041d00420042400007000b0248070080d449441c0141d0140544c80c0c1d00300110b58070420020061220444081e07482405081c02401c1c0f220680003541150864001042a0b58450180d1100c05101d04c0035140d035186244400d03461403043c40c01c0245140610462444465040040c0c90184d0350159060251740400e04108402c803034048404881042d41c03040045840c1d8440d6001c0c00000d00c2c06090743c0c903202e20076903d00041030400da01110303e81101d07480900c045a100d95030300005056a0420505255407800094903107410380c09084100100d82940e0040c005081102004248029180340d82d00d04001d8021500c0321000c840004c0840c8041d007140001610010031a0007603600c107454040d1206040c1038080240c00040d00500c0c18040f0940c0c00621000c2c10300001070b5440050000003000 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 217314937 1250 217313687 217313693
    0x30b072d0f08010e07080709030b07020c011d01090e0903090a09050a0623091b07030504050405062b0203100e060603061b18031011041809080405010c21030603 70
    0x144071654115810855090010098010302c0065150441c8080c00c21003203513981d0352002c03601150030341c1c0064030300b07070801050091098010801d070f8040380082e030350300044c08030440d17201001016865610b0b00081070030304100164840b032140103400c458040700360391518071020009040c07095aa00054051340d582d03014000381c04110b21070200241000386032001122030130300765243c030301640650749800341c2100400140721a8104800c0d85481d1240c0402584a071140d080c024465002405054003441c50840400d21328074103610300240021091600342003600c0c440d03060808a82102c801280c1522845002c102c40b0402405005e00e1466803400030516494910105450601c01a010405d4607803201040304010600c0400c41d080e80e01c00303400c2d801022051101007131038090300284442242e49011030390041c19219a0040085a107140c00f0403a145502142c040c003210011100100156400c2000300318079401852420301d09401500c0414201e802c0e6100002003e02400d80c000000f03580d00414020 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 217316187 1250 217314937 217314947
    0x3020a0816051005030f06041b090305070905090309130b0301141501030b060901030c1407050604030807020d0c1403070b0c031b07050705011b050307120324030b072d 73
    0x5240c02c450f4904541c4070701c00c0c0507040744809401c150400010300c00041e2140c0303807a01711306983c103144d440301c8900d092030f810001e01c9001e036808203c445005000e000034241165006090142c2c030808007651034240c2c0c080800201c031180c0e4221880035901d41a030304405075801c0c8070f41c8090075664070340800036142c00c1a200c90b0494091945605240c5800c6a83c2d0103502c0340d100751030005400382000110758200e0341060380c24a0b103070140d01c5103078900001e030301d41000b1011440c01c0c0914801e07150311344292144001a0307110307a51014090b00040756240007a011403805c1c003441543c0086202941e06d0300d0b00b1900e403103600010456600030421000000e110740c00100c10300e145c140c807030030607182810f05110743d0f81e46032280f0310b038460387d410001609050074400d000c0300c4041036225800b100f103c1d55060b00703103070800b00c4440f61b002d0036020902c1c11820503038054424050655a22840c803c1c1190b15056640d11850f024020300301508001340c11480704280146034214120707500384200071300d951002c1c4080c0100b0b = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 217317437 1250 217316187 217316189
    0x10020409060611010c0f0509130504060b180f04031409040e070807050604030b04060b0619020d17070f0f120c0806040513050a080742151e03020a0816 66
    0xf4250f07241814102c140d50303000c6000c401085c501d26150703955129150000780000208031101d6842490042444204025030344603505403001030ba0000c4584000400c401c1c0d00b41012114011800352120010380060720072500507110141c21401a4107290400c400310782191210080d00d141c070743c0184024000004104400e80041a0032a401c40c0340a0035503413000c1c06407401500082c003440e1aa842c82490340e5580c0c00345c070700044078015202d44058200c2c800a68501000c2c4250000c01e4109540c084c058051640d80c0b445461aa01c400500c11130301c0e40125074400100c803a0004001c0e102401c1d4181550174000d000100085583d030080c00e0408104200c01c40d40701074192040c824084045000040020078141c00c00b5070055150f035100c0c091402c0c42d18151414a0b03681410811017201180151404e405003006203803010400710480d01d9000e508000c45081c0c20b03c49040b00d800c08810000070703140702048503e0449501e80d004000750f8075404034840c400e140e00000243d800440307207454018065140c41d4 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 217318687 1250 217317437 217317467
    0x20a02120601050f0d0602041a0d0c080f160e06041203090b03040c06081009020708030103050c0d020105180109170706020f0a0b010306020703230306330c100204090606 74
    0x24035514110000d070011100884e414050300d10842d42c6000d01078a40e05480052142002e98480c013884a03072500102e6100ea040d01940c070389080d000d0449144503c224503c02e440412044110b511000c0341c1101142403900c40d01c00308103518004640303544514010344000c0090300604d1003015403610380a0903048158014a0400000344100004900c5a503400320448082e418000265282c6020940300c0c0c500f00d800a2002c94000600c00c8104035159004604890060050701c0c0078609110401484d0300c445500a070020300103101d454992084202200d0880c41d05041200d103507507403100030350b2615820090f41c0719181c0203080100a82071b01030001d00740d61039948001c0c040c0745030a41e4440002c03140601028014a50101c0c520042500a04501d01500e80264101d8400841030b06104040e5004980c258014034100030700020040c45902060300684140600e4520100d10170200900c40e00180c00c0341d078180c03089903d40c8405103840d10042018000010703021650074200400508100380c3c94000e0 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 217319937 1250 217318687 217318693
    0x6021b060c03010519091e0507020c010c0b070c05010912030b060f0406030c0c02060c06011a04030203060412030902060301030b1e0f06010315080f010203010906050906010f03110403060903020a0212 87
    0x9007902100d055420440d201e44000341800c3d80340182e1a05600103a0b850361030600390704c40401d0001d80710406039400400a0000e5603400c07500301d071502c13405020b4601080c0c1e520603100010f00002c2c4880d900c403150740750035800054240c5416082d0340000c501a031742c803056004903118066160180812402c41520f1183c03a00f07001516070b5a1500c283d20a1008040d07481c104646020711030000b4100c0c0c0303900180416210768071407032403545525080c403801400700c0508401001845140041c0e80882c0e40040241406a81d1910f5540300c3c403100c0c03c4110101569400c07040300596410024501030350051041c40c00901d00200c800322880460025102c1c94800c0408000c40300d040c0d1004140e1010083c40c000c903407541c81c10700101c6004da49400c051414040e401d80d41000728030550146040b658404c0c400d2220030743c2c5130280910102c058407602e0004c0c4040f000400c60714042d4100d008003041c40790117585416035035103c0d5001c075152520b04600581202c141403066186caa0f8102d074000d1110006 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 217321187 1250 217319937 217319941
    0x301030206031801060b0c010203070f080702030711030a2108060d020d020f13050a020d05011e05150403080a03021809060913050a060f062603030601030506190306021b06 75
    0x2a203601009000481001c4042c010f88200c400a401180c02000f0082e0703c161075412025945020703400c1203842034001100016000d260600c00c18680d030180210703401542c41c01c034554985d041e00340020665070390144907c984240001c2c00c41c4c03e5420180c490b13000c80c0c48400c2c0911000400314080074101e248a000f4004904c800f5940b003000c6d0700c1c2140d0381114071010400070b040211706441c40550b81070004914000030030170016419001401040562a0208200d80e25044a0304d803001098103806120309540e81d041c442400d1605540c41d110400681a50905a42e80c0d12421036034807980820340043c1d00490718000314144881d0094907180f003115460100d207408004120b4480c8001c0c680d1511846c0450341c04148041800004403840d00034005105600f685440c0b070000d0080b07403140882101c4a03a1a61a544045095004401c10500d000d1031443d113500c0d0045014090250926038400298014105a18145000c4000540c40b0310000750b01c0e603501501001c00c80708682d5540945410003c1 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 217322437 1250 217321187 217321189
    0x1505060d061e030213091109160e0603010806041101021903050702011205091c140301080c0108061f05090f03030703080f0108190210090f030b01150905091302060d06180509010203010302 82
    0x30a07010b103412038101c00942c40c03819041c92520003070010700494004200d5000e2265a40803a601d189d070115860b151008080b503414280100c52209100d45145a000140070600040036504481c011410500c100d078800500480d064070b01d48520041180440c000007017900031540c00400000400010800800c054076044c800291a9202101c2100c907140507001c104542c54065201c0401c04170402503040c0e103e60310f507101e880d0f540b2400120b0a02180d032001c001034442c40e102e00411101420004241482020f402c1d054403150000721b01d1942c441e051600384038050302d04102400f0417a0081c4e46e5544181445e81c02c2da480d0f8141a00160a1500203164800d018403030f050341147d01d542e058030b412040103882e4900f00c419001d05c0e0004d0054044c00d103400070034010384200036416510030340200003000000c50800d450140b224892142c011309114009105140d04840b5803032000c1c00a440300c1c0c9060824107003001141c000e0707001300b000913441c51910006180c191041c240e010768144000c503d5941190 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 217323687 1250 217322437 217322449
    0x30118060b0714010213080606120316030c020d060906140c0a0e09130203060c0d0b03010510050904030c060c0c05010f0203040206030f0408040b03041a0a06060801091505060d061e0302 81
    0x15409810145507003840311246001754100c0303010b080c4401140c00003640b561f2246403610340a0380c841d40320300001d039280c0d15848070120807210b01c0b003109407002c0140c100c1070340c0c00d0f01c2d0703020004420b0364419100100b0b41c3c00306101d03015245181d07215030310005020901d19030b02c80c1d26040180035401c2081007400203240e05508003d6803040002c2c01c5800f041299105a07078188444008007000303406020b0441400784d09480c410181081000703d500c24020481c005c0d0030325088036012500c661503d91a20410401404c0075030034030350020f020349041039076a59585c803100c082d20102c140000000f900b40c5014030501a080c8180800514611000d5140d800e103900010482e0001a00ca5080401d804010404000f180c0c0708880c02841c4000c00707140c40303203418140301301100303844a28007404040840000d01c035030b01984680d800755032541d03c0c1c1d503105900b40f8081c2c200800b41036888401c05d0345410f502044030303501c035000360020005901b07001c42e041d41006100c030401c0000c034100e54440800c058051005a13291 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 217324937 1250 217323687 217323697
    0x90102061e0a0e0c04090303150e04020d0308040312060807051302130506031e010b070204240603020d06172b022509090308060a050a06020604020d0501090507080102030118060b 78
    0xc11800714003ca03103084144c0c2085080c40002c2ea1281c90001141c0401d0b8054110030305040401c4010b041d15a61548101d20045003185d00961000d550807218000a01401c6d03202d801a01074a40031041c24198002d130012182c00e42c1100469a0010a0401c61490601010420006860000c0d42000400c1840040501135401030510411020001a0041004403010202900d908245074041d5075a5803190744160302819041e80618140004100c01c00c01c2c04040d2158890640f88140400c0d2800d24110000c0d042820031a5410b6112500041d0280b400840d900c06140c6490141c01c1400b0b108108212141c4420102020440c00040e000340f41d94010481405c807186038000000c3c200a606103000e80f40e1a640c206214041c90114000107140c1e002c05d00c2da1042d9004d03500c64001c00c0c0c4503020030101c14120311403130005a010300d00003001420499285048a48685c00114080300141c1c0c440342400c0307158004100e0b0341c0d808001006100030032005c500407041c42c3c9000304035450400c01015064400e03 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 217326187 1250 217324937 217324951
    0xf060c0316020d05030f0d0614010206040221010c09081504050a12090e16180b0d15080f0d020c2403071815020708030405011e090b0f090102061e 64
    0x10045420035501c914881c050155480b00650f80da4203400c40c0e021b0b0540d04000d038a030b04024a0600003080c0e00c010105024003e801c142c000300450f50b126400c00031000c4d404006611400c25070402000511070900402260712800d0300c1c0c40c0036581c28100b202d0710b0514080120203149070140305200100e540480d1080d40203811100f01d00c01804040020340382d01d55298030405100f405241080100c9600350b518442080d032956540302c9181e8540f21480318820540202d030742030007080010050501c00e0341c0c001c03960740c03003050340e4061001c1d0f80e5400d69042101c22b03d039900190304101a400c0580d6810b00440b50b40d541b080340c81c420400f00b241012000012240c60f000003108000011422090043c103640100c48401c01d06001c0b200e031203140042110707040c60075250240c4290715000c1805000441524103903203041c0e590302480d010f00c0078440304020300556031805000000c1400310341201860010030341082501c81d1a5641d04030000020701d8000024021a081da41c85d8440d03418585451001a0304081 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 217327437 1250 217326187 217326217
    0x5210405060f0c031326060112050a06060801020405150a0207030b0702010b04050723040803090423040c14030105270106120c0f29030a02070218060f060c03 69
    0xb005080100807072044a0a050a078400454102040c401c000141415500500c00c00391101c92a21564041c0c5c3c00701c940803140700d402c0703075005010112a2040c3c200d052030203401100c0940c401a02c900d8202d415a8104407441d075000903041c0154141120000d902e241384a9615181508111009443c0c004600004043c0314208000c90703007a82c400d40050342c104400500801c03590074400d90142041d00010755001082c04840c0302006d071041f024094800b00d564400140d4605080b800030030005140005550441d40761102a05c0403000301c9090f0380d4415441076000980395420301c90009951460108040e11980c104070421060740c0480d1300101c201c484c0d040f00942c210f448109041c1c05480280c200481c0d2640c1d0151603405d00100ea07826030704031903101d62640460340c1c03a03c1d11720200c0000f4401c106031001c0c040c5c8645400401c0e01c4000e690060f14140d0043c2803944903800110300a15444034009103513040814814185817a2010184422088400c0c43c903010600c11032684a00504004881240c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 217328687 1250 217327437 217327447
    0x307060b130f060302041505010c26030f040611040b0703080423060406060f1d09071502010209090c0a090302060904090b070206090c0105041d10090e0a0521040506 72
    0xd00c0310788006100c1d91400300c0c00e010012180b000100104207900c0700740d208070300300070102070003c40564603a0300b0303501d041e515803280720f038141c0329503644040e03046ca02502c00c124007400302415440e02000d5805544e80364851411401d0a040180954200303000e04d040381d031402c100c10407104041c08222006194141024482e540d940e0801030211102d920300306c2c000041030181017420b200e010500610480c4648400c210103170f03c40300b01615203600340c0106c4208c5080642c0040030001840001507105070110b0071603c2103034940412800300302ea10b09070107015030340200f00441c0a24080700516030055240035098141b0720345a400501940312480041d00404000403203041c241c4903900716612981e0450b98041e418105060000d5030740108650800b10741c050001400c14941c4900c2c00c80b8201c4498190701384020810300307550301250401130066104030707002d80380c0002c0c820203a028003802c05a0036800b074080280941031560402e4210751103d10382c590082440303d146c01c40340702070742c05552007510010340764 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 217329937 1250 217328687 217328689
    0x1503010608030f0d050a02070308060d06150b030103030f0e010e01110f06130b130b06040b040b150a090501020c0a0e1b040f03140a05070e060d08030103060204060207080706020307060b 81
    0x4218030303003050045010001c3c2494080394410000e100386051103034100700695562070444128054100024001103d040109a040c0741c1080400c2e4118052500003520080243c0c0580c1e003509103a00c98694240c0c04401001459000a21585c620382c081c2040500d11f405100000e0038401d80c9010756051050000d0815407440c030401402504030400d0045940714244002000f682c10340032001103801c52003010014401c508040c44500380c051f4007000105064a43d001004050b10103d1030a40c0c015a650982e0704980e40d610700d03410110a55414225600e140d01880102201125001541554851002d183d2a034666005580445420305010b0156440c1c1c641d84000d91501c0343c005c0b1101f20381c04140480c81a030121801d0f01200d126102642c2c1e82c0074080c0c6400c2d00d0303500c0000302510503001082c0c03c12184080403238050b40301000270a0700b12a0511030791a0381e02c0d41c02c2a0002d071010390380801d051080130740401148014084420042c6655807030204000d55074450028001c20030350301d90000001c9 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 217331187 1250 217329937 217329941
    0x5060d1a09030d020d0203040507080d0203040306050421081501031401052b050f060a0501051c05070503010f020c0c060c0604060228110709050c0406080415020a0c0302071a03150301 80
    0x811500c0c3d07800390360712039041160360040d41081e074098409003d01070001a44850011381403c0e2044560040c45c00c003461354540c28001c120083c0280c0d00c02c4105ca0722002c0031301c82841c00013032101c103640f200d800c1c03401c02500741000c7c082c1c2690304505052038812121481a001100740b411031b4002c60303030102441c04242c02503513541c41250300d40c200d0002030021441046804a03030401002500002c4079800c1ea50036040100791a0284079132900522a00f004038000742241000c4603080e80038100b112a042d9841c00403900311141c43c2c0600d0320240e400b0418103203134803082c0a00901c8100031200030381000c02e82c00c0503e0325041c002c0d100424055000501009038100f94220400b2500c00d21030303495800354640c80c041d2003034003428130400c003074003c000001c030b082c1501c0d1095030301561070f0031956414035040a1b01559213400203481510141c00c040c04c070007550102400100415005562191210303800c504d0041d240c002c2c86e400103502603c40800c90601025400d0581b41d006040744035945081d5086404240 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 217332437 1250 217331187 217331197
    0x1409010c140c1f1d130b01020111030118050105100f0507171209010b090412140f0403080702030d030c02101107060501030b190e070306021c09060504030305060d1a0903 74
    0x5004003c8412070369a6206000300c0d001c01a0142c0c5903441c4c64451504007142030040284620360101441d0f4185000104036488000b80c6071042c000025103035808483d481b66900242d000c00c0344102c150b8861408203480b809000e00400e0305494941c0c21520780e00005e810300454410007010000082111814000c21130f5070b01c0c4c51030f00501007950313503548408188a040c0d001220071840303070360030000070003114281207000520441d00212407801001d020441110b8000540c0041141d402052180a11f0080018000e10065102e1b01d900340d62a80648103150a140d040003041e8103161403c0002c070701494020400c44121041c076800000d00e9410307220030030390030300030032801524140c07801c0c0010040002041e0703424000d004800034500b0304142140b0580c195805400102d5068002503c2000001d900d5000340801c128440c00d404121580010044111035090005032440707070319038060105140d01481510b0300b00405035000c0e16198a551103506081510343e241c0d455000c500000904410070a0040c2d40c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 217333687 1250 217332437 217332439
    0x10608151b040f08030304030306080a0b040602030903120a0b01030501082b050409050a0f0e120409050601030902030d08070824130209040608070f050328080f0d0c1409010c140c 78
    0x180f60702c62003800c0c0e880c1c1003124201e003c03a00d040070101c0d0980002500c20320055100b000000107584503076542001e50070143c001d1032a071005012445403a85001c00c441d100355542800081c207803400d1000141074a406074403403011508031030000c041d6581c1e0340c0d500c00c1d502028a19a5200c0200788503048645109a600152081d031800c0f040c81246400cd42008040900e6074405025014160302c0140d150070f03c8036a8000705150422040200300380c190091030b44500e050400099811f450f40200f424644c10400040001e0280c008000c5090f4009418607003084a03440311030013210a054051440c000c4d40c5d07100c544180c0d6502100c00c1c40014a4044881502010b0018018143d0340c0d58000d0f514021401490711159040801290b1030400142d041d200c1b01c0342c0c0420b9000704050b031224000901c9110010744240c1d43c100003c0ca5070050013401040e0040c1c6074000000c107001d0f01d41006040070740c1d20b440d008150300100030560702607901c0031441660700e4200ca4480d82c40c007030b51f0042d640b80c101c1d000c01c0c02e = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 217334937 1250 217333687 217333709
    0x100e0a0b0a0209130b030a030e0a1203020a0c0f0b180d0c0906080c06120402010f0210060f06030c020c10050a090e28090c1406120117010608151b04 65
    0x19204401c1c1e00038294000041d6110900340440010150030385800c0c002a41e0540d010003070410109100e003881068061019181c009800d440303c1c004689020300c00420703005a8840c40c4804c0401040c40440d2000f4080060700f04003050030310b400054644611800785803c2b044881e00e10307000b5518180c0310100316a1000080d800d584c0d885500c000541024420300c0018016095420168145801118009403d0094407a040d541b01d600555019035084490021480b88180400c07408100c4d10544014121288024406d5071078403100030191000184180f00310b4101c0000421541c4620903401c1890034181007003901c441c9544e204448207480c40e48408035040007581404003405030b03e103280211151104038001c012000740d01902c15070701110b40040c000404081c040050b200b00300c86d034101c0301c7c400902c113514114100e46031182c811000c3c0c11080000c0c650804402c0c0540c02440350b4802400c3e00006003409100801e804200240002c01e4100110345003074407501d00c0101502200d010708000c2d221 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 217336187 1250 217334937 217334941
    0x30911090a1b0c110d050a0602030c041401110706050a030b0402040e0a0b0108010311040c030209130b0310060f1203020313030302010606030b150d1505030106030f02030111030603100e0a0b 83
    0x100001030000d00c0209120126100000014148203d6041120a400c0118901c03130070b1400d0300b401845d48003000152403a014025404000502c1da000030b5001d04034648200ba199420900240112482420224180101482c07136090ba02d00104054003150003070700b41a910341140ca00e05402034500e561f500c1e54041d03c000b9001c1115200004054003e000324101006807030509001501c1c0c5070720a00014140a44441c0b0061252601c2e07006508078002915015007000031400c04034624582844003221025240c541142c2542001c120f14100d000a121051003074501c5c0140303400620060f40900307625125040a51400e2500070070440301c0362801c110448035010b40d80d05009000b00307243d01521000a04048801c00750b0300d8002e002007000841c2c00b030001c1c40d0940c0b4031b44040c010001d60034a85a01001200c002819590a120ba0002140031300c40c040d11003201c0c1d204150848004044040c02d941042c814003010380c400140c01002d081c039122000407449004c00c08580707440d00714403005000c03840d2002 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 217337437 1250 217336187 217336201
    0x30c060103060609061a0f0d050c03061203160201030b0a0f0e070e0a1a09190803070501050f040f03080406020f03070507061802090a020f07050d0201090c08010e060703091109 77
    0x591541202d0180700704001050701c818010094421900c641c103c0314100040c202d40d41c2404100030701088042c101070901e40481c060400c0c0c15520b0803a0080f03007900d404810425907040100e245000f400c0150080c40c43c0c00c4081000303526401c61035401904041d941d08051406448903034949003c3c2c10720070702107000d250f9682030030349909100f200e0550010341d842c40d480741d090501e01d21040548011083c030250100c800881052150001c45240794050b01d151544101c8500394081d02c0041c04221010350355982142c01e0035404c0d02c02c06860385148096103020080401d1081680201e001e03458500b0003540e07121414450068040e542342c1da042c20310004244201e45800c1002400010310420080c40000c0a0041341d40c0000200074001c0d40200d134200004404612560091011401540040b402d0511381d0b12075a20700385d6210b25a2025030f5450003100c060040440c013003401462810300a02c0380e41d0722076000985231a070203000c0b5414561103030b4140d01044030341b80610f800c400001d40007401c5403400076 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 217338687 1250 217337437 217337443
    0xb071415160e012a0c03030f0207120c090203060d061404030f0f021011040b030a0212060a0807121104050f0105090c160f0204060e01061115070c02190503030c 70
    0x510403a41c66500201c000880e640280003044540700141c450b0b100b80e00b00c4920030b20144e12424441c041c1507551101d000c000407034a158460185d4001c0e5500b020a800301e9401030301c0d1044542042c3e1036052844190400140d078200030809603101d6141c0035071245c80b00340c04114009800d0100602d40c82c1407500c0b28102c050b0301c0e109280300314002d513204081e00c40e40039010b88600302d01c815820016000a0748461940c04240c118503000a060310110740307402c0e0384d012015038541041c3c490005998001460320f11821b00c03409010340109048440d00c41c0320703241614060351405148035044201201c807518a061001440c801d120252000c1d005004910706110020071a5009015251080e5400c00c003041e00320035018182c41549070b004100e01c0440195817111102c460003241e0481c0d1140c0c44220210304104d104220300d009004940b9414011701c100e060050802c0000103043c4404001801003004095008100340c10042e01507031030012420071040ca0500821840d08002e400d44000118014000400 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 217339937 1250 217338687 217338691
    0x312070204090c1214070b0f0a0f05090303040602010f050903190807090306060311040c050a0c110301020d1e061512020d0e010507020309030f120a050c1033030c0b071415 75
    0x5e1007034a0020f6103580d03e110141c01010281007403030314181710f4980864001c00780740b0300f140074505100341024804000245154007503004400140d4540340d130302c09240c802e405820f070007040e0708024609100c604644843c822200705841d808000c80c0801096610340102c8550000c2c581114081c03041c1c5850b07050075541c0048040f01e0320b000c0d92400c2400c8116a00c81c0040c1d03a03250b101d84c1d4418545421580f240007245034180041c5525560801003850030003124810321501c040380080b4510380c01c050a52270301c00c554090b401fa0034055942c000c0c4a481907072081107144e40743c40f61800143c459207640403110060541220b09041580380c4000d100d202600040607084200d400c808903013403010440c80d0fa03602c5030044182000800002e00200500f42c0c0960050300901c0c4900c0c08031164060482a0442504d100c1c0315541c450311380c0600d4401601110b51030321011700c00d0304007071990b51030f103035603204e200d07480300c4c0d21400c8000c003000300c2c02004103c28000e0b0403102c13081903021603900095211210760b80c0881 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 217341187 1250 217339937 217339973
    0xa0e0411040b0901090b01110d110f01090308060d081204030e0f041107020103050403020a050a0f0209070f020d230d050108060609130209131e060b0312070204090c12 73
    0xa0042404494a403030301586840b10000b60003164907920304012880a07100700e515040c148905800010101e1008001008011030321b9502d10950b8900d090b042c0341400b90255040b40c459040c001c80c1c0d0042504500070641000040d64480660102030500c0c10903800f4541c00d4403601d20114048c407051592010421916a0f0300b21040075807600300d40f040104070b0344440900c2c0e000a0003484548050340c0607510065103d4040d005903090001136a03900c1d8105040d041c0200ca031510641039207415810a03001466010003281010715a0050100c0080e564076401d000d00002c00c4840c0d0803110985800b80b0a2100d1008a0080c8540f101709041031500508070900132003106128800c00030304a407507c6e840c404d01440c0c04003030071030b4000825000e01030500c20050101454400100d0781000040a40900014804103049c03800c12481c01440d024003500e09101c00240300342e02001c6d0500042501d0350840d10042d60484000424200f035144c504001c258607400201f06480109010080c00100c40241c6943c80c4 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 217342437 1250 217341187 217341203
    0x3140d050f1e011e051f0f1b0b060a0b0c011a03030a14090612090313090c02030d021b0d02030705011b05040504020307020c03011a0915010503071206050a0e04 70
    0xa5030302c1e01a44080d42101081401442c0640100080b480c10440d81d258804aa850000b40c1c81e155070203d20521462400500c030a0070490441c1281c6a0011101c000e5150505e060601070221607524142c17107807052009800303140c0540104d4515940c0c2a05d10004100c40c0907499191208407000d1402080b8000c079a140c4407440c42d140c1c82c1d9a01c1c0210413206005a280c0301c06031801e0205100e088280c01c28802541c01c0542000654004640b4404581c0318407a020002d40e0b907140c0d021080e08140d0502d5200c044d00c50705120740900007540200171388010b600518001a1074501204c00805040b440711400b0410703009514400720b13496408801000e50a0040000f0700c1204040310030203212000380240c01000030b40c00d200601203450301f6002150480e10b00c1c81124440e50002000a0071140c03040d002c1a908120f500396003005061030304503194007104000c0001003088410001800f41d01c8000c04010810209041c0804e400f00140c0c09000a041d000e00003400103a00c07940b071000e01082c00d450035180c0e1a = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 217343687 1250 217342437 217342441
    0x40f3312051806060303071a090c030115060e040606020316060912020706081602030315011e390803060a170106030b010b0304150c052214061201030f03140d050f 71
    0x100b0000b00703d0f140a5840a0386150b01c0e10410f00041c23500d08042c00850250003180480156a0340074081c4941c03801e004400345040b9440c2500103410000a0003000d40074070300f0f00d0810450190040191000032410b1480b8010a80491500c400109452017000340a2071500d8440020700340d000031544161103481d02c44e0070058a483c065150300703440718920f090040c1c0c404c2000561442040540414068042c14404c03e40e820b0003800f007000c03155000340c110000d40480b03250348028004040041d0a00e6142c1c8503c409900c2c65085044582540c190141000f8000404100c040d2900c01001000306400405205c3c0f000316888800d0180090748020740303034a045c0500114240c0070070002c59018940c48100f12202c03450901c200c10146c2074402c601301c14000180550701d146032186008440150074030a00c41034060601030f1168113268142d8109008000c14003403a034103a0503441000741903d0700543c0080100f1460301d4215182003010640304203000c00840c1c4400344507500c0d0006030140e420100303030b43c83c40e07 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 217344937 1250 217343687 217343689
    0x91305100b0306130b010605091503070f030605061c09080f0304080a12060821220801140402130f060306240501020f100e01061703040f331205180606 66
    0x45120344c1006050361180e4070040200034001c0c4000e00211401400c41422401c03400f40c2c079001070f00120b5030400814028002d134500c1030740c1403040c44050a012541241403090209251010380c06c00046443d506a580c0348040600045c0ea00f60784194490000c499601d00d8a031030185040e0b00691182008940d5081d401401490319014200a68444500418081c824046061030b1111654629007001c0c100704103400940c80c10200d8410020114001400700030718280040e800c440000c0200160044070900703020040c0d0321180e126100002503a404140c064500e141800185055070008005519040d199504144032008900c1200c1e8240c20000125070750310016170700c07000c0310b03202d0302d019402c580c202c0b03072007800b641e4000e4800c0720001d0000280789458214512101c903070000d01c070850364404241001902d01f101030311070140001203e06c088111140000144514020388040040514032459842c00c500c11419040d40c0401400c00340030741d08242d21026000e003e14414900745020700000107440f = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 217346187 1250 217344937 217344961
    0x6030501080109020607080306010e04060b0a23040302150409060608010306050a0903080c070c0e040f0506010602010b0105040b09010302120c04060f03110a0c0206040806011409061905091305100b0306 88
    0x42581c001d40540e1400705691f841c14001da1009080d00d06019280455900c07540341c41c850080a090801e40c071582c1c1c2c050154015000d020303e0409889400340c0c141d50594071011140c00e031011281e060f19015800c3d9209211401d5602458103d40c2c0b15524000c1c002510356807003000309040f01d016410402003900e404050342c081c0c4039944005004186901c01042d10820444002d10700305018800d040d503c10349980f03081101c26029601912003440d07aa0144040c020180310540c0141081d0008000049034500060a10b001390b02c601203c2e020003280710041c03070f4040d40444850440b2849564504c1c5000720058216411600460000444e0346651100c0580079120b61030591000300d007400e0421481c071310100c401d030211420480c1c1000040c40f0005010004001c00d602030020004505c500c190b050040c4132a4002c0244014400c000c5503895101c00d02c0a80461820380e1420b4800030b40a61b030704a001c855072910355200070100d124510b414800700031141d100c0c82c4e109000300d00741c9103242c0300d400704004 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 217347437 1250 217346187 217346201
    0x1020c031b06040902070602120124080a020f030901060603060501020106050616060612060501031208040210081b0a110105060a030c2306041715220602070f0c060305010801 76
    0x240580c40890036240d800580c28a5000c90750008180b24a00340e2115010410fa802400040320700d81c1c0c01140d0028012a400321060142c11000307400c5100103141a034074070420be08003030303014180302c0c3c00b01c041800c00302aa01143c045011102d0b106903a030804802c001d0003066280b00f0800024a06800030480e5031040c0a01c40840b10014040b80c102a5201e008a00c01400c0d554100e0344242d0302e22002401c6502040c046000e107000700d100151f103615508081000c0c080000010081290b075804200043ea214500481c404c1c156260400269860303050181c14060300c003200455181c000306018808982c030959221190900702d000f84401d1301c0340000e02401c0c100f18000140201032601c014071082848040061030240071480700054100c0020200325250710a40007490409111101c035160380b02c00700300b40c1c40e0107050b006811599142c01074202c110003480050f14402e02119050740400d2021540686480303641100d0401403088152400d0881e010303491040300d022a060100004140c40b062068032 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 217348687 1250 217347437 217347439
    0xa05060c03060f040b04090c0605130f030206070803041407090c0201060506280302070c0b0304020315041e0309030204020406020c0910030f2334050a0b09060d1b030b01020c 76
    0x14039000f0361101080050503100c1500d80e0440d030390300302e1400407070140c170741c15401045147c07a59681c80f19100800c402c00b1a03036421051030040120001c10043c0c079213000701c9940d20703085184540c90303840f00d02c0d0000401c0d1080a249041e485000c0000c81c210599612450040038190000c100082c4d9031400d10080740919911040c0e00402c20302c00c1d0b6498600003e1f100f00b40106440c0c014030303050302541c50880003074640d004050150004000c00085050400c000a250324030b10150303c02c189001e80d00d9102201c000c4000c0d074052840200d484d410140512a03400107164000c00c1592210749900c0000d58031110000300030305c60924540482d00414801d1001402e90f504221181c0c644445604c8460803600e412002d020303040040d03107520007051018002c0f003a6a40110354980f41411100b040c40e203125000352810025891f404104100b0b0f9660749100c50304a81c5101303c031a40b40c0c030741c4100240d03044c0280e021414a041c14019000801e0240d0861043c1d01505520b041102c00d18803c01241d50b40e403110001 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 217349937 1250 217348687 217348699
    0x9160e0703020f0c0102030901020706050112020d1506030f060b151c051305010e010608060c12180a0b0906071209080307120f1404020901080d020703031412010303020a05060c0306 79
    0x224603018841e400400b41d030f0008094040ca480400b1001c142240d1040711182c0003a5408a031120070000c09001d40d50040c000c01000b590f04035415000582000c920300c60003040070942e200307040480451904075a00642e00702684040d070f0304d8103090603005001c80c07001c510f2251468445d151000e00c5044180e0344100800c00c9985a0034072103c01142c010070740038150402c00500800801d001500c01d00038240400040340010582510700400e4601c4c0850180c001440081c050181c1d02e81c4414a80ea0907911807540b4010190030440b4800351400d2008502000c0e00640c000c0c0d0030800335040000b4064050006569100a212405101d203001c86000820041410b202000480c2843e8441c203862035882c0c0307403c0d1000952020f095402c5003280c40300e242520170103050608010940c43e002c2045801090000301912845207105c03002925180e05020003030034000b800c01107018010840302070764000704008043c4000380d40c590030040e55450306504200d947e84501400580d43d03802600980f4041c81d405054 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 217351187 1250 217349937 217349941
    0x15140102060910090302010b060f07050d03060501170618040b040b06061309092a140406060203190e03030d0501051e01020601171005160906080919080c01090b09160e 73
    0x240b00041c04c1ca164041e4215900d424201b040c0703968260042101150049406943d107801d0310b04107080864103094441403601d445030400560740c2042d200074250175144071021181e699600040d141c0340d0345081c00044410007400300001c10019400a9018a001d084419041da841c1c908101480c407175042800320b410402103041100c5946a006080040d1044070000320000c00d865507100040342d141c03010803103152020402c00000b040208403d440b2035082d101400b50509000d0042c0da20b2003040303001240050000c40d100d440e60701c03469100d1006d58005080c0e13650380340c0440c011009040b0a00443e4410307a61500481e006080645081030f8042d41a00030380711580c80d00c55441d181e02100d64444e00980100380c6910b04980d444e00c191442801c049280b20310f020301110005040a030313150030210500c9440750600000000000c1c480524903405074071110201c6d060b1810078500d000d00d5054103203940c2040070800403c075034400e107a4171038030651048801010300324240291070713074180c03141d00d038181c2c41c1d040 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 217352437 1250 217351187 217351213
    0x90902181314010209030a080316090803070305090a080709051909020915150c0609070b0a0212070201090302190504110901140a0512040507240806041e151401020609 73
    0x11200030802c090b94001414001100042030511220b14406c842c00380c000003c0140244035004055002100d40c03402c8000b032428401030581c0c1e0b1142d4907000c0e041c030070007003842031a80d07030382010740300c050312804003624110717680c0d061900d01401c416160103a03000c0001c00341c4910551107208241c12182c0052008056858100004074800e48041545820154000302c108003507031504014050b02648100403c0c46140c04803402d82440b450350040400140300b04040544142d0014080e0b041495181e0600e81e00d03441c52005940c0032407150310094000d00e0181400e4034130b04039602c1d400102d41041e103041c000d941c014401240385114810300e4030301280c5034182e000c59110410b005000701102c00e003071036454200700800d0444907920450302110668800c49042c0130540401d11000311046005a00300700035459000050100040202914062a6126148a9000c1c43e01d0320702803c03010301e804200010ba41000c50300c90031113124040c000c58140c50039841001c0c1d510000304a485402d0308400707000450356400c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 217353687 1250 217352437 217352453
    0x3020a030c060204090e07051503040c0e150a08010b030f071508040609020a03150c03060608040821070203070203190201140c0a02040501061106090a05030415180909021813 76
    0x94026a0b50b141c1c284404100100c4a10540d0035150a02c401806024a010100407004042003180304003400e0900c03d2000280c62554000c064400300981c2c0c605641c3e0b1382c10602d0000c840c80038440c1e8482103110001a002c0c1040d8840d0301c10740c00640c152544d4071000c056107565943c81e0b21401280070f0b4103142d00e070310302407040401d50f40091007500003003215a003036000506a148039400640d0741d06039180a00e0342201c0705215002e494012405c041c040c00d8a440030242c242c0d00c0043c000780800400084403880500c1007510311115601c440d00b19903460920b000d0080d641c0e048848124000e214001d440030310b00f1a40c4c406103c140d0390503555040c11075400042000641c11620030f901d06840342d82c0c51440180c1c2c1d24000c02e030107055a95203000402c4800d02c11070385401c00190440090760003403296117011420100441b0305482400c521440e042e0494801101c0d600410303002c05103101c04012000c01c001e03102d60041100c1d01d000b11100c1e0030400785814001019070060760750680800905820400080e901 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 217354937 1250 217353687 217353707
    0xe06160e12030d0501060824040b0d050d180801050903030a09051903020105220b010605030702030d090c031716030c0f0816060e01020c10020702040b0a090615030903020a03 76
    0x1410000880280110003890354202420800080b6110001440f006d94881c2c000c990203129810001400d031000340d214030703000701c00e0f0195034060398840c09521002e858104100e10b803d940801110b00641e581440141a00f200c46000520141111400114048140525809645d548010b5440e54403201200e00c0103010306001141c031405620047c0800a240c03121a52a06e4020780000c00d0a1401006254041c00b1949501c0201c411030718090b0081402480802c2c151002d900300386503a901c44040503440c5002d0404c1c00700044c1e09100c0c02808200300b000c411421170340f0441408180c41c00806250409016481c14803a03508400e60650001c02c0c0311b0010300c0941030190308a000c403806603444215443d4070040c15044460a01ca444900304001481088042c003c1c2318004c40c01c0030403103040103454002c0c061003041c50700d4010030100b00b50340e9242e10006100300028540110306aa80c007180c00580a907100b103a00c2d120040740c08210840c001c2c00ba046490f82c0c140d001e4500b20403103540641d244401 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 217356187 1250 217354937 217354939
    0xc110f01020f0304080c030601050409211b05070311040507020d080a0617030910020601142b151401030f0605101a0c1b092802070b06040e06160e 64
    0x4040b0702981c040d1083c0001c1020700030701c20240c55584000c03807e1514064040c0d00c098000d520b0081d5032004241070b940008480e950f0740464421245000c0c00c102d540f00c60049410329040005240d500401c60001880012a40b04441604042c9072400401c0100d031001c83c0c15902681148020034003c1d8802c01e18158045505040014403646400030701e41d2240d800c0ca21046142d2000800c02501d181034105820788660714401001076604120011350805081004240105c0c00c40d448600c10108045140c0256514040c041140030700c0303030400c101c541c05400b1a00282c986016a24124005c440f8070150581b900501a100b206030766940c5e0380000d103001802c05000100c40b0001107011941841e203181c2c140000301c0d020b07490300c02d4010114180398460b0039184010790202081c03052511104402c42d071041008148039000c02102a000074407000901da030521300c42c40000c00340d0420501e01c41072030090000742c90410541c800d44a10382d9a450064401111680c2011448406140b00d00da5036008000 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 217357437 1250 217356187 217356193
    0xd120e0c060318100b010216060519022a09090705100807021507080709080705100e03070315020409051e150111070803030a0e1606050f0f03040c0305010c0c110f0102 73
    0x1d410ba0406013820300c841c00c1c18040c2d580310080300c0015a810007840001da09050960198a8038000e00545248180c0400552845044050b03880300e0b07000b401680f44a40034030001001481002144160311f070510020f240c421350b80c40c4040792149100140c17140c11f8400c00b601d401408000c483e0143d40c0c51200600c110214800c059070403090150310310b03100d0700a048a8486422a04151402802c0c076001500030384103640c8255403c01641e0f44800300c20043ca0814200204131085070340c0481c0c10007000390000341c50100d440d50824005c1c0d50560040048890902013002607490300f60811440e082400a108440400040419013012402003c4032010005051480340c4404142d8240d06165172a40608010340020080202c100c4140c080d5400362030700174010348464003421040500800c124040c04d000c008010800a00d079000314011100761040c601182c540b285441d28112040794031901081b2040d50030031028220300360085205c40002030f44801441c1c0c1c2e608200c020710a61103c0d6034107850442c8 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 217358687 1250 217357437 217357471
    0x501081009140a0b060c2104170303070e061c0f0219030231030f05120c0a0c05041104091e050709030311060712180507080d120e0c0603 60
    0x41c05441811184075802d88018103510741100380740201c80c0309481440c014401049107010100000c034680a26002c156040c122800029400784030502503a00194a00c5c05c8166080ca15401e00002039440b500322580c800354000c2da082c0c00c0c4102802000c0c0f80380c0c00b080b044403d00032118280d8002400f03580700c642c0014285480140320010710040c2c021811b012950000302e552992561200c040e581c403130400082c442d00a400814902d081c00075200240410180c200d2203010071209000c0d082900001203015611a02009040b68035446402021900304058a0001800381001e01480320b81a0442c101d29003014034000c442c201411000d400303400c2c4246c08607480c0d06c040c4d4441c407629010301e01558480040070304510300070304025040c8204003503551201003000486644100310351010500d0010100d00384d110418031500c40c0c0001a402801401803d40200305200d000903030440c4d400140d42d0380c8840000090170a01122880002c00089803c60386103840e060030694011901307c140c901e101002c074 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 217359937 1250 217358687 217358699
    0x70f0e130b09010f06081608010302130216080301080d031a040b010507021e090a02040806190b0d050f070e0103020d08030601020a06050a05060103060b030702100c090503061f1e05010810 82
    0x400090300200d029109482045c05501c1c2c1c07110519501c4080d0080c1e2042c17041c044440507004d80b070141700003846013410b203024034560541c540540300300c0005102681b039503030000c1c90074030180d030024021001c240c40b442c0c0400411600c40c1c05480c4042054110590451040c64140700180824818481c1400401c0003801c005840b0206c5900152500305d0814202e001a0300401485000150030340046900600040c0203e00c0c010503141c0e0402d4000c071800c980620b481d5002e00280480b02030035640001e01e05545014094042131200011100f14261140280c8607882c2c020840020300029401c4019500344034000b48001009540000d8140103c4245131035540d68501901c2d0129440e41d44640c480c000c0c0500d40d601401140058140820401e05514002000955881005844900254aa060118010380100980c3c00900009001c0e00d0351441d02103400c0d40181240d55808141c000080c40029900000e54102e1440d0080c4840c1c0001c010700d0003004503100c5a021703115000281d0181400186 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 217361187 1250 217359937 217359949
    0x906110f150603070e0f0606090a080102070b0402010813110904050c03070609030302071d0a05040204110f03040218010b03040305030c040b0705010e01051015030207080c0708060f070f0e130b 84
    0x441405001e4a4600c0c40c000040c5070603c0d007540d0021090511080034450890b124207511a80a541900c01644407440d48000500344481a0300480c0c0951000801800340010741402034800e6000784ca8500068503246000c2141c40c0000002801508000000c021340e0b04d800f041d8190803e01507011150001d4121002a041084940c0900c02003041d64408204044d0107000b560002c20b01861804003c07041412512441400100074904065594002034110341e2244c0c0a050110006044107844005121040d40c84da0b00a480a910403400d03061211204080441114140c0e088003241c40e0450f00d80c0d560507502034102400502d01848140700104502034800060030921b801030b00041400c080300302ca014210340000e0281e4484040d10503040c4600f058106500c1c0741c016891500580d80c50700b9050112482c001e84034901c41e68050000000f6400900084440c059100b0b903540301c44540b10101d040e140c90011038882d00c041500381c0c2c05441180b40a1101112021202a0101e032003111707400002c2d1 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 217362437 1250 217361187 217361203
    0x402072102031b0c09010b0a030609150509010b0405030a03050310030503033d0515090909070602061e07030504021810060306060507050316030507150b100f0906110f 73
    0x1a400821554881c0b1201c10380503a43c01e403100040c012455811011980c0704105002c0c1088401000580025440c881d41c071107030040003100402c0145450101000350342144500c0b8442c1300300500700011940340000c1d41201c01b21340005000348030305034196030103581c1500010913501e081170346a8000004160700f44011842211000700d5000540c00110304003440366640101c100801c0d00c4860301440026400561105036407040700c05e00c4103d507400c42d0840c4244101580302d40c01c4007607002070207401c05000601d20150340c00d980a0f80c02c3c81d5101c40c1c0c0480440c1d142050a140000450b001c00c0c0300c14043e904c40c90b000741c00a001c4061410312009540c05108050702d92103005172900740104020781e03040c410f00000e01624540039143c09400d0f1a1547d60b03000e55854042c162205070709800070540100202c50078580c1c0400c020920554800d0351a0050200b54249809500c0c0300181103d403600c075004e940c0780050303075407945044203007004d0086402540e5054404107620070b8505001c00400d08010801c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 217363687 1250 217362437 217362503
    0xf0c150302120a0513060f0605040608070311030a0c090b060409090c0806070e0303310e040c060801120b040213022803020a05040b07031e020604060501051c02040207 73
    0x26a40e925084510040202c0042440003154940801c0c024000100c0f024201e00396009800442c014040310191801018240e200c40d5019142480008403410007050002c11030b409003042144038948001450344641c40b0a20080020843e1403042c000e102d03041c4d0024841c00c4000d822142840d8030b0707400d01811156581c0c3c040e580081001810480da540070030003c0c0e446030903490722107500300000e0b010942d00e004244140001d407507212441c11129445c1d4100040c102115a0b2803280d29a80f000402101607042d203080d02c0c1080ca4040100d8964020408103040300c2c070020081c0d28140c1292142c02d43c03050090b2003268801000d41029044039098005020032080c0c445540c02086013046c18088004106c0d442402858014010424010740000590f42229003032120079903140f07964a811900c629060b890b03280a1a108030203204c565a0024a40b0700c6036200e80d0040000380d80752000c00c6100241e84200c020203140c032030303e41c038010700b0250090000030b489036500c0304401402441090b200c034203040402c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 217364937 1250 217363687 217363691
    0x20708041202031e0a030c02030a02060301060c330c020a02040203150a05030a0203070510020f03030403030c030e1b01050a0e04020c1f061a0307050706150609080106080304030f0c1503 81
    0x207519082c007941c030765000d4100315190303d0000a0312654586070071070405002e20501f035820105645080c089411080d5004010a940390b845600107007801c4915030080c4c480301003604410543e804000c850800c00a1100001841c0e60b036242d01030720180001403c0102140200d00c013002c0103131958005140610480c0b00104d02c0d40030307058144517140c607403640300c6846948a040d070074000d03840205403942900c00c142c5000c060700c00080d805074030b80410b070320b0200303118400041004281076155100080180075903406005284904031082c0c2e4890314a06e03041c0400306002c21100c1158061030051076601000c5c02c02d000200301c04ac00040032a0860030408009412440800d00d542400c81556650000e03030080c104650340c01c0001240400c3c001006c1032103a55000008148058012010f803940140d00c5401840020350303a10141c544003030140304180108041682c0800c407144113016880950704a81c00660420313165484564000031031803404e8a0022040d440071032202d1038404c1c07185402d1030607200 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 217366187 1250 217364937 217364969
    0x302011b0e040f0209150a110307030e12030913020d0b180106020c120a0b0408070506040c030b011226070b010b031b0c0309040902041b020f07060302040509011802070804 75
    0xc2c0419110114500d141c1c041c8108280c065607a5503058a0314201104c02420b5214000d401090b6020b001d48003075805030b8880450b4079020160312203502c2848140035240290a160003840d0a50790303000f038012440c0d110a000c146e1008108460b409002100081d52021640b8081100850f91b03040050096450142e10724006105440d010080600001d07420389045281c074144069850319a819541c00400c1c040502d008a002d00c0b01ca070040d2010f01d41c01000b603a2107414240f4010307184071028802210308403a10400060a40920039004140503000241488014500f41d1102e1000214003421400d54a09001e00740204040d410301a01034070280d28030035a0303820481a1032080058002e0a20444082080054480c04020050790300c81c07a0290350100d020040751001901401403841c92009241200042d488100c1e800070b06980403991140a40f1185070b115902141a48658007036a5040a1a0001003203c8101841416840b80040c000142803c80030b0781da510580d441944490240c01403112 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 217367437 1250 217366187 217366189
    0x31c1d0102061611030721020d0503100504050916151101020a0c08030a0603050f03270a0e07030905070b07050c0d02010e04020904020f040b030f100608130302011b0e 73
    0x91420800240020182e92510041c0c4858030024265a281049208180081d1101041050b1600c044d0b000d500041c105c2c41c422141e4480c0c3d002d0b1010321006101d0b03100c4601a55000d401101d005001811035680c0c070904100c144009440050854071a41c480c0380d215107160700724070300354001502e01c0c407048420500a040f002020f07403402010b80e0010764410002011580e400c052124142940003000584035a50200120014a001d500280c2540900545401d004002000401c0c01c00d0282c00d0b40301942d01c5101c010781024090001d13590300019460030900c10524421a083c3e072080c06841d020500441694885080c60510751003021215404210941040001e008071204450b09542402429556400090000c007588000b2402264002040707000c81e155038044401d1031044820b101d944a40e0340f484405180d200701c401c1400d040c402c50104040c945034010140c100c52465940004681312000f40020214141808500303541d6101404134190030b4204100304980c50b076880f002002c0007404 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 217368687 1250 217367437 217367477
    0x80405090705030c0414030f01060b04050a090b1008040f050304030c0302100305040c06080c25030e1e040f1b0903140f060c09030307020a03080403050118030c02040506031c 76
    0xd07048105102d018410416a14200c90a40d0110380080e010034030b42c039181c040424204040280503e04650038503802186440e200401002221001d55100f00e60315545c040320401c4641003103040da4400482d040049180c1c0c81900310320380041c01807030044442c107201d0352142e15540c040e1348120348469080f28100300307615103994045040030b1103040074803d518155545445000340c50007000309000c05500410402000c5a0942e00ca10b0592000c907402450786c0912541c0451198074124006013003018500030500f08510005e15984540c400c404400e04010100006403440c1e0a03c0f0001c683d4414640d00c03000c1031400306402d0321980b171b240d60082c40d08504140c446291030f0f0050b0324940e4000c0e40042c1c8910000206a544100080c0c119500c0c0d9809800080c00c3d0b00c64504041e52000d0031520100074000000014000c40f0300c650000c0000401c007030f02d0050504164000540070410010000026003825080305503c14002400c0e5843c0d85003011b070358a8810030031000c0500088000031400200d030701c10 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 217369937 1250 217368687 217368691
    0x33806010212030f042d061b181202040209090a020901030e07140904060603170c0c0406050117040507080f0307060506090c041802040503030d0c0806040902091b04050d08040509 78
    0x142120b14501d8590900d5904c510040c000401c440855030011207619580f862440492a401000300501e0140341803010140c200c0d0100c15076041001400340000318051010f241304403120081003168145810703038a515000005034280e070015001c00040703203a40e03a0302d00d045120710b1203c01c0068582012800060484065600480b02075110340c00500540d40c80b8107401101c080c0c00c948064050765a031030124054a1644e00c000d190103d0746180c066119040006014401d800c50105c0c1c24170392842c000c0100361840c82c407650340441c041e4901c501240c2c10b10b1000d01c2d40103004404a4801d56a120700e040d29000f05e4101c403000e0358001113004000c0044500070b5980001c801c40f0258014104038041603502c0c456486081d01c190002b20041000c8955a0140d0380200b900030240c0b501c3d290b0026850b0301400d1603807142400244100d000903510300d824800d0840460f000b401401c7c0a0390f03181041c0742c0c91000c00048401c0880240000a0300b5038a04030381d0f19555100390140ea488520340000d0025210700 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 217371187 1250 217369937 217369963
    0x7050c0f0609040207050c040c08010611070f0b07020d02092406030402060a031515020303042d021903320f100b0a030b0a0e0d0302070c0338060102 65
    0x418400c50481e0303141e0302a628070030001c840050382c42e003003840e06510307280d2020030761508541444940da140e190071030750450407101c041e00c6540d03807000040740e180d85400060150302c0094000030307018010214000c0150a189102801004820910360001640c4010403910714030603003c8400034520f03038648841c2a40380e00c141603604a01b1420641d0002d60745006040c030321810183d903500907038001038560100c0c000602403107401c0903403008013120081d00c03980b04403810381e000700f80d0303000c1c041250802440040a0102400300650700407842c0c0d08004480b9100381781c04600040300c0c1e9020020401120214034204240d44810a0320b0f80060191013641d0f0b520744000d0801d8010407040e10400e01d010443c1d0403001040e40000408450100c005011004150400303401c00e0f201d50b080080400695004002c958800740c126440c048006c030084069100d1104010701501d5840c4c1d04000117003801540047c4400303036020940e80256000d00040d40114203980d86014001c1c0c24003400310658040c003071030024a40e = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 217372437 1250 217371187 217371199
    0x1050114030d120c091a030f0c072102030f130503070f0b0d050618070c0b06030105160c1a0c07060b040216080c010b100906030b1008040312021c0207050c 68
    0x3442e4480509500340c0d8030061100c40d500c3e51010310020b441010128050264034002d07440c0c4000b50740c0f1300c100c69001203072803000c00c11102000c595981c9088080d1002c055114003210385281054608015400114400e0003c0d444148403010020020b000070380300c2081c604801a41a80c030f44000c0501e022410f91101240c100442c0c0b051058002d00c0049800299100e080414103445410125608030014090516422100400c7c0b05040d58050702c000b003407600851300384019441e03d004060880368250342c0b00702c009148101542c4070714025588400194000c140c200040700040b1030324151a44103c03404035420000085071303401c0100e94850101000000e0381c5c02c6061500081e85072045480c004005040c0141c041070169405400b50480030b882d89c0060280340e4500d05520004d05100998026080400d041c0005624141401039510507080f170035654140f0240c6450700c095a040368911400a00540c08100c40d00c1103102c1d83c60060465000d40c00b00581d00c3c0ca10342000343c100610584001e00c154 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 217373687 1250 217372437 217372453
    0x10b030c09100501180801090b0105011206050901060f09090501080309030d18090f020c013602060f0a020a0503040b1b01020304020102120d0b09010308040906060507080703200105090105011403 85
    0x10151000c004183c91003070901500d0419001540a400c450b6544482000d6091006500400c8800101c8034101c034070a0703d9069000e0780e030200c12829140e80d4014290002102c000411400d40720f4556621443c41600f49500c2998a41d00380d034040c0c80c400d801c01940c3e5400052038040b142410402c00e444801545845921f103072428115404c040411b1040c40011911140003101080d056411180c0c0d040b4810001c000020406881607481501d00032224620240941c2c444582d20310350282510081c0e006201a00d41041100c04c00065081001c8030000c40c8921041e8500280d8200001e00c080d009040e0f985440350305c8140e20844c4140048083e000070307401032080c040180d800081846810903082c507000c2c0c544042c019150700030028640308035842111480008103009200008106070303002c50320144807040c0c0381c8078165250f105580c00280312040800400c00860320680c800146001401d008100d06520000b050f804e581040c0c5101070740740d41d03c00040100c4450114142d180403001d0f006040b1007 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 217374937 1250 217373687 217373701
    0x1a0603010e070c061b0806031b0904020d170c030d0b100e0409050c030a14060c090114030c070209040b0a0c11120309030d020c160f030f0602070201020f01020c010b030c09 75
    0x3204002d400841030040c1620584108400c40d000600c02d840c03082c42c4901e814038030f0311004140034029202d490090040003100420159560403032841420064851421078032298280000c00350400700545134115000c11182500e80e000700241000c150b11001180ca45032498503034004c94140d983c820b407003104030040105209070010212103480004a90001e08103903182031690a190381084a00c2d4075000d03040038a01000f001020800c1812a01c03021205159a0b24007206828071606c2c0d8001e001c500d03441200740c406101c000080d41d118015070b62560510803580d02140008209031421110301401c8020040e8146691003140f001c01040d2400c403184154607a050342e1110403010454188000000005140f010200304603010124242021940d81c141c07010145c0d198411b00301c0e064031070803072481c0c001070401418889809481d0080300e6044c0c0203920b6690300d4002e5001c480c0c00c9055005400250745405000c0c4040d0110360003003400890302c8144007007010700b03142009001c83d124a0140b0144900 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 217376187 1250 217374937 217374959
    0x8040e0901091205130e01120507090e06220614040204051e060d050f03030403020304080f0105060a06030f0b0d060f0c02120712170a02130501020c1003021c050405011a060301 77
    0x42051400c0c1140c1e101000d8101140c5c40d0260b410650400000c0c100010b8003003003131010b007450136001d1415200b805440751044415a074043d107041c4510b9004002052030410481da6078180004000c2504003418100e40e1424141d451a0200c4040c08160000300029401c081c0103140c4d00400d40011541020fa110300b40581001000d0000d234020203413101d0100800c9401c01c00000007906200813030f501c91510f132400a68a0348036014070f188030700a9503060030084405010300f0b40220341c002c045070741d61800c110b4200e0040100d0004a01c50a44603041001540c8801d540318461600903503020441c003c03580740d1001581d800c030107280110352104c032410401c080350106031441240d000d08083d44820849400f00c2d10060200016094140400240441408a5801001115003c0d200902003594800c016611030f24914011504034440c1d21800100741e110740e00400030700490784840f40301c2d080342001c810100c5008880031220b50303545940f02c0450107070750601e0102070300084840c2884d41d0306007200525 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 217377437 1250 217376187 217376213
    0x1804030f120b15090418110105030a06090e010f0e03090603010e060120010b01080609010513051906030305090315010305030a0c050c0d03020d090501050c0d110705060708040e090109 80
    0x3040110700c0c0014550004260000022200014031025411840c0030081025030f03c805030700340c40b42e440c2c5a03441800002400c0a01d0000307400c5405800c1c50791f00c0b00019107081d44014120f040d21075991031f012401031300f24072402100b10041400040c44080d04082c942c1101c070780340d44180c801c2d842405403d0b180e90701c5d1011681582c00f00d03c2035922075140d0000690f0301600443c1c4103074482501008003c000541540a075080c0d41d0241d8601c410f41c0c4540e018020318040038021281c1001c0038013180c1010f201c25401c032503000310703012004101091084040501312a0142c200700d00040700004c080c1410329003001a6095074100203840155549150381d0f880d5a440350100450030b100510000c00d0034400c05029111084c6005800e0349000c62080c40d00a4540100d2301c41c1002042d6141d80110b40b0754400c000780c540c06046080140f0190690706c500f034603c1c2c0301e45640002c4520481002003569222080549206403050704881d46640c00c080c4c06034005040103140c0d00840e0314010700c10000c16007400d1100c0c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 217378687 1250 217377437 217377467
    0x130303051e03130506070801030b0f180d03060f0e1005011b0602070807120212030a0b030c030f010618020a1209020414070f020f0a0b160c0b07030506180403 69
    0x69655403510710010708008140d507440da11104048100241c1560f15640c0c800d42c0d40c8034a040c0c41d980c1d664401d0a664440081c0000340c4a0000c0c1000103050b4240d0040380d40e00004422403440f1030740300c100d0f00285408060000d4070006603c40c03200304940c914440304103000e0304903070780046154545040c1c44c2d9023001c4148250741c100f01c8080d0200803880500d410138400c10743c000905542d0f41e04d19040c15501c0e54000781e42102d4030540000b51484162022400b03010b0700700d00c0f4400a02d151203c2c0007000152540038603013540360180c943c0070f843c2a501040358880040c489400480c603a843d100703801103c00d00c400c400b601000d004200702d562065000c222080c40782100c0c20006515074441c0081002040c0d01010120120038200078800b0054004050710485030f0b4076801c40d5541e01015200a848800b0f801d40186011941004070b181c2030041031401c008192546031030764100790540c031189108481034900e0f1020940d1a4203008481c00c050f10420340c01c800110104072107040c16680141840158008a = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 217379937 1250 217378687 217378697
    0xc050604030309080d050406020406170f04150e060a14010501090f06080a0603080c07050301050c040807031104020f04061e141b030f18041a0913020102102a05130303 73
    0x9030101320364031003600d0200e804000704100a01d0585000c0000398043c0c010500070458050111076800514120207203e1071001442000c0d545a45e03481c1800b80841001200a041e00d9041e4103281000030001a4815080e00c01301251510001030404440803042c2c02c1035040001c8060300344400003004188004860480c07808030303030650f00c0080503c0200b1a503080282060000114600c442070005941c0c001e0b04d070110020001d03505c40c15a441c8844c03045210380c95050f001414204042043c001200c81505000f4001615100071125007039182d9000d42c00c9800400c00c041c2070014045503075040d00c4400c041d2400c100c03244903034800ea0101c0c507010b0b4001c00c6051661007076444600317020900583c1d0003000d0520303074282c0f90f450b403540c0400c080d40645141805185041c1d62a62160100840048032810203040280301d03803901060b03526040200c1c0420381c1544102a106442001c0d0b074411030305020b9000302d0070001d12840081c0301407440d80080b400310412400f800500084040302500c02c04403036050500b = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 217381187 1250 217379937 217379951
    0x9060604081e0a0b0406090308101d0402060d150e060f0d0204150302040c02010204060339030902180601031503020901120609120c03091d06150d0c0509010e010c0506040303 76
    0x503807807070400c1200c002040304d0100000d0004010490700a1203280d8480e4451105955405050b004031908e2407244000540200d0300c4030943c20f10b07954455030407600103050249441f14244442d01511009a810850750038410300c00c004032a82e00380310541040b07045a011706140c4010001443c036040841010303108a507100419032150b8881d80a04004590150042c02400350684000c0d000750854420800824146200c0d040354190340d201c48005034440341702c403e061075403140c5a52107002e1144400824940d03140307401c1c405a42c0e1000710100941082c4244803c40c0340680004040c0c408004510401c0408110b0130b0006a4800c66001e0644003040354450007107036241018005044501809444050a0f001c4200707882e0b0b00a40c0200024000e44490381c9517955241002030001403540c89400c580310307123804140c2a1030700410340c0500b501c0e58800740c0c1c18104126068022603440000080219100040142c03031541c0100360990381107003d00701a00d0100e115198035844600061000303080544d2240 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 217382437 1250 217381187 217381243
    0x2106040902031f060e04020a300615050607021e0117043509040902040f0f140a020a05040e060109030f08040e160f14040b180906060408 60
    0x100c00c0030015001000c0b11020382c0d0180011504100d2008511020f03420104045030340e240100c40c141c0034503405060944118581039159850b49080202e8010b5404000b82000500b052450801c5820f801180c0020341c602c40c005526511086540c0110b00444043c88040050390350050091544400b1000c05118044101d0048440300724090180d00480c2c00300d0184004d00540742908400001032400000d0102d942c000c0c1503400020781c0c0210741c10b5170010030036154281800d4210142561004c0c00104810003c514802c095604e400c0031001d5440d51a052604404c0305040d00380d41100e0129011032402c2e8011800403e07600c51400340664114003403000c150980d01c5182224000c0d608104007030541010703407402400da80d0040c071410204290040208840c2c10010f8810503c40f00243c0320302b800c1a811405c1a0740300c50070101d892a4088060000290440d0002c00505952680028070701e103000035041008551f40c000750110f4020710062009200c900c50000350841d0203442d5000d80207000907404 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 217383687 1250 217382437 217382441
    0x302030106180312081506073f0f022b0e06040501020709020702061201080d110c011b0f0b090c010201110301080d1b08070f0b0601030b060406030903110607020a0b070302210604 78
    0x703004240c01240014407235061110000710044002c0e40b45100c2403d00d000b00c10f480070141145401414030f8200d001141000e140980c01d01d030041c0e5414010368201450080300c100d400f000e80400d10f03100a07016005d05001e41c1e401070304044c404400311010b600b083d0810000030354810084c0501d606a60740080c04e4015951804152003203055629010340084d80c480e81001c0d110070815144070b0108845100d0b401d2502804201c09680c2801a0350b130310403240301030402e441034090303008091b10300c0e84500d4000c0c808640210030301d07407149003900c0c0180800d41d16074000900b10381c0294410360480600380018440d410020500d80d445c05c0461401802c00f958016031001350008811004014403000039440c800c205440f040c40c2c1c0707818042d00d880041551500019000c0d50301001d1166400001004240310481c042d500002406d4042e10b030080c0b0300c900d03c1c0c0b00c03245480c2c1d05032900d5015070f06c045042410003451800c102c0d0b012010f89400d43c04c08200107131510400a00400c0c0b90381d0a68120000340701d5444c0e40d = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 217384937 1250 217383687 217383721
    0x30c1a042316090c0807051606020912011a131b030518010e2103060d0b09032a120f03040807141506030105010906080303060d061b030203010618031208 67
    0x50024200d0b01070f40c40e070300c44008010f42041d41020402101c00138014030f00450641d1103400012030343d600028a5941d41070002d40c084214254480400b207504071811000b4417810a82e031100360450b00340000000100310700201c0329546011a1820010413607140e2240c0307000007001e45a64140400d40b0707110ba0030b6072049290300700c900386240e42c03810034940c618040001e41945074002d80420110400340c0488060650300c800c07030b552500042c591014000143c45588072039800007010003924204821003a05000901040c82d0b0104910360714100400034800500101140440c030540440c40d181000302e81294900000300080c0482c40c02180d14420b01c01c0840358420341d91a0202031b104400f0498020461130001a582140070798644000411504124071690302030350580b200440c1142d0b50310301000391186107a801242c80c1c50b210340361588020a5152403140d4404661009600e030340c1499402400341e11a01c001e84001248030408002103107032246a450a05500c0c6020042c45c0d450144201c200fa100c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 217386187 1250 217384937 217384963
    0x7030b0711101407031103042d03050409050a090302070303140d1d0c1014160b090a0302061609060507171309050603030f030f070e0409030c1a0423 65
    0x180502e800401d110507408000b1061480c00000c00684613000c0880c01c440340f4800d6200b0b01c0d8810030103c1c011030500204001c03c13044d03081415070040020008030f611244140411404035001007410721140081e80030303041e4402c020842c1001110030a8a0080d52144144000790a01801a8190046c507900004450070b0005402d41800b00c0e402000560060a5101c0315a0b401402401020b0220f0724001c03050034007ca4456441c049403170040421015940d0280c440302d41008107400410001175400d00c850303449421407030081d040c440d02d0750401034244400104468425841180c50000d5140c01c801c0103001d9400524110b07885223041c0c5454045006e2030110042d0802c1d0200b406e64104185043c7c0070140c8504000031712a84c1c540c6000d1566a004014400c01240c100340700140404964249c2ca42e13224180f480c000707002c00c4010000c20b044032544023042e4001584901c1c01d80a01c42e11045810f40c0d100394000c050410f05d01600c410030040040c241c0322803030068032040624440820000180f411003 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 217387437 1250 217386187 217386193
    0x30b0a0303080105100804080405011206091803080108120d0509030d150510020115030204150914011a0306131d0f030301030308061c06110412050f0705030c010207030b0711 76
    0x180364107000c0d02c0c0900910030709106140020910b8041482040e03200c0c006e84c0d00240e07182c2000d00307010041d04c411a084562840480e40d8610000c1c445209004038840305814410703c80380b00c80c841c00d00034440f002c1600292915809060380c20441162003084569180d2520f000041c6504c891401c2400d601c00c070381c441c11183e420960404070900d501c01040007120412a06800c0c90490440141d007a60444a11b810301200510780070009810113412a650f04101100c1d509192521088101c04490780c6607451901070314140011300030002c03150380d542600314203c3c280d28107625015000501905600108480c00340d2510004244442645c2e8440c1d583c00e07251081d2018100c100074490350701d8000f48400d4001400b400040b0740c1c00d003002c805022410f110800c812042e0f0200d80c80304809821028a003000d4030348100300000b24055814a090420b52099000c2e100c500c410f0b20604d890301d00d0075049940729401c0300d00302c0b0950303a030002450011654400102030f407543e07a120044c1c4120802c01c58840040c0 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 217388687 1250 217387437 217387439
    0x81f05040507030b010e030a02010e0906060f030709030c060e0607021908070e041b0f090504031715030607030605010c02090c0708030709150c0f2303160c1a0f0a030b0a 74
    0x540507006842030b81400e0742d40c0d10031b02106ca41010359460003110042c2c0841d420f01c00c0e200b0507003050780b8074540c018009415a4680001c18686682c10703031040300c0200001e0110130303041c801c0003072081c8000c006250345d10703010a52000d11030002d241ea22910000070710506c6140341e526046003e020090307004100307482c103484800d596084442159541110101d600c4e00b00000000b92100c501e0100c4030664150b0b201e092655403c2985180003410040d00a509000741d00c41c0343c441c2402000f071a00e2080000410b003030000e842e41d106061400c40041c0a02c820b05003084420b00549e40d003e00f070100c0050f0102e90889480e2902610040319118200c0054100f803000800c000003141c2106e040750881e00c813030000031200164804100d42d1400e42c0403000f130211000000751004102e2086008402441c1e02d10858060890740300914030319848402851454640310044070180070107517072220020f0a020b82e84201481074404440307100c0c8510800107039801c07404039105c07001a01c240c0c020350f0f03d104044c200c4803a107 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 217389937 1250 217388687 217388701
    0x7030e030712020f09070203030c0a031803210c02061501091e08070b0301060509060703020c090921040503150405030d0e01050414012309031c0228081f050405 70
    0x240e5070b4000c041c1c0c051000680500d07000e0402c8451148039180e55070145085481ea40440c9500707a024445103010117464101e001e01d40e00d80e0340d04200810340702c0e40322141d40a989101b9407030121000300b2030390312003480c05406500083d0041682c42d03000d04040160151800c10000586251200e5000b0802030101c1072100340f0902011102401030b540d1003403c03154420380d14080308600d44008d010303210000301c0c10322601c0c00c02d0800c40040d02c68544a03005945041c0d8072240482c09140c01120711811030b5000030195a610000040d401100c40c1240c00391170324042c20b000100e82e480c03407070340c0b003802142d10603900140c1400003c3c410f4541001d0803a0381400701da03c40000c40c034060103041c2c03000d85107009545515503150130140f050000d0400400104020140c00907000041c04d40002c003100f085010410001e1f42d03041a83c0001c020007a0704010068a900034101004030b2204260941c00d071141d481481c08164a40082101c2d40c8565002c0c807022250b00314442540c2510050f600c1190068104000e220340 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 217391187 1250 217389937 217389959
    0x903071703130e0709050603100302030609010b010e0a1a0d0605060c0c030705010f0e0f01090801140f090606060f1c0f020c0d05031302010c0204090b0403081005011403070507030e0307 81
    0x200d04001d07001039541c3e140c1c0c07641c4500400c00d90f104c001045944004200606048000d15404840c2c044030300f55940e41d03070700400d080a1084546c81040e95440d0540b103078568000820509116080c1d500c0e180450038480f00350002c00a8110f001100d40c4045500409410a60451005000080c1241d80c0b202c00b0052001c1c0c0e10300311299494428010303404081460b52081360341c40720450b010b17503130707000c41103404c40500c4a51a846902c29041000000020940e942c0034081c011840804002000b420b01d40551001400100a08145550b402000901819070f91304800c0d194200150000b0715a070300c090b08088245542d4007801035200d01d050403030380303411660541d000d424030110042c25940d42c80e5100300c080303c031403200710b814a2140c0030340d14212026510036400392060500c05400001d8a428680700c10045c10320848084000541403c104001c00c1c00c035401c401c004000a081680c042c007510003412059000c01081c1204200000c6407110506100381c0aa2201060240c107880d0160f44502410744 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 217392437 1250 217391187 217391197
    0x30a05100f02131502161d06030307050c132c0616021c0203040e040b012c28050109050115090f090b130501091407051e0903071703 58
    0x100d4500712440e00c1c0007a690080710140701e00114035410203810b00b026501200c061002c2c050861082408000ca88810151120060400e40e1070070f00382d0791140c000010100b4402070140f80240c1060003068002500000c0088a01c003044564181c502d00d20700100d0002d2800100d898052009548001c0310a84060000400d5400030015120b5a031b0310764070110030050140c004040141d20030101001056412804a4030300c0c0098030540e45400d6882c5c49800703446506680036564940f40d1401001031000c05450212920410903003c002c0d140c2d400300098003031800820040720315002000030003070250501a02d01c07602e0580ca808106950b1903a02d24030040509000d02c074100e1044405030094240108210421a014140a80c000a05001d028006441c540d002d994004104a1040c00c04d0324850041300d0107003840860004004c200710360247c0e4016809050002442000c00c0400c18050030000000c50012003030310316541d1068440301103450b0240c65408011000803500c0c503035002178000300081c1 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 217393687 1250 217392437 217392463
    0x31504030f0906170402040203070306050d05030a0906021908070c050d05010c08010b0c120903010e0a030c050d0302070210110c0a030302011a01110d0c051915150518060609030a05 79
    0xb10045484031400c1d5800c800d201d42c5524424a8000020010303c3d0a8000790b034880014900806c6056984010947c14402c1103002c48180c0c102064000405500c00c2e070540c0140305510080140c1e28401d00b8001d84a441c041014210890004400c0c0600040e441c0c0c140c010326000e031000d895000709060240c000d01d40084900001120ba400005140c00502c0c2540c0324020000090f11448407101045070303180d8001a0040d40554031158140103070b0005012034000340780682c03a90050220a4901075040002200442040c58030600c9050090f888160480e2001c03201e500b040032600401d01021403400b5060060f0341c1e40b0121241c5d01008040d41900101d905e014401c00d40210240084015240d84421601003040d641c8201e1a044079580318202c00074289000d54141ea441e0401e07060310034000711400c541030310818089210704080c40c62030310401d02e1000e80310744000c0c0c00a0600002400351124080d64401c1c440750080450126036a01c0116101084000d044038000388061821503214503032140e8503 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 217394937 1250 217393687 217393697
    0x706020d02120c09040c030c0f050711060304080304030206012705040c09061415070803160504090c090501020f0703050c0f0103061206050f0f06030d0f0c0606170c04020c07090b031504030f 83
    0x701a02c0d4048c0c01951006131803070300c552459100711030302100e880d00802000d82d449521907050f04015240d150066000707901884c6c4156a1b4549030030080e250000690000e0704030201c1040c80500c0010b01070300e8885010020314049000e80325401e01c68502c1482e80c0119140131301e000e10000e00d0030001010241e01d46c1c0141d0391100d051413000488901030144040140107090200001184001c0035040c51506070000e04155050030f403105000c03c103ca601091440100e1001501401a9a01009030200c00d2410030005d0000d03d0031507440c02e403104c1910042902950000a4a281c581c2c040c0e0001805846d140200303403002a40703402c014015120540b512000050260041380b03060034040d200e144110b80c050b00506102c5048402150b50301031030610041040500c046d1600005c3c3c1c94002c140040510040700c80400990030f40060409506000d0507200303610403c111418070380d01080c032504842184070002903055104000c2402c0030301c40010804a84140070810040541003007803041c001480e9a21 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 217396187 1250 217394937 217394951
    0xc07050303030408070b06150c060f01080604030c0602090d1a150109030c05090a0f09050604120201021c050606040e01030b0411090402010c14030d230f0105060706020d02120c0904 79
    0x14103071a0310068901500c5108108015404203601e0301c0e00340c0d040071010304140f0300403640384058090b94225603003d4820f030300040240a49112070448140c094845076006d45070504003070394090140070003d20010706071900401c043d0041da89a40f4803901182e00320b510100d981c00e101d03250010900013282c10307070790a0111102c02c1509501c04c800440035281d001104030812401c2204000d041341c8010060380c3d24580f0b881001524002c140140d440e91882000204000d040514044071030307000504044045a1040c40100d00c007031b05d4040c0e8103008400383e04c000542a1110f41c007040040c40b031900034010040803280000f00704031008050714821405001840074001001c0304202d06a071007070314040c1c002031b50400988007080e200850585601c000e142164a0005840500c1051301c018000040343e608451055840016030812920707401445081c08002540c14000010720034082d080d000350006602240c0740f5a40f041e50b5040701e1201105210a214524000350380f01503941c020300202d80a01d0034800 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 217397437 1250 217396187 217396189
    0xf17031303060513080d1a030c0a0509150a06050a030501080c1e0406030c231002061801020f030c0405040b030105070e0114090a06020312090d0212181201020c0705 72
    0x56842060100d000300c4801440e68540c0b03009071402070000c08440303280380f08110000d0303072079001400c104100141c0412600940340081000900d8100114043e070805034104842e03584256203041520811100683c0305e80b0f0b8042e0781c0070401001600b041d0003e60456001c290303640c004000e4640c600c007580d0103001d144e8a940d00329456900605100d0b420580009003d5000b100710326000705000000ba000040c55aa6600d8942c0c1e919400d9205180e25401c031120500c4ca9101c0321208000e4440c15a111022041c0c182802035070ba4100824044080710100152601c0e184c080d0111400001d218003516140d007412425800550301c1071007200d205a1510720594003a00b4180602449089641c9a0400710425a4010f4490844c41e084040100c5003c000703555440e03840c2182d070405880d46500450701d400510442520302400a00260420751000754518081940007a0b0250480b1102c1100f5450f9052500031030358034100550740c03580c408050220350100403415809080036aa005045a0400fa6114 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 217398687 1250 217397437 217397443
    0x103051b06040b0a0c0f241109120a05030705011b210c1106010f060e030610090c09030209040b09060c04120f0206040b04330c02040c180f17 62
    0x360020307400900c1480100300c0360b982071000d07000010090800002986556403100d02c241c400c0e44044941650801d0100c6000340501202109404042810440c4100044071000326014055803544510700b069070041504800b03100c0035140b107a20900f140c3d1141024034140e8003078101404d12a0030f60050610600380b543c4541c0801107581c840c2546807140341c4a443c440009801e0004180081c441c5444540300010380820045000341201c54840800300d041007801460016140384291090b400f83d001c0c050806590031080d01200c40000c0001200501010700b9505000c0d1940042d50041911041000340029606581e02c5002c1e40c0098400380d0344c4403000240e2074001c40c040c454a2035200207400c80060501098001403500003440542800c0d500c081e501410307440380e0064602d0102241c48900c00c9003c00b06c0e8503080c2075000140c1602c06000f00170040403001f0088010344200e48809107000314a01404544003010b000c00c40d0420380a89545504928004610410305604a0800c005172100804 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 217399937 1250 217398687 217398733
    0x40b04080304030b2d06010519020c1c08040e041b0602031812120c07031209060e10080c1303060203011e080a1211010e0a0606051e01090b070309030209040308010305 73
    0xe004481c0c25105c8600e440c11944000c103020b05100e0300300701c2d60005058a0a5000b413442c0345a0050007101d04040c14000c004401b40352404035120040c201d680042c0c0300a0035101514242c0c01280c0303036580c46042888184134008480540940074500204401d940400104295180c8080e0090745403002424011400da000c214000241c102038086140e100f50b00004050f05402d039400c82c5c4007192a91600400030140c440c0d21404100e0285040011541004902280740422540a0012010300c0c00262000304002c00450324400b0000e030800c1000f6082c61551702641c0c11500854a0f9a103078101c05842008100040c190002440c100180701340001860103103199001a18103a0307120380400a0b580512082c040340c0d200e54951050581047c800c00c07001d5880ca00510700894540c1c41c040c10b0019440d002100784201c0c100c030403c034601c1c80c0d07040550f14003100c1640c00101c1d03442c1400c0c2011030384980c0c6508021b500007070350428001032651200d881c8d41600e01907415241c84200344210704070200d201c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 217401187 1250 217399937 217399981
    0x41208030106031a13020a0c05070e09060c030408030a0506010c05060403050a2c040b03070801051003060f15061b0206040e1008060403080a270b100b1804050c040b04080304030b 78
    0xc00e0354501c040c0c0c022900030300078042c8a404c020008e1240f903a180b40c03c2c410140c010204481d162010090b400504018440d0026401c41e01c0f2851414580c45840c020700c03001780303810324039038a803c040b910591044030502d64041d08081076810504180c64014402d5014600c0070001461356a11050300c0d800f054a15551500300c18045102c0d05c0014090201405504c20381c11b0345806102000626500c1c207000f0f075882080c9150f580140c09040d40741c90070442e40c0c280c0d5103542042c50455540c10000003400e1070302c01c1c2c5005003844498100805800c01d070990918800070b410060215000890000c10361100e4050180b00c0406024580c503909800e60700c1108640c0600050320a50104c0c0506038541d12a00c0b40100301890000f0030590032110340e075602c1800004842506a5004000c0680909079050b8007612006143c9450f0801600321303011501c48a1004520890b075810100b41c4507105601200c00801c440b11015803650358a05c0190740720b1f041444280c030091550780c0024045030402c0480002c03c01 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 217402437 1250 217401187 217401199
    0x503010510050405130506040c0804030c150e011103180105070203032206090506060f09010501020c22090c081507090902070c1e06021b0d1502041208030106031a 71
    0x31800080004040d151040c1a081c840304220209030b68644607101c2a8900011501241703038248042400b00700d40041d1030350010031505109000000c0d901c0321030b00e00103d400c440c6003c2d2461209076007000425003421441850361038400643c3d21154804040c601c42c02940100918440e14060440e090303c5003160030320010380003000080d245031100c0a1140d0900d00b000800725580059944800449405100c25549070340031504210300c51500b800055078201e420750700703003c09514010002c2e40d1142c84032680740c441c116a900019012030031040075103a10800b20420300480165050150590440703002e0454207014080d010b90345900e129458501855150303617590704541c0350589010003904040c404450300071040c00000391103808604c2c02c1e07040500d640c0040d54810b01d0180042d2071700c1800070f8124072600e001c031032081c659070b1403902074081c894002c903440015100c0288150001c5c415604803402c40142589810188103441d00958162509610108032518048000d882035440000c40350354042 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 217403687 1250 217402437 217402439
    0x20c28090603080a211a091311060a0e030109030e15040e042307030602031e01150503060d0506100306141506090a1809020a170a1e08031e070f050301 66
    0x2c0d208003058001400d41d64681ea4198826405d0030050340d004242401d180107000c01d5100247c508107460765001022680c2940aa0080d6a501210202c10400c45442008003244003000e140c0210480400800010020000a042c41c513020306205a46948140280d9052010b105034030303101401c49064500007680b40c400c9036140c0e80c83c098900c11654840070160611103240405d504100866006144224809a100d00e05004148200e5400714000000c1d04500801000131100b103604406002e103041c500103503079546441c046010301001c0c600003442803040c0c104218900c06c0380c0303031550180ca00c03446c014000c07460b020300007400c041400c2da0307000c40015051407608070034a4444020802d010002c0c0900c02000ea903880c5800350f0b4403000e02d80414254a4510b0701046250543c80800941142d0720026410141c203401c8580d102c200f404010003400c0206051a0050260741307265105c9980800d6940d40c130300d040140504104040b5a02c0f00d803503911034020455541c02030090642d03107605955050b08503 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 217404937 1250 217403687 217403707
    0x1515090106080f0705071406070e0103020711060705010207020604170717030307080a0f0e0c0a05180414031902011508031c051302030316050d03050613020a020c2809060308 76
    0x2080601314009020040002d04001003a1282e41c01401507100050442032400c44809031a03108016a00c604040c8100040c2c0300080401c00501a6000140d440341c0d290000e9152060091285005c060761011f00072a00140000301c0340422206100740409480720965911030480d5a0300440f032003079100d6041480010f024620505400da804100440c000c00c0d000c54078100001100e818482c610500c1d001204d142c4810300740414002d00400059410001c551000141c02d0722012010744028400c0518022440c2203203010402e42c1c69181140e13070b0141000222201c064000e01d5003c1008030740c00c110500004680b1804025504c3c10610701601d5050b51a40d90b41030802040300400001507031281d010000c002d82c800b04050044501206107440405203d0b06000f03182c109000c030f01008050801f0204011030300c1c0d040200c9038201940c0d40150f00c4d042885416400c01305070300b04468221107035181136040810000b40d803508400030b10036103259003911030003010203403201804003900180d810001140a = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 217406187 1250 217404937 217404961
    0xf091514010c061b0206100b0f0c070b040906080105060901050f01030c140c06071b0507030201050d0b130b1215060d15020403080301090b03010902030d20151509010608 74
    0x14940140b5010348441c00c9651180210f030290284480b49150440c2e0b02d0560940401100d80c101802600b244411441c1c0500381560740700303c0120394501c80010a0805900c4070400910002c1d12441e4641c0740c40796111003091009091b1407040c00110341c02c00c1d010a40c036080030000706052750009081114050002001074024003030401c1080200018201e032889584850b801410350301514030081c0026042040001f018100e074240c1c07940c0c1c034500000890000550010f10401242c0d420300340b00f0b84508103c0e0220000f0a112952150404100da40013408001c0e16848030a185c1802c5515020f07501c10381c2c817410790b124541a0414601c443c2d400108030079141c42e00503015814400e40c0380841404400c44902d0598006910880301d0303000210040c07002e450702d80251125528103900800c840c00042d00000c1e640d0491a1085007880b0f00c0f0840040b81c0c003103c034810846802007100700d0b0900030740d018085000c0345084521004000300b8501c80041440e01201e114100da5184d640c2c410b1a488014540c40 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 217407437 1250 217406187 217406219
    0x11a042003100e190c0207080307150204090203040f03091e290a0509031b1305060a1d06090c0304051209010c0b13020f060406170a02040306090b010f0915 68
    0x2001901401e002805680003c155803142c00d2016030040f0038842c15480d07100350758403182000c0c15504103c90603c00103800105603444141c00070045c492071135510182c00004c0c400c40d0000024540000f04020910184c13070b40c03415401d41300303aa034150095640c20241089105007103105210010f0154100b04c1c82001d01c2100004024540340b25484460320300a444160b0310281e010300218a0100f40c61046140074040030f81c0d1242e0184c0c20703c000c0303e400720004885422542d07982040d00e07a174101250140e29a0800132000c0c0641402c40b0913400007090403080036110440d080c074490b51120b4000342001d080b50098034000c6030b01034011304002680421540e1180c1120b24424104207281189001182403291118002c00040c1404e106464250041c004007403016102640078120030841040345c26032103011401e030f660034546900c0d25602c3d400d00c40c1000e4840c9501c003402441c249245181031103443c00f08141251000c00c3c0790310b03620741e07075400510954090819981d500440d080003009042c0005944039 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 217408687 1250 217407437 217407451
    0x31e0c06050307052703160306050a0c0516050a0c090603060b060403080901050708071505040501050a1509090203120f0406120905060c0708070b15011808070605071a0702011a042003 80
    0x41d200b00541d021a02e00301807c080c0030b03208400402c5c1041484540c0c441c0517040340552000b1300004507407807405841445100620002c0303c503d040f0f0071003400002d000035100281c1c00302200c504655507105a030301403d080d02007690018980903030488c1602d031400c200c070204d80d80034124a0038000d4000054170240c0006e40c0641300c13405d00f04040303c001f501c400355102c628058980c1c0000c0398240f5050890840b140201080801c03032811401d20169003003000301c2030841d41c0c18000442d80c50141e1000c40d003050b07101c040c401070540010035001e080203280c40c013070010b030380380c555032012400c003c005a50240c0f00030450182c007580214000c15180741c07000c001002c00a000701d400324907100b86561558200702084850300c806800e82034a0800d1503a01094444240c6070302c0070080c46840c24044015165201c034442d14060100001d0f440c020081007079154084600d21401c0010b132403400000c00781c040d0059020701c042e45038070f0008003030a500e0148202e6040943c4c0c0206a0440455118040a194030203030800c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 217409937 1250 217408687 217408747
    0x1807050d0b0925090e1f020a0306080604060926040b0906040503030d0519090b011814010e0f010f1409040507080706021609020f0d0c030204031e0c0605030705 70
    0x2244a209094500c442c01d2076400241e240300340f501c0c00741c008840000c05c8000301d6400c150080c030780042966070441c14140440d803005a0b11600c203c0c0540007070800b94400b00030b60041804000a0000071b61200714518042c00a01c1d500300e001120300d201c0c2c101e54000418003200709000611a0064100103071200e603801514191505880c0da00091842d005400440702c2140c65030100508911180c00701881320540754001d0010103035a9035032698042050046030580340e48075954918410b00340c1c0100c0341e0400c040204180703d58440e41d020900240403507008218400d15800001c1c1a041d50082c0d07000c960350442110900b60b043c104002100360007601c103a60394400d900c00403c1b600020710074240103055640041c0441e18050040c580400c55980c0900607940c4117229007900c90f040c0c002121501e0f103c41350001a608140c40094009000e540c0014002c00341d041c58201154012030410b00d180c034001d400c15100103030307100001c565600c012100b00300010410300c031f1002101c000322802d000d40360364900c0d2 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 217411187 1250 217409937 217409953
    0x20f06041202010605060313120f0c0318052805060f09040e0c040c0f020105011e0e0a0e0102180102010b10140706060305010e07050109060503040b150f04050a051807050d0b09 77
    0x1242500103a91640070030784000e103007504210b105a0440a102c9c8581041c0c044a072078490b000e443c1c1d600e500400740134400041c8450000307846150b100c2011340300050205207001d0703010030320001055041c40b9030508004460720100d207030318020080d5251260b5441e9a00e00d0146150140406400503c4034001c15114444000c00e2540d00ca000ea0a00e00c0074940d1090b000d190314020007030960b4010381c08480035400302141c00c109121a00f10368010382d500f044581c90641c6840607108003c1c607408014884951001c121100da2009070414900c0400c0d09a000384155081d01d810014840800689500031a402c048110134201d0000c02501300340d8012100050019503d40341d0303d080d00c5140250290a03001000c05000e00d6800503182c0002d00b00070301e4a581545003a40e2543c42511002e805514a00c09103044881c660b034890002441c4a00080e00034031260500c424200050582605c44a580f8a905120540340c90000504502100c4c801817071038202c0038a07521900007121018180c102140680781c0 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 217412437 1250 217411187 217411189
    0x11030708070f030314071d090f01090c0c0512030f0a051614070519030f0801060206060f0402041d07030b10020c090a02040509090c030106090204180e03130909050607020f06041202010605 82
    0xb854512038801e503143d101080207c03005014800420f0290345100f40f404000340000c1118401d401415035000300d600140c0c103110641c05880480314060010070520421190300e01c511030b500e0295005800d0403100722401d840d802c041000342c99040710f5a030707207058240d03102e820000e02c60304c121a400b44d00e84260310700d442d04075252a4140703c80340701a20008168450010708250340300785405200c800300e1a2946507035040c40c800944480d8007a1a20f48a0700341800c8445090361168121801441c0702e0280081c0b0000281e000244008110f51100c0460310300120580241045180320001060740d82c007422118006038100104180003901503841c890b800d002c003103081e40303901494901a504940040c508101c0c1d80c81010300395951508010081030060000300240014020210310240c580000454040a05064149075014400c0d014030160006040058031140d20390040f5a21401201034510680e01e442e8203a9641d000a07030614020f40c444000200890b114044620b5088180e02c008075145030750b60 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 217413687 1250 217412437 217412471
    0xf0312090507050f030c0333010620160504150b0f2701081602010f0f0b040b04060303140d0204051e0112090201020309061c060306090311030708070f0303 68
    0x9a000c480d1a07001d01c42c10710041c900484a0364101404400802e44040305401003a19141c0c168070215001c51b030158048074450104410034801132000842040d00d41c1e42c6c801c001d0001707804c0c0d21001021000120a104194400b00e424010b40300e00c80100381c030302d40c075000a000c01090304242c1f0b010065004440440c80c64152402409800b04000c4044e8451598000b24405811000c00a00d5000c0505042a00c83c1e41c0241209910003906c2100303801c10b00c8030038003e03405401120010910940b0b00000c140d0b084241382e0202114510940b0304120f0441c9000a2000716051404003130701203001c40442e403014030402001007901e00b40c0c201001d810203a66901150341c40780e030500440142e1143d00b100c170205581c400b61282e26801d4142040c082071455170000703501c030b11038044820700511001410506034100c10400f03003458044a03100b044001d41e241448001040d045c1e208500240303101c0d89154151344004242c42242d60404d4078940390803201d9035420307080c644820084042c561074910181440f4150 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 217414937 1250 217413687 217413701
    0x15081f0605030706180603021207080604093c0c0902030405070f03110f09060d08030a0e070305030307080f010602060a0c1e0305010e0a020a080a1a0d0f0c0b04030f0f0312 75
    0xc1c1e05c402141c14014000440c141c410b54122100b010710500c00a0390f03401009010300c0c0c018020b4100320b815600c40f50003003400b070b1001c044080c1003100503203400008002d50ba043c0c1540c1960b008140681498082e20030241c88490100191100d240c030181485419000c0e07000f1504280704a0072a2b036042c0da60b0b031100001d200c0c02e500c15542c5000c1340c5540c10181c1001038a11480b0007044031111064601400041d601400d80303080500b0b90f141c040001083c034403090f400306082c0714944089400803513070307441c00300d54a0f4402c171500c0000400744804102c0c60006603606c0c505032034442e0050000d581d070700714048000f018400c1e8038404002c15503550080c00c0206403103000a65110350340100c2e00d0360404664104502d80a130145d4601841048502081548100a0b40c1c101001040100c0d03110800358600b94040000456594072505101030802081128031440518511611000d000150751b04840d5100d40903522024140c22080c20107880081d841c03083c1320403401d1103420154414494201024119000 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 217416187 1250 217414937 217414949
    0x101803030302121b120709091103010305010f090b16031401061d0102030a02030a05070204110f030f071b02240a0306140f0a050907020c030303040f0615081f06050307 73
    0x40080c0711512003e0b00300381d00c0e50000c501890740e8859481c1001d04002d40c8a07600c811019509400081191907204030b90860040480c1481031118410451101d41030381d0082c4402c841d590300e880e010390b015007030368001d0680729a00001d4240c1540d448105801d03504203000c4940c001c03d41d0703036108003000641c5008285d018185035502c0a10b8106801c0da072270320612a410b1010705540c42070084054080d4008100d581d00341036880d0198035100c0d180302040c040e1039528032103928100c010920250b110b0300103003d588520b0800000f500651125071045d2402c40c81041580802400c55620a001d07043c07801c95540b11492128002080d0a009030421860350011403c03640040d03203682c0700b089400c2c081c2c0c0c0b46000d004800c4407030000e1220b4800c0080e96080e40c5124490103080c142c2700191109000340003036540d0075000340079640d4a280034501090f0f015840d410445995141061425240e40408030210079103500d040107141000f900030704102990032103030a100010b03899080c0841d0a84091103c0f07001008 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 217417437 1250 217416187 217416191
    0xe07061e020111030112030e032e0e070e0c120106081b09130b011e0305040c080a02010c020108101e21080d09080904140a0c02010b0603061018030303 66
    0x154116032840100101184908682c14911109000c4400c0e42c1240c5c110742480300203143d41112898151180e845001d10395a142c0a070803941ca41550003107980700a90020a03040c10140c50b01c1706ea400c03007280c02e5094000d00581c00601d00723000300c0009104045c1c10030b0444280d01e04007000440d0f102c0d81d40074241c0040c00001d14500a2081301c084a0018070014500007042504120b50305000c0b4486e032130004810b65040d81c0380d040d404910707400789d0300000d40300d040c01c2e280d00e41c682c1341e03010003802815040d20112562190150001040900801c118003859816520034898050703035001152800b102905601108600042c00162134075101c01c00442c00d8000151411074900c0c1c440b038042c40d004480d2100d00b21441c0d0030019400208048110744031792459450000c1d240795541800b899034050741c0d40c0b03075030083d16095101502c24507083c0b52a00c40d08c01004c05000321030349110203d0030785003c01e0856800c408288086245c03842c0c10f22108038504203501d04403628034070f6015814102031650384207801180e = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 217418687 1250 217417437 217417457
    0x21c05030d0605090a02040302150304032a170c15060301020f07060509011a0d03031e09060b040b040b0a09050c0c03120406060803040f2303070b0c071a03190e0706 72
    0x801e1084c07101d94000c40000c1d04500701071a54010820365a0b481001e4038070050300100080c2011300405101d03a811203040d000e1070021a000d4096007001c42403a03800d0300d0401c0c04039444483d104e420707011121080074075400f07015548420302d42101d51507000382c0a241d040d5000e01206a200c0403041c00360a5041c000c0780c0200b607500381081e8139070844201c00c46407041250418210075940d01c0c0c0500b5031580660610700000d02921305060084001c4a41c1c905054035410098100e080c828507820403102c16104039810008005d042c0104811160a40c22240c0c1150312044200540d95403584060b9000c00c1c0b0b188258541601c05148900310703401000c40c0c05d9003075040b07000c1c0070502805116030405000240011480d0a00702114000500d0303045c0314184088150503a1654245030b40800074200000c0602120007040d03d44404000366000280032048503c40c82d031002414403211548980d05081041c64a491030b1206c0301c80d60780628420300303200d22003610b9007a01082d0907410050140100440d41c2d808030701d8 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 217419937 1250 217418687 217418689
    0x5010e040b3703020607030503130b040f0308090f120a050706020d0203010314030414040509010b032d0102071a0912040312031a0a0522020c030406030b060406020a021c05030d0605 79
    0x3070003400b5526000052508248016100e07682100c0006402d4200b481d03c983e105802d08100c2755054800402504007013052000300312480000904403882a2a140140d903541180c095441c8a143c5510b000f603440420414841d0220034018400c1000710302c0c01a01c2c0124070b1302c0314401d80c0c1c01000140a078550010042061104102c1101100d600302006145010714224036019154030010540f0b104540d140d000c01c84294007513000c290328003000340a480300400640881e50840c120034a204824280c60400c182e194407040c4202c45140780c3c0101510700c0410110b455510351f01d4010720000d101e2045070002c43d80c20340703410090001948903803034441ca1081002c1005054840c0544040061180341c420341c4125a18080031100b81c0b0700c1038610f48181d41c10f0f070031003940f003480c03014501901c9171000920008500010000f0010340d01552414003038030b10058280a040c1c4128070550300141c2100302244014901880e60a0081d410031440521540d40382d11410b055510000b0000c809079a689010021 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 217421187 1250 217419937 217420009
    0x9060203010b040f05150315040605030d030905060a183c020f0d0201081506160303020403051915051312020313140a030618050706020f12040f05010e040b 68
    0x20b840c080e6810000c1d04e05200495503607001c09072030f00c00328148071040484503889c1e6521100041400504840c401054602c0c050014910ba1506866034091600012000403032030040e503900c2000201c4100c2d10800301c0d21741c0300c20380e14104d010524034801c020040c90a5151440d903112581070641c000b02240f03940388108510f1002d00640306000f10182d03a40580540c0e04080000c0d07005c0d50101e0022109402c10000540328410020401c1104501d40351002c1455856400b4000781c070f101d21704461662201810000c0c013a00c50f00c0e001031107045482c03a02c8025000e50781110b6041362402d01d000080c585259100f9150054110800b00140d201040743e0510200900b000c000130b11900a541c0d034020503080120700c10303151901000e8405078a90060401428652500150003500700095500f03a07501c801e0000c0d116a03010030289620300c280b51468a2aa0b0a0360896003243c820300c0e041c543e4185400d005449a07400f68401d00e42c019610541510b42c0e485440c603402e01d03020001001c0164136150382d2030f082 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 217422437 1250 217421187 217421189
    0x801050f010e0901060f03020d0501110d0605090c0702100f02010603081b010c180b0c03040506030f09060c0909070c0203030d06090c02010f0e030708070c080d03200a0801150309060203010b040f 85
    0x3c0035a05000f8104036a2100031501816030ba0140c0780c1c040e9001c182d00300507025000c0511003141000d40040c6100c0b400760340d58014810b44100301c0d801e890a490306240d003801c5001e21000039505c5810100400d21590144410b0001581a4000410038030b82e43e488102c699049044002001400d2076180381c0e10250078441c04c65051500e0400c00040c4098012036045a60a0700554060a400052a0041c1c010070400c0c0c5008000040610346c0d00d103011402181c12050a449041d1507104190128880d00400c07000e030355040c6c1c00584a10762954460703000319a003200301d80e416a0140006c0000c41500c3c0d03035a00660703018181e9000c0114000d02503600003400c498900b4240c0100b03030b20700820201804408030495800c150481005a00c2c1c0e40c980c10501c104c60640c0c2c4c0700f690740b84201e02d0284202034043d04031074011850101c9c41c1800d0100019040382d0f40c81020706a40000c0d0a02c0014484240c10519080303090b0b02d6854001980d02107507036400101d9200780c012250800002c01e00300001d85d01c1801e0720f0 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 217423687 1250 217422437 217422451
    0x302010218120607080a02090603010b09040c02030f0f090a03061802010f05070230072301090305060a091103010c08090c1f08090a20150a0c060e01060801050f010e 72
    0x1401658041d075a541c0c440c0e43c040c02100420800b0800700303006007040c0c0c0541c1c44880d00144074a5681d40c2d2480c5072891a84580c0308140924240441d01500c54008030560301114404081d1a150036182100c01c034442d8491841d50741d005030781450107c080fa0581c480d08207031400090040505194074000075100300070980341c82042120410080c0016151040000007411685c680c1c440c40700d00010036480c444072454002d103481d2188810000f174100398610005100780a14401540d026541001141c40c410240400380050340101d01081010700143c0c4170804042c0601060641e40040c1e40000e0301755a420344d403050000e241e01048c4128898240043c003c40403044915480d8815208041d5481d04011420340c0f0500c000f075400140a00004e10080080c25802100c0448900c8460780b8031403a000c4401816020f003066183c0f9504100c200d404a44045010b900c3e140144142651114040e1803150b135402099501c90100103200e017801d004540c002ca050403003a60b00d540c10700d0340c040c1303030054006c0c00a = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 217424937 1250 217423687 217423699
    0x312150411030112030c26040f080a030905131e06050103050609090705120307060606120b03120d090c0b0a0512071e050c0f0f160e0103110603130f0302010218 70
    0x4000001c4030759080100c543d17041c1040c0c0d00c11803040c140300924450385099496000100411050488582401801941c406080208850340c07070700c66099540000d0714005001c1480c0040a1000f490081c060302342e0050040c030302040c0d9424401c0514102c00c94100d8030a40f40d40ca405040c0b0440d030300b5005640e130004044d02c014216103044070081b661083c2d2481040d0040603d01c01001c14120184120741040341c1050050040035075a80000b4004c500b000310030400207203010000180c9141c0425080c9484040500ea0b509011800e01068001c1101e460126440b0081150000d4441c0c004c1002c0c21041000e501c94580b07a000d004082e45016100074080c030200b2449440140d91014441210100c5028516065454a100c0705030507150039416500307803886120b503c0c80400440d400142d48200d020807071840060450750780d4140c00c0381410a0000030083c00b0030610303900c1c160034050059070b803041c0c18941892003070003a034842e01c0f040d11402070180d0060350001200d0f00740c05960034100219074800c0d105 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 217426187 1250 217424937 217424939
    0x315060e100b070503120c03041e0203100b030c030f0703030206060910180f020d0e0c1207090504030c02060408060601031b020606040c030b1c05010608120d0209010203121504110301 80
    0x1e6a0a000034900510086500128141061140400584001d4a001c0140c40041c1c18007113002d2540c1c0d0004c0314225000b80d158440701c13905018084100e548203a000e001051060205d02461003d002042265500b51103400c28100e0380365420401518404202000b41140c01e0550a00a0402100815507030240d0150801d2100d0001c03005d44120843e551802d51072580c91132080000c0142040711103c0352000e00104062140402c940e000900070f10078242200d404482c02d2081c440b20039030003d43c15040c1c0d0041c000c01c100b070020170707080154018803a142c8420b8152180e0b002581d075801a4002141c0ea9202c90200320955825219a03140d040b8203491450000b02101c0e4000d40c0c600c0010402409580c03560b8200300c2c11400790b08942522a001044500103240c04a040000306080b09800c0d2041c0d030800d1000140c0780d42c003040a82010f0f011080580c40c10041a1400d0f0195008200c4c450451000308215000400d090740c115009469444210f420b04204030204004e5a50308004883c045000b000 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 217427437 1250 217426187 217426201
    0x140708120f09100e1501080c0f10020c09100b030903030a0c0c0b040f0204090203030f091815190e0703020304061a0105160f0c0605030405070905010501080c0d0b0a0315060e 76
    0xd03014401c400f20301000308000c50341ca0106800c0903001d550f244046030700705001156010010902c1d4a04640584961a0210f03698040161455011a5880148e0080c20711280282000c510503588070f08104a82c1c518140d441e83d4201c1140d1044450782c07159000401445111400340c0184c41c078144440c54200c041c428a03403580d20303080b60701030300040508500000a00440d10760f40c05c00d2034903c2c4c004080e0781c0c4600004c210100c0680c000d4040a00c02e05000b404c460030718810031b030018002d03009140d44c068000f076210180401d0020426a4108000000000003112181002140d1040e451707135402581b01d00340791801205441200290000402d44040129500d9a20030256011a000e200019805000310700300030000d0490080d0117095800f045001086882c0c1204c010f502030b0b44901c0031031380f0440e500e440c40c0702112000c1c06580c3c0020b00d40f0000caa100d000100281c44100410a80011000351690008a0416060b4000c843e0200100518120942d9510405000b001e2042410701b561070140 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 217428687 1250 217427437 217427443
    0x1407080703120825090504150305060412022a01080105060325030608030c06040209100b040b130504150501020d0f05070813050a12020406091109010f140708120f09 72
    0x10360071000c103c0c0c0080081c4800f580070045052041c024042c80d0400c0025020007842440036002d06d034015401c013a00f007840540050346c084d0071281c01c00003610302501e403a03580d0990b102c6d01c54160800c600c210840c1c041c40001ca409540580d41030701341c064035203020b000009072425005a004610a900900400000341c03c100401074162054010b010b960040f566801c0e001450303140c120814900c404100c01c1c179200000034000307018600884014420707969501f100d80d1071161901400d01c00d41c106210800014070590060a588440315566803403c03500c5a0115040f50343c50358220320094001350040026523018890081c0741c1c41c2901d080c100102d440c01010b007661081d00030080043c007001407103883c4007101d0450003001e400001d044048a9940300e0380c001c18107099101c260300c00d51070010000703501401c0780700d402c0a40c00c884c405203080c416006d005464210490040b0800c0c45040c0175589607406404000b40301355481805519140c8240f03c1410760300c61001050381b80925106028005204000 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 217429937 1250 217428687 217428713
    0x2121501260a110f040b0318011e0b0a0b0c01051501030507091404060e0c0c010e06040f06021606061d01090c080c0703090f0612050f040305030a0f06030b041407080703 74
    0x401c2e00880d8001d00198a00300c3c61040c003c200401030004500801c40c0c0451030300840c0a6841c181c1c1c00c019241c0341020841c01c0303500c60b90710101072401200c98083d1100103608000036031031000b00028074030741da01c501c0b00865031b200304641c04c50f0b80d44d940c0030040c140388025829100f2041c286020030035880c0c040e03000f814001142c0500c042c0a1104134402aa907a61500440007a081c080742c451a2400c1800030241d5540100c2040324482d401c00000715030801002a031144100c0c0c1000c110421812951209002544480c000e00ca000e4ac1d4810814082200c038001d640040854419000e41304103020820f410803401070b000303080b440b0708040c100f000142c0c3c4202807541060b0550011580c60705540341c00e40320030007150305c450300d40403194400050654208412007154088800300f440281c1c0c41800354207841c6021180140410340c2030010409004075035112041300c0808281c001210f540300c0c2c5810100440c01c40c0e00321800c00c20362071044e511000500225001303000c8a0300409503141103550f00d42044000d = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 217431187 1250 217429937 217429951
    0x9150603010b1b031b0601060807050a0f020307020a181a09181014010504061401020706050d0f090f051203070e040203100b0a1e0f0e06070302010212150126 69
    0x4046408829802c45500040c0040809411240d844645d8201010003104121041d1518040c40b130001034200e0003006000c1c861f00745507484901d4900610419902d0505140c0610114401408080c0050300d82d500080b01130120386242c2101198102c3c181000d861040034002c0d92918495191740441e21541c41960308505e83d01e04040100d2500503201e0300d040b11950301c501441f400c00c00c01035801209060494182c1e4002e0b14203005003a200c13094031903032101340c40010b0f0042c1c2c4844001c1064900c5030014204040700400c0204100e2a07040950041e0740c2419416143e40050212903001c2150030801590440703940078082d411807801d1f1201500c415143c1d41c02901442e000030000c0c5819001c40c40d46405042240314542c0c60380041c040c000c1011207131650210058000b900c080c00418003840201400b0010382d9101602d52001000740180c1d80c00c424400c50a56400b0b0015002d11301c81c560a031407242d00c903c4c503180064410940014001c200c4040d4840c103036403040040b00f480341071691146502100e = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 217432437 1250 217431187 217431209
    0x304030b040303180c0905060619080703020c15011d010f090203060310020409140603010b06070f050c04020f0a020c0402070803040b0411030d05070b060f010f080901021908060915060301 82
    0x599410207402070301c0721401300d86100a0944d10340c001c004840d192030041e111701c00d1080101c2d0b645d000030301103140b080c00b4015485403081081d0900031361090580315402200c03403901504102180c043d10b03182c02c5d1000c1004003940025401881040c41c0e041000c0780d00803400c0480c000c107501d02034095141034203501500a4440e00080000c0c000d0f01c0401c004810940e80c07030b20031036486e9550089980104554181ca031400d0340f10700080b0340c031490140524000307001c001300039514000150351482c1c0c40c0103050380101c0d4030340108000c1c1c0c8480d0740c031440500200100e031031307040d03a540c00b210b000241400451901e0034427a91061201d000460052408e0382c0d070190307001c3c0518002d0f03151420110310103599030b070409603d4864954030410302c2d0703842009451500d03c69100c441240d21007000308210300d0b407101e403e1030020f14a580344044d0741c0c0c800e001e0310350004843e500062500f02e800c4039141e00c80c1145900c404c0442d000505201043c00c010007627507441820000901c0001c41104001f8040384818456900129 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 217433687 1250 217432437 217432441
    0x810020a08072307080304020405090f1b040609060f030b0108011802130207022805030304150e0d150912082401030612060e15070c06110403050604050c0a090e0304030b 74
    0x180005911040f00340203005142c0c0720b01213441c00b400c0503801281c4c124019818200031401080380090130181824515014140b01440082c0710f80404084041d0140d205403100e2001507101114441e040c05028814181601641103041c205000c50f4181d000703d08980c0b409a00d00c40b0700700380d80001c640b0258129100182c80440600d80d0010740600761010f903201c80007080d01c0002c4441003145a05801c14042c1c8544041c0d030380d104040c1c4a018a1141d1b016910b002e00349207204901c2040190031956009100c840d07079240030348650511940c1382d2007024013555540040b0080c0a82c0140d06041c40c05035141601d16032402940d40440b40c40300302410490348141c1c030701000f416030003a0002400350888803400000740703450f8100715000c1c040e12408091107000d01202840500f8180e4007151040402c1d85480c180459156035160041c80403041a201c0882c0601020001442c01e002d51070099001e1001801052140d00c00c001e09040c46602010a040ca810b844600860003c4103403400c407a0420041c1c07040d9 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 217434937 1250 217433687 217433717
    0x11b15020d020a0801060207060201060b0702042d09021305010605090415080a03020304031109010605121512031215151c06031a01052407020d0501020409060810020a0807 75
    0x1074050010580c89590010a410800030342c003038110f50417244a5802c40740342980d900c070141d08803006400342c40b4074048100210750143c1802e40120041400c803c12440c0144003540c51004488156400301c2c600079100d443e941c0035031400030200c542d91029400c3c04c20843d4984880a042c1d0311803026818001e9844000c1c00c1f0f0340c20031903d03000c00180048015510301418030710f0025100c1d882400100c821040401c240006400c2c0400814141c40442d01c4083c5000c0c0117030104820b5400040102c3d141021001c0c0360750658607100b5140e40e240907a0401141c0f104c4951500003075600b0020105040300c600020050354503901c65000124060808140b83d80c2e8280b079604c9900c046145900c04c1002600f090381c004108642d90302c5165415a040000103141e0742c8840c1040780c000174a054031801d0840103074028140e0316070f4800502050f0310040840807520a540c0e10203003a6001a400925019640c020402048506104801040d91032280441c40c2260428024090610141003201000b503840c480350390b2 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 217436187 1250 217434937 217434941
    0xc0d09030c05070f06030e010b0d0f06090507063b010507020a050916021c0903020f0607020405010f1403030910111227010f080403181d01080c011b15 66
    0x200c5a0400c0c2078429050719a40d03010351100132031044000007403034483d95407030040043c4a000c450040041c00769048400350313110aa07000001e0401522155602c00405d80092400c0110100500480d2034506030244240500c200007070400f03800c04500303c00b400a10891800303c44010107800c03001d00b0000e444201c20700204030040a140c03c015001800c0e0340030310041c0070094500c2219000540e08880f00d14090003026181580c0e0090301c803000c0344001c1000d000515180b0410301c81e1410140c0150b09040f0145c0000b0103890080c0e00210079400901c0091180e0566600c210318030350016001186802041804964071b64424038081007000080440010300101c18400b010800310068000b40c0c8907400d0054403150885200111091021200c014140d15400755007400302440031074490851682e00ca4500f036410701c402c0000040d46000c0b008001c01c40c80c0700a0b0250700602d0755189140b140d076051001042c5407c88810040d03040c0800150f03800c01c030031484a056104107a215411124003071480c2d0400700 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 217437437 1250 217436187 217436207
    0x604050a06051c0c0f0810231006091202130203040309050315060418030c14010f0e06100f0503060411030a02040e0a0203250e060f0405040305040e0a050c0d0903 71
    0x80c0c480d1608050340d144540d100305a0f5540d034051410600c079160f55072124285000ca902c9035141e1034000782d400d10f80112441c0d110f040c82c55040b000714020318040c07002560704c080c001c841105040f03040c000d05000b43d5904c10008805031142d862028400241030b00090354010043c1347e04250550000000f07000c05103c1c40c03041d801040c02408642407903c0503440d6085085007111203c0c05070380b41110b180c0c80c0004e43e03a910b82050f40c25840340001e40c2171503108c0c88462030b0100c1c0b101c4850764035605428103042a9221394a01c405076480540958108a020b807501c9880541c081401188810800d105980d008a0704030b030440c3d8004c41c5640c4500300540803a0403d1140322010350f0052412581034140725020440200a510840c01d441c0283c500031180404a98018000c0c0d220205080342405009905091144c10440c000c2c0700100b540c00040010303080d1407003180c0841c000703000444c0070080030000300d844942003480301805019514200100c003006010340340000760450f844120b00700506000e11340300300c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 217438687 1250 217437437 217437439
    0x7030f1103011118040204050603070509040603140304060e0607051519020d0b012d1103070b0a0e1207021503041104110a02242e0e1005030a0201080604050a0605 71
    0x102030040481220100d81d00302407110b01381400c1903400c81a140c50648215011b48900800a0341541c489000440d483c0e00701729909070700580e5038080400491100c03047c8030320314941440110b0b540d0307040c24002486200071b906628000c2d81d05000340310002c0c07001b207500301c1c203c0300a0403031036890b03941c44021081007080b061100d20741910018407210a06400c3e0800c07040b0b08000e032500407c0c2041984040d6515100c3c8c070071072214050f40152058000d2069142e01014050b0504883c10580d941c0c86895284001f83e400f80c80080d51419001100c401c203104a030356928404007180d090984e16001b20b48c0c524040040d00400f039000200140401512140d42e03018040050401c00241112048101c070304e9201007810f501601c40c002c01c0c900d2140c803010103041d040400f803142d51402c4d00d4240103040401d4182064a1284600401c898003000e40851030b04001d0040c5003060015041170b1200c0040d80c0030035007106000f604444500740260360000c3c011508904290380001d240c0c0d41d9200b1140040074150005 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 217439937 1250 217438687 217438691
    0x103090c09020a09030201030b180a05060d0b0a0f06060503070203340f05011503080409020a140c0106030b07080403020c0f03030904020409091b05090115052503030e06070207030f110301 82
    0x840440f07603103c84041d0a81c1c0c03007030b28100141c60121040102040d0781d00040c0e601402c041001807444178041e08644d4105034043c20790551750708165540010000100c0d8000e50050392032480301d05007505804ac500c01080d13503080c414914204428000e459214044d480440800710060b40c4070904094240200800d80041142c12402c10a107001c1d644122024015500d035801c0041c05034801c0381702c0d845481142c0d4844011843c040ca80260280603400640c3c1c02d1082c004408401d0225101d00001003c8208d04c11000041da20708603d010070030a41e019015404100460003000f002a8000031074050079141125260303054501b02000038a10302c5140030960b0040d00114002031000b403190000029507200d00c61020580780a0030036043c800c40180700302980945110010020196020f5000100301598a0f10620700244042800102c1d0600000c29940c415144a003909065142c810301c40051b000b071015080a0a10f00c00007990f40816003c0500481c6540c4110000c000c46c003050814040310260003 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 217441187 1250 217439937 217439947
    0x90315090a200628090f09050a0b0405040807290f271b04020702010203220f141f08070f022803090605030702060109050a1e0b030d0206010b030103020103090c0902 72
    0x80138a82d1042a080d03000710134503d0030040e0303445000e44000e400740c03510010a040703001e00c0c1c46c0440e0043e09000e841007103655624428a00b03e921b442c0686441769006a100503520200c500d0b0141800380c0c280d0b50074082541449051078203400401041e6044103000c00751803003075220307012141200c00c1c102980080001c2e4030180f5924003500807441c03c40c80c003081519a1704100c031081c184001da21843d003000b40160400c000800d04041c0b0850704580e043c0c042c030000c95080380ca0328982d603402c0d050b940040d041c0c100c0225840499282c003400d5100c04d5030035820340da03840300c00c0001301401340c0304094056014050701c42c1d11651094401c0005001400c0b2070745864070044800784251000b48030120040d80050341c00040454103c0c0103100b187c0c05640103500400c4181e2805070120002d060103410007000540301c41e1744241a041103100802c60410700080020b041503904101480c10b45003440d0b41096402120042000c0c1d00d00805990450f0380a08010803034904034900780b112203c45130420180b140c80890 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 217442437 1250 217441187 217441207
    0x1d01090b010501020c01020a0506041e0c030305030609060f090402011407060207062a14300f09010b030709020a091203020309090a020306091b040801090305090315090a2006 76
    0x90903604807030007a000e903140040708000481e211210a00c0180c0140d0155010800003850b05541d045249409000100c810510340c0c0d403000c1d0362407642d2040d00020404420700c003491928140d426002070044405251078059580440d1100b1300050000e41031207071181d0310450404000d07013240c0d0320b03903070090302155100001d00d8031000800001c030010310542d8a152a241c0301032040c071900c0b8040c038000d07140e0761111000c0c80c9008105621400012000100420000f0303244c8020010007148044141900e001c5403400382c25544449000134413a0845a0401d02c412000c0d86005c917007035042c0c440548025075160001c003c203036201d042903400503440b90008640e120034180d0110151404100407503054015032200d0501c0780507400306442d940c0e03110601101142441c00c1d00558000032004040840f41481d68401d00182142c0b071701041174001c40e0300000c20003100d180901c6500300503420400c10f00e21606102011079070350f1404003001010041c009900080340c80b07114160060032503008000390754400c0150 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 217443687 1250 217442437 217442453
    0x709110408060f0906130309050d05010f05070207230a03021c0b060f0a06050c160906170307030c08070606090623010e01140a0e060a0e0108150d061d0109 68
    0x403054040900826000c00d2014442080c000c0c01135446600500c41d42d1500c030401403a03c011018101c080c4105840e001070303261541c1d0b6800c88224010400091900e0010103108260341006002c07004540050030148030500c20f11007051801100c8400801e10480c3e140041000c000300c0e0f801c065484003490100401c005500e13488541e03aa4810070035040c01d038480c08284168a84c200ca52181d0088120700140907592285015000ca1a00c030021101c5588074044640001405900107003409900c2e21010302108400e5206c0302c280010740b10084d0b00e03001d4151001044802560401070041c0c0002a0000910482d0782200e0090110310341c0401040e50340d2a050b140504440c400300d000581c0342c5d0702d821aa0b600526407500005d00c1a110b01e0381034480103140040550008440d1402e000c1d541d000e0003100c0e00c03a10080c040c1d019040c4c031512401015079001500347e02c3c0080c09600400583d2040ca2074a8030b5418079070f61202d40c400c10110340c91406188100d2160600304482c0c02c15031030401624244201710b = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 217444937 1250 217443687 217443689
    0xb090a081b030706080606030c0a120905060601110f070902071a0a020a09050301020306010915020f0f030901110f0d031a0d06050f0c1e070606180207050105180a060c0207091104 78
    0x110b04907841956100415940c03200c045442550110080c80094000c102c0380008003034004541c60b08407204050011a68204c4010241c1502d195100c40e003048540e50708240d40110800f49603001303002041c11030010340d41d03c0b00e4a0040540c00c58000c40e0354010800c801214044141c01c412003009180b070444011340003500800440ca00182c0f000200140c1c1e81410303c2128002c0c00d040e9111405a420020a019442c450304040c104500c64000303649813500050041011183c11000915a02d4a1001c0010f00d22060502d6000f001d411281940280d0100041d540e9459841402c0200e0764100f11040c0c5e500c0020100380f9070f500300d910b0f000982c0400040341e202511a10280c01201d145480d400f4040002e0b000703182e40300c0542c2c01c10301d01190009860703001415916104002c00b20303040351191400b8200e04a07807481c1c08840c50300452400c08110003070080d107502400090f07140c204501a0240315039604e0a804014008640d15064042c8592080c000c01c1c0250039010403e00041a9456002c0455801 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 217446043 1106 217444937 217444939
    0x6060d030c170c01021617040e070e0109030c0e041407050f0f06041706100914040b180613030206090105040c1a070615090b0d020a0b090a081b 63
    0x9000814041b0722004100e001c0314401d00d010054840e0303c1ca0411400c8005002c24032030140e42101c000e52010b550b1500100752100d5900680e040c02550300b001d07048038002ca5002c20384401d0100d541e80101e01c00c0301d21040040003100026112a518001e46905c0441001191100d19104500c05240100100424503081d9a0040400c4070030302e10704110701c1500031a080000d440e00002120000706602c00301408030103004804000c0c18200148010007080e2400e001c91000000064140310b1010300404171103560414600e0040960003c900c12030040c490b02d00016101481070040f0360055a00c0048032199509020701d943d0f21918070a0482c082540c180f00a00208500c3e0007804590707071104d004501e295061041036026500400c1c52540980d075500ca590005840300c00741e4004507401c4c0e66a1a44074018000040c003080c0056014404e02e200d030710000c00448191100114510f20 = true := by decide +kernel

theorem cover : BRFrame.Cov 217266187 217446043 := by
  have h0 := BRFrame.cov_init 217266187
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217266187 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217266187 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217266187 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217266187 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217266187 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217266187 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217266187 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217266187 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217266187 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217266187 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217266187 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217266187 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217266187 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217266187 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217266187 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217266187 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217266187 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217266187 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217266187 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217266187 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217266187 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217266187 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217266187 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217266187 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217266187 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217266187 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217266187 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217266187 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217266187 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217266187 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217266187 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217266187 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217266187 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217266187 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217266187 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217266187 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217266187 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217266187 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217266187 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217266187 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217266187 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217266187 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217266187 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217266187 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217266187 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217266187 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217266187 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217266187 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217266187 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217266187 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217266187 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217266187 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217266187 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217266187 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217266187 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217266187 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217266187 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217266187 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217266187 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217266187 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217266187 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217266187 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217266187 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217266187 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217266187 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217266187 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217266187 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217266187 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217266187 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217266187 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217266187 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217266187 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217266187 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217266187 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217266187 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217266187 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217266187 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217266187 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217266187 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217266187 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217266187 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217266187 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217266187 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217266187 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217266187 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217266187 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217266187 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217266187 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217266187 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217266187 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217266187 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217266187 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217266187 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217266187 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217266187 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217266187 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217266187 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217266187 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217266187 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217266187 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217266187 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217266187 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217266187 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217266187 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217266187 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217266187 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217266187 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217266187 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217266187 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217266187 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217266187 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217266187 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217266187 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217266187 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217266187 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217266187 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217266187 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217266187 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217266187 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217266187 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217266187 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217266187 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217266187 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217266187 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217266187 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217266187 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217266187 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217266187 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217266187 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217266187 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217266187 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217266187 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217266187 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217266187 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217266187 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217266187 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217266187 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217266187 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217266187 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217266187 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217266187 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217266187 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217266187 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 217266187 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 217266187 ≤ n) (h2 : n < 217446043) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
