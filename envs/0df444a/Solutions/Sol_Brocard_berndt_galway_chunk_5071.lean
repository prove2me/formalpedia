-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5071
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:38:40.726897+00:00
-- url     : https://prove2.me/submissions/ad7b58b3-0938-4279-85df-1f50841075bc

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 911870503 ≤ n < 912050359 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 911871753 1250 911870503 911870527
    0x314042103061205061006050f03010b092d040b040501081902030127170f0715110304050307210923060301180c0e10080a060504020a0201020d1803080606 68
    0x242e006004480c000315000541c61910a1750750400300c0d252003412107503140c0081d10740d00601c01d6030108071441c0740050541c0e0900b04129481d40207464a9035100d400801280c09241c104490a031766810004031a210300d00c641011300058800001c0c0032406645044010402080c0c0841c03544040003035038101c0c035865070041c00028094280e000000495809a03002e030f82c1002198914880f07501c0c4696440801d003034281c0180d001d070b0b0094021003180068104038030b40024034040c000e605101400c50000803d10840c190442d9190400c41f01181c4980c0006000801d202c0c00c01d61004812520600300e001040102d00000d0081c012441808900c41c02c0d0b100109a2900e200c014102100c0080c205079121f69403600340000500190104028071494149a440e0040c4100d46074000300b0341c091310300380b91000c040d40110780c2e90b8801400b081c2d03000d80d0350101140c142d1365400107203400f55403540007503115090010f0b01d8085440e10342c00e46851020180d100c0c2d000a0f00010300c10f520041c00c0f214070351146d2400c00e103 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 911873003 1250 911871753 911871761
    0x150d060e0303161205010506030f070215010324060536070c0308131728030c1b050705010c02060c0a061d03070c09050c25030314042103 60
    0x102480c0c502011041210001c0811034900c81c1900c2952041c00c101d020924080803940c0a001c0c090b0072100030000504044407000d05990011401d104075154299400c00740d0711259805c0c0c200302d420200b003020000c82040b122a001416080362901000b601d490000040c403901960315807444d089010090304201103007622072030740794001c0144003441d0324904500001d150112001c000c030701040b01000482d9100010b100802552a80800c076003c181d101c00b2641c0c00c840e04260b0014900b01d9202440034111040c001400900a4a035100800c2c01034401102400310704649081442c00080107034903201140000a940d81214000e00740180d100303469001040e420b104a841c140482c0c410200903604204840d406480300d0701c8019a8500b0340700706001050380b20b00c80c01101a0481c121510b0512540c1501c0d40641e4004c404140810710f0300501100c0005a441c000e54507144441c141503010061641600510108241c1c502c001202440c1c2591801c07094103812198a001104441f010803280d4020f0740 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 911874253 1250 911873003 911873021
    0x10050903100f0b04021b0610030305030609180d0f03050a0b010c02090c0412150606080402010807030e19030e031b093c0402011805030c0f04060f0803180108150d06 72
    0x8025952000801e01d008020040111958464460103001540703c4260342c0001c800e49e035240d40c0d541d2450b00c7d410704011550314094401020241c4043d120a2000d00c00c00052901d0b43d100c0d1a0f042c85103202d64409812a000100b41a03405414541c403403400341e901c00f41680c40c0960454840b107042e1100c0036140e005010329009039054003c15802ca5090004001e0f03500100008078005005132910354804032a0000c00b903d00070301007280c0401045069019400940d071240c04882210f44030740090400c200000c0349180f050340450702d01d2401d6022420140f000301000d0803040454950704800394049290140018030710a00c1040c540c100d10f041a106d4000d0b00007042c450300030100000c13214020b0b0f03280c0ca1000d8504038082003840000c09001340726140310300300320f56004000d040b815104c141440100c80005060a5100d0b90762000030a0003003100c0c007003101074902900255100c2c4e121840c0d4951400d0340c038401701c0c1404041130400070188220000d0f00094074098883c285441680d20b41840174000e180e13 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 911875503 1250 911874253 911874259
    0x10e03070b07081e221a072409060509030c070e07110a0606081011090609130e0c12150714120115090e0c0a08041a0103050c10050903100f0b 62
    0x400303038210350001d0740503100b4a040c40040900416500c1d080ba0b8000d017141c883e42184001c04d100680d8910071040240090600622104000c0c20180f03d004400d107181c0300d8412865039076020f10000303000443c0304042e4041c2c1c40030000c61600101414041c1d4514841c85492400f410718000035072820b2164010f110396050000c102d414414491425038041d040c03d0041c04071511505031000e180340740c1800340c007104002c0221854070708000309092242642c00711400d590095412010041d84001900c1903001c030b02c4488000d045041e14520401c0245c15104003004505e0340104d041d1301b0340141c5008941e4020016080504503804540040c6080f405a41e890b25840c0070060300018107247d40130070540078a60a41d030f901c10300d2070f00d030340d1f501400d50070a031081105407905100044199014100c8030381c015018104000301c08607108440386140109800844807500840c0ca1800d113820091100d001c42481c8c0e060050801c03040501090380c03a00c2d0011601c1c3c80a49078034078070b128861140e2050900080103 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 911876753 1250 911875503 911875537
    0x913140708010203040b0606071212061a1207020a08090103050403090e0405070821031f080a0507080105070302070b04030e041104090911030a030504061103091f02010b010e03070b0708 81
    0x10705203081c003d400842d001d486a00e00c1e03a0000e4141d2601c081114030300d42e1300500406021541c0c0d1790445598140c85d94050100d41e07a001e001c1011010b15801c03240c030240d4650718a580f076025414036a00e941e0003412503802d544c03103426000c0c0000d150030161800b1840a05e8009259911814110750076455039106910341c44007102480b003031001c08a00942590000740841e840d101503100501800c2103510300d15a030620040c0302080500c0c03d007130041c65014481c0e4200c4521943c55103036807400c1a50b542e40858056001100802140c9000c0c004c0c03e500a0b41414110305001050300c0e40b1002d000c0041000701001160b1190f404030f5a9154010700f181105419013070307112500c0e40d2005000300a00c03070042d1184e40c070101d884a11840d0001c1d00542a642c190f8801d41041c1c0b8061040d20034018640b1003601c1c0c0e010900081d040c980b981c050031054841c4080030b991008192440190840f40041d415034100318140244441607200010030404030b030b800c80032280e651516410a0340300c500400c1d1600600240c0 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 911878003 1250 911876753 911876759
    0x70c0308071119050112111905030f011410120e07090c0207090c270801020d06061805011b0809090702030301031203140a11090a2d0509131407 63
    0x403400d880c0c01080b4041d907454062400c0c0402401100c2182d210b05400102012048001c0f180d0380d4104041c243c2e0309081c0d030343c2018441001c0c0c07491481070042500000710003000b08400c0b110800c080600401241056810560302c12010446490550100c402800f0a01c2c40d10080765403507901007a41245ca88040d02c000030303190103980c00a003180d06034540040c803030395602064100440c403c62849903440c0e1940440c600001c0301240700600403101c400c614519803100068810070a000a000c815080c9400060490420101408481450608050002408800384090f981140c100c03000e40c103e404010050000c43c0c90201d210f4826881c005400801c80c800b404480d0740c0000103141a1f034403904d00540e11100c02c5200710b04403a0440305002c11a12900301043c440d11080e03009005c90242080c150345401400004503411004c580e1210b00e4448005404821008200003202a550b600301d4002c074020740b405c0002020504054000d00502c8175000301031013008281403410802d2102041503a224a503 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 911879253 1250 911878003 911878013
    0x9063f050c030c09091b01110102030108010203060901080c1012020f1303060b1801120c1509031403070b060603090109020904030c0507050111060403030f0e0f0106140109030201080c070c030807 85
    0xe904020501a205400d0502e40c5844c2040080b807103544102c2c02030680c1d4108060100000400b402c0c46810f0208910613512000e40c00c1c002140078040341000544d0341d04006090001b4503070142c1c0200d60701c0d04031550440082e80d0700780c2c0d2600b14250900d480300c120440e50006000074030a0500c605a0b0890020340a90b150420300e0406080b00c1c003e06040080322411814004200410b09041969800c0d520042c0079012006c00360217419070140c00c0d48540705455090480f10111040700250209880900401c01c0240310809268032003940d0b8050360400d815913803007c5228901800131441414040000342ea04c88003544883c44498005010f40020700b000e00740540300d0000f000c410740d500d001d0240080341035401040b8604010801d00002c06c125a030f59203044005201c4015103036000741e214040e01501181c10000d0424454041c4c0001400900e0a0040102030076602c0086042c4a03082c4000c001503a082060154000000d106841da0303500f00f80f80c40d8444840c25003006004640210381c503030502c1 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 911880503 1250 911879253 911879263
    0xf270605040603110a0b030606030c0d02090604080a0b01060216050f030114070f0e0307030f11010c05011e14090604120c0b07120e010e030904020c011e090c09063f05 73
    0x214203840b00c16900380c655804440900c4122343d080c0c1c0208007080410440107403000203058030a106040181419041d0000840301d502a60000f00c182d0b100300e83c140d0500000a041500500c04c0e8001459066003080c0550325001e014030405204141c809900d0110740c4080d0008038030070358620444441071800c0c900c0a40001c03100042c240005075168007843c7d45050002d007410540e50410b02020302d071441640c4040c1800d82c0e0321903003410091501c00d101c0004a007402914100c05525804813280708119203a40101c54451143e05000000303041440f00c07400e0049111504950829811404928914016101c4402d91000140441c409030108400c0d59848991307100e0341000174009100c0d281c41c07000d049090354009811549150020000100b452030030b540200503204095002280c85030301000d030701c1410049102e40d00c02c1182c8440012041180c2e01030200098040103400308200c40c140407d144034045050303002d2401084031103442000c6820100100301051014002e03801004c2d5514041d0b0326a = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 911881753 1250 911880503 911880533
    0x30a0c060302040f0801090b04060207110d060209030c0904321f0e03030f150a0e0c030f01080f03030a1a0405090106170714100c050a0b0609010f270605040603 70
    0xf0078013070b01010030002c1042c09807140490300085207500c662215120840254041e5078210381402d4003010150403a19aa8a5585868040c40c401a00c60078240245070401d9428580c0718401d41802040000246074418200700c81c0001d065456211380c8030300c10007441810b030b10945000900c140794910411800442200180340800201402f00c8170003001442c2e41da000541c2c840409581c82400284220300342c02c000d0002c0100100041d5126944d410101e00120301514400744148001080104440a801c201030041c0260b80c0189040d2014500d1262607001c00303004610359948402501040241d00092040a0300006200f007000e0b0500c3c2d2080b40c02018984202030307849d03140740e407524403410b4003040c138034129a130490803510029081c0d02040040c6480010f24030a200c03088010b0310101d9000c00500b69194400c040200d2a811b04408101501d0b40503840001010803222090040c140306000c8400d2110f203081180c00e14030b94800e5008058030458108540241c42d00c0c074004180200d5100702a51 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 911883003 1250 911881753 911881769
    0x61503010906180203010b09092502061509040b010909030e040c0206090f030a0e0d140118051c0c0b18060c0d0b1903151112090f0109150b030a0c06030204 68
    0xc80030070f441902e41640030900c60b241c9002401d01c5612030608081c1c0d0071641c85131034440001e0800280204848075114103c0c80500164085000c0049003417080c140c24007040d4003201c007000b035807609071b550907245070050086994060316003900c801054024032540c04110344c0200240113030906200003d41e118411921902c0c28402c1d1010340714002c1c0040700b03c1d420040f0740d0752824460320075a41030100d5409090012203003412807814907400c1444c00e02c035034100920100100100c48a140c00c020307240c44182c0710486410000d001c140e02246030042c1c260383d607096000320803e501e0740e50136160040c000c00d010450a81e81c09010204100308500d0700c01425214003041e0108240f0302d83c1320500c051031130490880e140c002503800381400421100d040c1d01c5100c0c21003810200c0c00d580c10850700300340c1d81c1088880ca1001540203040c007022800078402e100079154224000c1006510780d0f280c2c8900d044118a01440e140d80c0c0d200e01c012a0344051240d034040704e4100e05064800740d91085d008009512a12818007 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 911884253 1250 911883003 911883029
    0xc050909132018010b040f090501050609010e0d050d0216090905030901081008030c160b1e03092a0102010c020d120f02190903171e03061503010906 65
    0x400a5212207800d6141d42112550000248090b0380342d201d01c00c004126a40525120600303654900d041c1149400f0300b0416840319200e91502d94035100c0356400e90010440141080c0040c841034683d1000d4800040091802c001c011b1080ba010403644005140d01030098081c0302c0c6622070441d000103800302941d201201c600e122031360302c01d1104220781c10784034001e0180d00700b001000020342c800c0441a03040102213059040c1d85070344030401e910f19400a071030640c1542000d9160210058058100703001400000212840c0070844804074420701a454940c1e25040008400700303900b0402004880c2c4000fa00001c0204600025403841d01c4240d06564401d00540c20154443c045501c04600400d04022603255941008040e4007044080c1c010000507003d22036013400728078110302c0400421440c044281d210020a1350650030300c980c501d140c400405004a0003007004840404000300c60101c1c40c044040b40507181d440c0d080004042e0359820620011700f0201000229a0000c254422802c403582d619140b4 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 911885503 1250 911884253 911884261
    0x6031103010e03191106010303090302011706101211070b0a051e220803190e03032815030827011718070803090411070c05060a05070203010c050909 65
    0xd8241d803504281e40c80160014801841c009000c1d007180340da5001e1314100701045900c0c00640340c4c500b101c26802500007404281003041913580000d00d8880c0c03a160001c035410030b40f03028000f288404030040020070822101c02820540240980c1c01400580980c9034980d688031100d0401000008013645c40300400e0349403c0c0030603101680c0d410308418808081031b40e80ca05a031004e60700c19161440c20601d2080710401000c120004034410002e500c00c0f000d4903107014648007881c2c24081140c0d08415900a154020824492860680c04022810604c20980f02c10144103100d001c001130000b04e9840507018240b0070011081080c60000340440050042040c15085030b02402c588040c1400c08903180410030000240b00040460044c40303500101d1428040000c04006003110300c1c04061740e00106058001080310001ea10300360050071010030b000c40341e041c03c000351602c1d130201e00e89052041e244600000154200720b14014415101c8c01900100204150301c071506025000b5400984164459401c0b44000f03 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 911886753 1250 911885503 911885509
    0x2060732030901201813090b0421080105061b0106050a2444070806041515030c0c14030409110304051216151a0604031703190906060311 60
    0x3c1c845144001c025544d0303010b031410500500021703006012074447c2d120f0300c5c600c0100d2000003030107000ba4820b0f0810020491034a00302c0c440411448121706c01c001800300104980d648501c1507074100e104820300d03c01d504203821607460050519600503074000c1e60f500300c00204c0c9140c40c0603503414260007811946090108107001c50700c5221501e60341902e0162980c03070030300402051081001207881c4000840406000007884401071070201c035020005010401000f03014142030240c010307000103420340d02400030304105c0641c0422501541d224101686d80610800091060a1240195401040c205021715010341855101c0d030081c043c0a140d030f410540e0760441d8030f4202d000c0300d104a401501400e020f060151500c62264417456000f405c00043c65269400700d4181101c080150805100c00241340d0071402104100c0d0820002c5d4903c954420310080000c59110310a0f40207211314500d40750303030380d6071100c00443c41b005003412102d040c0c903e0002c200c0c0800445038810001d484c02034220381d01050342d500170 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 911888003 1250 911886753 911886757
    0x2a1506060310050621090a02101e03180605250c1109040609020a0806070912050307030c030320040f08010c050a08060117040311012f090a0302060c1c0206073203090120 74
    0x86035804c600150314943c0d592099018002240300ca40cd0200303040300b9500d520301036034802e454035003640d01e000700402103241c025140802c0c560b80604041c40c429619480b0b4084002861090754010285c0d60f00040070891158002c8054590041c0312403845034440881a5403564100c481602244400401154030000041c1d00d101180d0f00c2002146042400d43e8201c4188100c0303c411014180c8403029941c1118101ca0f0041d54400440143d64466117040746110510303a0030f0b4030940159241c003003083d030b105034403400303c1e90a0034150170684803a031035080048030314041200000030500d004034180300030580c0c00010380702e0411003000240106184c0c170168a10400e410410840c00150303800d0505001104400035103942ca00042030241d4081d5681c002c10060fa0290103020b265130825508901036a8110051480515043c4004c050900d4080c03009421001e044144411458001160a6281c8015032080724000e80c0c9a5200780c4900704100014042c0840401d285081c201c100640800031201a003 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 911889253 1250 911888003 911888027
    0x120105010825050a03140c060d09051902010503010308030c04080604060506030d1701140a0f0902040e010b040302090105120c0d0b090d05031b2a1506060310050621090a0210 76
    0xd841d40d124a5a41c80c0e070b021b05101450381c0075030700500c04009810359500c4c0182440c072407202c101080761183c900d0524200064200050884081c0d0317144000580d034020252415280e0014a19559031200c4650380035501403540404a00c0c41003030100400c00a032608014000d842c03e80c00c40c2c110380c1030910b040d586844041401c210b00c1680000402c04040441100545200d02a224800c066119178072261203602c69001a01180c2d0006020006420640a4a4010b14402c3e2071141424295400103103c0d04041c4141441070751f010103c200c040320140642200e0329401008514200d0306850052701c0c007102240c01a0700c0c0d005109891920304d0240741201e200308400d40340c10503040c07003644100c15640c00441c5c0d1030294400f00e502c0580b0381c6001c05560103031a07644074000c06802e5950484100c02a60051034580075403418010f11241080e40c1042078240ca1040307443c1c64071007061a041d402140f20f00800600030311310140901209160224003000c800c0e00070303203170000c1e07248055105481c0040107417 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 911890503 1250 911889253 911889259
    0x71514071202090d02090108010c09080f0703030f090e0f0403020111070305120408040b040f08120a08061e04020f0919030b160203040b0d0b01110708070e040212010501082505 77
    0x60300941c128180c0341d00520396940c00402c0c2d40d00f404926004111114026004000300343e540f540c001110b02d801c568400024181c00c0300038526981e4070850b01d40c40d9001480000d05114901d1800a0100d015a00c508060b2000510540e0245040d080f000740c0540d0070340d000d801551038000003140310940082201c288a41644030517290040140d468101c2c50303c0100141c0304641c040c8404103c40e110f0a005000400704103040522990800c075000b410030840f441ca800768402d04116140c00d00d600f215225502c28422541c1d40c441d90007001107910540d00480c0c0d21b40c0c0c02031001411700d0503010303071a01400750b5100580b411080130490740450740c00c1103ea400007412078080c0200042e0422080703600e0802885207031060360b00b040d076568142c01c03c035040400c0710242161659909046035900c80d2468a1074440c40c1c0061500390320b080da007151540c160b8040c1c03504c0540d18000103070943d01d032200a45503591000c0700030403244d80d680840c56212100300d200603500e07083c2c80b1108010450313042002c1c0c003941c1000f = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 911891753 1250 911890503 911890517
    0x20906040b071406070c0309050307181503080f0a020c120c0907020a060501230108160c02040b09070302130b030903042106140702100212010b07030504080307151407 73
    0x71a5828103030407452080b5840d8010650642030240d0602c9082d02808950701d440b1801451881d0203805450140c0080c1e010b903110600800004c9503241d4800b031940c1d4006000a1030600c0e50030900f8560185820140c20140001605e001c040076500080244294030350985a41030400010441c0c0301d2002e00d0001500e40c4108040a070303c1c681455a250020900d0044403000179241d9600020745e0b08c03d1b03010f0208182c0102424140101010315840700d000c007440c203400b0524100c405040348101c06001c50040009420f544011911103034816104500000c1c4039000303501d08030500034080e500074850700d2414240e418000031250588415640188050f030051410181460003d202e591518007080b220b41004920300004606640716110000202c0340c161811803400c0c0c0006883d015000885500d101e00c100403c01c01a00c221140606403107041070311f00c1e45d030019070500302c0f030038041e64000c801b15000015040080082006c1c0d6201040440ca40034800c000e000c40001c0d100d140c2c11201c0700c01244031 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 911893003 1250 911891753 911891759
    0x1c0308070e010519050a0c0c030b010509070c0308040b091212061c11060a03090b09060f07090e01050910080303240a06120e030c01020a050913061508370b030102090604 74
    0xa17001608240b401762a0900c01c968140c1c90301c90b003800642e801528101d51240060099041c0980400da0290440c20107044901c11590014800500100003400c4480d2039804513019400620040103500e0041e024143c91711200061032a40103801d440d041e10544990758601c3d403900b629020300030707402d0700580041da045050a050011aa01c1982441c0405a592902000056180484501581c0908018442c0d0f2800d042c0c180c07040000907044000380408004204416180c18a0150660750180e60340d141503210281ea8055200b40b54200d018503007c0801004603140340c01b69001c1036015a241c1c610300403190074040c0042040c0300e004440c00101e80c400c00030718040c81c43d0403c510502c082c00450340303070000484055003240c106d0603015000800000c1c01001c0b0b17243c042543d040e05051507a081049602d040104400908100325610a000031480082e22625821150b10a51840c201280f88140c03050b91110f410302c1c1c0314168941006140240c04090345c1414825104401c1c000780c01a0301d03140c2 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 911894253 1250 911893003 911893007
    0x230f0c0d0c1124280c050702030d030213170102070804080a030206072607020c190f051c1709031509060f0106080c0705120a090f150e040b1c0308070e010519 69
    0x205182d42c010305455440e0900c03011300510301c50700c84039415507903803a03456078001d20405040c50a070910a404060050100410724011120020300316120b1100510411044103a001d019000320000905520300c0410005201c840110309420030a2099003500d805035140d19041e60141004010401c51020350a4007444909440c81101d0308821140110341e0003207004000112000c400818141640071500800c10000e078130702d1590400352904480300c0c900720f001a071884c8032203c4040e2000e40805080241600c644d4407640c121a403103440501500e0f040c50303151503154008101500c141c44035210b4080003441d004a41c41c01c003816030f40e1507610b010294554281301c0c220344d041014250380b00e018008102d05203408010040142281c1e5454500e80940350101001c0700319036070b0340031500c6a424142100f0841d80c1c13140c805610098100c900003060090070f40407401480300c42402c0f040c2a001c03481c0c01c80625422204040c4500407640d01ca4094240b400b00448041c0640c0480c00f211064088500c1041d80c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 911895503 1250 911894253 911894281
    0xd080708090a4d150306060702180405011b0804030206010b1b0303010f1d01080d031e023c07060c0e060a0c0303230f0c0d0c1124 57
    0x540c00c0704108901108850b04014000040181e10702207011a110001c0f00074801e403161507000f00b04649004120741c0c040d9084016100c01085244240300000d032950456075000c004100c400c00d0b13071510715101d05e02032600318001c000360405809007080004006150758421408140301e140e042d40a014241d2821a415080e900070703d0120707840d4513089541d02e680d0002000030314020000603586101d07a81c9000f10500340c600315115001200001540103002001c0e000070b000340343c241c0e985400514144291114803800042845102040d07000054600700304c0030b41900710b41c0c81078001650810032000907112081c01d840015114588070b105107c424045000c503440f00152541c1810246e041400d1400060b1a56004001c501c02041c1d950541380c0c14558144682d100090080c0342e1010b107000300000c01d200d4448001c040080ca41900000a498a42241c0c199400211801e400307002a01d03904d90040e0401c41e200ea249100c0c0d1144490031000c500445540a09a9030030504042e895265400100200 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 911896753 1250 911895503 911895533
    0x150907030e01180210030e030a110c0909060f0a0501120803310b1506040306020c120307091403060411120c063006031009030207170d080708090a 64
    0x8140d44140e520700c007000a020700c441d4050070034a544218002481080207000080301003004051400d24134001800000044079441046420b0040f0306103003a81e156131402d4140f050042d0024140d4051003c12503000400c41d02170b100d0202926410b82c0c4e01d04070302c4101d9600740305480e01c001058450b00e010509680056400200900045102640b040301094001c5034440d00c0d08004810074a03c481488005d1070080e4002520140308035682c2c25440c002581c0c0d00682c00054040769000441d400780d0032003003201030340040144944039240d05e4031020240c0328466910504501c0c80e03011090301810300e004030f000f605c100d03480b0f1b00c1f81c143c540ea4101440020401c64103021075500c81c0480b424490f544e00740c0030304404122050f80201816105880300e104200ca070005410180c154401e000d100d80e00819800103000c440b40300054030341c1c4581000c9245c0040340d4001ca10400c0c0301e624034a410000440d0f501145420f948850041e41c07552038048460700e208940c0315070282c209095410008090365504008 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 911898003 1250 911896753 911896757
    0x2a130509010f090b1f0e072601080c121f151706010303050c24060117070f031e0510050108090718020a05040b0a03050a0b030c0a0e06150f030105010201060e150907 72
    0x24146d00c3e84801e0b03130203080c240c2e0510003094003148005841041c4104040121518000100c4035514050070181c0e00d401c107055481c8a4140300e8505070400384208a80144480b007807000220860550041a0081c10342130322840c507020b603201020541e520f9001c4651000c0c2e802d0002440c00b41e01e1618101c50640080d90380003035170700030f07958400294034411040502204003c00007803058100b0800150501c0c0c1c00e1480d089050481c42c0c00c200c04140c01810550000e2694207000c01d203c1402c00c1c0300140e40c1c07481c1d07000c00360300c030316120502400c0c00b0a4402c3c1c03c19180c081e2101010360b2682c040240c0d6a81a034403900c2c88103804107032681d0324906160060300e000622424003600340382d03c40f0000c01040d00410403020002e0390310800c10650681501441c00c401030140c001d03000ea51b0103600403c031207075110700402c0d400e8803482c8042015501e40e00b4224400302e8810000305c2d16204044000700c0315074400c3c8141da00543c00c20710089100201c8107070950107040e682021000003c0e480c0180088080c0c02030460003 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 911899253 1250 911898003 911898061
    0xf0a2a0302041d01050a152f191208240f090103060b030d050c0c060c0f03030910050702030a05181306080c12030a022a130509010f090b 60
    0x849501030449111403d403d581d00d44110740c141030602c11030415940c0030214040c030f45e5010000ea11707001805800d2107040e5035410260403041035080402c0040c2944007021a01c03034030800702c4c03021030460f103606202c074032035868848880c40c00e107070403103c80005441104200b4400027000d0b990880f00c14415201100c05018084d4041c20b010000350160307401d038002d94580b81c640c00f2008107841c0c107002d00d01203802141002800c3c0151400c40e02d56803036900d903c2a0080100060351414030f801044114100b49409003201d940707190409030151110b2054411f1308140342804082036603280040181e68850000c1c1d51030038100740440e0700300e0a904180c2c17221540c04c444407201021900b91203001d91400390440800802c4885440014041c0c02d2070718400b4502035801c1844002c1c280307039001c29040d56400000200c14884a6000a040d1050046414543d40500c0c4d0343ca01c10f02004250700514410b0f0241d100803c540c000000c51031081c0c8600940007060101000f00150916102000b8491070418010803e4 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 911900503 1250 911899253 911899259
    0x7020a0e04031211090f040c090b0c030c01060b0a080106020d020a08181002010b13020301031a041a0405010501030c060c0308040b1003050a0b0f0612060103030302030c07050d080f0a2a030204 84
    0x1000c0320135000c2003803a42c2d100042c2c010200d04080565000d400c1c81035034100045100c200b8001c3c0841d426010b2100000c00008840c03000110400580f059003045030000c01020359100210500d980c407010752180032803240d46c00020254000b1440c5104520103030050021409682e03100015a40710716072099544405c8100d0301406d80395003c10b0b0340c0d0340906400000740d520b040303020040b9100c0d107413902080e80c6004100500c0029006602d038055120324030041c0001d62602d141140c40f414022507000300c3d04492074100f00500405402c4503040301d0184000c1450151281c0044421500c00c581c041c010640020104002460b400e02c4142c1c400c80104020380303815140d44e95203041820919041d10b00204640c148041041005413090304140222603001034959600781103900c43c001484054180361b404800207050490b00c20807199075503840f805642400e4070240c07024040d1030702600c0740c5080740302a20020703540441130b1150401030141703100100e520703803001c2103003602948526907100308142e0288400 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 911901753 1250 911900503 911900537
    0x3040f02041b11070906051e0a1e050f180403231c050a0522081201030605160509030307060b0d0516080d0216060305070e210f0307020a0e0403 63
    0x1840e2002c039035658070350601c107000c0c89007860440950004202203241c00410071540d0b6800703002035000c185100c040c1d01c8009a00c2c0c0040c52404803a402013081800c0d04a0b0180b40c40c40821255082e03501c01c031011241040780b40c080c4010300c01c45c2c04140c1c04851229001ca00480d00844c03102440c1c000c40400c1c0407114820500e41c01d100c4c0c0200000c204a04100d09a202071202075010307295000c20541c8003007100b89814000680b2440c11074401e43d032081c0c00c03024800e040c4105402140d0342c0b001c0760f961625103540d403854510010401100c40c003c1c40e00c401800004098410022581c0e450b1000740190304106c55a142c0900801c8810070003a0700c81c00030700714200041d80a00c40481a2500e00b49142c0800d480c3c10015420090155a24030841d001030600d95525031042c0b1095003035500a2500059541c1c07a04810b4035403991a444050780101c98503402c8042c0540e200d403402c00f500d8910259144446429441541e900075800020351101c09003106200c0e0480110926a120b4000d11300644990010350030 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 911903003 1250 911901753 911901791
    0x9061704110d1112010e07050f010906081519050103140f1f03140604120c05070315090204060e0601140c061315090c260c040b011202030f011a07050303040f0204 71
    0x840507060351129481d40c6615028845080101402c1d5442c1d280e027059080024000030282c0070b0a01402610408285181382c03810f00b01f4090741000e0310650700c184807807000c0c000003411032080740c0c0000e0401420b89842560185800c0c0680800b11134600c140e141c4918281c3c1c580c83c5492440d0725881d070300390008040761902421507144910710005d01030905207410041410812889041c041c81001000c540002d0070016403c02207a410034000d0b003180003519219009411a071201a5016040075000315401620400c1c41c1c1c003c503000d80b02c1043c0c1c0a030302903a10129015110f0386445640121000810a6140c0300300003031701324821044080034055401c0404101c520709441901e110f8050f03081400001d4a02d8038030003903c0c1016415a00620340043c0740ca544001d4501a94002d981720540c1c6410ba901940390100c42c0501c0c02e009644a04c0c0c4011101c000348001d103d14100900240700c03020b030080310700f42100d038150b8202000d1455951541c450045800d21082c0807604150f491554158040c20500 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 911904253 1250 911903003 911903029
    0x903060b0609030106030c0509010e011a03281e0b0604051221031605031911040510080f060a03080d02090a03020405070302030603010b010e100e0a0f0609061704110d11 74
    0x31804401f10f09110903c51403103416048248003200c9031005018440c0c02401d206603201c03940080c40e03500d5603120785400381441e04403490709141c0d14600b031407102c595290b0040043c0129070721081d25014030a281900c180c03a0b9000035160080000c100500c402d00b030800d0f131005c202404404865841113404818203080110780b820150840c400710912148860003119201c4511541c40c0036411420b00c04020558007440500380400310340e4030310030541610722000c00d503001818000c004a85c05040641c0152900e202100c8881c40e0051800019003107250151441041c0e03034005862508012100c0300250003540080c0c43c02d0341c00f0518040001c01070360340b401940d10512096030056141d00341340003854251903040c50440d043c0304810842c0c90f010703140c000c0e250f44d0b08412443c08000c00d28a07480400d082055035004011300001552000c0b82e000d420000380c508507185681c0c2c0ba032400d08020362900114000b030f1001003104803171351202c0500d8942840e843c1600c0e40160030364504c0104c6100090102c907001c0f8 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 911905503 1250 911904253 911904263
    0x3042f0103270803150a0f1809080f07020a150306030303060506070b0711011107060605041820040b04090606030209010803041d0c0c060f071d09070807020a06090b04020a06020d0903060b060903010603 88
    0x1a4203000c03014030548143c40c08686143c02740030b40403059868240c540910f98006010200100b688001e560b2150030700c0c4020301000c0d044c20b5900800b00d400402030142404142c010074209400010642000412280d03c242c0042ea03a4034035841e150403c80d6019000d070104100b56403903901207068140c10030001c0021900c43c041c0046e4440c540703010701c004d44140f200c3c10507a02c142c00030310001041b41c1071024203034820b8407140552401030700700024000f8102d040600e900b0070301c0c05030b03000b041101c194003800982c2e00844002a0030780c3d03100c00301a52440f843c0101854041204180550700500d402c43d40d40042e00d0300e51040c01d2130294460545051003c4030034114500120342805034803038000407107a210154005001c032804c960400441e4051202500c664100007a4100040780300c1d03c03d10070f1104e140c0d0b01500a00c002181410f0180d00464160b80582c421042c1540000e00580000303071b1101c0f43c0d0416142c90041c180b95448401c0107100d00020b00e45c012508001032030480d0f800f842400040c500c18 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 911906753 1250 911905503 911905529
    0x20901020f15010e13050a080a0201021c14011e03061d0d032f16061b0c02100302090306060d080d0e0a05010b0102061b03042f0103270803150a 63
    0x20200c030080806000d80392120741c1e40d08048050121b08081102e6100c580c121007401c0e6111a1054224024861340810740148800d003c01d6000c4020070f600a003801903c03031401d401c5d269807103640e42000c0320000d8140148403001280c042000420580001c80701500754a0a82820865808000d06219034000550700296540140c6017600201101814812a907011548880496800c00a40d107114902030341e4118a240b59003102003010300d0700020383d0030b2400c40c01c81c110006064005400340784120807ca2041c50081c18072031590f8070038404d0350411000103005080070b450307072810b118265201101c152100c0d001007004400f1011980682102d10a4020040170407003114204a42102c1e6148411811504103006001440409000d02c888a080408105a4a40311884c050081c4c0000520000078030183c400c0700b10b10f90307c10f039001c0403080000b070700d05001d000481e800c0e500303808444d4000c09185100310380b00781c0c1c08126210301031540010516112103a110309040084e4504040794040d00d40a0341e0 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 911908003 1250 911906753 911906759
    0x6010608071713080f0723100f0f0606050d05011212031a03240108071412070306060e0103142109061b030903150705030105010e0d060614040b0d0213020901020f1501 73
    0x3070040c02c1c0c06081000840087e200b12820036961600b10b0120301c03140040d101e41100203681031130f0744900d0604801403c10003a450307036000050410740050381c210b030281786000300000d03071003c501c440b2020301e5602001c502106917803c1c07000c3c2e0042c06070b020142d00890350002124455141003040c00820f03440c41c0c1c00507034031140038801c909a41d0416040003095811849080200b410045c0326460130360300480700b031074016400c440b026151204651014281c2800c09800103400c2e034082c0d031030f075041e00d004407041e014941c0044201c4c0d035a241c9003a480f80c04081d1a00002d00038560301c0000e02859400140b444d4900350700548000084481112001269040040c03149240d10b000c00c9071f400c12034016603c102c05440d06940241c5140014031640c1d05010200d07005020540d1000c61071501640d100508001c15500c940007400d4081340b03070303c45500440c507141407000383d49007041a8203025540100810006201000d1102c01b03508180c181034151300c5078010755412a40b051050f008140c850000342411589 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 911909253 1250 911908003 911908013
    0xf081e090304090b060c0309010c080f03040b07090503011b0e12120309010e161202040204080114011505310e0903070b0f0106050d050907080d02070806010608071713080f07 76
    0xe4454a89114090070081b03604415004410b8410303240007402c111007948050b0070041e00500c614100f01101e04000000c000800c001c47c090107004135017980c6e400d14200e032100d040c54221136805038840214130348183c0601c181886005001150b07a070180806500c2c0070304100c0700d483d001d030402002c032200b14080704004204109118000d000c1c2441d000511001030600018154880c0e00e01803510540340c0c0d10404000d43d1503a80444006145990003007080d010150f002c20400a000c2c02800c1d00b80260700341c08410588110265040038602220b0368685140190580c1e072840181007a00300344119503000000c0541c03c2c1041c1d00d1003103410b070020350f5070340740a45000501a0300043c2140032400c2441e00600c40c1c00d80c00740941c0c10a401d0f81000082e40d48a00442138604503e5a0001505200316844809a01d03804641da804960b06d10045800b103076210501030311103402c05c41d4108001500d001038500b60041c18410315801078a0740b00040d11031101e60321002d590358400c3d8030085030b4140c001151002c00c6 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 911910503 1250 911909253 911909261
    0x501050a051b0301030809010c15090c080f1207110d1a060a0e13050703120e010207080106080c130e030d0e0f0a200a0513050403020f010c0f081e09030409 68
    0x15820111446140b000c4502c600450006001c00351210a0104034500c95074010030070390300384039080303201101420740b8103110001600c5075442c11104148040000600f14400081c04103400e48048084c2c540700d08410798041c12500140c100362000400c2c1851000a07454114194000500407200340c0700244001b6046045484040c00840c01048004001c00c9181000c211035900406070340d410070400056418124541f011a4201410a080200e041811550800d8050884074001e0702611601d981c1e4046450072541144207031026070700302c003030700500070f240928a00079035400030540002e40b4070100350254a5604403c0303d584485946840805109404001030b880100120380108002c1c01c465940e004030284810071082001810070280030f1950315246014050308002c1c2802000001d805ea000c8050301d07040e038040d009405a0140310b016484180185c06030f00b20302c0d81711081c0e11403071040b0460303050704000d2a0351400a9142c0601c25100205481e55007d0b40000c030007140c0b51400d20003010112 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 911911753 1250 911910503 911910511
    0x30d0c171e13030c03050a0e1e040e071d1b0309072102030c130b040203040b150d0c0302010f0e062a0316020405250903030206060603010e0a0e01020f04030501050a05 73
    0x1801480c10b80400a94459032403802541e042c6885a15142600010b0b070315403204c03c24180c0d10401a0464448048101d0042001c010b0119018841001500f0009440c1c0b405806070b0800351b14982c181c0c9a860b42203440c3e0315003005180d2040212401f907220800040d400a46850381c00f07400240040140201400d1092040e07112048601c0d80703003c069001941c1e6940600000c1e000d82040a20394030090240c1d80000880c2d00c01400a6699150030300d0052100c070400c9464544041c0ca1140034981420038586d8006407550041031a542e2a05540056508000000040080188405121100740c82e604094a15035001000c009840060301c09529041612038060b039200703610a1000380742d07035694503014412242d0162000566521034010589145080c5601d45d01d070106d0041200c510b269200e5a508100c80c00b0381d0994207582ca810003000714510080c071038050112014000300b4030741c00f9564480840141d51300001458100d9800404145400070b40c001c1c1c400344d540e90100002107106000c1c4940c4 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 911913003 1250 911911753 911911771
    0x804120807120c030e0102070309090510060f03050603160e060a0b13050607020d020a1d09070510030c02010902030f07060e03031608180d0f0203010e010e030d0c171e 73
    0x203a1400101c000c150160009500d104261a080340d62002d0b4001e60168549280004c000d664600a43c100900154614460300d40094a0003000510040132800044280d414a646e0404407c003a03242c124094000541403940c50b0240c81814000319100b41034520013080003407100c0007a850f05008001000d055503011044901c010465203e5100460405000ba82c1080710140d8499110303002042800d00e03050740003500440307102d40c0490b241d00503040c03000c003016092480007880d0303490056041d12242c5030f104080e040001c40004070801402074000400340c80716840002444050b41d00020301e41550302404511982044a00b4482141d00203410502102d06071300a500d0250800e149003601c407994000601464800707d200f10b03a118440401d10640b10008020200140850901d0759a195031420120700c603620b040d6240c00080410701a200c40c034620711000e94101541e20319002e000e014101022420844031400c40c45050001d042030a000c0e048070340300ca185042c41049031034103c80c4080c1c04441 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 911914253 1250 911913003 911913017
    0x910030c0210140627070c1b0302030c01030b13050f101a031315090c0f09051311010201060503010213080601170a26120a050a060305060109020f090a06080412 70
    0x9030314480d4034503554004c00b094900386510f40e41007090032426401070820300700480c096001d00840030340c8580420303080d5020711102d9540c1c1d0440e80500708040341d980300094060b00030720700c41003096003e5071142000800140c04040c0804020200c0021500100d42003810480d140301030100207085885504050100d01d10041c3d045443c800400044d4040142070244034205444240100030460380302005c02d00d0060000d010010040c600914902e1250040310402400c0d003e0000d00300300640903403030240c2c0f0f02010260f005409500e0390000340da003013940c0f181550b480e06000207440c1c80910080030501c0f0b40700340e21030500f401c02d003555040101c1a07015805281d4908044070900c500418007a41c0e1039444a02082d44103417136a462400f4103204050f1035006240030480310018211001c101e4032070600d8100800590340c440c074100d4202d5030140005012684080010f02c000c1d110341d03000340038480e0111041420a080d5000042e0414010b8014a00140400c0140410007010540c96220714a10b814004 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 911915503 1250 911914253 911914271
    0xd03050c040b22050a180c0201090219230913020a120c0801060602060942100503031602060c0127061107030f180306020a0504080c060f03010302010c03050910030c0210 74
    0x101b031900c42e005010a40a0391000d0192440e4000d5010340b41066010b00150400b940a01440c0d040291502c150407011406091004032880002c0740700e18245402400e51216490310081c1a10a00066a040360820f2250b2404500044115510040c0e0307880382c2c2c2004400790074241003d0a480f1140d0010b0155440042444000c03600030500c0203041e01000c0d01c072076903403015034640d000405d0a800280d03000c2c1e103400041d00c5100a004030721482400c3e20540c8440c0d403581c48050582d03901c28400c45421800003a100c2000601d856030003003c0c03c00142d400400c0503809982c90311101c80e560742c4000c0e040c0da00302070408100105401189104040d145640303041040ca610301034051405082d00200304075100d12118202906c0070800d02c041d6401c44411511400f643e480502a58018000c0c405203100d02c1004c0b06061803c0d0f4200e0b420b420b400c078fc295003107900c1d40d030055500741c04c2ca980803802e00006200085190311401120403200e602daa4010034903140c00340e8040d0810703c217110fa0304d55150406600d8 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 911916753 1250 911915503 911915519
    0x120708040e04080909010306020307020d020d1b050709050903070b0f0c180111060406021809190b0a0315060603060605031302010e0102010b0301050f04170301080d03050c040b22050a 80
    0x5034007226500c180c00040c0d070381c41d440e010030640710b1100000e03801071001c40080240001503010718840c490765022540f241504c508142c0e07852801c40315400001d00c2d115a40c6555070480c0e000c511046215000316001c10303071100a00303400e84008949420b100d900104169041c44128214550049800802501c041c00c00010301802c0380b050409188015440b4030154440f80d11621005a0140014003962001c0c02c15281481c0079500c0101c00800b1041440c1c2d56800500d82080e034240a0b84505917195290880d0b04890b001414402600380d500c1800c244000010a150a80c180f40380ca0f408040050802d04260303002d8102e5106070440c80c1000024410889601090000090741310740908024580520444c0104d01620784903000c0c80e059402c007010300001400140245009503c0754043c0185441102e8211103030b0f0009124290090380000f08860a0034086e40c81141c001141070714441c50a41c840c0300d06101e590040c0d01003081c0c0120b40d10310703009410090014001402c42152040c2c0c42a26260308 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 911918003 1250 911916753 911916757
    0xf0c020d020a030605040f0b090c060d0b04061205030a090b2a011808030618040c1703040e33060f090604170d080c030609010b0304030908010f0e120708 67
    0x2406000004004000e40d0342e081600c0c0700540c1d01c0700081c80540350518200e0b07402d244901c030482d5801c0142d40030541c0320801052044035010301a00203403c05250b45854400303071100700d140c00d41080c1d80d0400881c084c44507680511000b03004600441da900c2c40030100508040040d0f002004510045c030a402059110300c40d82b1141c07a680c04940302c241590070318a02d0040614116101c280c4005012040c00c00c036140d0041c0d803248804841c4601741110040403a80d4581044400820321155194180030003007102d00035101d10a4801c2c1140e0910342c580c0e400b01c5100f8010388849103000c0c018a0b16031310304800211a08030078100c200d14401544c5400000c184a801410102036401901203081c0802d5202c00081d10024040d5107a0003900b4230328084c2460302c2e0f600411210f000074241d8000140318075020b80c22607020701c4000d040314007d0383c80c080c01481c02d030700064002c4007041080d03500050042e20074001c8000310551303c2d000160081c0c2188040e0314001080e040291840820f000c2c0300003107040101 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 911919253 1250 911918003 911918027
    0x50a0b07060e0715030903080105060a093b0103050606010c020109061d030a0b061302031504050414010f06060e03070320030f030a0306320402090409060e0d02010c0f 73
    0x70012510500b021245401c001d25a049100c1038404648104051a0b0541055405500a8480d6905e0766221814820720f88a15141480030800d400000c00c4100d80d0003024140b003e0f030212461500c0d0300610300c00d05c1c2a442c0049204d0307801c0600c8c8014000c0c080c0034000315030440024200750186190750780c00a40008920300c58042488245081e214208149000c038901c40e201c01000d88407030b20a0b9261001c09690280e4400d802030390050011520102075200703c80c02049500f1410380d400200341d04100103000003c2045911800d202520036104109008030f100a43d500030b00452114140b940040203a40503d446602c42d601c540c03070810118000904c008075090b884445031a0000301100403e152403014448803040d44000901ea4000c41d525034440010303600007464a0341000c0c14424030358903080707040f000c882ca03042081c0c0302c1c0a0039181c1540103255648000d00042580383c1e45460760000c0356084020170041da041840d0b46168254280314400c4034000505054074105e4250342c2c01070844036445 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 911920503 1250 911919253 911919263
    0xc2a100e15090a0e130b06100e06030a06120c05010f021209042304120905010509030c01030f1d150a02121f171e06130b1e1f050a0b07 59
    0x1c038615251a60010f40707000e4140c80d0401c0080381420b600c0c0b401e0f260748042c0155407441c80c0e000401c0142c60030120720317408400e40395034071903002ea10300c02000480c1e4005460b2031042681c0701d2000819040c8221080040360181e4110b40b895484d100014040880400d130a02c01c541011001040c07060001c1d00b654241c450533580001c0b017800f0203100003510410480305001e000d182078208820018400825005256260b40b15581d440e82c903030041d6050300940000d2903141d00f1140445540354170a5001685000240c107001c54040c0c0c3c40600600224140900f01d5002d070884a6212820490030419540040d030b440d1f411807406403421425005071001a0412000300005007046503501d840c2901c1001400d940403110610310050502c9a550b0a465a403600c20f08540302a03448181001051103480380b10314681c0180201c2c41690b0300e4010300e500074815400d601c41c1e070700d40060314400d21300e0041c801e0101410a040c04d1000007120003004490f580312601c85d0001090620440c6a00c0c015507002c20391003 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 911921753 1250 911920503 911920507
    0x1d030c010e0c01051602030a230c0904200109051c061503050d14090a0e04110a060915090e010b0301030b090c031911030d02070f060503090a080c2a100e15 68
    0x1600c0001d0174002002344c060310407107502040400305151403140c0c160903100a002c0303a004040340713000d02507285002c490141c090703203000c581c00c0122510700641c9110004140b40c180292604e44001a400580f81e0510f06454106d1080220030816541318003201060707401081c540062560f5102c983d24101e1a03810030400c1910224045076413139060a4a005110052003440d0040d121400703039001500c100c409442001c1c210002c0140c2d03003440d1060700250b48a03030b520385545604211207001c0c980d11007202c4170304100b8004c04c00100160a4443c4038082c0c03003844030303499695146003040300c0e620704d0151541940340c001442c2444142e0b000640c0040004045550755003660300344c10b1012190007215510750f054080c0c88040f402950340070031418255052000e000e0b2640d51a040219858001203410303181c20b60120040d0030101700071002408110b44902c0c110307102071000709035202c501c00c4c10380300148500380070120b440c16a1074840c03c14914200145403040e080c82440000503041e45602007140312410340 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 911923003 1250 911921753 911921797
    0x302070c1710050406140a1a1c0b0a1a01090e0f1b2a0c09010308160c0923070c062027190b0a031d030c010e0c0105 51
    0x20b011903400401400030800c4503241c43c2c207003c3d01030030102079148010196040015020f030701c41e2091540c14410865001510f801040c01e00c8040300e2081d050908110050045600182d4440c1c04507210f4007507007401040c1d144040302512000c1c400c01c411903041c400f40c0309051000641020005920a880820900ca99103079001c049028020340560001d00003000180d0300b01210766030a120f0028016403440d40489000080c0301c0f600c030b0407000d41640c0d00c44120030040010501c101c000c0c1208071900c01080400f508243e880300c680700c1050784240a015291088541c00c860000020980b0b402d01d41d025801600d000d40b801850311071b12440003002c0c142d0f00c80c821540000809500b4103a41407100030303184d445c034000901c2c00002c445205e002c00441e0254550718081e007003041040b05203601958401c4401e5051082d44800f68210004840c10141c2d282040003d0010708807a449195034100055130b503464101c1c680700d096520388001e4400507401080b109160340d070b0141c1186c02805080543d1010169 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 911924253 1250 911923003 911923049
    0x61305070e04230c040803040b1e0316170c040e070c2013020702010203120901180b1e090303150105040801060e100801060b0f0d091506090c0302070c 66
    0x81040c0503074006107807200c0308007890301c3c0c41620210b1a440000c040010303a95111840403c0c8613600031880d95410501040081e518040c01500d6140c240740c0545090040000d0396004030b400454410f6900010001038485003a002300003c40700c20958101030039149851410f06800d841a8401d0352414010f00300061360117032094a0034261190304c4010b9804200c8a507240300446001c0401d42441070016a5100e004540c0a100f160616035040e0003031414129030703000140040000031b00300d84055485003121400304245524100c2d00300c0c0714070190f09803400c15110400c415003d0a041f00d070210012001d02c241c0c206c000003070301c1c1c2c0410740380c87c40130050241d400101c5a0740129480540a5800c10502007200e0040310342c01c41c4070303010500d13140846560b1000391030b083c1c072200d22440d02038840030803c0002017402c3c400180381d110000440401c4a0203141d40c0c407558003031901c850061440d95a5000c0c4481101e0f801040c0126425240540c10b02405417103651080240b072164072140c040c04202c1113a055 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 911925503 1250 911924253 911924267
    0x20102032101050102010f06050d060222090f1b020a02120f011e0b1903060b04110d05160c051203090708030d020909131a070e0d032606130507 63
    0x1d00c84004992044464980040300c66000b0700034039003d54203010000440428510408049483c0140298100180f0f911504000d500c1545904034100340404d2254500e42009032280c02018405000208494000c61610403184221030048603100d043d01c191040542c0001d01c40087d9804403044001c000501e0f2426141c1040040362109a5083c9104040c09110f80c8030103221514040f40c0c14880701898800b0000c3c90044243c1544800001100c10300104407554003a481c041e1018100243c0d80304c1c0c1040c101e615400446000300b405850340f040000d080c00b4038030321726010b5a080c1005400320b5569555603803614410034041259500100000d4840d0504000c05c3d0014075000342500ea46540311501c1d00b002e036203c0c50800e0b000340c075141c0104401781c07050100a462150080b04000741e03001c960034100480072002e8102001c00500707240c22049940c800690008051107511010012110b4038074420102400d0124140c0340c5400d54208001500c401c0880c1d2004d504c12007000940c2d60300c40c2d00c159244 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 911926753 1250 911925503 911925517
    0x1051801120210031d211207030903050403020409061a0f060a0e031905210a0c03110708030a0c0b010e060f12070b0a050703120902130b1c05011d0a12080402010203 72
    0x40390065600b0090080c0820640d08590580c03414414810031a01096024801c2d047d183c0b5140303400708000b800701e501c02e90040b01e04a120b8a05a440c0950307030740000d82941c501c0320041d2451a40c8040c085548508552049440d030800e03100203800d10035480001c0d0060150108001c14010400d82102c1e1564050000e403020780300580046085504038280141d4aa100545541480b4106000c0c20079003000030701529214512543d0f62585415203507000c9680b01c40c52a000c40700c6218299010400c502c081c8081d0090105541d1240c0c16203041c0e090003208540181e11240300300c0c12400c10302146444da1186507641507401c0c0d450740c018110310341209142069560081c3c1040b8804555884416400350045c249a8026070300c460401d0400030107041100c01006000f1f50100482c4100c1140244907008030301142c0c070080218900414000070b04181000480c1d08651a9645c0c5004ae441e03004c0c0c1401c182c3d14044404001d2000f00807e541301406203400c03011100070700c1100c0c3c00103011680300308112054 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 911928003 1250 911926753 911926781
    0x60509060f120405030c100e0703020114070b0a0507121803051e0408010506010f110c130b120309040c0807140d0b1008072a12020708070803030105180112021003 71
    0x9030303d403074103020f6103139000307241c1c0c0d851746005071b480e107000318840340c018000ca0715020009098041e103582e00668401c494520701c0d40c00a141800314030003007000b0807515441a0088200440e6502d4200c0c001410242c80f5030760110084e00c0c2c481c1e1840d807148102c940714101d65050078401d40e20140b0125184005083c0c4c04104450361000401164092041d00715902075002071729082c5110542c200f003034504031750303c40065026030300814111446261040a41803080320300350000418010b0000811442e010b0740716941300b00d07400090307082d9490038140316400c42c1008078588001da606040400400c02081500c80b2002100041000340030b0350300d01c0d806041c0c2000d000740454440c1c13544140103000401c04131107100208013104010121452508001424510203140c034002c0040313199600034004804100140861181030404288c0440c10061100039008035802952290714103c204104c6015200c070800f0300844030001000185070b842e0380042c82079812500c101204642e44402c0b001014030307a411442c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 911929253 1250 911928003 911928037
    0xe0102070b162a0515040e131b080c0915010804030e01030f18060f0606120e072606100b040e091f0b030c04090b061504120822060509060f 61
    0x2400c0018070401c40c22540245c4885044044002180015020358455040058030450016500c049440b10020000b4400c0c00341900c40ca0f001c2c0000a08203034070782c11085a59004156501d420701d00ba05d92550700c00d802c4c41c0e00410402c0c4190008040080c06030005060110040c03040d54241e0103500640c0107046a84001c00260310701c00c5514007101026442540c5030391800300000c00000b4140503103400d490150b21885070100714813822800519a001c7d0902150081c3c41c00400d24007003002030011410800c00c0787c0e0310711a1a141c00e840c18440c0107080000b494061500c10410b070420134054404841244842010f2a500c944a00f418030011b50f01c00803041d01050b807a80d04200c5558001d4040030401e40448024044c41000c0c40202c034400c1c0c0b8060f0000119000084442c40d01000e98045a03e01c03d4000d07003844d5542c0b0380543c02c4500c11078211250704010403101200100240c0b20482ea210980e4032044041c94160050402c0c45601400d5010b8140001c00f13115038100503089654521003451542 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 911930503 1250 911929253 911929313
    0x315062113031803050714030102070204050903070318060801032d03031a04020304080f0f0408030a09060f020c0a03080a030902030f010f180c090504030e030a060c0e0102070b16 78
    0x1c0448000031021008211850f8000310700c5600054507030203895210b00180003082c2410300c9040c500d4030720043d5580c1503400700000001a1154090344d4050360580d0001d58a981e41d5140c00340544d0000c0100c526500d1540500300300030b55000007000d0460b038000c080040544407912050b482c0c0310440b110b9182503894014a5010168558041180300c4107040301420341c0d103011002c2105a2005640261407903038207004410807044108014000e000d6800d5105281503070381c0e83c0c4241513400040401c0045007061101300f00c0d0f81e411000031440c4031503a02c003409900b8030090000310312034a180800703096a0004100209994042c1d844012210340050440d03050450980100f4043e08500c406032031740500302007040d002c04010103064542c4650002c0100d10450415038610000c00004000780e081040406110000d910140991101c05008040c08203000c082c85401801014481d00e2040c110352150504100600321078064071183c1d20300d01c8650a919032582440360f51401d8516996180c820803006203 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 911931753 1250 911930503 911930521
    0x6150a03110d0e0d0801090c02030d0c03061a0909060909060f07230301170106050d151d030c0127021908070b180a03120f09030804181103150621 64
    0x250904c83d0490340c404030f040ea244c101030740590b01001c40210159201344014142d90f001508405402d42c0d09160001c2c060355600800f10100340c1c2c4489020b41c845001800c010300c0c0c0ac06c8800c40c0c2e070080041d100400c1c035084ca80110ba0340c3c0c02008001c46079004843c80428a03e610440310b80030340c103203085019864604c000704e94241782d40c42032060035407001440c15590300026046c09002d0468138000c2c501c0c50b84043c00e03114070070329115000001d884169585000701c0901840503451311901080802580c8071600810424211150071710080800c0c440da1002c28100d0303800c60446401e20f0340c191015000440744c914130036076448043d0440b16903030060070008070350011004040c00748480800c2250480b00048070500040710040d0002910710100e500800400744d00940324900a404a0301d86000d00603980e48443d20650000e41000001600707101080745508218001c02c000302c00b0b00c40e070007440c40c1800500e0300c15038051015624000e8201040100c99034070341a0700c0c2814800d04115000e01c0d85000c00070 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 911933003 1250 911931753 911931763
    0x11060906090d0501061521091a0c0d020307050d2414010201020c030d0905071a030115020c1503060a05150a0f0507051501170109050d030e0106030c080c010806150a03110d0e 76
    0xa20156114280c1c8107503a502c465001d440f4600d03810040c9c2940e11141119620160349000f01444098141040008048115440294401d28030f0307655590312042000c010324141c8940c0f2014008184090b0101c042c90300400820200311044403460f18800c20b0a080140e002e80926422112180404a50204484c0c00303604988003840c840d5003a20341498446c60194090b0032420000c001d2003a0901c01403080c10b520308407100e05a0400c0c01150301000420002a450861115000d202040040706012280c10040441c2c1c01500c8101c0d01d0045520440100140900440030b01d00104403040f84032940c03d80c014408c0320074454010060b960161216411803046500c284203507100c0783c1d4000684040c1030410f00c00c40610540c80000303008011031421045020748040c05c415041c55607142c80000004103a10080801480a00050400300d80854000752442c40d00400585c081c441941d410740500807110112410b143d000c1c00d00180f071071200050042c080c003c1c03002e0304801c54034000650350541d00010f1 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 911934253 1250 911933003 911933027
    0x41509061206110f03071b02060c0d1e0e060a03060b0c0f39061b0105060906060c0a17070b01180c030e0d0c2a0311060906090d05010615 60
    0x4001d100031500390800e01c18910844440302c03140329017800070a203094840c07940c00b8112081d030102d65508080790340000c2d8850b480700c40c000119900648007450b0346c640000310715404100081e00310050002511025001000c0b03070504a02c150000501044a2400381e130010019144026503143c80394510321000395a0f4a21101d540c00707034420206002c1c4407901c00300006c002e4201026586003100c1d07590040c9e003044c01003400e102d0781c002428040c003800300d1940c0c8141c0c8000d0780e00d14008078180c10104180f1070100c2c400b401090060601708044c007800300c00000e500c0c00855210383c0d8401300c008404503850342800303011401071000808400014091f4501141c4024280d0010000c002e50300c18a4000d504031810600320440390340110b0300810343e0b0b9000f40c0741c40c4012401808071400440b440ba0982d0311102060311104101005180140140684144120b69540082c0e0300ea0385401c5440000540c14041e00c886207125080da0b52035401085000e4224800400c00c690760030008045008000c0e244c030003000 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 911935503 1250 911934253 911934263
    0x60b1b1002161e06050c040608090c060304030f02190b040b0f090d0f0c0209010e0f010b040602070b28030b01110601050a090b180c280e0415090612 65
    0x6809402103540c03034400c480340303600101410100e010081d51540c6034048a0009030300801c2071030220f40041501c2e800b07914031440d0b02014440d55142030100c05040840c000d0325030b01c942d6225042031201611380404aa0300076070107040081050000300d004902c1c00c02c1035501c68000c1c2242840c18001c00900e419024091445046503065603a951200396112a0f403c451602c081d600c000400b0064900608010070120803c0ca8002c0032040c0c80e80119aa5440071b0b03000c214480116400c00a08030b107600102070241c0344185e40649042e26010009641d002c00b8003030044061800504e440208019080c40740303121000412110309402c600d007010300100181c0c240140030402c6000e2500490502044860603078078000d00c29101141008021001005401c2c1c0103a00000c22a0759105044541803d4038070800204015540e2140c800a400500305441015181d00072071200c8840c00d15a0424001e146401040d0b90002e11250549401d01150b541a0b00c000a1a4900840880c154500182034807440c1e00036 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 911936753 1250 911935503 911935513
    0x801030606060f090306240b0702030c030f0d0806060903010f05060108090d1b02010c0203152409070c0c0b0c070510020601030c0303030504050a1202100e060105030307080c01060b1b 80
    0x1640e03060b03c48070040c14030000002c50884091002030350035030205404464801c03822401c03a941042400954546812400170391801043c0901145020415503c6242d0305a001c2d01d00992000400307540c4440d450390304000d1140020014105443d500c0c29100d40c414020000d200715019103909400508054a00314005019040080ca403031200040303a0b89016400e6980011001d03104050f088000200b002c22410040c030400d280002d40c0e0308004900005001c0040d401107410700310a400001c6030403000e41580c80d00040c0501c0b6195035a8007101c0c1e072142160501c044484903a29129144803180e40000f080d040d0b003c2428659000005120420350f542681c03103416000ca01d440030b82e50b034182444001c000480c0018140002482604400c1d0094421811101c4504169071006a00095911045c0c0140d000c0c1d03400d0018100c150055020002c0c4480c0a40200d5043c50003003512440340030307000f4200100000d0709107211502580807070000e001250045031185450039241450960082400c5103c0c820 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 911938003 1250 911936753 911936759
    0x30b0a031e0609141b01050d0e030408120d061d0a020d0e07091d01020c1c0504031203020a080f0709140a03051917030f0105040b040e300c0d1803120801030606 70
    0x22140305c29164001610354a08124841c144040601041403140c02180001c0c03000040c44101008403d8403800000090764585a15400f04c40885d40d60364856080d1171055030541301003180d0030041c1d0382c1042c07501d0005a9681c4007a88120058a0202c960401d184030300c1d08001222038196026000801808100c1604540310786602c070700340d003c3d003010501642c00410b007000c00221904c041c102010341c41c0c2400f500b040e5403034807074003000c1c009202d4a0011030740000d20f91f89110707402140c907984108070301501d00301c6090107035006040810381d020307200c1c11101c50038041c061652010804001954840c04442045d5844065000c0000c460102240e03039042c40f507040b0740301b1800d61098900c0b481840041070201c0c0e192104000c040c250300d071100340e04a0b50307515071802094414814018501e4042000c11340700000c641e426800040340304200f4428020900042036100c0b000b0560200800e41c0c0e14103083c1e254002101e03942018556480101030401580d808808541c0210340f09040301e0283c2000c0000640d = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 911939253 1250 911938003 911938033
    0xc2206020c030c090612070b0406022b30050408190f020d05030601050706020c0619110702060f0f0703020124050d12030609060311040606030b0a031e060914 69
    0xc83d4035074a42c1c01000400061814103203840361041c00c1001104a40c185a030b50403900900740c0c0690030550050700070501e06604841089410f030405203920b14075070310b0191190780040004000700c400c10a1003040c0c5070300d544131074068545050110030a41042005082078501103019034010300d54075100c2c3d140c1114003101a8010a002c050406058028111001941c90704891660000303042c82d040c06000e100c0240414078034805052044880c0c00103086038149000c4089006907186034480b4003a08111200001608030030541e410340380d050301d16a840348030726044038241c4c0c040d0302c91440201201180304024598150403802002c01c008036945208000140e01d02c0b0f0040c20350050980000072950810009480c040310030483c0442803600040b83c503107952030312060b5a0303103600c151140c40307c0e45910361462500e84641c000501d4075007410421003070304001043d9001c91620000d0081d003103d00807111201012840c40d80b1b03050340844200b1410045240a403019100c40452200390300c10034003c000c545c1 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 911940503 1250 911939253 911939263
    0x121902130f06170f061f020a0c0504110406110304050303030c18060f0f03061201060602030c06010f15120e06010f0311030c060319110c030301030b0a050c0406080c2206020c03 77
    0x1c081c0b0320545466a881229513621443d001e86503980061800b0000c45011505104420290569030701910140f8021300300616403e8840e0802c40c452450032403051702c001820001c8a0445e41d04d8203040146010f411017807420360096502103a0140030000810000448400061058a110382007241c00d0034034520608c1918012102d4002e1149001c21a1103480715922000e941d2110380140070440e4074220000503804d480103a440324001da800401d4036440c82e441840341038003500c500959000b41902d0004c4c1d00d8001e2041d50915800e000d900c0c0e000600741c0461380c10000a504e62641200da00c0c1d6540e580d0f814080d1450310064403180d0032290b5141030741ca00803c102c054000020810b90030b60700c2d80030f40a1101042c0c810482e01c0789a80e0078507180c07028201d0f4042d069507084540956165072450030421400d00300104681c40032450001042030700d54240066400740c1c1c00c00c2c5080c0300b20350394200c0c180d0a14440d10180380041e44e49003c0003c00000c80c00d00032000d8840503801e40b400020310b002450b42e64 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 911941753 1250 911940503 911940527
    0x3042303070c211505011701020309070b0a180e15040207050a032105040501050402010e15160602040b031609080a080d090602120a0c02120c03121902130f06 69
    0x82e101d006410420741e500000b959802882000c07203010000f409540308240c00740340b0001c036203200761030788010000c42101c141420b420110540095140d840c1a0030031645448890103880342c88000031404104541c404c11010703030b000080c2c010000e010307034980006002038035048804425001400d48100c0762410907000341ca80d8103a000c4010b02179881e4599040d1001c4030001c000c185408001100509080c0c41802600c1c02180114000243e038140b034000180080010034409000d0200081d40e580b90458540480305030818075481e0b071241c8042458100081d10a582c060900f002c008401e00460340d12102d00303200000d0954443d45209a034030494192070321007148001d800c20034103000082500c8416003101600c0c501c116801850040700310400900000b0649850341640d90350340e0f2803881690100b104d0340412680c902c45506150f030040d41d05a503842104101c80050b000d5001080d129103410300c12807440341d02890299101e00300c25134066540b55262141c4032800124000000740c040c0681d60007441d03 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 911943003 1250 911941753 911941763
    0x90705060c1519062709050706030e19140105100b09012d0c0c0609140f041d0f0c0f060a0f091806090f050c0414010909020304230307 59
    0x6084402c8440c000c0300002041c01501600245280b1403040151040801600c0e1381c0080480e03260104c00c2c6001965000400006840d1034034640002261000490388100d6480c0c1c034000c90761402c4400c15a01340300c02081108964113108811382c0800031090002c19800083c04000c1013580c1d00d81c81860034070f80c69440ba00c150701d04108411180340d441420740030309013a50b08110030540403090658001c40303455012a10300261406600e075003001002402034006000900c0c1c0181d80e18100058044006040d0304810f1040c4448800302c84641c0b50b0f6004148081c1040d904660000c007607404840e228040050210342030f0003030450840961400c060081da070b01c0c0000d055141060846081510007800902c00c03035040c0103004100140c049202100c41c025030b0a45600400e00c145002001006d4a42c1100c0d215a100c1c102010841c0c1048480d09440440f18000c280a5601141e4001071b101c0c01e4071134000d0744110703000200700000d001d01c0f04041c1c80c290713040000508040c041244115141d000d44e050040c0 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 911944253 1250 911943003 911943013
    0x602090f010c02091305010e030309030a0f0f1709010902030a060e010f14070c1e0303060905090a1a071116030309050111060106030f1b020606010224160c020a0905090705060c 77
    0x17400c0c4064040c4003849100002162014841d40601d1500704840c1c91400768400100302c0e0000360f000d0b400301c200c0c00903800c141c03d0b2102d0b2800701403c829400058610f0f140710b071400080002c032094100240e83d40d00079064690845c03030307400d2000241606200a1217076608166003014a12078a20030b512407c82e2006449104e6251000101e65103000c0707583c141c0b0a1481c0d4620500c12031000d001145805100e9100011844d03d8068010280c410050418481b90805200d071000309507500b103d1152440070703541038400799441c004140c4402c1c182000c04d407400c1c4104816010112610706110085e6402500c440f071106540b4801120318a81c41c0403810003035003025004000c00381c000e4003d6005901855004a00c10748403500c00d8440c0a0300301060f01c0181e0001d000d06c02e0958040c0050714004490f04140c00007802e0120600300300c80c4020304803002c015100c50485060511944605480c10360040504440c0d0346c0d9000404081c207010340700f10405010fa404001100e00d41707070045a12406520b00980 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 911945503 1250 911944253 911944261
    0x140f0d0c0e130b01170705030714041419110c010c030e0106141c0507051f03050606190503060a1205030a08070c030801051c0203030c0312010b04060503220506040602090f010c0209 79
    0xa41c07002102017400080d2192680228065130300340555409004c02501504840640100300000e59044e155003014013404e110500c1200c038000000300c0195000c128000c00c1e802e0b500040340302c036481030540300c44603075180c4803001c41059419080034003002075000080c042c49480c8c2c00280c00300041402041e034043d6212000d104004011281403000600800660340ca06a603203010680041c5203548512100c0a0001607000305038051107a65003014050b9440c50600c804840040f281c0403282d035120b000c1c40b00100c0020030941d40c160340c400242403a4666032840e4901490b16903500d8102800d84004509903100107484244110b80d800e1740180c00d80c1d41c40c0c025034038083c140710070614200a18081c00050720000c40150318104018581003015900075691440d402401250818068112110b6540c04000400110b41e119080e240c20404180f00707100702c00c0c11a0700100c9582280c0c01c004042c0d0041030204024015140d01030300403031005586108490703803500011100d005880da802984021200042 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 911946753 1250 911945503 911945519
    0x2090105070b0c04080102040608161403010b1b07080304080d020316020d21050406030b01050c0d030519090b070f0e0d12020f0f21040f140f0d0c0e130b01 68
    0x1da40c0140154811134501520b500f01542a0b80c8290440c0e00402e14180510a1030103041030101400c411a24100c2c2c00102502060081844184110f280404000c540c0203d003d8403000f0082d0100071032030403200c54680d10701200d80c0300e8015100c3d02d03a1a0150340c1d120001030340044101c5204041c2c0d241c50200710b03011542000000b90b010302040d21864a0107184403030001207800310100f00080c503120f0b6034071545006c00041c1a22218421181001000e00000300c070700b9030000b88e2124a5a9505010415075180350316040450384298102c0c005a06110340b8a0910610341c0c4100c0c001c010b240c1d18180601120034003603948881a80525400c200395005003004109246245c2800e2048e520540d2140e01d462025079290408101c2400001d40199950100c080c85520b00c40e5985003e00c2981410240740c0809009145810b10a415051032403640104141e5240680034003041002408a001d0103410f080c001031102480c09411006c2c2130314804122041c0135000d007071400340d901c5002c81b181a0709100715 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 911948003 1250 911946753 911946773
    0x70513031b0504020d06080c010c0b04060f0e0d17060a060f080406021c14010905091908090a1401081012020d021912060b06270316180608010209010507 67
    0x8241c8035404180e03008201955107000520032000900b802003451410b0064190410050000349414031526100490000d2842c5410701e078050f8204200045101407229020083c088000f681b03a841e019551003c1242c03038200007a40c0022604011103c8290f441f0b5040c01046805402000007080d00e8030340c034040d07413485000c1c2c20398414403858025003041c24200300d408200c404040f1031002d00343c94086104100c007414403100c0c01882404000d00590605594858444401c484409400d15408044d4404d000190048039032141020340502c1711283e0300e540a034548a5000314140c0020b0825005c0703450702d58030f628510140ca40624000c8200c007002c0e403c0040b03200d0030020032030f006040700c101102402641e510b22401800310121901c00026140b404a0480d504407030094880c807414481841c09401018001c16540400e41c0c030046d0f03105503840000d1401481c00b00705100c0021415020070b454204040c966080c0080c20014003445032135800302800d0b03000c0c00c1e4516002170024400000031681034a0 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 911949253 1250 911948003 911948033
    0x5100903081803010c0908060f07140705070b0d2c100b040905010207080a0f05040e060d030507020d0507172103060105040305060c0306010806031504110609180f07051303 75
    0x402d03075901d90300da00071900392a10400014081a03210000700051035062101c10303401410400440030514203c20081c2080d0700c0c401d864005e1b00000b10b00b074010054100f000001418440c1411600c0d03400d9251000701903c40d90714007030b4041e44401c3c01c0d6828012081000700c040d120100203003d0644a803c0341c42c0042000264641e801340e1202c0c18030703003c02c0d420300c0144281c1e40a1f030000d60303030740c000c410002d446128444001e004210042000b00074a40c414901c41d60451800c9611011303c0c45542400c44890040b40700207548101034008410030080c0004041c800c90369107115444108141e41542502c40074030703c03003240d021000b0552a45101040000460748150141082424a0f480351a00b83c82c100e01261400000300e80001441000d682181c2e03030543c4088103d0040c28242e25480710000e01c4a409800203004103200e06401c48281c0d5604140c2c0d80c001806820300410401c0c4181e28101d07040309403101c006400403400450403040c412011200021100038504010614642d07132034060081300c00c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 911950503 1250 911949253 911949277
    0xf060c0a032703050610050a03030e0d02010306090f1e020f03010e04020d0b0f01060305240409081605060114030708120f1926100902160501180c0510090308 69
    0x4030310750782c401c0440303400741c2c02a60040000f00054680900c10800d0142d060304545c0c850921034408100080d0b000d42c00300003200c0240c2d03483d41d180310b6910059019102a406c1468168100f4030100301c40095584200004203035104070901000001c1d444000320700c20100d400004400810040c01254085000c03203410503c0a001068014010f0f242d003181d04c60155042c0c801e0308014001006455494002e854200400b504a4894a0b918902500d0f0036200d003100140229107030355a102c02c0c0403143d02960160300d07d084012440343c0c201d140c10754840c402401462808204141c495041342030019264080c1c8000100030000c00007130f255085003c0e001987d40440c608010040b040307242c0000e05840710341001036151700312030701c50519031440c0c0d803c901c10006003840f44242c01c000786c3c0700408004008540104c0c03001030b81c0704c0d00748080190400658402402035030801416001e0740a58501c440125030140392038009071a1110104a82c82c3c11980300440000c91b6a0310601c0801d000078000c0c0842d080389 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 911951753 1250 911950503 911950547
    0x13060e0309060c0a0317010521120c01020c12070b01180b060d060e0f071202070317040b0f010b0a0c020f04140415060608100b0a020313030c050f060c0a03 68
    0x80000d400c0c2d44030203403800700e582000890b00c0c02c140c5c00c03011146e01030000e44c1c91804150704040214606a0b80710071106008110201400c21120041c03203566800c5013418181541c84440002c200d010f5417041e9130001c0c103403085d401c00c500b0800500b81555400d6a01c0300d030f480120b900c0c0c54404850410300080e0310310a0390b56a0400705440d603802c03005203e041e100c2180404c0b0203192045c401c0610200800101607440c0c2d1504009009500c00c0e01080c50010203400141c4428281c103044410503014464070500c2c01c41780d002d10040c0908081064891142040001d11913a03c0c0e48000e0058000c903400323440464035030340d2040300603d0202140f001340780c001b50000030100d042c0000340326004c0c410783d400c1e28041120040f4010b05411405050050b046078100440b1608084a0400e01e554140c440c40d0f0080c90041030728000c0038802e0044491881c42032038501100340d12800e0050703034028a40f00751072081a28002c1c0411301c2c2403000640d6400c15160000d00030465a0791005d444500307407076060880c2c1c4494 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 911953003 1250 911951753 911951767
    0x9040213090906060e06060a08071404030c03080405030d05070308151512090105060105131202010314010603020c0c01360503030a020604050708010e060a0e030f0711130513060e03 79
    0x124480c2d0304826005000c0841d1881c0b03042180801c003480038210700d02400c01000b00c00f00d0700d0b401c494246e810401c1d6142c6000c1c10508400d9458050256401c01400c5003d201400014031011034080c2c825141e04406032844950002c100b81c0384c2c2d103d620401408940c849000440010800c88924820807020b0b180410000c805034030030600c1e511004c000031a14003800d052121106092150b10382c80703e002e0900c3c52a152880c1c1c41e034854460544181c206000030039001ea02164402d402149981e5048140207844e07584542003c1c0281d000b019a09282d032083d604407031101e44c40ba2040840c0000301da40345040d001042c01211891038500f5410000c0200f8840c4001040d860410050081c26459030250459042c640342003810030901c3d502401040c3c0c1013402080d100380d00464a250045800200001c040c50010b2500d4118021519003208000d00070030030304103002e9100d081a016160032a02c00b03640402c0840c0283c1240c00559071001c51807803000508d00042e441350312980d50980480f007200c1c14051 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 911954253 1250 911953003 911953019
    0xb0103020d0e0102130b2713021902160e0a09061515090f030302070e040323090405071d04090c050a0b13080a0305030a0b0d0c0b0c19050309040213 65
    0x141e0b02820b03007103a5000901c001900d095502c0000036010079801c8502d800100f40c071154445408600502c28074406a50480690b81e8005041070400d04844040d1345804541c080c0c601d841c8e2080301900c0150040b07040403007a1045803401d45042d245c25070301c881e01980702d594000c0000d124100c022a413655480d84032440000c9079510200c01814402c101015584920400801c3d4008903405070000b500110018400a0b401154060a0710601040204e040d43c840c2022190101440c01746200e0049100d0f00680c6080b00d60010000001c095405102c0c50b120010b040b200c0460760b640d0401c0143c0d01841082c91450903811420500e0700845507280903035192400620360328425880a185e4010000d680c0070b00c59008070301d0702c0042200c3c1d805001c1c00c2c01d40d078602900380c0c80002c2086000a586610352040c81d59410f0000a245402c81005600e05496400791542d0758042d401d000c0480c400d1003920310380c00000001d850080303071740080518184030700f04c070621000e0f4020306c140c4004100302410118442c4 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 911955503 1250 911954253 911954261
    0x60a032c3007120e1f0e0f060d0b0d170403120c03080f0903040905090609010605010206090604150f020c0a02040e010b13020a03061203020a030f0503060906100e060a0302130f050109090b0103020d 86
    0x240400175000d0114402c40406040c4000e542030030b60203a03010318040b0382d5680d10f060607140500030502010030030410500000d0b04888600c0303c0141103501c3c1e5141115000110030150003a2482020320162180c22004107492001001c2401400580b41d00009a09082080e86241e0070282a10891f030826896244c1041551030440c0c40240d00e078030101c100a0000d8090084000403c1d0a0002d00054280b44025540782c42d001800904039100c00718004050800030752020030310050f10300046450300b0054070081e03107900c01013000740d2155060240080518406124070803080f00300510400040280a03110703c081d40040985009140c0c0ea000c0000d1640c0b280b0a0200f221072003540540444001072a0180c007441408c8003050401006000f0000c0030303100c52070042e070084021203008010000c180402c580003a08805601e8102078086800d44c4d420b500341e0050024000c21600081140d03499900c456501242d0340315103800035080d0781041010040e01ea100000c03640042c50098600880c4160f094151 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 911956753 1250 911955503 911955529
    0x8070e31020d051905010305030f0c0307020d0f02040605060c10050a1401170d02010605091503100f020705070806331f02010b01030b060a032c3007120e 67
    0x115031500f08210741c1e021800d04011110415520412207941142c40f00c903a03d00a822007000208400503c2d00d460a0040003501c0400b5801405103525a50300d142c14111560b403075038100e004a00780035022030b4924162050310358204401000b003440c4002c0010386000b5100142c0114003081d0780b6000070f0482d90f0f0704c00d040e038007820500d00c1c40b42c0b4900904107644e180581c3c0d9580d220869151410500c1943d0302e01d0803d80c0c03c00d03106a013095064000000003410318083c504040800c0f882e000e00c0029510f0160060104103000f0825500030340c2c2d46980791902c990003150008210b622020460044100213081c44025007109040600300850040108401410f03801c51602040c00201041d000d040d4240540728482c04280303401c0c0208943c01001c600d590184090b607100f81500c95001c07007003d0303045498444000e80c8e607255500351169054103090710740c020300000300c40007400d0560003007800005062320540d404100007480d16010041d19441e40710074002088a04010245d450340240b0380ea20f03501139040d = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 911958003 1250 911956753 911956777
    0x50a0c140d0c02150412080c0102222105060c0313050111030f010503010b010804060c111b0108070c0317060d02090405062d0a0f150803040608070e3102 67
    0x2000501c0c0100704d40600400310f51301861004000900c141c020010f4900c200e240d111032440c2d00d81c503400c0083c501900540305069014101d80101042e44a40c99503600122800000285200c0b101c4450a1a0314500800041d189510884c04550429010002150701000d030118036204c07a44940d94107420341d041d5000441c042400401131128402d0203030b0780c0b503004020031802017140344000c00c0040c2c041c1000402c042c150030b689025040340c1d0790048030044881c0c00d41c4130070b0ba41c0b00c0142080c500c5140c113105c00d201c0d00103112a0000746a02d4040d030b19080d02680c050b1549100340a90f03a2413244440300c014800c50308009070b84000340041e20f07201d00c0b25001ea4401d602420380c501e0181c1d01d148000d0310481d482c40b903468103000c0d0114523003003100303100d9082850302801140303a05484404c0c002800542180300402000c3d1140041e0060700800503000f52203407075682c0f500c130f501c07844000c94480004141496101203d000d03212105201e030041e050603c40700300c04000b1100303002c5243d001280c000e40e8420302 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 911959253 1250 911958003 911958017
    0x30304020103061d0604050402040204051203030a0501151b0314030c03090c0405070c060b0d0b09071502061e13060516231209070806250e01050a0c140d 67
    0x11582c00d4002d0001038020212031310b0441c0b0b540c406108040002410b4070340500e030b81d0808a01551103e0301107034050302001c0c1003040031420300080595294400c4569031035240c0340c0000400d800049494090801c2d86590754050b03100c07049800004000d00009e4202d045c0940e85003403001120b44074001d10310940181400035207901c2c00c170428600345445400c20340c1c070407450081088109600b200c40c170031780310360002000a080f100210200b009091a41e102074180d00e607800070821084400501602501d10100c0080081c40c20000183da8650040e1450b0310856410340d040400040c565907050b0b07009840f800e40c1c0507000e0040d01c07118100c0b0001d0740c4800240a20000c460f1149410000600781e042d07040b00d00071802c001d40400c0c3c3c140c6001d680d11006003943c1800c00300b40304100810521028142032002e070717521403d01c02000980a0b010661080644001007598042c843c056500c1101e0042c040c1c440c686003125511003112002154002111940301060704a000c14000b084124134501041c1c40c0c01d1 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 911960503 1250 911959253 911959261
    0x14120a050105030c0307081b0d050109141c08070507030e0d0303022d070807021305070f2d2a050303060405010b04030c03170f03041b06020a0c23120303 67
    0x508081100010a0199124090801c040b410020f20000f025451808410014070b42e07000003601d5003488240501a036090050004c18806081101c5015511000881d840c4c1005080ec032188840000d261801080401d0002050301d4060f40041445520a02e440072020f641070001070040340407480b0940001c0da0104407102c6607a42c031220100090b8503ca00240000424426800244201c03403009110100100b1140d0071910b61151b0744003011b014902c00d201c1480d00c801c0040183e480b00e041c180000e40102610140b009019140e015240c00c000f19030803d003140042d05403416048442c440c02d040c00300002102c030405150881c0c02e6034510540c0a16602d04220040005842e4180c2016400c80410001000000d640c00800c0b82180d90007410291205003c00e2206024080c40010b44050702e4004100420000400d00300c03c90700811102041a8070f0f2030340e800302c2e52001004802002d4a680359000e01008269646038511f940d98043ca00000b02c0707404001c50000010b80c0c3e240d46050f4408801c3c4 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 911961753 1250 911960503 911960509
    0x12020415020606100e0609062209020309061005030d0810050a0e04050f1612051515090124110c040c050a030c031107030e010c0506070c1505070f14120a050105 70
    0x15042949103203062017242c4040da0003d1101d00c10301ca040d0307108580020f56400d0300f800300c1c0c036980350702a4400d003c40d00071a036541e4004080c0d84116000034150246400003480c0410860500090700c901a0040000c0614840140d8004002034001c035127003070600380c0c00601a9108240e8401400c07081c4000344003814a85002c40c540b1403070b4601113080d6003000c0007c079600c0f02c0d168a80310131915442508104034115090040c01d009000640c0c1c02d01c0d4400c0010040761640c256420b40c2070726426501291075070f91742c1c000034603804003801032485031002948032070b1000c40c41501381c81400700202080d295040341010000c1c0c1254000460b40000c42c0c00400d138025010b070235200d60060607010b400e0034804070075441e0540582d072103100c500406018903100d00d9156640320b6001c02c0f4149500c00c0448409003055017003d400a8021081210345400d19240e000e0010b045000305401045d0036150f4003105800c003030094806180e0100705481039030051111600122320001102d00a018000e0005610750422043c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 911963003 1250 911961753 911961769
    0x913110d020c07050d08310320010309020f1005280816091511161e05091605070f0f12020313090b0a050904060609051008060712020415020606 63
    0x45105c1c07103102040c1d42c040344450b802c8514404100510804100401042d505038a5980c42c10303512103449102d002c010885951103c05003c04c1b030341c0c071007014803181000460030b0342e407180030094000181d00c0220030b613410038545003403064513039050240c14000070f10450802c00106084100d248045940754018164120b01c50582007504414442d010301254040903042d1001440340f255150925400450401e00c11021910680072030016a040380300c10146441c291122030150503070b2109090540f1403c134510765449001c990740a4902d0403c0c4d03688a441e0482e00f0042191030b4103010041200b000080e510783c1c0084243c51041180340c1200000e4189182090715849034901594410803030304015028024140341181c4040801181c1d2064220114005030010b03400741d60030511b810305000802c01c950700090269810070300c0401c21540d4402000d450500d00c1d1040100c00d40000300803d035480c1c8140081c01030030440300710151030301703603121a841400c08095824400680084c000d1240398542600 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 911964253 1250 911963003 911963009
    0x20d0b18061c1b0e010b0405010c02060c03070f05011b0c0510050601020f0109050102120c16060917040306021c06210219120c0905010b0913110d020c07 67
    0xd00031110102144652a4030000980340602c9401203602e4281140b0503001c000321426842002600c2c800b01d440110f80300d00445000308000782100344000704400802400395001c40745e0580d0307145800003054081c00115800619260414041000440007084c0b8400e002c6c40b02038454800041d00b8109142c450381c3e4114181129010405001d0400e03010400014413000c00d190180c0000a06480703410060f4a058032840e140441d03942001c0c1c00005024043d03002c0d06100f01c0160030100380d81e5a900300142c0a20400c021104146540040c0e1000b25405a201140e610b00c900e25441c2c1202c2a41d02d01d51a035001540120740c403503000190300c081003901c45510340703a40d03050074020f002d15410910b41c000c3c841c19a980508198110311a8401955120405103001c4c40f0310a22100240342c0714842416004410a8165035900310a02c0004400035240304881c102d40d40f4500240c00c0c030b944001000344529a03800d44182c0390b80c80748540000003284c030300200410001d14500680d1980020720302402c280c5264 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 911965503 1250 911964253 911964259
    0x1020f210c090a0b161514060312030c22030c061d030c0d03022505010801080d0801090c050d0c020c150301050604030308090f0a12111c0302090111010f020d0b 70
    0x10181c0b2859480f1840210140d924010850b51910384a4101360b5500345a07003c00380c024014050104090702065016800701e40c0750300c0307a050141d61220f0030305640e070340d080303035454104038040000400544104016007a03800425025000c01c2c114251100c151003a690429621081d40c54000c21134a80c0033850103003100c0400599000501c7e0803000286c54080b030f19065405520039000c44400c0500c06e0040800705409017aa0765401009200305412504170340c040c480c0424400c10001c6810000040c00034001c850079036600d0b403072381e00700101c1c1c2c0702510030b4420220a000d014020f030416030440b40548412800658010500d100c2814108214007855080041803040e0420041c410794680390200d80560b234150030442556280c5191941c600000013120a459004903202e0301c04001e2100d00c2e010407040255540d00e2405054074040f0349070a4600034401e5010001c00fa154000340c06078020303001c468414144614540c2d4002d20319030a440958201c0358520380c2c005861860880d8500c03036202d202400b6 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 911966753 1250 911965503 911965507
    0xc030614271906050d1a0606040e0a060602010e06090304060c03050f03190b060a080f1018061404060e180708010f0e07060504050604030b0406020f07030507020907030506030304030f0501020f210c 86
    0x10b42c40e900086e0340c18880760040d00b03040d02c00003585a00d90001f15001000003254503042490b04d03011100c001c00940c000d61006500302303010306d01c1c801d000140940c09101d00e030000d50700d0301c0c1c50440d0641f1001c0e00382000700c062210600208a1007000c1c9000345108e504000c040503990113103214148222415410000d1091034240103a0025540c0141440d9001c20700c0c07007041c0d0194490062103c00b40400c1e82c0303c0030406004551f9845120407d0b00994210350301c60312441d1480103c1003c10064850900030402050143c00c00901d203000040b90185450300c00c031099510190b100c2068a00313480006a4040b0019218000030311848005c100d1030005040a00e0f00504007401d103000102e00d8466440083c00ca4107000e0041070500505034121203209403650b4081d07076501c031a4900903080790805142038bc40381340c4240c00985018040d000d050f10461005001e10714043c1543d03250840101034080c2030f201594240481580c3c00507040c01080c0761903007600c0c40c6410700c04900501e2024040100030503040501 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 911968003 1250 911966753 911966779
    0x1203020a0b2518030219080c0409020607111f020d081003053a080f0906041218030501050f0f0a0c020604030c05010b0d0606090c03061427190605 64
    0x1159282c0b0042070340c918040c02250303104031207103020006503000603600c08050000110100f007400c1c6001c0444074000107503800000407600f0841203031111400039402440802074000003a1404098060312200106000046000790300d600865040c5c00302c02c1400b50340034034501c3d001181c03c60b205561010364644183c24250865440341c0c0c43e0180905c2205016040240291001d00d50300f003410001c50249e64030203071080040200602c82031041d00c659001c44179190100b0355008003c540039104982058402d240100d50b101c0c2100c0025090215900308000454040300243c0203005680c004c9001284081d940c1c01d0000820b115901d025006058592510441904003038010441a52040d010b00303054086400c6400c00c240503040180400d81c2c41801c00d5280c408120003540408141c80d02200104400b182090040c0c04640050141c00384c1c115486a041c00349241442c10084203100302403030900d010580e455400d01d000815604024002d203002042d036101c019910030907000704011203641c549490 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 911969253 1250 911968003 911968051
    0x1060902160f0f05010c02030a0e31020c030301092012070f110313060906050f0403020411090a0b03160906080a0e340801090213050703061203020a0b 66
    0x3101c0c81c0040c04080d60545860511078a1281030f418150002c4c000c0c40406a4100001c0d100d511040000002c1070354100a60210700b4000c40700ca0300c82d66103001d420141d04100d60300d040319029180c038182c09a43c08003c841420941031020758000c00c400e060104000c01c0d80c0101500b002e4075403100021990061141740c0b612000480541c0d001140c03402c101807210440764040b01c4845600c00903030307614840054103211030103901c48250106e99055a6420100740c4400d0300f12014412103054000d40403052000b031015181560104040c017010800307540c9000302c9040480d42c1e9200a610081c46c035030000c4104042079020840714805091a417400c1c01d41a420000c01502250002e085801c5042d514030031204507640401a240380e43e0304a004d0313515130b40b0500b06441d03040c070741d20305241c044070107502e02c00150130805000c0c00b0100d9034014143e06440b901780c24190300411008100744101520303040d0000d00400d4118a00c0321081c0a40d0140c0b140c01e50500702051969000b81c404001d540d041035910803034007 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 911970503 1250 911969253 911969287
    0x604110310062304060f0206060915060d020c0a030210110415030203100e130203010f0516050c0106030803040b04112e03150b120907080d030906091b0801060902 71
    0xd0700c01d040200070b81d0304044400103c840e1607020228041400a80400c0c1e8a0700203101040c403070300e10303030848605a40d0712080c80447e010a852102c1d49480340c2c070070f5190340d19015001e020800105d26006041070018080c4514001d00d940e41500580c12410402240341c085019009421141584151416180600d600f85244c03500240700d04043d404004103241d507907503002b0794008041d0751654010508041d40d02001902181001300d104c0d6282c9090410380c1400b600401d481032459000744980220314160070340e8107078010715130102d1a540e40c139030220008540602071070080d400f9804144071458189410000c43d05200c40380351041151650440007040c5141103500040c038411407030700301d90448040646c0542400701c0030b1000c0c520016400b0074410881d502600401c070070102c1100f0300e9102d1280d0341c1d031100154025801203803c54a40c01a909009401100c066031080d440011240e00c0b540f00c220400d400d040e40d410f070079150100204aa60000d0256402402c9400401c41c60301600145070a000 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 911971753 1250 911970503 911970509
    0xf0e06090a0e0715030c080108060105150705300c100b0f0a080d020c010f1205190c1706010201060f05090a090f140105150627180604110310 62
    0x1030003203900003800e90805604a69445061041100d01d216194031030201140341c2c102c010800030b071030709800d100304a1050000904030740c40c00001d03001c030b6404c110a01c614100040c0c04140e07407001c10440000002c41c20007442111407600b40741000c074082c0c04043c40d440071070080c1c528260303040e00703100c0e10303080503404681200301c14050500007640d10314100105015200454005500c820310303520014034003401061b0b408154030300382e003500c8060404030010745000a6000320b2900003282017070407001540c0680d100542000740204100c0c2e03038900140000c400c0e1003110030514002a40a20006540380e1625080c58110b58240024400541450889481c4140911400d841100001d0100d020b41c030199001c07100d41c6400c80d42c0512181318908000c0c10141ea1158409465842d00c00000c11200c200da49003617403003200808440c50002c1e8003000c00c141c007101c00c0110242c03e0303007050400b03134075500c0c410411941c44016101d5070486c41e220007040100c85118100451042c81042003000702c1c0e10040c030746019 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 911973003 1250 911971753 911971759
    0x90803060d0201110a0302160504050906040f020a0f08241603091b030b0f070e091f320306130321050112111e0d08070c060e01090f0e06 60
    0x1c0c000c64001242d0345808a13982002500440720b1030710a2507404100003900000048800035502d9a0700701307000071510100c0300f4003000e801c9440846c0000314880c80c0034141c1ca000a0114440136255a201140c0060310340c00055150f1251454810012103603410901c040c42900201103a841c11500034001c1e42e07076444c1600c0030140d40f5035900b420000341d0840041d4054200c845012450b86902e00203811407000e4542d01d912440c031a000560b0380341710f072044540b0781101030452151350300c65540d078401424400080054400b12420b0100780c40e40d0a03206052080640400720136001d100e6070135800030000300f0500310700030782042007001061a00706000710803544c0d0500e002080480c00c42100460360401d07024a002c5c00d800c0800010b00408400000010f080c0030f054a208503040d5801042002100c81081e080c10890349a2100c16914102d04a1001a40038a00c9146400031943c0c5400701e074001600080003041c91003e484c05296403001181018024113101d5030600c07405c01200c4803c00380000c101b40c0c4 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 911974253 1250 911973003 911973019
    0x9060e010201020d021305010908010204050303070f150903050d151a0a140c030a03060e040c0902030702070504020705030c0606010f120f0b040212041b1211220e1009080306 76
    0x9403a403003541110000c0f10462030071500c68014182014074030314103100e001d00041a1220202e03520906108a03401c9902c000d008624064050ba24404106140d1806642d5050102f40030075002180e402140d800c24407a590750b035500c949030341100003161889026941d0200303031001d0900c0041400307060248007141401086844501c40700701114080b8048001c0d902e003200106150304540d500101078003624249440c123120a588410381c041d00d40030200c5010341403421500c4104a200e1940d0b005642100b158810f403041c240c3c03a00b0108050382e012400880d45507200140c0320091a80c1400302d15005582441e00d64440d044109005028060105007108070960301c0c00d2103014440254008840c1d01000b8000355200c1001145080341c4844c229015107040c1d42e00c03101040524005d40180e000e0303030942c0226070241c030696124560180d290300400da4001c0342c01007070000c0403c403002d51840e03d45200000401d840c02d50300712860404c000c0c0c0901c0c24802d400e08587c00001554502620340c030000c00d4507648 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 911975503 1250 911974253 911974277
    0x60f060f03051f150e0601082809060b15041806032307050a06030e010e010e1905120714010b04020901051902151e060f0d02061606140a0513030906 65
    0x80c002c01e808041e400e8103602c4c1580000e110100c2e400000c0c400e40703098035031a83d00c0c0e0b00c02c040f03105200c43d610320300100901024000450074483e0b521408400c0d0060300001030081d41e140100c0d008020480250702c1c0000003040c200a0102295503020480701c40c041d0034040303c0d00c3c42c1c0d2445550340036007444942c18100d00481c000d4100003009910003c000c000d00c5600102d5441d080600280b2580070161050350a050300700c00003250500407200c00d4005a001081980d444004030791070744500e501d044885010308624050211102e40242401c1409119a11120060b036026980ac540420f01500d00480c0140b040a00680e08002901c203171080501601180600c030520485c28810301900389105162001c06100145a0311000000c00006203a8030368419102c0100300400b07070540200c0164070059100e0510018206900940041580c000d500b00103242c190784c401d0295203144403210f0000301c4450400051524038020305420550550010314180c896840003041c00403140500014400608108 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 911976753 1250 911975503 911975563
    0x1b03090d170915070b0a0b01020d03110912010213140604170c032505030303060a03110307180b15071127100f170c0d060b0607060f060f0305 62
    0x54603000c1c401020520480c40c607444004075604803013403d541041e15140011030340025032081280200058005211420821a00b00c0180c658654001543c440034000442280c45801c0c3e02a0104104000541c950f54000020004065164403c0c01030b8001080b0300003594491508450580d00c10403a00f0110400c0388000d94588114050a1905840fa00b1031b201c5000340300c444407881a0800000c2d1607210740d0384008140d520702082d1800c6900c55204582000010035801c900c04042001500351084155078100c44102c107400c8601d100034040d1680701170600c03071800b000111001c00d015500c43d400c1c0040c075181c800c000d4486228450080c20503042d641e8280098002c4085650f440c0c02e03100c8268901015420580c102c50b2060304003800340000045510800ca6000326090241c0000a003011000c40d0100851480b40c8101562071a0303580100300303290f0700d40304010500355000c0c28000c50007000d0701145904032207007a403008502c0c180040040c000610701107200c1c10110480300d07804c100340c4007440d54 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 911978003 1250 911976753 911976757
    0x10f180317070903022407030909060501050909061309080a020607080112030e0906150f280c1236050103150605131d01090f090b180111040801021b03090d17 69
    0x1b8110a004010942800305a07000c64a00c0a0b0750280e607081c0001e5503601c005513010b0098401c4d299100d82150009203403420310200d001302d0941400d0380403546980a440b4a0441ea0002940c2c000680104042000c200d80201320540105110501d19a2041060302c0c003c0c054859021014421483d0340041001c907541e0744500560020503910701e80e950b40100b18043c016902c069108110340046240d41c0d404200c02072103107205102c068443e41c24424107a42d88421400341c10010505000c000c1c100d22441d030307503004908402d0482c81d81418048d020b02c4a10280003046c0359110302d04140c01c10240d00041c0304825140011202c207800d0175a00c42042c07580c000c040e0300058016102d1200010344028082c200800c0150485510f10010040442d083c00f050040d2102140f020300107401100109100c000032408600000d10702c1000050104070b0b950b80101240d1050f03000403080c0c0e40129400c100b144012200050151402c0010345c901851100464203a06402801404211500d54401d0408803c001 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 911979253 1250 911978003 911978059
    0xf02010f0203090106030b0610231e031f0303052505191b0f15020a05060720060412030207080706020304060501032d14010f18031707090302 62
    0x30040d5240e150181a081c0204103074801034840c0140c00c0c0101d0701da07082c40c0d003c006428800e96250307042d4400c081b500041e6580e208048540d691800c00c00000e113801481c5014840158079540d840daa0f080c503007121140b011140c0c1c0e14006140c1c0b059001c00000303800204445044a0702105650382d00800300e5400d41d407218014001c2d01c140580f144035004d08c0c64454041040d20720802505200155000070848040454052641c44182c1070b002488016000900351300060380c2c92040300e01ea1450740c0d66a9091400c103542c407070041107881e400784030311290540c0c003481705000c00d1000384080e2426407200682551101451018145e0024203502846012070466607070030741124084d50b07a42001d16000c40100b40c2440182c4142c48901c0751280d00d8030b201d19412000d400d500d01044800200b40d22150918080299800010b641e600200140e07560640038070361000b000030f550302c07002e1100c0d424080c01c031080001c0d1241d14580310808000721150000444410380707405992a10707051001e056030308041d8410304 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 911980503 1250 911979253 911979281
    0x1090b0f0f04180c03060509030a020304050411091309050d1706090702070b1314060f030f060406050d030903050d090f170109140a170a02070b16022706010212040302010f0201 77
    0x81c0e524801e000812108400b146d215403010030440ea50404110380f0b07801200d28680058000700420002d071b00d881e410007202c2030001590103145c00b00d40c1c00011484810b071408000100c0c3c40d41c1c0c11405000c1c0030711a088000c40301d42010140d26285009032080c01100500703641c07182010002113a2210310070010300000e00015088182e4400c60a00b021540c04e08074812440c00c0107050800700d14604010b403d40f007281404036100c50540d02d1303116051100440c010813840e040741d51000000340d0f542d030388010040c11601a0300c540c01842c0c1503044c0b0f00d003000e02100c1c1d01c03000c1c4241584100700072002c0503030001c103d800840c12450100100101a400340050510180c00d40031141a03641c8280000b0032080c4a030f500c181c44455250035250440322841c014035030b403103025800418003080409032820040ca8404180d030b01115080880381e0001e60046034400ca80480068640d00e144508040ca600c2541c109900340000d00000b1840d4900240d24840c2d030100904218806003000049030003500300c1e0100030118 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 911981753 1250 911980503 911980541
    0x20d060905100f080d0c0803093d06050d08030405030f281707050a0905060d05040212030313060b0103020d06060810091e090c15080f01090b0f0f04 65
    0x41c2d00c0b0303030104403402002c0301d00c00304540c0043e4076080000d0383c010b100c929455902020102c1d40364110355810080102c8106d0003490308245400441c082c0c018480a5035070038666170b8901c4180c141d281282d066444460040c90880d092060f903540c1400707600126400f0f03c01c40d07900e5586160090031070003140b8881c03c40c60701c049020908105011071403550503c04820050307011052030b00c121070401034a1071703480e0380d0070440000c44c01c00c80c03142c001881e95000350300303024124554950201e01e0fa981310302818404140c0d504148030443c50103801c41d4107a0741036031008500f5400d2040101c00c0595485c4001010b1742e540300001e000e00c0e4040e0301039402d5030595080c101b101c41e40d20b080150507000200d43c9445040c255000104000c24540320f002c0000c2080c40103c46144484070801d0010013090905a41840a26500049200e810f600b507280560269456000c903045c103100e915032209043c0c0050304907078100000104180c965590b200a0741d042114090160b95000000c00e0050100400c211b4401c134030 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 911983003 1250 911981753 911981761
    0xb2b08040e0105010809240903040b0d14060618010518040504060e0f150f04060207051002130f06020c0114040801090501090213060b03010b0705070512010e06061909020d060905 78
    0x7280d50a28102c0b20281c8800150341d0324403480544400d0300b100d0010749003c0d0000d064071001030039030740243d211b6480b800700c80c0b42070f40710220b040e115040990407510980d1205070322061003165502e40ca821000076140c090420503006c1c40c1c40501480c56035206d0420101141c401c112581c40440080f900c80b01a104000340d091504100c1c0191401900c4954148500c201441280c00300052501d988a24072032198540c0e2038003c02d29134400c2c405803040c1e40480c0c084c01850040764082c0310302c46a154101000695800e14103019596030083c50f0301100c5021141c0c00704126403500454007550f00f84007480c1081500008143d001020301440c0c1040d0a25803030000071070200081580090181ea000f201c100040d19030032581a02920f0860203980841c500c140f00400042035880c000c0c080552060054074200e903224408584d0340461082d0406a6a4503081c032038040d41414480c058119401f41d42c2600d11006603460314445100d94402c2c0700c41a0b07400545402d108800c0d5006101034502000c0601039414 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 911984253 1250 911983003 911983019
    0x605030d021510120f0302010c080105101202220e0603011e09060f0c0302040f08010c020304060c080732070b0415020106120c0305100203060d030f170f010602010e010b2b0804 77
    0x145d010080300558130b003032100741189000d141d1141c12100c0003404004075420461044940304907071641c40314002c0d000d00154052031441d17030700d511003144031002541f0440d10b00031040d00c8201c4040d02d003601903494440c50210b00541480c10400107602c0e400c01241e244021700c1c0c000c0003081c3c50312424540d00e05c1c10001c0074500d0b500d90020003c5402c00c0a80354081511420400e08a50a40c07207145c000d40d008000c2007103d14010075000007440c0c02982058201100b43d10350000360250b208942d00200e50701106400003480c1d603d009403101700700000070440941000c03000e169a00c80c070301984460044411485180030b00c00d4021034068031101100d09401c0300c051030f010002c900c103408110b49a000d0401c1410500b0b900b4401c1d02d2040000420728981c00c0302584040e07403030a00d40c4da00f000401c94800354209601148041403401080d420003550300d598034041009084031121540000f899040401001040e594649207040d04102400c4000000740c03800100703001c170310907040b0040c2102c0c00800c000400c92 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 911985503 1250 911984253 911984273
    0x4110d0606020309030d0314041e0618140609072114030405030124060c0206090301090b071d0a03150b030d0302090a14090a0b0f04090606090605030d02151012 70
    0xd13070240c00316184900204400c2c1c00b43c0b203c4004203401318400200085c081540052030180c1d544070390215150090715511200306584545590714684450301c807a40082181d521034031080a40180b010300403d0425a00b00b0b81c540025200d00103d604110030011281c842e0000700f5940590300080d041d441544c000c442580701e40151013102d104e540b80c82c420415110480c03005101640d948401550806d0800409645a005035001a60098414016011103481c240f14202c5424055140c001d2a454161001410401d001d6100e0780003a45090704480d50351224140d040a999202925199000c000340300300009284040318960301d841504944d024542e0036500070311140205407998107a00d034071043c0c00c0c0101c000001d800c0b9000151000000d4612090b2b50140303040c0721000706402d80b401181301c002425038555410179183c4550742c81081080a4541c41240300a150660103015000300e03002d4080e40311060442e080b07208000c0c10002445d550385000322540a0800040303c0681034206050101d611 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 911986753 1250 911985503 911985517
    0x3f050f16080c03010207080a08090111040e06210a06020d0e01090b0a0c0810030f020f0a1403070e01060f110f100e0c09090c06090d0b0103081c090503030604110d06060203 75
    0x6001c0d032242c0c500c0908040c02202c22160300205080d107004004d41c412683d406000f00b009800703558032a0044404400c2a00420003440c40d03401000240c1806010001e075110704011102408000148001c0050800701c1c0c100c1c141e5411490040c1c8818000e49038101900303265161408952030006100d00f0003a120212900840352481d04020b03500c20180c007581d00000540e800c048091125001f04000ad101c4450507501a10203010354014010b554046500074115411001c07201d030344450a5000341c1810818800201070042c0c0401082d4034050b0042c010815aa000e00c003002520940c40c01007250410285540600d800116000f8450a40701d0300c0040020104441e030710300450442c181c0300d20f082e10b40e080c0580c00050241080ca1160020007020f81e000914140d0003440300b10f41c1901188650075001d000b54041c0ea5000c2d0b642e02e002d100c084442c0020107004680616280c2400045440001541e07804074040e80e000070f01d004516140410750080c1018988268184400820940d1f07001c0040d10807 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 911988003 1250 911986753 911986769
    0xb01090e09011d15011809060509030a0e01020a1a0619080309010306050405091f0605060d060e010b03040b040b150603070908190b0a05070903080a02073f050f16 71
    0x11140c2891507150301c403024800d03444038415504c001886550214420480040b05252000400c20b03120303500c107019113808a40031f043c06e03000801d1001c0d07082e4100c40c0d82c0c2078400003440680512030707295442c115a41154049050030203145400680e003a01d540b41c40c00005014140c94600c22030317403010b40c9603032540110601e60011f403e241e8001040d003801c0c05900d004005d030b14043c0190440d103c034400350b44141030003d4031040b03480308000074203500c41d4002480000302881021540781c0c01c00171032402da0340040c2d0200b81d0341c2c0810000c0002043d0b603c420b941d00580d001c005841c8a031a116000c05901840c600d4040e440b0000100380448250000805800c4800d080144d9081da00e039103e81014074011080040d1610501d080040c50302d03e0581d001c140e000c1c0303850a0080d4125203e444650681d004034002c0c2e005071380000010301001441d5200d600c001d203615560030800101ba01c04000c0d0000c8080400c003c0810b405420104010b4180683c805030b40130f22003140d03003d07a60038140303010f000c2c024422118 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 911989253 1250 911988003 911988041
    0x10c0b1009110f030a1e15230102060117070f060c150e030f25080705011404020d0303051e0c040504180506280501030b07030506040606080a0b01090e0901 68
    0x1d88454203060f10100b40140c003c1d0340c1907039194501d90f00684400c060750111280c0140f4000104101407240000d140811202070003c1400e0844410148600310b2070304070030f02918030307840b520360380c2c001303180c42c10b55010050982c000860340c0307480b900e0011181c02042000a42d58008034050b540121098003d6006190000078841001c065104072070103002e112845400402294500d10f00e8500108290402465446414100d80d004040c03081c0a0f02021603d02c0d2000407400103101090280d044035200000102003541400d9002039145052424001c05164449000a03401000f80040c00e0007004400a9103800b403a1003880d000300381d07109006161041d450411142d1685001038410120300768411b000301803c4d12803003003c85207000d0003440d04240a402c4058039800101034001d5a00851244032025070720b0034121400b0302a01d00041443d0f000e80d00d408002c00c8a50342c00351090b40c024005a00c0014492800001210b402400e030304402c03e403480b200180800c003001540880d00c00324000e80101 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 911990503 1250 911989253 911989271
    0x16120e1f02060106030b0303120f07021b01020d0c03020c0918070f12080304051e01060501201b0d06020712230d0f020c010e0c01080603031e09010c0b1009 68
    0x1580626000c94001030740b10000500006019500c415501c04000381200d0800486e8039030700030200c0049aa4484017002c407410f1003040e0740c04016142204001c05c50b101010035032440002d54560313507816a0010401404180f00c00d041c024080145c401e4400b81c01081c0341d140880c07101c09807a15070082c91549100b021400103000300030448440c296182680280400160380e00c0f5801d00b0303000170327006841c18080c0c15a0380450740801c48a40304400282c00022812a1400b030026000001103004482905030b00c1030000742200c404911200e000590740907e00480b604840400d548113002003008042c5031001440d1001e10a9000140c5100c580998481d801c00d190b0400030040c10202c507a004011031014081e80009c0b01541c2c001400e01001a0001402e00b483d03902c0312408c0d2441c0041d00300c07540d000031400e0400c550740f001007990320900c1600210301d0718541c51003001c81c070f01500640c15410390313008c2124200b981c80303202c25482407900502c4042c41400c0c92456064401c0b1184201e80d04946010004 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 911991753 1250 911990503 911990539
    0x2106071701090204231203030a060f0b0f1b120a020f06070e101b0b1513050603030d110702100f110a0b130606510516120e 54
    0x407000e0303c1c5021000340450550306120035516070003c0c585c0f40e110803541c2541171199030400103903110f0b042c002004140c40340303819412040005560807000d80d00e60100300203242c80500d081220742105c2c0d5504074413150b2100340015800c0088102001240060014510680302e030f000800941501522040d45c1340c545842e001503501c1c8016a003065080844004120030490240103a66280300340140845829955541c0c1c3c020300d5034040300d0011501901815030301d41410305905c581d11503052048100428100107001030b61304c0c091103202c0700c2d56a80310b607010f003100e01384c420035104443d90141401c00000d071401e40c050425094a2240c0c000901c5407028002c4020000038040e20b101d8101d6020022a15030300c0c101c602900345d100043c1c52031516400d0005800c8501d22000e045c2240c02c1100703c80310f00300d032040100c200c0f290303034038100011050041d180058113400800000c60801d5052131a52800001c441280d21020014041c0042a04017166407002d80c220b13101151146045440c2c04540000310302c0 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 911993003 1250 911991753 911991757
    0x40509010501060903030c0c1511061f1208040e040506240607060209210106230334060e090609151c050a081e0c030921060717010902 59
    0x2280c0c00140c01c61030170004079000f0001111000c1c050201162000e4480709682c1d0040d2085100d20000350070f08080e104241014004150040d4000c01d494010003a00d030100e8082e03002d50f01400c07240105040c406000c010108007100c009003e8000d0344181860103040c21615a0411a09103450015400e4800d480000b203a1501c0305400000300068113019094640c0c0c4000d400c00441c0d642c0215084036446510300460500c08610040003001103111400c1c00c00500081c0d80ba4a508050041c110381401625980440d880d007100305520b9041590001040417a4a00f03248411100c8000019803001f2a43e0b5034055651000d401c0103039040c0080744c0744c200a20410040488000c4070100d1075443c00d00c40d924040003081c04059280c99410a1646292146402d0800d42441220b804034002100340c804001c01d40c800407500c2940d0292400d0050301c6003020f460748500901d10f481441c1180e0f1410310307000e000e1169000300c261441201d49034503104038060b12222004001454646800000045900b02802 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 911994253 1250 911993003 911993009
    0xf020904110c1917090a03051903110c0d122706080105120606010c0206040f1e060e030703080310091409010506030303240d05121803010203010b03040818041109040509010501 77
    0x10300c05034000444015005904080b240c1d03944200c0c114400404236108211124014041da1148080441e503843c0c081c2001c840d0b0745803140c00380c0104010740b450b603442c140031195440d002a61541d1040da070710002c64511918800c3e00383c170302c1001e0709403400060300700007900e00340c0e006034640558513600c37601000302c02e800142d60001c8ca90301c40300001c1d40d40d521074841c0303110305803000d01142d0500d5100c1110200c20b4440350800561084a81c0b203103c800f18845036000c000b050103040c130108610000d40800c1c1c9841003808013030000a400400300e580140700794640001407210440c200060f540c020303000f03648010140d944603106e6080074040303006441c0200c103e81c0618946c210901c0d40e9454424007500128102c441c0e2980004c10002d100007080341485280341082689150b17541d40d030b403c1203d4109401c140b040c41c0740240c0c810301c0140f003c100303100c04694200384c0100e010341e03d40e8811a1541c44441c0180b54443d00241410020300c11a4500c00242403e131800700c03800d1100b41e0382c3c0706005088440904c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 911995503 1250 911994253 911994263
    0x50607021002070806070c060b090906011e090f050613050114131103010f2103050f0306030a06110904060503122a150703050718090f020904110c19 65
    0x2551005142410310154603081e140151036030182d803038824905001d41281c4440110302d038000c5000c05c102d41031140100e01c1f2800c071030540050600ca9030b241d130f58002c140911b0001001d096440a524034103107812100405601c0814010465002c90f181c000e0b00040e00d405010310100420540d402110340a00c9050301d241484003c01006c00303408101044c0d04542800a4403685c885104145001e401c0085020b03003e00780481403031500c1c09400d924011000c01d40500340f14030429545002a43c0401240d0410040c0202c02e0b490b0b80f00d0200180c14444104401804940340c001042d41015403007000c1c1500c020304132010000b65640f5014035071a840d0b51041d69160040c10065104041400641342c0d54101b00900b440c00c80030f40b0036559031701e081002c6002c0c140241c10030042055a56150140650044492030061035149980119018201080c01900d40c41034031a40780403400182c550550b080720900074401c0c000c0071880030040005500ca641040454001c005038448a201c42c00d00c46102c440d441 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 911996753 1250 911995503 911995507
    0x2120a180308130611040501020d02060705040905060f030f0c040b030a0203071a1303050604020f0402090d0201230d06050a0614040e040816050312100b0403060e0f0d090603150506 79
    0xd0341e003268141c030b00a10319641c89940400410100e0124414510a00e40c041060355407141440c00182c54202c0c3c054040d000c40d4400300401c1113440d400800c0c1c8017103407140c000208e0380d6146c880000d20902c11503050b06405d48103540301c808034881c000550301d4070700f6030a1b503080007508051810715846802e48400a0b40603800140c3c00c01c1070105a00060b8805a1007120b5142406008080c0f80e075080c11940c130079100d640c010800d00c0b017580350039030010f0011001110b0441c68140c501c0e0100d401c4046048001c0d0601c00c005c078a441c0ca102d201140201806180c1c100283e481908010070001003000380140c50007810599004188140540340e401ca441c002008603a041510700a42c0b02d02c580740c0100110350500f0103010f0600c04030211414050294403400155841c1d011441e50080120001800300b11000c0c403265040080440580072030b000d0b20703001140425029042240307249030650300e9058510500c5070840d24041e00341e10260801c2903d80b95030b4148003d020b203142806140000303003e030683c40171003 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 911998003 1250 911996753 911996801
    0xb090702010507031a030a0b27071d150103021b0105090f120307092102031c030509060f0105152a07060810150e04060e0a0e07080604061d06010902120a 67
    0x94030121540a074481c0c1904041d00d0842c270401d4420782c3c40008250b4607a004c00828003515150180c96016400500c05e00200d5107058542182c80e500190348140c1415800140c0c006448200c11075a100e11207018000c2c005410401200b560fa4421071403080c90394002c45960700014014801201e00400d216071700c900c400390411030181d11038102c114070780c3d20440c41e82c29020011385050203007603004090000401c991000c00c840140540e60000e01540c95500180b0800c00549403c0c070a442c1504d8082da101c02c1c6100b01201c4941080c8280c009065102c6030024034140b943d42d00310455001e40c00102c05841065564800a8030820010703a40744007010403540741070125040c4c40010300650003091070000050b9030303900d000c5400c036000c0342c0140c0103414030003040104070041390291600403440b120050001e2403030720003020b44520020b03000901032510390b5001c209843ca501c519290420502054940650707603030605400039406404188505250040001c0100c0359521030401d00745640c0450400c0458 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 911999253 1250 911998003 911998013
    0xb0904021e01121a0a0617070806040906020304060902280302060a091d0402030d02030408030409020d0212090c040b01090308070605040c082a06030621010b090702010507031a030a 79
    0x100d034030030880c10044004022410400280190b5984c05280044c0c22004284803041c00384048035034201d0001d0150141d0180c0d0b442d091040b0fa0f40d800a000d00c0d04042d0380d29060000340283c882000041c11039400401408240b04060380100001c500c2290810341e1829070940c071440b50050b0070185100031444100400160514900401c800d041d14941400400d458441c81040182c804041c001140743d03280801c811811f08000d140002d50305030000b5030030546840ca11560b00d01c110300030000007d402142d20003441c4043d0701a41c0018800041701d01d99460030601c500e5542c000e0b0316485205604104900e2519402525018145c0e60480380395880c044854940e4405003202030070880f1960750540780050b5881c810b00050300c0c0c2e4000852041c80612003c4441d494140c540d24030740d8440c942c10024801d04d591828146140c1d14010100c0c00e0a080e0190306144c010a481d40c1c0702e070f8201201800304860756906600c00da11035000360b2000c00c94803100c020359020265540075010340561080d440200859 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 912000503 1250 911999253 911999299
    0xd150e06180a09021e030606060f0405010e040f09260a090618050907200c03190c031b0305061008030315120312011514040614090d0c08010b090402 65
    0x102e0658000c2a01c3c8060340c08600040000206080e240c5540c032510442c03841c05000d003e800c802d0441d0707024100105059015118400c52091f5414010806040b0b03001c0d4031690843c241254103079800300300600003401c005000020041e4440b0508207600c030741031080b6030441c041d510000800e0b92030107082801d00e203090f0385030f07060702c908840e400c01003910000e550782d6150743e414403542e1107541d82d61200c82406000790924211603186002c075044003003078241e01c2d02c00140160040ba180254070656044c0c070b043c260a4408170f40c10141c42c070311b4030200015504048558042c100c83c03044040b50595a0303134a03c4410050b86600a00d145c0c0c1d00100042240301003d0030003902c6001d0001c1900701403a070110741c100d20b558026010160001c2c1c1c2d44c2c0040140c103103080300d1081840e0507801d2101031550b1650740e0404520442c010788c4140210340c0200d9a9401004080e0703000c20f54041c12400c1c80071154203110305035982a10810910358200008074809040042200f801035034094500d402c11101d0b1107040002d1 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 912001753 1250 912000503 912000511
    0xa1b050715031409100b010302090f10050c01110306180f0406020d1503110f0102070609030b22050f0f010c050706090218070c02100c150b0a0b0d150e0618 68
    0x544a071032003180c590120039200e001300316180050125094000301c07407095070f150b02035550600d40b0610503000152105445003503045000ca81590100d01082016555401001c101400642c42c0c581e66052645045c0000e5001d080200c43c030050003140c081050780a22801c4585401404c3d2000218000070107139005081144070070f6801103514560360301010030920359540159062640ba030301e106510b08143c6500b120411080c400f07840101c1c1042d50141030410144001002521a2000240303542000b0034030028007004188140f000040c02c2c104141c1c0ca00c101d21084040d07025400d42d01c101d0020510401d41c0308001070301c83e0b6003048802d0300d55400a08604100781c2c2c02180d1000c03a440c0f15494254950310440c001c2d12241d0004080e4018412100c0220708070000f031080c09018040440c2481c007940c80d040d41266000700703070984000f020800c00102580044589940032031542d050315030710f8002880e215100c0c01109011a80c40d43c90b61741038001a101181c0140d048000c8820f0041c61010b02640 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 912003003 1250 912001753 912001757
    0x9050403120b030c130506091e040b060102190809100f091e030209070c06111806090a030c06050a18140d050a0b182b0e0307090e030a1b050715 63
    0x9814405010036100b850564817190a01e90b214200b01c114540310720500d13082203824a200c09204001100300002c00c002030000f410305440500001d0b402c0c0c0c4208581051400104044101c045207031405041c00d0300710400c03003841044030780d201c1908244240300f605071010103680c07100d80040c5060000d17181425007107075044650b482c801c1e0110240e1242520300d070041a4035901c84c144214281001800c8407090301001d035074158100300c00301a05448100300040c1c50350464946913038041440c005000708801e54070041641c40c1c0030100045040c2c001002d010f0081480e2075004030342e06030690306140c0d107407c0c0c040c0d150005503c000002407410f0124846061074491001c50381c402906d5151050710b00d000312007045a07180019038650700554180540b20b005c0030f0f1080500916411740d0108010104482032032001c018603c507079001302d550f04120000050202460800401c044160306c40d843e03074014281c036000b02d00b00940040365441058072951101c1d41043c0501011424208141c0c0c000c02d0034103610003 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 912004253 1250 912003003 912003013
    0x806130c0b131a0c070b03040c090f02120405011a030a0f17220f1d0103022b051513050307151e060501080105010306030203121e12040c09050403120b03 67
    0xa040040c603e00070150008039505a502c80102c0e8156602c1c1c000240c01103a1b0901c018028040000c00b1400b1900654034816008100c510303030030000c84028090446159100714071841800103008040d8081c1c40908043c1a00d003106111241c18995128901003009000403649094000030403544000e26080d080451001d61500c44203540c18035140711254454840c81100e403004004510307150b12076100511562003594602c4590300b0030054200720511010f40912001c07450520718a42030700c01d820706101c00e5013020364021020300703200e03540c0e4034030095805444003c00e02190171414002c00d20103a003640200118a850340540d903d4124920001c1c2d032844039901c5545855409841d8002c015502d01190030001e8034600e0003000521085042c1d1085041c5071074281d05101580380450b038a11411000c41060381d4a14002002d181b035965006030f0ba450b80074020880c4400342422455150003540500d0708400d40ca42ca404141d0212402aa001000300c5c021400303000c1d080085801c0380c2ca4080004040e01c03 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 912005503 1250 912004253 912004259
    0xc160602030c0412051023060409080f0d0e070909150c09030807030503191a28081c020105070804060b120303090c150a0f12180605010806130c0b13 65
    0x4882c00e50a14003c8500d90080c07840c04103552100c4c03281f00c09001c44411a84440c2803010400c46030719601074940e80c0501d8480c0c489805111700794007103601682b40d9036501e5694092005a0800a010440309003059004030200010f58100701d00500d02500d42040310070922403a40c0006400408440301c14400b84104800000040703284040500100b0340070b62602c40e500d02c0c204020718003a0003001c1c501a0050700d04121a04106800502580d1112081c4c441c4510821640d02000340c00d80d0b5448404805001054041740c0c01328085a102244111441003010f80c010f201c000382d00b0394604840d983c0014078820002030201c0c585403c09080c0e00c9001d0641030b41010703803c9000c2e05561044402c03241990121454180d1800c01c0380f44035422118856506050030020940145a407914200c100c1c2046410748211b12200c209074444048041b44442032003000d01c01c1e20b81400985000d00c0f0b0004036000d41e0000411080d2030300e0108407a10350111055076250308012804030b10390410b807051494180d03110004 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 912006753 1250 912005503 912005519
    0xc1c0c0b0c0a1709100f02030f0d0615031e060e28050a15170304151101020c010b1305280f02030f0115090605091311120f0c160602030c04 61
    0x1030f6090603803107065604c1560340e007031041c81e0059803040b43c00c1001c0b558090181950200a8801c030401440380256200d1404035010007520a5411680c02d0036520080180c515400d03a004042c10414040301141c00d018440f00d19084903218825134a031100d05c6c40000f040c8990000c114070f807420700010b02c0720141250000e018221203048500452481d5107811400c8100503140054004001900c2840c8a255440c0070181c0c50b0700581c840c40c0010031591308840c007070324010080300f104c0c801c1c840b00864548917145011806451000d076001c0c00345a20404150756030601d8000d5034810091604150035000410f194800d4105044601c0420079960700d0361040000c003031f030000310300850140c8811881541490540340c2000222402c03a000d03c1069081040fa03a90406d05035000708008440c4038004a00c0200050b02034003400600c1c8035450000244400c0b27892010161600400d40803d140001c0d940320b050240d454403442181c0480c1c02e0103a0203c00014a05800542c0d02c43c49070218071b41081d50f14024 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 912008003 1250 912006753 912006773
    0x31003230d170105060c150a11070f0b01060804030c03080910060306060e011409040627060e0d020f2d060c0406030b040614010503040501060308030106020c1c0c0b0c0a 74
    0xd500002c1d2404007000b185440e0403040c10f014100440710180b801c48070796817060f5180c00425010001450000000b00c100480d588540022014903031a140d40c2c01061604200d5800ea0032021514114004008100382e803007020002d104075459100c020807025242c40958604030020204002445a07088000c00b01c203450049100440c401d050210300c1c3c90812808180c9407030160001c0080340c0004450300004d59442502c0b0750001d81014000400c08806251400c00000140801140040b0b541040c0d08000303085c1d01800c41c0b441200c007610f46030700c0c03810300813600c40c600c1940d5605a41e01000c2c040709040b100340d5402108694003000340c1000350400024034203201e0212204104400003140800036941c0500508540c1441100c00300562401e02c03021802c01c20301028058100b0002100040800400750f000b0310145411007041038582d0717074800c0020340c8e4103520f003e46c9000e0348540d07554040d411b0021121584003a0300214219080741032101d642d4150f040300c6508092032040307061a030040703010140 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 912009253 1250 912008003 912008023
    0x60603050a0803241c1b17070803070209130c030506041101030b10053a270c0e04080c2b090e060607020303040e0108011a03210313020a1403060106020303100323 71
    0x4010000e9011200e1114188441903101d280f031508204070701030040c2d1345e0314001507000b0b503020ed0314510030981e4240260742583d42c0d04014420700ca006d05002c203200420704141910902686d003400052035080038003800846141120012035001e100c0300c1e103035401e09029980d5180c10941500d2490310348905600c03810000e9043c0d0724156690301c128200503160520007030b250900744c0e18080300b91103403030380e902c40d8180c2e252054141200584010804005005003100c021040c2c03e02100c000502500b6a2259141c1c441032214580703008e141060029030040c4012070441e070f02400840c1c3d0503134802e0b0510555a020b100e0490389070000304000b2074180b00400c4c0340785c0078025600001a16590a241e48124070ba092400c03d8481e40c84100d07201c8150a0001603a0b4094012400c02916a1920540000c4290000b04001d5120082070b07004150f4594402250398222012030032504030741d0ba201d01c01da88070710064500b40710740c1400314424404102c1c0350001024481c1c8032241e040d404141d1801307c60618030900 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 912010503 1250 912009253 912009269
    0x61e0d090318080a0201050901031e06060f0f080a09020109051509031006120f140d02010509191a130b13030207050603090304030f060603050a0803241c1b 68
    0x10155800d00d5801860640700c402d0048070382c5506400d00c038503d540d0b0040b4080007810458002103105450f44260003040c140d4184071100d80b503180a140030003024000601075040065110041e0f490781902c00e8141070304040490b150342c0c4007600c1d88100c2d80d0280196180590500c07041c01c20000c1c00b503d0300014620205840a002c9031982c060400f01420801c0e41c04000c1d0a036418180140316420348200c1d0420702e1a44440081b02c824581d1400c00c0c040c50840c3c0c4611454040c4400713501490343c040d048584035a4440090b51820300580d0202e1036503441d210806400c0750902e61582061024200e41290000c43c41144400e24410540e2005803816049400458402d40c4230207100825404002180107004200ca03c2421445d00040d225030340d000f503110151100b0041c01501e401d0081d5940200061600082943d4420205081c4542c0540c0141c40d0060313100124001545880b81d03540003000803120041000824030840420101003165154040d6800e48030003280b2003ea6040c035030b000c1700400e486 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 912011753 1250 912010503 912010511
    0xd0605041406090a0506010b07082b0609150e0114010c03050c0601060f02060907081c030b0303030c13081207030e060d09050718020c070b0c0304080d0c120c11061e0d 73
    0x500c5c001c0d003403001c1030780204900002801150300044111041c0c03541a070307040c040070050101c601206990650894800b0000340c3c071b4940081139080d420741018014001448004041543d140c1f410403d50509201e0103103000500c14091982d9845401201c0003140070f441c01070700700019809179600b808400c2c0d010340041280c041c4203d80454043c86600c3e40440454050b009040c80d1001440d15000000c280c20900d01100300307107000460080d40022040d50028003240c0d00d0785080c03044441c20340e0100d440c840c0d030701c1e1040c040090215400a040620114030030031a5003040e11359642a11540c440e9010fa50f409038060020f0740307440c4e00d103110b41a0710900410041154615094103c4407003142d500c2e005c075110780104050b00e00c914001074000c003161208030000f55541e00c0075281d5821801150803800260040404440030503034800b11050205014589418104e0b009140583d0310109440c0028946180d004050140d89021b4001e0081d070b81c4c454020609100d401d000403100e0343e0014807104015656 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 912013003 1250 912011753 912011773
    0xa1509321615090f141e1f1407050607030e0a0f0318050405090601060f09032a0308030a0501060f0302090102063402011e090c0306020304061107030c020312090d060504140609 77
    0x990040d03803100b201491b402ca481c440c0f5201050381419481040101130000c4584000701c144119004030b01901c15407083d984581f11407602c540c690b6019100c0e840040d04100e0041400c2c1001b0600c80d40b1184d00240c50310120b415541c083c1c42250074901100d0803455041c40028894841d8040c141c42506100301612080d8142400a040011080f946400b04840c9400910005164141458250b001e24010180140e01010902600d0303496400040c40000c011050003c4041030b0380200703040e520591140307045001c0f5448210300300d0051444050050f44440041039400a15064410302d25541866a0300d007080b803180603640038210540b03a207005079074a40389502d0b1001030030103038030104109110611400c0380c241c070b6070440301020340009030a2540c0080400c1c10092030f0340c000004841d4100301d180c0c40d00640d040c050f24003014010180c2c028041c10340e510007042c01fa08200c034040000107140d1074404219440b0f01009041c0180211110000d9103d224100c610800c4403a104525000050141e002 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 912014253 1250 912013003 912013009
    0x90c0807022104030b150d050607020f15060f031e0a0c050405070e010f1112030402030d0807120b01031104031103100209030a1509321615090f14 64
    0x40300110b51280b42089603024550b0002e85030450b8101ca4008842400645620320740c00658051007079020b5004026124000030000301082d03841c410034003034095030144029a069192582404241d48004803005000690146810844107030f490801408403200100a0f0900a40d1550090071010380750380420030107420070444216000c05081700340e509000504094001402c0391490554080c140150807001c500c50922130325851068902c0c101c100c81c0030721019640b0300c1069105503016800390041c038000329281c50149035954003034003d650362441c003481410044001804240c0c1c10504040c0c4949a403918051503030083c001031405040d8160442d003103142090319048100940d02261030040c01540301541d00800c0960750241c0116884000381d20343c2811038001e0442c0d0341c0c001c1c000050600e200c035440c2c0c42004c10203400740329082d004045407003031400b207540c03102c0440454912034821042408104c0c2c4820300b0690381086410704199070350b00c03a0110b940700001904400342a940130342d800401c5103 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 912015503 1250 912014253 912014263
    0xa0c051002010209150a180603060e090f0604030806040e0114090106060c030e04020d06050904030e010e190b0f190e0f06040501170601090b0d1a0a0e01061107090c080702 75
    0x3490000b1883c0a11031320108141001158400302404004503074101041e0140762141d01c504c4140e4400354005450b402c014004003c00e000d80e03143c00e000c4000051a1200014440088081c2a0700800309036803595421119040c1c024507468100d0384685207050701500034010041450300903c8200740501d859410b05007142d425600a40400c411a0346010209130030002c601e0200c401642d0250ba103081c00b0200401501c1a54001c41d00469072500300801d15a1007455840004030981ea440b02c1c10600c802002503030200310980701c00b850060780042248a41e0f00f00108602400080d1190030081742100f9188284e211086042c0400c851408800c00381c545021002c0d2813490440301c06050a0900d000280711804208250210f101501c02098040c5c2c0507001e00c00041c000002c4080d42d90001c5203502c406030a402c0711031003581445040c0018079180200c00c038400e5911012030301c0c1c001d03881e00e003044952044c031100c034019500030300d9404200480580640b103040c094588448a5900b40600002c4c582 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 912016753 1250 912015503 912015529
    0x2180f03160b030a02090a080d1710050904050717070806010b18040905012d050a021e0714070b07050d02010501181a0603040606081e0309120a050a0c05 67
    0xc0d00400785559204180000020644828450180d180e55a003422007001b031284c4841141e001c803401400040740d240000e414000744d140b555480c0e00302041007140f0404420255685074160a4116040c426404c20003c125441401130007266029a580c4008a1410095214a0007140c00004080c03020450800940d801031080140e1180760680d40100100e4035404508010b01c00c6440308805024800c0940084c2e4086c0e9669803205840c2407428645001c2c1e08a40047d03840103801c0c01c0c0010042e00c01da100703840280a40c26200040c3c86098143c060407a801100c084034005001900c2c101882c2042100d0790181020710700c290b680701c182d41000362801001d0040700b0116810000180320082c952040031021501c80e000101e543d0005440300060703640c004d50741c00e4004034007008000c00d200f83c2e604228112001201918003501c814044510b001a254003c0b460303907441040b01a2107800c04541070205c001d110810b489000d04142d54603400c01c6502c100c1550706150b040814040f07850440607103040c1d = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 912018003 1250 912016753 912016759
    0x6120b091612030f170c0a14070b0403030b03100603110a080c011205220c050a082a01050d020d0e06070f08150d02060f0d110c031801030b0402180f 65
    0x7452038826400e8049007000320060800a40800c4100094001d40715620001c4896070840c0c3d961074000200c202c190046032114000503240150000700c2034803182200c03c45a001a400c040c02c3c1c0e65a1401e5018001040741c064042c41080340c0c196000b100340c415000558464074549500c095881c3c100580c80c40c0700e40004046400140100106030b802503164400165402d401040c43d9031036a000d5040703c0042440342c0045210000f90108001d081e200c42000d0307903401c50303012440035118071040307980303c3d440f0030810204104001c103080e5941c607905e454181d07039a05140061800c403480811800380c1e08000c22200c40d80f9110f030410013504600b800642c0c0e000d002460010404801820000c280c10303001b6042c1240b00c0c0302070360495030075100d80c10417040303007a0068000e640e900005180d8450b545d01001c00351010a2030031a00f03d6000c3c10040403902842080402107040041c844c02a420f0328a0700c2812605261b690030070b4a4558549002074080301d141e07400c007102989441ca0506c50050074050400748 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 912019253 1250 912018003 912018043
    0x80609010b190306050307170609061308090607150f050c0309120306030a120c0c050a0605040506030712060914130507120f0b010306020c1603020f040f06120b09 71
    0x202000c0244180e9640c2c40008a4401c190340e500c1009600034040743c0c05c031503010f005054011900010899809011407581c00c110f0301280d071240085901c1c1c18043e00d4107c2c00c0d00c03111040340c010811440250081c0000144024036140d4566989519640394200100740f00c2d882c0d00d1044500c0d0850300ca0305a1050032642ea2520310700e400c2c1681da0b01d50300c2002d00001207030008804101c9903141008024110b562100d102c00c1002c0c1140c1001c1c6c0132507030103c402c90740d8000802d400b10ba5410040107410460741039488060a06050908200c41c50300000c04505c10411404a50803a40c05203000300c500900310002e000a0340c080ba82d40d80314585100804009076214880703103690014070006262400c4598010645060480710324000808054140300038000b80203d10010080c0242d503802818023054040c02c85400300742540030000b940c2a40d02c0080c3d407044000035021030904142d04428011040c4000c00900580c480c02c0c0c000c03061a522406455a00c854401c1116003c0208440c0450400f4510b4001d = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 912020503 1250 912019253 912019259
    0x429090f0a02030c1c050a06020c0d030e100906020d05070519050f0301050405100b0c06060f03060f0a020f0706060b04050a0e01080a121101020a27240c0b0a0c08060901 74
    0xb543c64814414090150022507401701e14801d02c003812000d005c0c0d010064400341c00b02800c091001e0f410040e01d0300501d00910300102145030080c851500384404510107829600d40d0321100f0300c0140380305041a41c0d280d400b08a811415003040c82401c2c86003501b0b8558036102d04a8100c10341e964004035809100b0302004114101c4d007020701c00150380c11203070121004101c7e43e5606007058804e0340542c0c0f09112044020908505203500810b20603c21442034403d41c20401d90355003090380d41c40068604900b104074100c041010104943c00078492203182c0541a4607007400e40d52180201c4003c3d41c4408440740740810203100c42d203024a4513900800b86800c0b46840780d4180400561038055401005009021605902d0b1003107000300003800d040102e001c002c64540b00f24ac107000c1c0407814000701011020060b030103080c0d26030184049080540c0c40d034600b09295041d1a8198400390443c0010360b00a0046000c2000001b42c42e511599100310000003002c1140b01682201900c4541e01502240c0300da00160018 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 912021753 1250 912020503 912020509
    0x20d081e3c0c07020a030c1715070816091502070e060619030e010902130c140a0f03050c04030b181b0d150e01020409061a071106030429090f0a02 64
    0x420741160581000703540d10f81261000400c0440c90360f00007081582100030002e0044e1800f41100c0c048030050301911000e00c00c400d28130b1404c003801c03900ca0707000c601610b000c204070048480142c09200f8a604120508070b4448d00d0902d038165112204800581c440d25050110030070300a402038101605590150a0403481c1c030340c08600d50a0b4044c4039080694075280105200403d40000c00300c3d9401802144031071001252030317009007482d56860400700d80706283c4203e44440d640c086030714403d41540c80102c0b1000940c001c4003c0d00020303000300030200d820720001c804a0794130a5528010340c04a1030203030741c1c08502058181480010b01701000c0452070030084a01e251241a84004010b91007011100c0103640c01c820720004211900103414550710214010805450b281d001f9001da52041220348806c0c42c00072104010f41c4905500182124035181540340c2c03d003001d401a641246c0319480b94405603842c001000000440e113503203001d00380c4990081c0500c0a00500030241e2120510b4042c3c8140485a004 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 912023003 1250 912021753 912021871
    0x50306130c12031706090f18010e16170c010203041401021f060501020c060711011b06020a0903170a020c09060109170a110a06020d081e 60
    0x51104224002100300304100c51490003030081e0800c0c5042c1c1c0e02c140d419007070080c0b10844503440710703807210241d0011414924040030040e2065001805083c840d9560941034449861202c4200c8001c0d9250418000c00920510020f0b01c92028110782c032081c0c915105618081201000c4100d803150072990150f0400d0342c0c04000c4406880c040c1d000f0300321460004004030f01d4401d150b01080c848155480301280300c6401900a0400c9600c00d0f030840382504204401c0210741d00c9003440c014000c42e000c1006011550081003800303100d948405102202000c0d5032900001d0307900c076845070000100548018410000d40c424443c81000c510031015090114014000e9a5844c0200055224404136400920503a20901481000d00484880d00000c0b031002103105641c1c10210b9022254054a81500015030400c06101400c8071b401c5d6000380301c5000e0408050300c5091010342008030b82c0d1b00300729501440b0424010800d000c7c00201c040d0070f07816103504401d403022071640d20000400b8420313030b41d004034290000700b2 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 912024253 1250 912023003 912023011
    0x13050c06120a090c0302031510060302041d090111030f0702120309030d151203030b0a08030c060a0504060b0406030305071205161b330203070c030320120c1501050306 73
    0x4000f401083d641440400c400d16070f4070007981071003800c9882e202d1121504400e409003160042281070325845c0c48056060f800750b40036100c559100500f1072507050b080981c0d00c1d60408140c000015820a03018a402c1d0329134000c481a0b01d41000440c2031110150381046444100300120f0449400d6040c4629100e480344510341d200c541c0c0c10340315515030500030f50341c80010000b05452031811840d0421450054043c042c0084c00030b104400b0743c0c01c0011409408411600f0080000740648a650b580700145001440d02620940d002c0f070380d1303098503546900c413842200003644c06034071002c0d2204500d1030000708000080103207c0c1004405c2c80340c00c03190001401c0c803500140e8010440302419040f6500001c0d92600c50707000d00006060351800c510035039050f2400d240070305180c1401c010a40c408880a980c1c038819164000c100000c0d82c00100b020a10480390103080701d00d6403918651010300c04060038542000c1c840211002c41e00003501003843c40041240309022610750004001e158540700010780c0740c2074024 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 912025503 1250 912024253 912024271
    0xb03010f0302090613020d0c0806060429040b040f030203060703090506010b0a020a0b0a140a0e100b031510140f18101208032707060f0e0301020313050c0612 69
    0x101c1d0540c5d60b100b1011004481e4040215100d4004140c514080c00d00400c001e40422030490201c1e01e24184402241d040d59180c0a5101101d9054840d0302400c600725810990758a81c1444007040400010000b8801410300d1618201a075086004040c01c003070000c1c009109061a003014000000e0300860a2411141c8501c15241c44032100c01043e42130204103071000305a6000001007080711440740d807140141401c81c0c4552010360396000d1013141125000c0104194a40c08100806461a02c0f40c014030314034500601500c00080c1140c5400b54003150a407038940500346000c00c01d21000b0780c4200901e9107800c04403014031010280317801165010210f03d074264080e8580307034002125010244000002480c40042e4101c0c4840c01d805c0020054200765502e5540700403420484000a110241c0c08644c007490340050844685404c4d010741c1c0b070b4030f003210b42c1c00180036015405803e15502803010b58440d800140050140c00028034220742020b02c1c0c841072a1196400340145100020800302c3e0540c041c01c80 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 912026753 1250 912025503 912025519
    0x20712050c120309061803210c0d0905060702010f02070b04020d020a18020c06070e1804051e0604060c020105070f030e070302150a030b0a120b100f060512010b03010f0302 75
    0xd0501d5080081080360300400d90000401d100018600144c074038400ca40d4007441c0c003406007841c0c0303145881e4466584502d09410720a1032980703000c0c0203140c8264012500d401840d00e030002e410850015943e640505130341c00e0b080107003040106502030007120f076052560320301103103440320964540000090141020707006820300d0402408648512540b2000303040081000b031500d0b4004a481c6010354800600350f01c01d0300400000c070310a213000710f00d500c643c1d520040c45017040410b100e200492400e00204140d40f24403a2803810b2404140201860010036207000142441d490142480415a1001c3c1024400c40e8508010041c40700d0380300d84880304184c80b510700401c68200d000d64141c07811109400c00b960000c10200740c50128041c8200604c1c020300103480c01d002700c0011004000210500b0310404600d0b0000200da0000140039580042e84692811005684c580d119901c0c0783c41d81d20160061780204400061031081c1a807030310306d40c41c010100151541d01c0c541c10a17a05407001d243d00d2000900034812 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 912028003 1250 912026753 912026767
    0x1c291e061b010f09050307050709110909190501141212030105310b0414040312020f0403050607020f071413090f0b0f10050108091c02070314160902071205 68
    0x200303400004070b007503e84800b0b1103c0001410002d80700e034402181190288100d86000801001502071540c0100d10244514103080c00c180600ca24414000d101e040140060840c0000d040b1080c424940601041d1034504140800a024004100300280c07402c10b0320307440b0791100000d03600410202c81c152001038480444003030705112034541c1440017040c6c900080c2a00da00901d103104c00b0768000c00784420b00715014009400360202c00c0160a1003a100640040c250441e590f03000b070b005070000c100b40c0380302c110043c0c505071341c03030320789a003840b03416103901005801002c00c3d00c0308140100000f00c05001c03489500c2c0c4c80810340f00d0002e081005050302c2b20220944841ca100c1c1480755101d80940b406400242d03020031440c02404601000d40107c42850031651001000b0465510421301c00c0c0c401d00255004116240380c4100c0b00c4a50160040079208500c00e58102000183c8000c003003002038801800100301c4000c0004d410f10240000d41c101250390382c410301092001c0f0342074de40d018108090f242071543d81d401c0 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 912029253 1250 912028003 912028057
    0x140603060a0302190909061b0509030a060b011b050307060b06030f15130f0501050a060f0c0f0f02030f01020a1e020d12020d02040f090b01090b1c291e06 67
    0x1403681e000c1005c0c6031401010b641400150380111a10b01c1503035401a80c01c1540040640340e6019100c3d803240c065215031112800a04294011100c8850504040c00b404405c0d6040c500c9100c007803030088551342c00105030b09080007030600840342103100444a00741945041c10940602d000010b016800030542224140900d8840c2009442a00d0701c1240911a21922280c0d04002d81401e1203024050540f0210010b8102d209402418044040c0c0e40e07040e01080c60742d210a1802142303c10283c3e15140249100b0700141d81c20031500c9280382c000720016860700c0b004003014142ea9100c118080c280021902405405035010440d254070100b5030529083d040e880d041c4c8100207010318540c01d100544001004640300d81103413108c8086078812a41402185126001110454901c0c4291840a20280a0380e600114000c1422950305d0b10f101d400a5103c403070b003010b1840b94000380c613141c00c040b000000c10307442c03810014200554281044403802d0025900790110b5850b00c9a0745900b207299251400b5a100300c0 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 912030503 1250 912029253 912029299
    0x705070f06020d020904050a050613020a021e0f0d0807090b07020a03140c030105070c1502090603071d030a060614040b01020d030906060f060207080f0f15090109020a0906140603060a0302 82
    0x5c202a204004510308009a50014141520024803817118100044c4d031140d094002c40c4e0368480c1c298060807081551290a0b080c8081034846e5442c80e025600a0b404c60b80020041e0074a04001e0b0380d54500c650034016400340022982e600725140782c440401c50780d00540c03248985003048a602441c010340808450545a08080c2e11442d0b503581942070005002100350f10004002c41c4a018100720603041c2d01410141040b445905d070b0b030580010003400000c900c0c030b00841c02c2c68500d402c0004c08981d9010b0340000241803020035a07084505075514041446034100c49800020058002d0790100030013440030340045d54806101014504058443d060242006025000600109031144100041c079032113403001380d02e80400c1c0c0242c03e62482541180c40466000080f401c840032100c03006840c100c01c10040140004000070950a929922a043c140050b12500096001060503d0000a1481c01c0c00c80d45450071001f0a1440d104071000d00038800555503550200c0c0c01c80e5811510040c51311024002e4030810 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 912031753 1250 912030503 912030517
    0xc1106130801060612060806040f0f05010507120c0c11042f0903160b090108370509011a0603040c12030903020333100b040605040306050705070f06020d02 68
    0x40900d00007800080540002c0243c0f046500c0d42c034540b40300310000708215000c2c0d1180d0683c5900c103101141c04146500f040900c035900642c1414040405522810300303484098940500045040000000d501d031944509404142d0900d8410030040640d01c4064042000c40e0866100b90340d40d2101100340c211300d41500740811074041d070070b8006140b144401010354000e041454003d00803c80009110070750b200f6000e0558046001c2e0720305108c003400c011200810002c003284040d81028588810040c030750701e005101c0f027541201403010f80c00c603040380720240d079030140c1481400ea04001244841f215800c0742c11001400550b00103840782d0f980d0629541210310f607840650b0011100210409040e4000030b410f0a0328020f400b190070600c112104204803002d120148080c81010903101c0e45220f0700b000d60b080d0401800c40111a00903220300c1c6065050340141d01c0341001c148000707801c004014540c01050740c458000c0c11312a0400b03045854038048a4801c9000501140d40041c50003003554240d41a2070007 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 912033003 1250 912031753 912031777
    0x160e0a08070e0a0e0303160e06090d0503070c060509030d030906110a0c0b0c030105010c1b08030c031b0307030219080d05010e0f0a0903200c1315060306060c1106 71
    0x81141d6460310030102450690f842c070384060400c3d40a407812070001040302e0040908400b2180d102102000c00c5070001140801c1075440441040005942d50b43c81c0030403c08980a50091582c90483c0d00c0c10703a100e83c0d541c2d031041c3c007030000610104035160340100d104601d0008909000c03469040030b1030018001c101d40a8021a8907002103030399021650321107000c007449441a6145c0c49607440c0e40d106400c9030702092068600058010991100041986454854140b070400110300e40756200e048060031750b000074694210580c408521040005006109000703050710000107189804c2c000d0310000e4880b4840140ea86448201d2601d4004002200c400c03590700e01d11000c2d040055503101c80360540c0c400300c1694400c00040c058400303e807180e500303841948480780c0e042d02d0b11341d540c41c0c1038442103c002c070f00383d0a1511039008a1310110210348801400000380440d10a00180012505100c1c98282000340c108804142c5485424040c04c1d0300181c0501c4100d81024800408d80f50003000200c4a1103044103201c6 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 912034253 1250 912033003 912033013
    0x9141210020a02061f050319050309090108030a03150b03011e080f16050f0a030204111b03090102190b040b13140f010c032703030b0303220608160e0a08 67
    0x6602ea81c0420b009018405d80c20444c449081804131a000c400e0441c01403560542080d00d03102c1404801e40040702d00f19210310240da0500111800050402800740d000c000765400c00140c8a42103a4944142002c038010260354840c5d99080088030310b4a40014011220038081d03a8101651620301040c40700002c0000c03000f29440000d209042c1078076605d40701c0020481c141e10303250200d41031a00303040000c5101805000d80b1001490760702000007408142c081c14401c01c40c20040a014800034184140008070480300a661b1020700000080c0361207461000500ca80400c150030900040b011600b80d40c102d41c11000e92100d0b034039080b01000080c40006001401c1100f55120703501184004240788900e8034041d0000c02090100ba07005038265408880700f140307070b40300301a06451004d924400000c0d1103800703490000ba5401484000c289190301a05400700c4001031a007492507100c00081070312020b03148918106000d1709040c485c044101d826952030100740b00641c0301303854050f19180a24030081000200b250 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 912035503 1250 912034253 912034267
    0x10b1504030201140a0e040f02130b0310240c020102070b04091a0a05010210050901061d100803160f030e03011e0e0a02030703170403020429010914121002 68
    0x405a481031204a000c00e010070700042c6402064002e96002000b82d0322000085141e50301000014003511041814260b820312103402b90700710518400d0003400c444800140d5030304200c6403d910010341e50380264640815400c00105000410158003160750341d03420055102c840030720041c0d052020541007400119408a00003440f641b070740e00302407082200e03514a0b0042088035001d0023a4240c45000341405a4000c80808181e0a000d90200d680b0100c0d0400000e00307243c481015030046007000c8450a074241803a0284084168016070140040c50608029482c1016920352034a40c0fa001c9038000c3c0220310301c0041d107001e050041c6007101c0e2a000040080080031140182034171101096002800164030740501e201c2d00c000e00060b0b0118036900203005009291841e601c0e170440c0f407086d004904c03d2107418400040140c40e50f008020042104058094000030313400d80201a24028034a0315041102640d820003800c480010200706100d01950300c4680b5202041e461464105c1441d90809100d100040e0700c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 912036753 1250 912035503 912035539
    0xc1b0309062a160b0f0d020a0512070302030103031b140109050609071403060c03130519031403060d06201201060f2a0f02041b0e30010b 60
    0x58901e01c0e010004003168200307494002c0d95564842c00d074411100c642d1001844030000060280200c48411103600346861244a503000c281c2e0440c0c4c3d440c03008118081500703074000ba4040c001d16440019032408500b1980f468030000c0a614000c08080c004491502d0680140803204181041074440500284020610741c82d100d540c0b50811a510321050003000c80100703004241000180701114010014a107035200d44514407500c1c1c0c00a02019144503a90000700c00040d4280b101b21120000c01114030001e14170303824090050310b847e02c0382c0302e0625400c0042280c03981e59441e800c400143c0000c00060348070780700d031700505c0c06001296100b5800c0304007060411403c0030482e00a41a501c0582d65013035840c0c4805400d58009200c22008010160a4140b00341c204134078002d500c000c00d00074464416028456000f040803600c031250300d299a80d10042106402c2c58100035074484214064070aa118269160b40c4007442003100302000c4281d6586d6203a00d0030246094004210f500c1008220200c01c002400b04 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 912038003 1250 912036753 912036787
    0x2b08090613030509030a030c06110a0806100c051606170606071103120f0d0b030307080d090206090402120702010b0a140405061f050d050601090f0b071a09030403030201060b030c1b030906 82
    0x8441d0032b42031501d10b420010140b000d40340e00c041c4544820340640c031000108001c00728403084035010800c0d98103211010401c104205205c0c42c803000b00c001d8090b428030740d004049504125038090545012414003185403a14000ca80046806c140a668205e000700006402e02c20417441000700428003240c618101785080e8010321449030b00070400c02136500520141a00c80c050b4400151a01c50140202e4101030010342003c405103100400aa1030070703c00e4030000d4101d81111504010080c0031404100e403441d024072500d00014070481c0c00c0e180c1d2519010084980c09040d0b182980540c2d1240c000c00c0d40350300c500b00b1061440c0104c14542d48030407005c40c40101035412040900800d181060040303201d9501030718147e410b5912444289424a040074410741c0035501c403000c100d6814900801c6584425914901540210080d42c095035076507146050003801d591494014500d22202003042c440d520648804940b030303117000e0780d1030044641c1d6420113044c19801186060313034202800040d2409820740c10f13a4 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 912039253 1250 912038003 912038027
    0xb030715050c073c030b0c07050a060c0f020c010c0b1501030207080a0509090a1802010804140604140d0503100603050c0f0712030516080403202b08090613030509030a03 74
    0x20180440c5502c131440c500a041661101400721388015000c15080880d000061164a010340c0c00c582030700075656118012905880b94690020310300d0a46880455414029012520303400d1a00001c60340e070503209c0c044400790240074180176031000c85481c012640240c05603a161600100015210b090400015009903c1402c03024429025000040d603184c049101d080c2d4041c581d04010f50800060f0360043d9001c660143c429100d03402510324ac15050b807030800c00e0130302c01c034840c0c0064190350b20080507491629110220710f10078010305200b0052442c20503a42001110603915011030f03140c27202c41403011075200d40e200203070f2043c0c00020f2003428031000c0300020000b90300a80d0204100d036a12044006420005002a00002e00740d0001c00d0102c8c1c0f203800080c07240c8100c0b041c4080600a1903107000d2400d100ca407503941441e490041030b040300900d0074840302602c2040d0304000c2000d24018001c142c89440040c058000030501c0c44440b030038035210f04190f038804c180207030440b50810b4590074050074810f5418 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 912040503 1250 912039253 912039329
    0x106020c03060a02090f090a20040b1c1409010b0102010513080d090f050a1a070c030e040c0e040c0c121b170f0c010902030f0c0109030b1f06120b030715050c07 70
    0x44000c01d10044400b1034be520f0b0701d900e0618103810100d0300000a0000d02c3d400e01034035520034901014403c44050b029100710b0303000245443c10100063300b5645d0007007140e40900080110f0901003a00f0f031003116085681c6d580c00260545030303460302600c1c4007181c1c0c20190880c4903041d1003c007000f02000c03140d640020549a906882d54840e90221a01d5828080007000a09040d02980300303410309810840c4501d4050801881d0f803c1b004002ca8100d0b08155850320004903507011250a10400b081024a0040146080000000300c18600c41204005002c0240b10301882212100c252401100741c03481e4590261105503a158001c099501804030844240c0c841d0168030081d03004404009841d040c2c0c414180c5806920a15680383d03a06039400041017021030401c0344005006841e03218081402501b21a1a40300800e00140040c0d01200c403561b08280c001d0f030081c4018810039442101c0e95805401c1441c20315607900d85003070b5490410740c0642c03020440000302c100720150640c51602c010701e0401301c5 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 912041753 1250 912040503 912040541
    0x909080307020115030201050706051918020a1a040506160807140d08042604050303040306020304031103040302011d2139122a090106020c03060a02090f090a 69
    0x7041c10084044d440384402070204004102c80000266550040c5500c5000f00b00412155104a01e511080c0d5011441d000c4421040c018081c04600c1d140440e480034002400030030f50402c16610008045205600445100700b0000c1000030041c200d90985400b040e80c0b00d590562101c0d0b59103001203d140712048401b680d409000600c00d02e20748265480f0303104607040300c5210512854558290208480c000003006000e50410000c00c0c2910204020402140318070801a035078601828000c0c0340c0740c1101090703c030a401c100300800250780c0c8440a2030100e000a1001c158030180b001c001a058900b24102c01c10010075406011544240844c0c0d078040101c1c0e070040c58013800c3d4140c140e000e210712901300c1c111a1013404c480d01c1c14181018241c4012141c00903044030024001060700200001e43e800001d422044007003c0107a0f24141111300f60f0041029000400602411b00000b039111a0000d01c101711495001c0b5500b0410b9070b482a8001200d14050488206801d00d0100740c3e02800d50401980196011 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 912043003 1250 912041753 912041771
    0x50405160806100e09040537031202071a010302100f0215180303090601060f0c110405090c0604030506040b1e070f050f1b0f0303150906030709090803070201 69
    0x1140d0200c9850400d584100099441d201000a400c000f0302c51141004801d81e1401065110350242e00c0c0540c0c001d200402449031248106000700c4c1c041190005048800b2485480c0303155840007016a065140c14407400884501d2040c1000780585500900145900210040002001da002906807402503402407050000c02c1307001d03a403ca000c0401840180d004a41045510081945094200598000310301d0a12102c0307a4152030758100b601c5072062030b000398004104903600464a1150840141042c0511a5a48d111910380e02100710a10340145d85903400588010018425400031200092a01c0d03100ca46904103259590800c80741107130180f01000100d50318203004e1070500d1580060213449801d658401100316251001e0754034a038107000c014031030000801c9141000c1c1c29400882812000b088489643c001d2038007002000c0100250420020b00c4100d22041c000f50000190a0f21050036680b95140417030318115161f80f00b104c0062070004003400300600440214040d40c1c4982c02403060950f = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 912044253 1250 912043003 912043021
    0x9020d080c0c060f16050a2f040c0909020703030603080a1805090f0112050f01060617070807020705010f1211031e070e040c03140115030f0605060403020f28050405 72
    0xc10801c000130340900500140300f00d15090210071407098480c00503660300c00c6056481c4982501e070403140c0c80e22142d21070038041124080c00c80384211150203c4003444a0152030320041c04801345406101c6860b038000030b020050500030707040310004541c0002c0c1555034866660008004581660b0b0b0b180b80c1517102c100001d9245040d010550041c1c460384103038562070340f13002220400d950050104481038010119081c0380b8030400e124541c007e00c0c1d00c2d150443c1075171000c0c00160030850000c143e0400d110030306c000e1100c1c1541c000f0382001510400e00349003007000044842543c1402450940ca44000d080c462500040e51000000c1c40c00381500300444203155440c44440424443c0458a02c000103008282c005860301e0140c01c020407100302400c00140c5c413804203214508201d000d07001508802c60408180c500c1d1945031040081c0f210030003508002d06400d00002800030b10903440040d115442c8034910f01d1850395020401180b9809002402103410604e41a0903807400913840342a04c10352038280042c0d5859 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 912045503 1250 912044253 912044257
    0x1c080a02010c03020c0712020d050a03030506100318020f060c1009020f01050705060705070c03020409050a150b030604080a11030309100b010f1b0c051c060e0a020618010309020d080c0c06 82
    0x605e0000c0c000031810800c04000441e11a00103136403100ba0741c81550f0105005200190045010b660086a20310b80b10f41807040f4400e083c2c281108051500d03c0d060302c842d29500400c10f16550403607101c9144002140090290701410310f03410868007554040e0191a5855400300c0c44076882aa64195240911001940c040c09041e1001c0e05982041e400030b208103214200800c0f00e5403040130708041994503900810100c0f8440300080703407190b001c1022242407103011041d1710140d101044081c0149880f4102098850b10301800041a0441c0031580e0b0103010b000741c3c44c84d5034a0503060201c1e5141d19220881c55940c4c10802c00b00600c103440c10f80700e505d00d5485035070019100380c10fa450b1280b140c1e903c18107413100c10480040681c0c80ea28522030104c0c403542d80041c2c100841c1c8801c01d010035006140c3c10480100d40480a40b004190f0024030f0540c0103032251130564035585c040c150700c50541c8101c1c5005070080c1078602c00095000305140b074030804100e00d01001d0442525400102c8110b176000600b0701c2828 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 912046753 1250 912045503 912045517
    0x42a120b010e0f0c03060d0602040e04060e060c0708090f12071d063106120b01170a032006010603020a0e0406050102100216021e2b0b061c080a02010c0302 68
    0x586074803000903603021004c0000719000800074100c10b0a120964441c203080340c2081d0482c584044000701400244192030040390000c0c59000007510b070a0030102e6a0726628400e02e00300900410000c6000300103680c400140082c43d242c0540361440b4507002040391520b8040030700420440024401c4400c91161240503054071482015051746006024000c4144695428900e01c2e80c140003080d00d00d8519001d94000c0000034040100d20742c0d0240e1940c54483d202000580040f480c0c04480008060840c0001441c120790b65010700f807000380707600c03104021003000c2034654170f01000b4862a400090502da01d503008042540b041c0c3d60701c003900c201003410001928803521030075005910520390f01c00500d4040c0c0c028100e0001039900c001542e0300c02d90200c0c2003804621042c140351035501c40404404e081c6141a103c0700c140922402103004084007818601c01c40350000a00095007134000140c0316180c040b50711041c401010b1a40780e8207505407615510640c0202c10031401075003000b0100c0b4050f8064000d0b1803c0c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 912048003 1250 912046753 912046771
    0x3020a0f031413080d0c0216060c0203070e13050a030f111c1d0a12020909030f040911120a0507020d05041a03060102030910170f010509042a120b010e 66
    0x41903e506103c12400c0000080564a46004101c401d9203c0d01522400032103054540290113000d0340c00014032907480c203035400581800b1001c0c0d14000141d070040b410409440c81c01401c03151540301c0e03906000001c01c485400230103512413681c000041c19003000210b42c1d8240c4582da1507001c240e0b042043d0703440c0e0b50030032004510721183f076030002c105500a40c0405540490706040040b007612120029800c000b05902541d170490b00503071841c0c158288901c0107a030012041c80214034140c1181c90715200fa200300d100c2c0000c16540c0c0d880c102d16171240c071001c54960380c0740c00f1400c014030308180e07880c0c0703000382401d440f00c0c0050f201d440c0340d001d0418080d400b9941103481c0c00428400035410300718600c800d644000c00c0d45045000411000342181e5442d44052031140059449600074503061880401c100700240c6201c44840c40070380100090303500c41c074039507074002c1d400740710302000380150403d400381d10918840b40c1240080011000c01c2c41c042c88001600c00c44c0c01801070750510307617844072501544401541c581030 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 912049253 1250 912048003 912048041
    0xa080c090606090406030c090c02120f090d0218061206060d200604031514042a1a12010e131704080709061410120f14010603020a0f03 59
    0x8114540060816071119001d4603070391500000d10005004c858040e0021200c0d0200910300340030300c4049104103515680c0c540001d21094202d0b10420343c003030082d5224108090b00c00605181541c461040e00120968003600ca032441400c1c07180303101400c5000325200d5008000301a1034000d10617001900c10f015510182c6007044510090321194044060003441344481c1d441c40c0040813040d150400103000650040d22500304003c0d1501406042d2050010120051040d003070a20002c200d04031440c5070b0407206c021014043c07a168200b4207041c45410f500c6040b44071003c065609c01545102e0003403e074160358401445c8181e0329003606041e121030a0702c4203030450320318074140d0300040c00c1400380c0b0a07228905468181007981d20744a0030300d00401c0c0d80102c1c00381602c47e4020400219064084135000707200b103c22502c14200d4210003080904a000c17600c403510740307a0003400d609440c2a44031102c110442d5400220700c2d0b07100c0f04090003a40c0548080e100242a000080219910278070581240d141540e031040 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 912050359 1106 912049253 912049273
    0x11d180612011406101b14010c1b02090903071203020703170f0705130b070803070212040f15030f020703081f0e1605041d01050406050a08 61
    0x1980c1000c000009503d111403089501050039911031400c1d101e10340c41200c03000001310440440359000c07046401800751000d00074015030750360402403104062140d8111422026000d5442841107411b581c40b0052a02d10b00a503001030700d0908a900f04a070035160146c404259015a80110307900080c07410405402c02c004000300e00941050004510f85100400f4000740c004160300104000015102c610840505008016000c003004554940b503646c0f40000c001c1e0f005440038805031180310440701040c0145803c03201964400640c0c0401280b41140b59540140700704880300c1810348800d0020004a040d20143c032080313001c0e40d1a0520b50030040481d09952015800d950312080351342e00d049c024081d003d012260000c400940c070101d041c4071003604a56500598000b00c00304039000c101c4600542c90401e41c1d90503984101d80812440303580e0b100300300b0500164420421a90170038000702c = true := by decide +kernel

theorem cover : BRFrame.Cov 911870503 912050359 := by
  have h0 := BRFrame.cov_init 911870503
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911870503 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911870503 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911870503 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911870503 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911870503 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911870503 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911870503 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911870503 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911870503 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911870503 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911870503 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911870503 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911870503 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911870503 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911870503 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911870503 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911870503 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911870503 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911870503 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911870503 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911870503 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911870503 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911870503 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911870503 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911870503 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911870503 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911870503 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911870503 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911870503 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911870503 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911870503 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911870503 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911870503 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911870503 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911870503 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911870503 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911870503 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911870503 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911870503 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911870503 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911870503 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911870503 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911870503 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911870503 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911870503 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911870503 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911870503 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911870503 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911870503 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911870503 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911870503 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911870503 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911870503 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911870503 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911870503 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911870503 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911870503 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911870503 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911870503 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911870503 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911870503 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911870503 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911870503 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911870503 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911870503 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911870503 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911870503 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911870503 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911870503 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911870503 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911870503 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911870503 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911870503 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911870503 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911870503 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911870503 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911870503 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911870503 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911870503 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911870503 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911870503 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911870503 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911870503 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911870503 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911870503 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911870503 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911870503 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911870503 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911870503 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911870503 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911870503 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911870503 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911870503 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911870503 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911870503 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911870503 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911870503 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911870503 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911870503 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911870503 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911870503 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911870503 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911870503 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911870503 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911870503 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911870503 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911870503 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911870503 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911870503 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911870503 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911870503 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911870503 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911870503 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911870503 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911870503 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911870503 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911870503 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911870503 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911870503 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911870503 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911870503 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911870503 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911870503 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911870503 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911870503 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911870503 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911870503 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911870503 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911870503 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911870503 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911870503 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911870503 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911870503 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911870503 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911870503 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911870503 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911870503 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911870503 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911870503 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911870503 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911870503 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911870503 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911870503 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911870503 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 911870503 ≤ n) (h2 : n < 912050359) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
