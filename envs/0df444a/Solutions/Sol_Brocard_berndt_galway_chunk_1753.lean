-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1753
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T04:33:05.569408+00:00
-- url     : https://prove2.me/submissions/e14bb1e1-f5b0-4e5a-bcc6-22626eb0a7d7

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 315107913 ≤ n < 315287769 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 315109163 1250 315107913 315107917
    0x61403010b040902030a0b07050c0a0807230607050a030e0102180a06050711040209060403061e06150509040c05040f12120c020609120718020711090606030c090103060510020c03060c 80
    0x1010750903420480246c00842d40720401554404035a081c010716000c54801600d18110400800366191007022078503c1c208410034401c0d0441600351045d401130018409800303030300c1c0c41000e0300d44414080000f4100451034040c2d0040304408003250000c5448045140100f40e41004840170340e44160442e1700c000c140c0c80e0181c000d0351541a0441160107075a1151414400203510603102681d2205050000100064050140d802146607008420084a6501e000fa10940e03000c0c3d0410703070314004603444d804900c52740401500c65003c0304680108201000c0b61041d00c0da40b040b034004c6010b04085800218002c65800c107601c515911490061211a00da00d00450b518100d40c10700942c08001004101c034580f400d030300303408c02d140104025203c00507920090010b415107103105054440344c001c036440040c1b0040c400610228041600c4800d0f042c608240020080e120080c0407003071500780032440e85405d0740300398011809000060011114002080c201944e0340010101c500d200340b00b0900000e25020803001 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 315110413 1250 315109163 315109181
    0x30f0e0d02070315061a0a0c0209040501020d050c0f0a081306050108031c1506030f0608030a0e0310050405060402091e2e0b091302091801150503040c050108060d06061403010b04 78
    0x2d8292051315412140c0c03030365102c8070042c010444623100c48000360740c0300c0e404680294402e400060307440400d0140076003502c0c00100030040160b01809000c0040780781c0400c03502c61034000d20f0625600c1e921034646510101c1c1140026060914010011072a901c0c000020850000141000c0c000c00740c01490010070340e07402580c15290180302c3e031810000c0d98000d400c0001c000c036000c8404940300ba204c94220385581c112544410000d030482c001c1c202075003005d0000240341041c0c0c803414409407410342c0b80d041c0c1d900d8018000a00400003040000d0b20320344101c10310f44800b50135a21b910900d0030184040e440344001400044c8140601c8030101c0c214602c5011108101c91035a1000b13030900c901030081204041e42c0c1c0a004070015020031405915950385001d030b92042420b911040001d50400006e5000a5035120304081406801c05c00d01c400305001d562000c04440c2c0034a0111115a15440800c948550b4040018002d9040200100d00174110701c1c2d80808400d016002042a03200090400c010780d030380740c6 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 315111663 1250 315110413 315110429
    0xf0e1b032a0d1a150a1e030f08070812040201080717040204020d0b060310060e0a23060904020d06030501050606160b060103020c19151b030f0e0d0207031506 69
    0x11030314031941000710303900141e10f0240701c0324410007403a8064484000c804580c5401c007450003c000c507405107030510610003e401e9000c000101495510340c00d01000301a8000a00101206440700c03041150150480b0290383d8006d140e1034941d644880300303c20b210000c0d20100e0121301e40100040e9460300c00d04207110356070780c041c0100707059807a150203020082d80551040d461240c0c5030660211541c03a0a00218000d070502d10303080d28410301c3e04c14000d008550506031688501c421420401404082106042c007d9113210141c1d14152000b0740018650700c504001c03150050b00204038100180141e603c0541281d0150009101581d103aa0402c0894441d040c44080406940c00c05000800c803000009540003806042c01031505a40108807407424984030f03210780d0302c0450a40140200810030070004070100c0b0503d414014500c0b91008078000700000300d094010566641111101000d0300d801c890101003400b01070b10340e24494004025150750b85400b055602041865901c20040050312500003110000 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 315112913 1250 315111663 315111733
    0x501120903020a030e0102010b030f0a170a050304060b0f0a06030e0708010608101805070e070e060f09061c050109141509070c11031002040612060b0a030f0e1b03 71
    0x70384e01690b8680e040807070360b4110344d41c07042108010b48040180e2140f2040081c028001c1211070301c4c2c02072401d040c01800240d180f6080c02030881040e0490300380c9400c243c0c0315501058425140002c14510824001c46603800208040c00043c51a0541d0090b0190011041560031883d114940325003a600300f4401c0808a501400c59101e100581e5030100f04410400111051103807600c1d00c07014506040b58005107802281c4070144410a6005120005181404c6c0d441500305030190800c4c2c078403401080c040b00d0140c18006540c171001039500c04d020f0b41a00703e4136002c120558540d4007000040224020440006031040d011418401c203052941a89182c0100a00141e40d1030310003c071070740d003c0c41004030b818285000413143e05580070b208001d41c000c10700000589552038240000c140700704080200c034036545441c0c001c1c000b140e4003500700c56140d0500d044c0411506c58882c6084006e000c2504460110b004118000c0000c81405c04e10700a103200440841d6022105141004c054940000c603140e031b15000 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 315114163 1250 315112913 315112933
    0x1a0705030a0906090f061b03051005040e1005190c03061208071a0c0904111c02090d0804031b0f14040c0309080a08010302030730050c0a090204050112090302 69
    0x5500002d004900c140400301c2c031480b80d0b40c0c6a50741454aa201116480d84801450800840e240001c80692443e031600784440d040c020a40f94001e9204d0080502840c3c84040604c1000e0b81000070002428418a08000c0c0c1d00d402421800d101c495005203125072400c010350f40c200c0034400e01400e019a04d10b000c1b20301403a28141c0c0ca42c401d036880140212095584240c0c87d41701c00c0302c0c540a452183e00b0b09031601d82d880085d1030411040f603083c401c0c1c1e605034000612640b1180500c0d40c042c500d4900b600d603c0144e035640450700048031356240c1c140c001c0a2040006001c8100300740d8414050070340032050091aa0240c860035582c1c03e0038030500440040134408010300005142c1070b0040500038440d400d0000307480119842d841c0c05940000110000708a01c18010411420108920801003032000034004094000340f900a038001e19441941380c4490416a180d418090144802c081120005084800c0341d983c54032074401170740043c400d01703012440a0b4040450b01012340104402c0780d60507809030480000d = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 315115413 1250 315114163 315114181
    0x1080c0a150c080304030903230309130605060a0513052b170d0c0809031305010e06090604030b090105100f0b130f140f060408060f0c0f0d0501031a070503 68
    0x55100000402c00c070300c1d0384505020800020055001d40e01941d03074207540700d00714180a9000d07500c000701a101e071400140e06038486000802507034041ca404135a100c03110070b2016024406400700d50040d5520060015824400e144c100d0300615465049403459031140e541d0b841042a5141c004880e6034109014001841c0c100781260824a9030303510a8038400340720340c0e000300d40300d40c4e40d0006c5109c854030b02c5d540d0b022108090341001c446944070007000d00952a21301d51494000070043e003440792605002a02098100750ba032400306880040d10003910103515240d0300d0809005500007aa01c004480d46032034081010309042d80d00a409481012400007502c625002c103070030b2164041030b0f031021440440c0c400401e04103021000d180c01014038080c0d600141e25000c0410800b200070140203445107008202c02c224060b030101f1040c0d400380340d4240c03148465031180c490100318400c844030180300c0c003000900b0151003000399001c01d059038080c69105041030fa4514044c0c0501005540e44030200324184006401c803d = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 315116663 1250 315115413 315115439
    0xd021005030406020d0903050d0509060c0405060c150a0506011d060315120f160e040b0f04031404030b01060f050a080a1a03010504200306100909030509030d02060a0501080c0a 77
    0x140b003403c0c01468010b0402e2050100e07181c09004900241d00007400b040c64078458000c1d20b0704040008040c2009040c4403030101c01c0c910440c401c442c06064042481d00c1d0381c4400340100c002c4e085444040744000c1c81c061040400070102114001d007c100001c6070244100e460202007001c50402401705c80c5107480d0500e40010400f00c1c481050752148120700d542c0c00c0c0c0c3c80180200071801c07102000074020b0341400070300c48030303030307000640100f10b4000c1410100400301d0442c20506810100e003e805890035159420111544100c0d11121602d054001500100700000ea4011030304844259032a0444500310180803a03043c800d0f40d450310300280c581c030003140c04a80319038000c2d08015640141304230b0200c40c490220342035a0302203d09850361080c2901c0d5200d0030740030910a19101070110080d018034030f84100042105400c500440c0c00003580d4042070130070540907000300c96040e00004c0846404004d840b000954986084034120302c41400c0100028101000181072150740308002c0489602508100f8080140303 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 315117913 1250 315116663 315116671
    0x5040929070e040b04110c070315020703053408070302010f05091b1c080c060a0204080a0b150a03080304060c050a020a03111222120c1211040c05180d02100503 70
    0x75a40f442280130346d11000004040c200350b060081d183d1103140d0b003800d40b07010040045210070603004000301f0001a41c013030211004240004440c0101d205803900200c00308a900329081d0005804c180c044c002d00c041c03076001c0d101091007a07009218100f1541d06081c02c0c1e0700207449801c450b40c44a1083c1c001111045462103484030301400b10100d0030040108001c00441e49403090700c5000d0006459120040103100700c0340d120710001802c0d4a41031511413402d60f143c2c070410b00600980365240c007240090b508003101c1c02580747c000380304448054413410055065841603d0403901e09103464211103c190064055a80303008140c0c0261038000100d850136284074422101030a824000e840801c06a82440800707491042100c0a4001b4400ca0752402c482c041c00880e04440003200d038580365000019003030a01d1308244d454041d5446400c00c29442c2100070f25140924072a841030a2000407c00503501070040c3c854280001d20104041004506003d0503802c02000a5041054a00c840c80007d004100440d00 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 315119163 1250 315117913 315117919
    0x4060911030d1107081504030f0201020403170c10050c09010c03120525031e020d02070b0109050714070807030318061401170c031b040605040929070e040b 68
    0x3000c00110002818180700707003a070401080d8201090855160100a96070161203404002c0c1104405080350b14561140104020204032602204404052003901558019a409003509118401c0380c2980c0543d038004809200480c41255020402d14002c0e01900740920541480030703141c10318810045420070303104c0a0075020f100403604841c8142079288600c41c850707440c04140e00d1411a24440b000c0e420303400c00280c2420142411048031580c1e02c00300804c8207034480706c400180d9422080034864080d005401c0045e02100c0c01c140009101d9020381c000314454521660f40000c074058038031541c6020300814102a010350030038403800d000680664404600319081e1130002440080607070326102aaa2103840e1101c144a1042c010844220501058401050703244054a10103030300c5008240d44040071010002106d01c0440210025103443d4007010103408050010b2000f03514a060a00c4080620b00c54941451400245000b40c001880041400380c441030b81d4480c1101115400c01000d4203500c000705078 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 315120413 1250 315119163 315119183
    0xb0702030f03011e0b0a02030a0804030c050a060e01110f040e040f020303030103081210051c2105070c05010804030807031a04060e0a060f140402031005032401060215040609 76
    0x44001224005140240030b2918100a50b80100e0f0200107964110b605c8500460310a016421500d034000c410380d001d100142c03900000c650340f40d040c121100200e45102811307034001c200e03402050190b990008082190800000c0c000c1d04e001030303084071140c806c865084110420a010600401340d9840b43c8941190180d104505820f01e280c00003400c6074000c3c2e01c02c441c039035800608940074040c02d42d1780715805209039510700300443c070f401c02246109c00c20009448d04411000d002c0d03810171104c2d05070b580303444122142001d008480d0301c00140140d030007008142c99081b441c81001902e5840745844500c40c0d50306a40354015600c4004042c0c018000901a5103000204181082140c2e01c031440b64600a04c203d0301e140b03a441c141001c1c200b04440300d980096071007030340400050042c16910107004c1030124080d1030050f0350307549a080e1340c0c0203450150403042e494040c1841d0495100c40c0105610043d0034103040140150b640c5420036a5034085424900040d80c103c500018085030243e80301006460242d41c1c425 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 315121663 1250 315120413 315120427
    0x140714030f130603050f01031e03022a130203040c050118030f1a1303020304060c0201020a0606030305090102100b0102060714120f1501022103070c0503040b1b0604020a030b070203 79
    0x180903030030060014180c540002d104101a0f54503005480c0c012601c81c1c40f1040c19410754480d680c1d071031201442500b01402449030b50702054400c02c1003005485030203d0194281d80d104068048500a0000c0303984105507842c2022804441d500c00c6034003540d84100c1051640f0b203044015030303100c01d03d10702181c106001d6002c0000030030340c440304151015100d029441d807044100b03188499101001f8021407030205010410000181d000002c8500792203d80c00c0051071020940300403450141036400c0201a0f50030428004100764000340642880e400036001d48965008003103d0324112241c0d0b0200d240141c3c890004550303220b0244000c6407034240000e031424030742056044440a4103509880d058072142d00101002949404041001c440f140c0c01d101400210303410303202d0002c10a200000302c40a04e000000461003030b074007840c0d504400560200640791a603603160788183c40c54111140d1041c2003102140c0801030000c4c0410303290b12855000b440c075000c0508684640515840041159044d8070042000e5 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 315122913 1250 315121663 315121687
    0x1e1b0d08030a02030f070f1d0d050712050d02191101110607020c030c010201060e011406160807050705120312150607051b0402120f070905040c0c03020d14071403 71
    0x1944203400b211009680c0341410014000603410080050080040145c00d41e030000c0e603ca800d8a1a50441e1400c40c0c0d01401034000156403c840400000d0091040d0280012080d001150035900107020310140c40f9403040102090ba2210031a244e130aa00804100d034000016140c140c0440b6a15010b04d444006544a40209072804906440b408050b922403803500e19140750030482e580c0903110030b20090112a142810380f424511041c0100382084c811113184980603141c65007a140900f00c004090780700c40515080a0f00c1c1640003800550b0940105203011401c3d0802c0d0b00e00034181d2855400652404024103070900090303801030a120a11701a144144405a8a5002408129001e80b0141c40400701d010350191241e0b0090b50881c0c0260300502c810355a1824400460340d01c40c00a4070418400d6a03290012596000c1c5504180d6200e860070b407201d44281c0d80846e600111a2081e000c072240c83c114401c00342d440d4204220303588554002008280c002882c41100102e400464408503800c000c00381447c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 315124163 1250 315122913 315122917
    0x409050106081618182906030d140d0902270c03010e01090b030c030f031201090e0703021c0215030a050703141306060e0106021606081501111509030c1e1b0d08 70
    0x31035003403000001c406c080d10045100d070004801c070010010f0480080c00540310314881c6c526003e483c44042080718400000741c2140d102d0f81d90090080382c3c090171a401c2040d61300307145003242044040c510000f0301e00703130a4003040741c0c107980f10303c11104101c4c0e2900e040c80c2c010303260051003260940101925000c49072020441a04103045041c041c540f114108804c12103403c9050780070040c101d003060040d6600c0b00c4c0102c1c3c800150381c0c0540d102c086030400102c1c00300f002250300300000e402c4040c0e11024a03980212078050360082c2c103110410721490311019011803c0d21840c41c172034001001c60501007407007410720f4105c015800d403240e0404a8200c4e501c0c034040320f403604268420000360304001010024045800c0d0740c60058540c80c107144040303040c02c040454819580303001e1141030203000d07441400e044c40100f108080c2c03030150380305031071302032a00050b501c1e01c80d00140d00c5610a80700b11100404001c942085e514075000e5144010140c07030184041402030b80c00e201c80784541082c60320301c141010801c4540 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 315125413 1250 315124163 315124193
    0x30a0f11030601030c2c2205060f011806031a030a0b0a0b1503040201031104150f0206011a0306040c09050d0501020705060c030105090f090c040905010608161818 71
    0xd900e0340300e10b41000090251035000c41c9503020440d9034800c4028200c8040200343c4200322003600e42c040c2c09101008214101107607845203e4806031126030041c0d080c40c81c0c00c07803072060109030392016088e00244019a4403c00c68280c0840c1c0d03070220b540502c020742c4298401040c01e094020115155000b03017000c02d0808045a1069a20050880400901d100c0d240a52500070300c0c00c2d11040e050b0314403c02c0b224518040030f84000c0c1096111000d400d01c0c1450300c01985d01030103149400c0740e6505092003000d44100c00610240c40580500f0000088200c20010324052008910001d035103540e581d8010440141540c0c9410030511130305c00c0000c2116111802d141c0503161081c40010794507240c40c10400e152160050000f6118041080140f1850710f44003406500100203030088402a01c880b014141410001c01e91035400a29100b8031038140070054001c4001c40c0c004005032558010001c0b18440d0000c181c0c09100c60b11001e044450460401030381c04407403203d12002c164481c420f0f244c0e54440700d00803841 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 315126663 1250 315125413 315125441
    0x2100603031e090504060b132903060303040306061d0708010506070f0204020c070e0a180206070311010603051f06170a080d090f06090209060f0a0618080d080f07030b090c030a0f 78
    0x820b034480005008c44039580540840300701c000c003140c8070130f441c410891801c0600a40607040031002c140c85407810000c0c1c60186900000900501d900c441440724100b54074440180c400c20054089145c480c0a009218140c9030090951460a08c65440e03480054850b00d40c202d810960806c4000306804c270a111010140003800704d42101402d00e0624201941c40000c480503140804c1c504c1100141d407a081180d54440d45405e000e00340940c00218a80103000c69030001d0154002c41e41c1594409511500000c040c0000704002c102a80c4c0300e00310401400b2031104103864503031207491800b02140508000d07100180c0c14120116205441d90760b80c03500d080c3c1540c0103ea0854884510030214941245507640c818421741300040014012400281d52601c0741c0301c0c580600081c01c7c010303074031a010b040c50040030744181401c42d1030340e10101d14001e02c004c0701103408200c01956000840c4195101c0e02400059020042001260b61100054030380030742e0018050100d425981c50404260307400c203005170b90b0300c84030350 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 315127913 1250 315126663 315126667
    0x6080114060d0212041523090f010f1b0207050303070b192405010302180402030a020c030f03010501020f060103050319090312020604020901171504020105120a050702100603031e090504060b 83
    0x10301e0800329500201c41c86c40c41a5051062400c04090304030040c4900410400390841d003610380644850500d0b400c00d00e01d01995082440c08011001d00ea080030280800a0300e0303041111204d0b04c400c90f140c1c0300c40c2c050707107505403c20018480445c030070000036a00826002150b0080740c2445c81504102c80807240b04c2e640c01084070b40443c014810598a1800500003030a06610309140078210307007110140050858401c66000c0302042c404000c55043e521110820380032280da80000d03003070b01c0c10560024031610f4014858072414450440000c114541205c4e8000021400c02c80d0450142c002c00740000920300030003885100000218404648803034092100d80c01500d010b0078240140101508141c00940028aaa40000002e10030000b05004100401c228542c86603c50780b0049465201c1d0201141c115000f1409026038120268030090040ca0a034080346c1040c10880c20080541d1010700c40a000301d84600304440c00303501c904a1031a80c02c00a0300e0440861525500001d044030041d4024225182d40 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 315129163 1250 315127913 315127921
    0xc12020f07060908060a0e030703031d03040b1803010207020303300109140105010e03100519050103050304091a0d260f040509010902070b1605040f0303080601080a0606080114060d0212 81
    0x4284402c51b080401c00741c042c040c40b054101d2a650b6441108001000c040e40d0f8000c5107500559416a5950340c100c034001e681d40c450b5107400f0151145c005001004011080c904e02210030315051003180c480c40e82c0a000b0f1420074a07440ca6030782c3c500a04139081d500c61413100b6482d82003070380c203030b4081d902030215858001240100f4400c01c180f4948160020b03814010000011420740d81d000603ea0038903c844817010981c1ea40c3c1d50801c050030312a41e20401c0041c0d00f481c001008201011010b4020b662542d901040710484c4801904c01400040c0070361900011025042804210351003007010881c1c8c1140e04504002600305c00c840003a070f005000008003c0e00c042424802c03071030000b94090040c01341c48015824001c03940ca81c0040014040c21440b4254119044481560f01400030396005020040b00100d11660b00c1c240501444800c503101c60001e40030500054011240c2d00c80c03c0b042c1e82a070b9a41140340c3c0e00304503805060441c00c10b040f0f648258180406079400401d030004202442d00010030f07400d5410 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 315130413 1250 315129163 315129179
    0x50a0609050d0207060813080f0a090815070c02040506030c090a020a140306150a140a0206040b0f1302040519021602090106050c03030a15081006140a05010c12020f070609 75
    0x18038005090b0864110540400034a94440c90032a000100560303074540305582c0b444c00380e08610603a6400d0041d1080800c040030615001425142124185000c1e01c00d0071440744181d0b2400d20b0110b41d40c00108042070035080140c14140d000c02d50065000d0b0032216a10602000181d070801304840030062a900060440340455201154070b10f0100c2516001d411410180f00052000d6a50310700036a2921021403107400f55446140d200d900f804060500655424400000a481e40801c44083d52007170305038400301741003000304210140301d1089655214a1a031465007003001030000546540068022100004102c03206440100300c0354608034200c3d46c40d25a144140b040c0410164000024030406000107006c2c80e0001c805c6a51005021000240c11080e0289000350000380e41c12600f9948108000005000450b40c01203040e1b030304041c48201c2c40320505c4104007600c200c5001c0d107800154803e6403400080c0301b81050441512250050300c01100d6544032081c68148171754805000190840c4003000961 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 315131663 1250 315130413 315130423
    0x504140c01030b09191103040302010203160c030c0201111608070f0915060c020102070e18060105041107030e0a030605041212060e0127020d020702040605240d09050a060905 76
    0x11001c2c2010b00107245000000740c6401d4008104031049071030521801030248095104800706003180800030b4503070400f824000d0007500300b10b88580480720b10100640e880c500502000443d150f05580d0b844c4a0b6801d5030044030819400c801c070300b00314818010001031200301301943c50080d224a000030110b051404598204104440d4403e01c54a8604a404032003c400001d1038402d840c0c2034140002c001025100403858644154042c0080407000000d00441d5000b0400e0210b01140307010440700c43c0c0c1d8840301000308440032003410328010b0350200000400603000d15642042c0d09130003410340f201e0390f41d640c85240036540100d408590f66407030400c00d840855001f113000000c401002030104407480c10818828011581800740100c26080c500074641c10782082c038510b00070031030705007400d545940b4103036020006900428422407180f81040c0000c0303001d00300030f22056002e00c1001d12400a000341c514004d0703210b5000740320101d0300ba80c0301c03036103500411030401512000324490303040041c4986081c1000c80c200 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 315132913 1250 315131663 315131683
    0x12030a030b0a0e041b05060304060605040506010f080a0f0e070906150513030f020609030703121b1a1f0e0a050f04020108010b0a09080a0b040c0b0a0f0509060904050414 74
    0x40504a90030301003080010643c60f40b00780d00c2043d01800000580d0020750400082d401564408000402c000400c4010303000360381101d03405d4400380102d40342ca60040d0350003080c800c0d510b80020310007000102e4040d525004080b080c4010440046d1031343d00440d686c3e042003a00e40107004015168141042001c180710050b05189242d0b207010750405c4800110b02d0340c4050544409080720504210602c25503035001c00302e840880d40141150681c41da00c0c900f0318802c11400099801103816000c50450740d07042c012034280d440354440600a001c406950a12070008400340076134111400e000d035049582120b04408002401c28404082c4491810051240c10348500600d00c5440300448418440142d030010240b60540d001603107016190307158071a0171070b12107202c6c0d80300e40d80c24812440440148440304020740c3c05180103d80021255480b0501409103210351000013001816006106441d80d00c603002a0500500c0241914074107950a800074003990b0060381d0a845011210307140100b500d60030400d001b01 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 315134163 1250 315132913 315132919
    0x110a0b07020c19050915040905070f080d1b03020a0f1109070e01020a0f02041503080403021801030c120302011b02010e071e060e030109050a0b1008010605101d12030a030b 75
    0x804001c02e80307140c9581c248134050040c090340010074000e1035006003c540103034002d003007048a142c103800d05503540c038030a2003441c40303628600201140c0b800c8003142c0d941c0c1160468680c1400b00d01d0b071035041008179441031003d070114041d00f40480c0c0042d074ac540c007094440303000d10464041031041404103c2c9850000c0c3c54401881641050502c0598020903c4401c90f500f007002c81101c009076001207005018600221015658a4400031080002503005081540e0084d030f0164042c0d400b10340071030a03180f400c0c0000b41c088504030004020b01598800307101c441074070070f00c00818808034010088182c8501145114050f075110489034461503410803004004185407041502042081004000a070f082409200100080020500402e440035000340c00c1243d401000c441018440b42040d840203c4152414000a0049000014020340c140640002d071140204907803101d000c03181042d509042150903011814224008405041e40c85e0012000c21044040c00396942d80c80e41c070401411070b0301026070148 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 315135413 1250 315134163 315134179
    0x9060c0503041e1208151201091106070f02130902100c050c03070e060609011403090307031101050708010b0306010309050d02032d0901030c0909050a1e022107110a0b07020c 76
    0x32a403a048134070300020035030034501900c0e1128601e5036040d01802801035048101410003020020055101200450007040541964524001003008521800390048d0002d00c400c400c160240c506910800030b012a00d01c1f00150384035055020442098154400381c01050348102b800d802c0c86000e0050132030208048000e010f840b401c21003c030420720000b400b0680141c8010030390304440c0c0d0182008100b4100d038601d000e516460014803139a41e0f0352001c60200c0000f00914501c03104100f0501070b0b00d0003107075a601c80d07038941d03800d01e0f510031200e810041c804c031b0402d03071611103000208009200c403500d09001c660145a442e10302d44010544402c101005586000e128550040c040c0408070039204042800d18022440020b030301411224009a5003002031454506030500600c0210350384200c110442007100c400c0303040400043d0a0407400b6400e04602d50040700c1c004000100113040c103c0f80c0c0440b113800c2201d0584800904103140948520044900c8581d4001f031001480d0104900700c003502003214041 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 315136663 1250 315135413 315135473
    0x170a0c0f080f040b1305010501080d09170a1104021b071a09011b05032502010201200d05040206040b0403060b190302030d111e0c0a0509062209060c050304 68
    0x38040038801000034250303a03081e1010407a902102c85c0713a90116078101000740010f50b103501189440d090480ea0490100d1b8859000264140d03248804440f00019840a06014101ca89440a00e10190b101450780903a00308040052002c03c154031944c84140715005200840c145008100c00107a400c1d0114040c01d41442904096030340001d80e080080d0402040c01202001c501c0c1079465802104041c5078000040900e60300800d8000d0880c0c500319000341c4c02070004428680504030340141414034048a500204000d0a100c1d1141d000b1940083c4003618081c502661801345408030741050b001102c2e4180c95a070401d01c545041e0403d0940350900090841140785183d000035580d0071041550418071042da90480c818003000c0c00040b4103889008264003545400451058592a41d40b03031181c46850008404207443c200450b0a07449640c01a002c0c81c0a482102c6280f0400c0202e126021306458403800c0c500000f84560244c000d41030055101c0760703101e00b003602d820308502807100c00d20200701150030642 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 315137913 1250 315136663 315136681
    0x40e06010314060f014e0203010e0a0b010c080301081f020901020718061a0318010605010206070302070c091103100b03060603130f1a090c1f030b01170a0c0f08 70
    0x2081001c002400c0c0708000c0c401b09500c49010069403020040300301050a110028140c608070500380010040380180345003500c4100030412400280a04041055080005103a0000d198840c07203103620141044102580c41d9910201e0641c4241c00500603504030242a00c0c0c80460001d030f0100311000c840d01507042c2800d010000790380d800386104240e0085600c00d40b811b000c4880d940842c0c05800300400401c1c0301c02800315503a2240e44141c17141c400307914a441e0f02c4040c0d4031061044c4005c0c2c400503805008a502e50302d808070080e4100c0700c41520089800c2900141c0c202051007961135410080340100d407030745131184044012000d194840845c0600806c20800c403030742c2e000112a406564488922001c040c181055103c5c2c00c0034200042030710902c004080101e43e010500103224140039011600740136001c209000b07450701c0d09592640c0c0030801082c0000c0f501d01070f0700440d80f4980189010b070502c1c100b900b000031009400781d6040da6010754454003a81c4c8540c1c0300388010103001050801c00c1140c1004c00f42 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 315139163 1250 315137913 315137929
    0x302090403031805010c02010504211709030d0609050915010602030f1c020c01050f010f050a03061d071706061c110a08010c0305010f15050409050a02040b040e0601031406 75
    0x6041507510700307222400c5510f10b246502c0c080c0c1c001000300500700740c42c440603001703090981e0196040303c125030302003550b100c20007180d0b03107111655614100844500044403202c4080601002c046000c01c1c0304001c0001024402c017001801075580109140c140030802900301160001d03019104890840180182a0000221500f245400c18060b948000301210000120404c9808100303071800080c0041000005411050207031107000c451550f243d80e240f40c9120308206030b00c030700c41e001282100d0400110b501c03540140144085c5a011a83c12641c0c0c21071182000169080260306420111030190020710402200c2e91011023980e403031101031030803890b99422200768a0020040362400c07405c60f4507522011401c0004000200003844010900f000140280c90240220725059445000000d018920300d45c050741d500c10b458480e03c3c98907050149010107070100411780014140c082100107501c086540050000f04805035a8008a0801000040a036070f44590104040c10844003407108030703918806 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 315140413 1250 315139163 315139171
    0x11d04031b08070b04081803010b030706030b0604051018080303100b1305091e06030a0809060309010605100903060506040510060f02010b040608070f0605120a090807020d151104030209 81
    0x21602400711a600c1e0488641c0b003529030091268000d02c0c1440100b08856000e4100409507103061b0075921040345c20b2500b05c4912108255050b88080010020385019501004c0320400280c81a454540c8580104492800c124081000282d08001c00d09019070f800c49140041c05450014610714100b05106031685c94040c001c030010b0190020711400034410160901008220141c003205086c40d0a03060000820800c22102c3c600781030860020b88107140206081c18025072008803281080801c83c00e110094200400e08222590303144000315855841c582c010a500406540d400403880c1146081d030141c403806484140210b0501042c0143c52282da0461340c10345e0540c1c6450071900c03000345812400b50400d180c995420518103080410508404108031055522842c01e02c0440ca0742d50000f240c16104100e00c1d000101032010110724206179035008440c240f40101d407180d0504031941c0004000048110702203a840c444001c880300c12822074060071150b02d800008181c201440c54000c01c104141c014 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 315141663 1250 315140413 315140447
    0x903020609010c06050f06030d050906072a0321020d091518140a0609030c0905070e21010e0304030f06020a09080703062702060d0908090301020d05011d0403 69
    0x1141d50461648180d04900010750000300511107410040110920442c043d50824064007a42000b55101405482101d0080c40c029001d545030200301e480d452901e0301d0551480c18050055007244241017485851080514000c0c2440c90b040600c200d0080902c62200c0710040030f40d00102084c01466400400d15030885603030420144007034071148012079014426403100440c1c0c0f0345183c0c000c03901c1880418501d51012040d502c10307d02d56101c0300141d40e42d0002d071000901c80349488000744810002604010340012050401c040c0800c0208000b0f900f0444041001d5441c902801e02548018424000c05486c0340089024526003030542d03d9942c0c0840200002030845500000c49050441c4184031960041460b40e00f640c1c42139849140400c0600b020b04e110b40171080402e55400882d90038441c030f87c040541e00401d114078001805a010001d40010102690100424000500561000c5c0000c003c0719080c188000b0f11581000f40086d0b4000d542d006801e0640d038003208100000b03401c05400300c40c40c2c03505 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 315142913 1250 315141663 315141667
    0x901060905130515071e02030c102702041e0f0606111e07080a0b07080901150501110a08030108010e0118030206011e0b04030c06020f011401061d19051302090109030206 74
    0x417410998070f0701d1480c00c50f106412a000601c60740d1541c080050085a4920010348400030700c0b000b85442951b40d10342c281d84032980098607015003548038140d2140d546202401c045140ca00c0c94401d840200c03d18010b03400c1041c1c03242900310510036070340b142d03401416803801c2c810801c070841c9900c0e603690360f150101c65034604000d2881c0c1c007041208007c088001e00b080380498025060341c0c940721000324000e444010100c0c20000103e29244810700651820a180100c4c4e0a143c80ca04070045520107021070322a034a42c01114426000b1517001c80065010302562000890360100b40c180c21821030f003030104900c05400044240c0d900103130b03010805604403240301001e05c040420030001080340b26510307403002c200c000e4006000004c200d1410561003c442140d001d462800d003041d880c0b0340c00e90f20244d20440521483c6401408143c0c0920a100c03140c01442e00b006c4140b1180c800802c080c0045070150a805001c6803000300128078040d03800c1e0b034410f2000179056003428407100010b4450300740c60000920130000 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 315144163 1250 315142913 315142921
    0x110d02030f130321120b01050d0504061b05091302093a05010605040e060f01180209030318150c0d0507110d0b0403020c0604140607080c060901060905130515 69
    0x3014908001039074000c60300c5498910048219130040100d0b62000002c1424900c5192400c0c540e0320450b00c054006849262601c16000501401030030001c2c0111080399842040d0300e000c1162406200c1b100a1903140c0e00d81d074035000d0040207190b401015512100c01c0c01046a03000030384038004840c041c0b52240381010480315590090003803403500006a002e8804a840c10744003030080540014049178415071b41044035050171030800351240340499564070181d0f00c07070004104c0d0b04440400146660401d00c0c0041c00c0c0102e18000a045034040030b09661042c010344c0b1640918174004c842040800b0401c1029490040c0c00d04406403070f800c103d070a20342800b2010030080e050000c20a209040c00d14000c11070302012485241502c42c2c030320161419001403007041c00e010310700d0802100b00c03026200350314941101c0309011030070800c0c42c2d40310b0358003165120818490030074103540801c102030049190800115200f428400c2c40320403138030020b1001c0c4040c00340d0744851000c188042000204c64072039002d523610543d2 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 315145413 1250 315144163 315144187
    0x170c030a08070203030922050c090d030e01030b03030a110d030b0d080702011404031506050f0f0d14030403050d0e0f0a050409031e022a01171e01120201110d02030f 72
    0x195029568200720000c2d06401c000e04040c07c0d403002001d0080c8100596126650401c1c514003503000c01940248501d24040007090041000218100301498003094140704440030a0554111400320004500b91030036800300320b04140001c8002c44854541044505212800140081800c04d40904565400503405040d0b9102c1e101c007002c03101c0c00007800d1ba9103d03564500100c00706294200102d100303140140c041030394504000d99a00e0b5203001400d051a50351260b0130040e0319506c0f940111100c00d104440c84803520b0061010301700550040c4003420310710b4a45030001c0c0681144896007480340d844100d084c40c2584c0c54510500649106480002d4584003600c0c060361005501080d11007112881408486c180303a000030240a066800c2c41011111a000c0e9408280e030b5038a080c88a001c941007c6c02d00e1a0710203a03001440d882400d24140304210302d2504a1041c3ca00020b80010b204440700301031400079541c21620240090101c00018136510b111850001c0d180c1c040c44801001d040030024130145094 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 315146663 1250 315145413 315145417
    0x30504050303030411031507090b0a2001050714070b070302030a0902041b020c0a030803070e060d0c03050411060c1b0301110f0a030518100203180109030801170c030a0807020303 78
    0x501100d43d01c3c00c0904001a894400030361a92191145259404503245515410380c090710642e100d08007402d0800081051319000301c2185810025003d015446029400e038480391003c403200000101802c15010080c010128803206800a42d01000040001004c54030300c164014424a80180c0340d03196500c920000d0b0014801c041c2d8043d00300792900d2071500301091540b001017000e0b000c5801303054041081c899018800d204c06400124144001840036000b00300c00040c9200040500349019010a81201150008440b20380069500c80c00c02c0200050080c1c8030340e0240341241e586040a111140702a560040780d41c2030b5030341800700001c01e03016485c00d403c40c00d881e05540451644628013a524000345c0c2c4c0240c030790200000e0a10010a82c600c7c0ca4000741c0030541c00b403601800c003c40301d280c1e8581c041c4d4005040303c1a076986190b254641e5290070b105010305d03d0710139036071481107515086510010100d28030b03280d107540d0230000c20420139031380000304200c1080e84500010348074000343c00024114 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 315147913 1250 315146663 315146669
    0xc02040c0e0d0515090f0304031b030212070303031406030604030e01020c040c0305061005071203051f0902090306092e2a0f021b0103020304050a0c0b090108090d09050d030504 77
    0x12401e88218901040400304d003000500c032000203400b000e80d513488151583c5814a54004006800410050010805500359100e41441101204405c3c658990124144004007490060190803100040c810503515004411b00207000f00361203a014185900003d44802015200405102101c02130059a90090103100c89001d8000c004000280b010080540900011640a48107001c0702000d0b0f50f1290259040d100c000c0c1d080045400741440d2010280d00a02c8047d251940d8007540c10804c404050040d036440010b400c48420241e1075898920525107081c80107401020315410150700800f40c42d500341d0030046026941904d450b41d000700e461202e8000d2005403007403c0e01d0008410f103078442c154655540715281c2140e950303041c2d03030004e450001c984510000103c0d0400780380c80b100c00d03c425842a0081d58000e4000c40c251043e4103000d40c0e81e41a01d0543c0d034411000200c0102c0c2c4514a580c001802c0e076448580e000280c00303e05410b400c0100a18040d020740303031054542c18141d109141c8110305550103 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 315149163 1250 315147913 315147919
    0x70509090f1b030a02040f12030c1b0305011d060f01030b0c0702010311180901060302070b060f0f0306010806071103070b160513080c0a09020c120a03020d1e0506010507030c02040c0e 80
    0x140b03013800e00811020354041d0003880c4480b02019000a007051302c400c000307008603416070340e10320444100359111424000748861005010264080110104100b031050344601032407550a28034004085581c00c0c14580004c1070314000044030401000440c0101070780c03d034070040c00c2c0e150b142e03100c12900c0141d0040c0844012111000400f068268022107405c030b492601840445000900e680c0c0e40200300c3c10b034466900000c219906000106045050000c455032400340d005224842061200021900d4050309a0002d01158005000d00c4078403504990030b41c0c02d4402d407030302542c584090b949907220160000b6200050141503141d10b80410b038410002e9840000a02510750a05683d4038003070340d91840491030305071140f00b4102c40040c032080e03a40b08942401190030302402001c0d201000354007003500000614410305800300001c289950840c410303854080b52102040c00ca055008084200b203031401860f5905120b010403801021a0708410ba240300d4983c1140c1c00315100c05c1c0203008580e908070340309a55030 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 315150413 1250 315149163 315149167
    0xc2104120c0e09060c040311120f0706260103021509100206040501110a0e010e01140f0309010b01080c0409022107080402040510050a050909070b0c0d0206070509090f1b 74
    0x104018001c04600308450740e000c454841034440c41901030300d65900b60340010100e4404c120401c0000c0e11080200040040208040d031070408803c005402d00c0001140d200d42600150003c0c010603401c25542c410301c058100580c03074a03045841c002c2580440601010b072088075100c2d0002920314501c011034100710009040001e85400c0900c010390342c4c40c070a0f1002c030342a50800801c01c02d041d4074881598009001d5650301000c82e4000001500c000341c042c640c071070401002d0b01065a0100e03586005250010700c0c1c0418aa0300c2c6007804509084802001d0414104009002130012144c0c0647c2503d095803070000d40142c1d035801001c041d8aa43c07030f8076004460808880400c1080480d00310389110705ca07a00a59007803000d590b03000c03034502800c8814028540d100c500501c09102c1405e04010303441c4d00000b500304403160242c8840c1118800e810031041644903074000c00d0b42040080e0705015054004055040403800d00551800240b610b8000601c900b45080700d460001301c1d9050180700510340042e9080140e5 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 315151663 1250 315150413 315150449
    0xe0c0405040c050a02011107020922050624060f04051c0b07090612060806011406090319050706031404110d0b040804090c0203040806070f090f0602060a0f020c2104 72
    0x30b00983c001c484c012016501c5c003001e250840c440802103c1d40c559005150742050b80c3d68840740d8844030240b003125040781030200044000620104980c602030406040c0205290607900421307000041c0c001d840c14064001489040804074042d4141d4054640032111030395000c0780e100700d031402003000b1070380904010361070401e000e10960807a25070000d54440f540c1d850310040900c0210025180248104111035100100400c081800c03051590180c0f00010410b42c50241140c00283c074003661308001c09103540e094004a4100f0100b00b0040c001010766050034820140d1200140d0204100200301a2590160111410990340c03003201d48000b0b01d5004812000c141000e04048201d0b401501507062103528104004c90780500010554013140c60030001081143e441084c00c560403012907101405001001c40046240005140d409010b001c155000f8155482e2001e1800103480e04c5440500c40d00c0d2041103d0f0300c4403240468000410031260724581488030015152205621842e4840e14821031056001 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 315152913 1250 315151663 315151667
    0x1d1f09050a120f0908010903080a11040b040306021209060f131a070206011806030213020c070506031501032306010c03021f090c0f050109030f150504121709070e0c0405040c 76
    0x305183c40a6440f44035080d12101c04500300e0f4a00c0344041c000c5810b41000034000042d54200f4050b84841c82d44441c1040d44d0303081c4e0811150890b4008546254004c503410042c0c4406808140c0d00c044404020401405c2c42e1803c2c0169017406003500d2019100c80307881c10184120707000710854080c0c41d0f1441014910781048000c0d01c429080c01a6035070320915001c441070410040c09510300f92a00205054240340811400034002d51089403280c03c0c0f4002c3c5500020310740d80d1440658494030700340b415544810710403400107040362040001441024240e0300f00011900314004602c2d8080002e00344007040d0030316400c0c10b034540114459002519403005441440054040d0455001c0b10b12488427081c070151100c2e5031480e520280c3c007680b40042e00c01403040000c640c02521404400c0d0044152aa544039100002025644100d40c113540c00340030340310383c803813100d03440004108001c403540d0841402e800c0043e200754540401c0d1062000d07685405c1c010134184603101301241d0080c10001c10810840300f00001c0 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 315154163 1250 315152913 315152927
    0xd0b04030f050c12030405190c060e03030415030902030705040e0708120a08040f1a070503090c0915060d0b030f061f06020d0f0c0b04061d1f09050a12 66
    0x400c80010303803052801881107020300156101103208a010388014800c4094200319508014025903040c400c01146081014141c035205401c01d01038011411290b007002000342680700c55400450003507108101c1048810441561031500c00c2441c6008200c00301c1c10f000181c039140403a000b5170f0b8080d18007054031b811450000354500c21114914280d0b52103d012822000b650b0103004400d00110755034000040008550802d00320610348540144c408180301e6880b407800c8000115685d00108030004140003e02d0030070440b45408540846050340e0a1404140d06121925118101d90040c0000f0403202c41145858010000c0d030b02c03010301141d19150034100c40b030340d490ba000d03070351002d040c000c03410f1450500814807040700903207034103400400100801010490b13003004096419400c12120f010705800045145c1a641e011380d00503600400e4000c11443c0007182101c6542d01d140c03d940c001059403a11200082e031600204440c42c2e40040c1801050501c241001d40051004108000d12502101e1913904124 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 315155413 1250 315154163 315154171
    0x10309051615110c01050c030705060708190b13021602030f0c04061d04020d08040e1003120f09030f080c0a05010504050c01050403080d0518030d090203010507090b04230d0b 76
    0x5580600720700045042d03c007281150341801494000e90081000b9500030341c01000c0d0344104000300c0c0d1034410760f900c071a0f08215041d10320000050030301c828010643c1482400c9003100310fa04200304500401a000262902c0c00c503100b0050207500440c0b04804900d01144440b03005401400340e071f500e01c010011461312088403900482c07150385000380c0450b07090f010013010400c1181c031045219881d22550200700026041d80702c00c030350080041201017408908030b00c0c01405800d28814908a050071880d040001d03280b50b650300c0080101142854200c0f50784039020301c0c1160b0700480100c00312023060034400b01c203109440c5c1d149420300c601e00348201040415840350384141d00480a44000100140c011a0f20784218030000d000d50304148010607800c0019449140c001c0200b58500111281c3c9500103415600001c000380e962503956054203066007028050503601c5102032801c201c0550a000416160740154068104c00c03015041c02c038558210045060410100002c3c024110580903107080c3c1e1140808032 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 315156663 1250 315155413 315155429
    0x606080105130203131104061a030f070318031202120408120106021c030e070e07050d061a1e0409060f05011706091807030609060b01020f030c19020103090516 70
    0x5100c20200300000c1c404d4a014020a000c1e040740702d4110303260a0008000340941d99841560388000051001000e40d00d0280000d110941540703916255803920102c02d40103041105150030544101140320046a540032441e03450700f000749002a101410000a0040801180d010b400041c14082804200701c00380c40700d1088500c96803103503030700d03184100d03280c0c07062110700080c3c00546000c0c0103425000b031300300410703034620300b000c035070300035648070070800d880841520031601240b0b0018100484a83d42c0c050240549650380d0000c00ca881010100303ca54402c0c0c10342001100d503440c042d0340114658808440081c8880803043c000c560300c4c2c507003400040e0303401e200e00360200700e002100490a24002d1b840360710510004141d102181c0d01e402501004504035030110b02c103400380c81c00c04000154103110324607005000300c40000d41400e10400292800300c07030300500109a0b000b4410100850b5000407002c00d000001100000b170b007603552005030040c09071007100030000d004041d07039002100030318146041203601003 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 315157913 1250 315156663 315156679
    0x3040305301b0d08070e04050606070305281d0d030e040203070e0409050708121306030b0d021c050c1c0807021f03050f010f0b190207090606080105 65
    0x618844155540700000c90224254441260105480310018000d407038202c061070070000c05504103081c2080c0300c114418000c503405000f40100e096011400145940e4191010060350070001d000070740e80e0141e10303402000c00c04000f42c81908921104000714a0104c1d154080c494800c4051002d40018200780240b020103144003049000c92030486404078000c1d4150700e0300d140c076a07080002d002c0a503100400d843c00b48140c1c4284080f03291034500c5080b080c01d004101a02419080020542c10071600114080301d41d04140034120380f01d620b10a92200320350160800045098a07540030510b80200d0082c043e606c0000000f1040082c9d002166180c65a4070030000d9800c080645020454034a026a525043c0014010582d4001650103402420020300007022659580c4581e40d00742840e03042e030090b1800103a01c5400740f0414044507500d00d40900044102503044509280014156010f41035120f2000d000e01e00c0240c8401d4000c3c06241c014146a000510001b034072600c01415108080c8500f82c00b441d11 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 315159163 1250 315157913 315157933
    0x60c0c0a03140d140306040c09051306030606060305160315050a060c1103030a0219020a031b15030b0f0f130219110a0305190e03010203070c1406010f060f02120a0203040305 76
    0x105115480b4815204c4ca442030075922250b0911004001c0310b030725442030182e05d41e008901e65030703600c071a2903204c903400340701140d014110f287c510305031103841d8440d1080c1070400c81813100202180a40360825001e030b140c000340d031036003440c1003000c00c040303a601c280e4015040050200d0350591010411959601413504156000502c4003030541c5d07441442e140c480141c0154000442c6480c55046200b09940010602c5c448191680c035580001c0c01542c102a0303404c00d01038402c00041016041000b61400507013800c104901012010480380c07680480760a21072132600029441540d9015800b00345954140e10840d114140c050381c40100d07040040383e88010550084000e0000040003644125546d0305a03100707070904001c0750135040001100040101400108462078829460034400b541c032842c01c0340d07a409809c00707150410f03803c0881400b117040c500742c00442c01444941407600030007003200c00030300d0441d030b040c0e000d114100c2c28078020040d000d00c8a640007a080c1c1d9000e5000000d0420390b4041d006075840015 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 315160413 1250 315159163 315159167
    0xa140702060c13090e010b030615010503010506092e020f120706150b27190501050d020906070c08060c04030b06010813080a0801180e060105060c0c0a03140d 69
    0x10221010001a48a280042e070081410b501501e03031944601e51042c2c50030b86500d00741c400c1d035a01c91100345407699a10083c1a09140c10010b240d00074108801c19440724140c6130000300b0a01c4140905409031800091186583e1944140082101c0004000c5c01160300523034070702d0b103010319030b9950f6800501c030394903064102c242e002c911444040c07110b0400519000307240c0c2d5484041c1809080b136111401902100107280036513400181644102c4803107070900c0280803402404207800c24040603000b40940d441e180d00350f2114424060544a090a1041c0c59840704010b10002c0d01c10b0f4506036130840e4021804008200f03122040b141510701c03400584032541e562416076502405140700150000b1586408282c903540030300d5043d40c0000840b0351080501200b5220800c595000300d400200003a650230040000b40101c2c00000c040d00d01d00b1005109040500c2c03201980c407041030144902c1040001350714244585c04211803440b0410180040d40b11a640e41030080b481002d03545968014016091011600c41c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 315161663 1250 315160413 315160451
    0x40f11040204180522051606111009081303051005010819060c050d06180c0e010c03050f090306010611190b13050f011506090803030606070305220e0a 66
    0x340095401c14210031030072a034480501000303817528180e402602d203161001540c41c99400318140c092801401e641d1100b81d01d0581c21134480d486242008040018410400d0001c5113003215409000d8000c524504070b400c04403094841e031151002001e4410000004004010030080c2600c24230760b42c03c02540c3c1e0781d40c411a0b2a12410b00c0e864115010007450030001441540c0005a03c4090345401030800300308800c2d038801c99030180c01007100050881c5403c0c200001178060448c0d80c15091604c4a0404c1100b00007810358507a10100505000011601d50440032140041c1c54200310028100c0341d0b1075940f001c014040c003a07183c00036511400354000804000c4005a00d011000303500110900e001e99600800c141d01e80d00f0002d0445003402100030a213500c860902030326840665408500c054180752107000361071044242d0020306507030030600800020f07903034203001d0341e000d2501810403981e6007407907041050359800c0e01301035120240c003400b50201e80c11040d040311600c03c5000c1c80081103004c03800394185841c0 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 315162913 1250 315161663 315161669
    0x1608090c01140d1808090f03121c0f0c091509030c0e0c070f11010f0914040518011107140c031c090812030412080705090d020d050303040f11040204 65
    0x4201002c0245008400c48002094500c0c8440c0002682038400c0d03000a0a4000c00303981504c51a0000c00c00b40320074904520400d10300c1400702c1c0202101e00d803003486c45100340504442c001d03030311903d07500d00c03044000c59030008080705042c1c80c1d00b000017075100803010703000d407001d8021061480c540c03141204c94140210a200f0aa0b600412071401c0c1d14034161002c1c408640080424032460300a201520010b400d20140c03a103482d105680c071030111300b001e1000408030312016041000304440c2c00c208103da61014180014450000c0d1004205952406c0c0701c200d90039084800300e801da40c80c00030300280224400c0c1c05864107900c00e204406419440c10f008c25aa9500c6c0b40c20254103400602c00450313103480d04807032200100024100030054a6a45c032102c3c3c00c01902002e40041010700200f040200a0724440b0500360f4501030914140c24188650700800760301602003501c5c001d22480c0f1848041d0340c2d0f607080c12008154004100ea58138980b03403401e000700c0002c0b580100d900c03104c500c040040f14a058000d480503 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 315164163 1250 315162913 315162917
    0x12020c161701182604240f020102070819090f0303050316050c0606040f1805010902031204080d080702010207061b0e0f03190c03080f130f0b070204020c010608061608090c01 76
    0x103000318003080513940c9139020843d903c0c04c81d4200400241055154100886080c600415a071030342d4000c0005810110007a6031441164810800c5200060300e10017500d89101007200c000c40906d4108806503074504454100000101002100104159100c1c0c0118880c2031200c24002d0034100b040800c0d6228068024250002e40129000824505043e82b0442c4141c111101c082048040049110300c0020624010398481c2d440c0c0d90000c0550500b000104011801003500625040c5443d907a15142e00704e20ba010401c0000307241c0424a064401d4055480d21600400b0030003035681a11002c40e0644100305003031022820000c5c0f9038250380740c00320342044a4100030b801b4045000f807183c5030b001c00041441c41160301070070f0040c0200c046803050018010803840c00d441c242d5110040c01e01c00c10348440c00e0340a0070400f100340750b050001001004c1a150055415200541c40e07850000c0454050b1036240c02500040c8180010400b04500c0c2c0c40350310980c4c85c16a1192026a2516000c0c0c0d6103500d41c1401e1540 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 315165413 1250 315164163 315164183
    0xc0a03020a03141c030b03010612020a180b032d0105090d0309020d05030a08060a120507060509040e061f060206090d0e0a081002031008030a12020c16170118 69
    0x10030040d860307121180d103880c019121144216081980c4c1a4030b0411103c00080c1c0d21841d40820381024851400030306001451010058601d500060200c4c0441c0a01598084c0000a41c040c8410f80c1c1c006411034080101904d03486034100401d400f2414103003515035148031400c4038108040e40c041c8102801401e2001c068020f20360118000c2d0041d1070f0030001247c2040301d51071860003080040c07002e48506100d0355554940e07801d00348208607440205820283c2210b075940350423800500300140f0441191560306015895180d18400200104120b41c2400c400e03000d403004000a03118200d040b015002c0760614140d4009880300030481c0e5078a401c0760101d4142c0e02500500b90401c0c01512401441c00e4020009503455845180c0d040c28501113186202c50b5540200074082120440d002407000750544500960a00881c404002e000d00910345100d00c043c1d50004041c00846400d01c00c00300440b080c905d848502d00d5035501c0802c0300091403022104103520340024541030200c0c0c19100300c100768021a40d03403 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 315166663 1250 315165413 315165419
    0x90a020a0e10050c0102040f08160f030312060504021602011b020108131b0b0a090605031909051e0f0115052805090c13050405010b480c0a03020a 64
    0x41162182e1200c050b0900000384610001e01000b40000c00181000f144c0c041701a51614007001c3c6845130314120010442042c80d400d016107240403110b1030840e905494001010305a09001200410301ca070401a01709000242041c1591503410646030304a1007aa1001c0f04488000c0d03400000100800d4024000382035031000c901e18601004607540124081c5c14820301c040070750803205448400d82e82c0b0039218680c0101e0688122500440c000c0300410343e5042c224a14504032406400c15004266400246540c8a49a8061203c20028620701d90041c5028070300102500849998665503030480c10042c0d03090226681d5100c0a21501301c0071a00042c110310040e0b80c000103100b05100354a402e181503c079010000203800c0d82c1e0076042c1401403400e01c510f5a5150002d03085009001d6076900054061814100100090030503c400c50310545030348402042010007009000100b89000c0d541140070075410701d407440100031a01001c6908041180460b0a520a20828031041003128480654400a10300c0301f0 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 315167913 1250 315166663 315166669
    0x2060105220911030a141009030e0904110a0803070c09180b15040c08010e1501050904110405060f040e15150904090506180d0206270723090a020a0e 65
    0x202c0024456900c1800c50142030f40400d14012117114240e805811070034108950110503c070b401030440c840e03001406100b00030303240a00200c81c03516101d8015084440007905001c80782c400d002c0030b9a0002c2218202945e50305e442c0e6940e03023141d181a02c0842013004001203c0a00c1d11443c200300038a070084440d41034003502c40d0328080c14000c28942c202c1c5412660542d19a945105403500400e09480e0310300a0b5041c080b1202e400e4400402d030520f00d83c0c000c640ca0302e9581e0840d047c1d803920701044402080400c03014204440b503000310340c44980c0144001c1b516001e5400108050415904020410005951800c51106400220101058101e04480400b40001186030000c041100c2d01500110f14400c1c2d41d52014500304085a034916480140c1a05485921703050181c501d580340c1910041a4509101201b94031000342210021561030385c04041462091060103c031000b00000da25000d203506040b01e00780040d096454106100d9441400041c801e8405442038910b59070003030f0790b0301010b08051824 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 315169163 1250 315167913 315167921
    0x512070e06150708040b18010f08041106120a0204030302010b06040f050112060503031c051e010e040c051c03093c0b0d02040e090a020114030a1b0507030206010522 72
    0xa2590060707000c0000d9070102d02803500400041007680c206c0307517031481410105046800c4440c665410041800e1010030015803003180ca0b50001d8100400c4039803c440d0100181881c8144c05441c0f02c00c1171140308001c403802082d800b07001245d009400900180d0008010003100c1c1c4101d0242c418280c500c0b007810701665116414000302c02c3c44040f800584a504c0c0d50009145400800b1110860201c5404c0b1140549240c080e540d0041410b203605120080d188004000f030090500403084d4040c0d031540060309200d1015014002040702a0142c298403d0a210014405045071825008501d0405000a40c8030005101c00451805804082d045414019001841c1c0821009040340c1c101ca03170401003620340d4444010807101d02d14110060392645441031141031400c0041c28804640c01003d10000581d0700004440301096801105a40d2a40c9010301c4000510038200220303803448011002202968100c001450518040c1d000c84c2d1880c1e0380e420400c1007001a0385188807002800f04480c9002031402d0300 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 315170413 1250 315169163 315169189
    0x1605030109050319261b1e0d0902090106020f0714090106120b0901140a0801020307050304021c0b1602160b040612091407060f0507111e0d06060512070e06 68
    0x50480c0d840070303100c990014070120f4000b6885e1041030707070b0041c0450703000560002c9240342c808202c40c41c18810007000c0f480f40c0744441c014060011a00041f03100c2c401003240d004280c403130b6008142d1402540c4071709000356290004c140c41c0e50280b05540c000300e55402081e00e482100e10300200040300aa00381001124040401d03034400c21016198000e88032280e50318440c0e02d02900712103010740344040c00e0714108150b90400d58040d440a1f4810070500c01c2039540a02126841501a904546030700e41100043c0081440000007502ca40301e04020b101031100414100040b1075000d40c01c5490702141c02d28295a00d01d00c503c1940186901008100641c1d0700500355040c13108458080051408240c0c2c454508812061201150a0300000d1041c010035401c51a400c2800149207001400c0c00010380d41c030070031005e154a01c40d1003021240781803184000300f40405414032a018013440e08030002441c001014183d80d01802d40b090034843c41c0b001000c000000c20404442404a411140352284070074001c0c4e804601c1 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 315171663 1250 315170413 315170417
    0xe030f0303131103010e010c120c080103050a03030509030c10090209161710051201020a08090303010e0a0216050d030b030c030d051206151314012c061b1605030109050319 75
    0x481006d401340a00c69050a0b40050b00c801c03020140c20300484027101c2c0c0c6912010280203a0500600c041400003403111801035241c20000780c1070f1182c141035840c5020710f2001d1502d6200d000a111182d0007039401c11842c0c00e20030303101c10344142c42c0c3c070b42c20710b65200f68100c40030001907000011160b0f41c91003d0000745c209080880030382d03407140c482012484882901c0703004421780c2e40000c0c60398025507020018550103030b4104082c0d800c40d414280294250200a080e50002e6034011405150015040c06644c2c01541d210003150340840d0010301c05005040284500341c401c1c00749800f261414240803466486e0002541e17501c529201030001c0207240048041e082d150004007000e60400d13050720550007400098440c807020f01c1d109150032020781d6200c1c880e071201c0307040007220800100c212607400c00054240c501a101a12a441c044c40424414024210001500d62121189a1070841701055248400b21010000310001c0c0c0c40348145400c2c0c80700450003c1c41580108900a0b1880e5500c0f8040c800c40c000b8 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 315172913 1250 315171663 315171671
    0x40b120403111501051806060d240909120201050610032a050301080f0307020609100c020604181d0303070c031107062c100e010e09070e030f030313110301 68
    0x140c08030914007074414641c00303d4192503200520083c07510200502d00d080c1d400b81010542c0c50041c001c0b4900c0c2c021201e0003280705458030700c0e000d50341180c0848000082c8503007410910311650745040c50040c00e20701200352210040103401c0741010340706020319481400007810141d00c2c04a900411002004204803001d200707003c070030300060142074448640c003c00d80c07550f481644039410004024282020000344003d0baa0081040034010b8440034140c0b944903a003141d10b200d484441c010180c0b00e031318400030025071000000130046103c0400d50390341148203200b40b40c1003000495051813466045507986041209510a0001aa07010b200e55040c6402601c40d2404098040c414201c0030314101e480e4000401241ca03400c1003a8039407490b0080302c0b8030f644000c1200500300c0000404125000ca10000704000c105400f1400c2210340d004083d08a940e41002d040703400c441ca070032800240002c1084030030a00c6401504070440a2172030010660b405000d8030f031202907100c80246d07580700d00b5140b619003184d015500e0b = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 315174163 1250 315172913 315172937
    0x3030405012a030c030807020609060601120e0105010b130e01050a0b03060d0807080301051c031e0c0807050a060c140909070c05100506010e04090302100c0c120509090606040b120403 80
    0x2c051600c04451080e02d5180316241c141c03502a00703066001300300d10115071000782045401f680c0002c0c2160401001c3c00c142401441d0600700c14047d2295440a182540c24075000061814428009141c0311044e01480398455884e00c2a9052240c070a20600b0390100c1070b044140000043d0500440e0848401846a241c1c005942d803082d0080e00a60020345800f4170200040259043c90980c0038484007120098006910065801032b00f4480d2600c2540c07200d0840c00010030f0000e00030320000049a400030000d03034940c1e107513240c000e6860048007801c844103030800e91641c02041c01101c10180c0340b04d81c0c40700705080a60075010701481d1b5a005180c0410868486410320100d901072260361255400080e0200380b0349810070000d0300d41d145c1521142d001d6480c00401300c000c40c0d07020405201c2556111404100c42c1d5881c4800ca60341e620a1902038070081441c8030061a0581020080c030224109032296809070703442104210b41409103200c0e841d00c44008108418a100124444950003031190825105c1250 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 315175413 1250 315174163 315174227
    0x304032a090203150d03050d2c0109060b03031903022a06070e0f0f010809030706062402010c08070e0d1b090f020408071e1d0106030f06050303040501 66
    0x3009500c41d0003007580c000181320000701204800c489521059944240c2004140e0300202030f44115100c03800c10036618001d0340a400b2580c0d103008001012590340d50180300c512107405000f0301490350b0850b2100c1c500090380c0401c3c00c000c41900d58440c00d1482c02d400409180b44140c0117507108202e00210740480a0140350211003590b03401214007501c1000305401c4c54803050140c80050600740042c4504164180c0b0b2035169507028244116800a1803c0a13490b241c1c2c00c1c0302c034550f004490000780300508107440458804048a038100100c9180020302c40d404000b000203a01300d03031911160000203200c90000481c1a1b0003014018800c4802805e00e400500590301c030f0a0b190341e00e07014821500245890b0420003000c15000b08014003441c0c03c0d04500d03152508444d0b0303607204058407400c0c2c00341500c490030944241503400d88031300510401104146e8110905043c3e0080c1c1001d000300703408603141c4100300741100728a02c43c0c48152200a0019841c09040c20015078000901c1500145600490307081061580 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 315176663 1250 315175413 315175493
    0x20c0604030905040b0409111c02091320030304171e0607260105010c05100e0a15090b0703050903040504231602060a090c080a030e030d03020c030403 66
    0x103806966031100c0d41d41000f00f080141c0748030b40303005440340d03040001480c00701c2c0d242840003444400880b0340d840c0b55550448003946049203000d0181d4021582420004a4030030000e50020061089084090b0040162540c1e041442c001015a41503801880144100042d265944850702a0901207c030f10b0318106c80044d2405554a00f46070b00341d04043c050240064119403045000c0000441d1100d5a9a95611f00070803000144180d504000e0205158400d1290a008512516030460030a0001a05004005994500d0044100e80f40a0844031140c03415074207100b103025451307000e1490310700d94442c56421800340402400301c9010f80410800011550764920407685007012000540f11242803448270580380402c0103000d100035441101c11300680ca60702007442544542d00f942d001130041000c0c20048170b05102c42c0c20a850a100d60003403a82815000807403024000f200b2001c40d42106154102101a070107040c080c403403994400c0c0004c0c0001202120090041104407420500405041d00400c800b0 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 315177913 1250 315176663 315176671
    0x3030f040303150b1b0c03011a06030601141204031b0302061305030c030a120f060506040902030c0415020606040f0b010c020603061206010b0703180303141b100b0103241206020c06 79
    0x244903015100b61010004c0c0103004c12120300f00e00804c5000f410054681084527040e9105104031000000158070381e01032004d5030310742c03042030780303031039240d003108000003000c0c034000c1d40e081c0c004c00c409240c0d285a94000c610f40300c0c2c1c1c882c3d165019000c29115482801c03400f10301001c088490340420703c40c002c01148100040c1c030110460380e450301441002d6092840c2254040c0f003010300240d040400a02840d12188110740c2150385d03811005982e0795030b0406005490255810109030036031508080f020540d40022620700620080318100500c00711a04240221001c039001d1b64045140105400d0140c686031001c0c41e40a100501000841030341d05c0b55007800d2120903001741002d42008603124081c5076100420004003030301030741d1b0921094110740380541001c0c48003100340584480000c0e4108240302070140702101036108012142d000b98103c005030003401041280d01d00081c0f400042c15208915241d546914084449550303107607600380740c2141ca200200150544265400704010a144401006000e2003 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 315179163 1250 315177913 315177937
    0x5030c070512030909040b070201154e030203090405010314070f031709010e04050109061404020316030213030c0311120f0606010509030f1e01050903030f040303150b 73
    0x390034144810000181c60420030380b091688240802103e0780c59000c851504590014100e22041c0d841c0d000890140c10506c4803c0341103803200400042c070401c5c07440541044174094100c94040a40c9000e202c80c00000419050b007004445848889190207101c2c4451119020384180c91910580c00041016500217078011540124600342c1115640024841d10780a40319007440c00e00d4031403940d113030740000440a80c51030600e09400106006140e002d00144080b51001074801d12880d81d590b000c0ca40186034511590741c9611051441c984d051502d4421684120100c00e49450482801c0310110000c0d0050102e03000c41968001000c004130340142424001184030b0301c0707400540058882400200d02000c01d0f0800d8513406010848403401d070224449074407200a207061600d9203401e4002070300c0c010603403010840d540104442c60fa10107050442da00303561800000280301036255110756a40d2440101c5807905000441c0307001c100000d10a401c00298940e10480d40340c04103480e0300056903503a00c22000e40312 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 315180413 1250 315179163 315179173
    0x1211040b070b04140604050715050c0a0b06090112021f0309050f1c0305061c06111303170310090b04060323010b03071203110f0102040b04030c0b04051c0303060305030c 74
    0x41003101c82c40451000d24244005060303641407594401ea0f9819045c090b030030004540309400c0002d14071600a0b1560592f0301c0c011030320790b240d40c3c0c104000291003e0720a80d005107000070001c01d103402000001041541d014041c1100500e0311880b0100601c50800c01e0010107031a25a05c101050040213042112039280004d8841c18015002ca01c03041900145080203050400c420010320b40e0b110700c1d43d6140c81ca0804481100c07052146400f00007040c0036110b00104000104688107000100440c0c181078902c14514550700342ca01e8000c103000f9010468118080321119001032101844030f8104100d040c0d0050800301b03a05440c3d560303410001e40c0304603003000c0d2284200000032402c0e000340190f50803454250041e040c4070307040000401000401d031401a041c0030710040c3e0070050a0040010b19500710240c0000c5440d180c0307450100d0f426502c54403058504c6079413604c0120380b00303486030111801c07100014070752010282998090b407558a1615015418143d4800c070006c00720303005100422042e01010301400c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 315181663 1250 315180413 315180421
    0xd140306030f33150f0325030b011706160306080706051c0c0f14040905040b1b0301080a120203070203060a0b12010515060702030f030c0a060507050a1211040b070b 72
    0x212451038461440c8942c0c0c040b4003482540e8941144440d41c010013030f1441c6003c44a603501080c42c0000090390030110011404c802c41c210100041c080023621301c00c5584142036642d40303074200d450352003400c0303c8003441c1c1003240485c0d810005201440d07260030705401d01040d4070341ea608040303081400e01d50100380404c80014203c40054001e03034112140c105030344801c2205000140700100040c2080400800780465206801150346407202900c0042030040000d00c1589803130719204018210980b41c04441c261002030341c2041030428000c1e40d0503030794910000c0c400c42209072207002d402580103005100f98081002003e0160314240002413059042001c081390440341c100911941401c0b094203403846034540b4042c0003024110300704d4120340e102d0884a540e00c803412400003030b04000300c028454115101c00540440c032448086020b6816900814003005983c3d0f60120540b0359116840030400050550346840440140c1c07a880700040d0020215131500b0320b0f842d900310303030300ba5404000281ca81d103801074208 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 315182913 1250 315181663 315181723
    0x32508040801062606150d140a0302150708040206070204060b1204020a1202060f0c01110304030f0e01080f0601080901020c121315171b0d050601030b030d140306030f 73
    0x140305002d03840065031015810305941078603482c018181c0e4010691240088170b05998030801f03100c00d107401070401e42410b5100c0060075079921050700100c01600a80342c2c020007104900c48410312507955602c132440e00765516030801c007850b40692422070f40682d07a007401143d481c04e400c000e0100784200121201755414280100800000c141d80700c800c54141c2800c001c40161100030941d0f1520501320301c06078458600c225a00d000d81180e1820340f2014402004120a00d58402e038500107007007154640c0e0080c910700c00011910303120100d641c6200c14400c40045022541b242440f640d201048400041c06c2003080d180301410a07583c1c100500303c204011604084007041c07450306000400119100b04880840920003901030240003443e2501034840b1400983c4581d600300301c0441e041d651f4200b11342c3d108441c04221004080a481d01c80c0042d207001c0d050001d90500042204c0c0c0c0414523141c003020b05a5088107980140d100501003501809100884403201030200051070b44074078604049504401c01140c9 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 315184163 1250 315182913 315182939
    0x271d0f06060a0612020d0605040e060a0b04062103020c1504170705100507170d021c0b010206060f04150b12070306050d0b130b0412120203060303250804080106 70
    0x110780c03003004820402c2145a030804100815140c00840c056114000092a00000c1201d030b4401500141001090101d03060041034940c0b203004400020424600080d040c00111f542500541103d1100d03400c010b07007550010f01c0c045107aa4480d10440b00032482890102e01410420512a102404041400c2c050740316001c2030305848070f000e90000c0c80440e01d0000021283c540380c540c06801d112000460001f403160100555000f4440306445a40e98110124041d00035402101020104600c0645180203c000c90050359580c450581c000c18240e00c0d400104140400c17420125030b4030681d1007003141115444100528000d00880b008180c940548185481041000414002c1014546201405955140f80000024507006404601d955503601640f01401c1642480036010150a000300000c2000f901ca240c041e01c8405d03a190010b000c1780c0040d640c1030380020799035590300d42c02c10b01c800002400b5200d18001c0b02c80142440604100340360f190141164407a802000d101e0f51100018410f501403508 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 315185413 1250 315184163 315184171
    0x2060603100e15090f0f1b0103050402010906180e01090c020d020a1536021212090607020612070306050306060603040f0b1009020409020c011401271d0f06 68
    0x1020b00603114032801c0b0a407100000d4040310305070004030f0089a07010310200321010419602c44116246204541e0201c1d036201e40901c0f840c203800d01051081c81165100340221402260b040e190f98070500d08041007500e4074081c1450140d030908041d080001d010074900f400703900a0210700400a03040d03905110081c01c0c1032400c40340006560040e2140000901d54403500d401e06e03400e4000c0000c000101058840c0c0109400560f80800c3d007503802503c940149030701d107010140f8401c4030282a8955900a819140d0b0007003030305414050424485c0c00d00d1420315000030715a40e40b00a203500d1a24109a0030340780464803d8a9140c00a6503c890620450508202c0103400460485415045160a548100088011281c0204100141f1020490010001c0e445ea000742802c0c110554980c0d0703c44101c00001d420106640ba9158201480256030141c0000800d042c0c0d0303407011420a101ca40b010354100120548402000341d65134540c20712242c0c0c140000c0d4110140461030250400041e410121440c0400c007030 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 315186663 1250 315185413 315185443
    0x1c0e04051e04030c0804090504050c040c14040b130b16150203041101030b01020703020303030a020c060c041203050a0909020f0c0d110705240309031323010302030a0f06030302060603 80
    0x107018a603490703124038801a0b009501d442c06640d4600b80349000c450602503540301c00405400c1a0a1004108001c0340c02248018295800c010741e140c034030402c880170a0386501c100c04001c020442808120103400040c4072910b4400003107240183d40f8140140c85500107244a6018482404d4a904001c1310320102c0e00704c07240404082d400e40c1002c0d1201c00f024409d801c1e210b07050640da1300f484c1c0c19036402482280011078005050f2904c9182c80417038440a540622601c117081c0c01104001420415800700743c2e0213603075001030140c01c101e00b103a070207031000c0d4000201c48080c010082000a454001c40c0002c1c10584400044252502092420075140800380400780b400d102c1d0020b050105514001620800c882c0101c03900d49003a944210010b00041c022075204080304400010460040000801032204100b81c0c62038000e003035075480c201015440b20381070a1900004118104019600c0b81c0c02071134014013612400110a00111100000c803010707a8001c40158104500700101403a00344406e240c3c0c20340f44 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 315187913 1250 315186663 315186691
    0x8120a09080a0320010e0f03090a05010908060c031909080403030906030207032f0a080306010905060406023c010f0b0406030807120c051905071a0909091c0e0405 71
    0xc0e0f90702908469051400741e01c4945840041c1c110300c0c500350041c442551085082e954203051741d13a4a29143c0e441614003500805450000003034a501c9240000e007210151000382905450301a001401a48003030714160f5403801710044085080b41c580710303201d0b405100341e807015681d41c514138015000811a6000105040c8144500c1c1c1c082a00054595005040040300c0001500c550b40300942602c441a03c529980c07180080590800440000650040384240c0b1034035805583c174010040c01d44074902036080160040110145140f0408210f07401c04a5035000301c03010301d44e8180e00400b10182d2034440c0b410f181e46541e01d0303850351451807160166010058030203000c624150b4445058500c2500707402030908003801515410309102c0c12010000c0c030303841802e0350980480c26815424004003007a00b43e4a070f005050300082c54040188014598240d0090b40904055244080042100005007144864081c0c40308501e40c2500c180b0701c95120030103030340b101580307086407100b880121000117000f0790f60102a = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 315189163 1250 315187913 315187933
    0x121c03151206090c090903090e16051209150406050a0b060a02120f12040507080d0c0b012106060801060e090c0d020d060902031b030105072c01020708120a0908 70
    0x1200407480180d030b000707400412080d200b4a000c0c840000203034003c1280714685100070301090f6122241c0707000ca4a01841c1d40445460b8a40d40d49001c2da0302e800404042041004140c40a011061b042c40e80068514180ca003410b50341ca2628105200c22a03007205c149594400304a00c1911030311441200a500b03883c0c450074203c12807000303541c8080300800c20003141804107065085140071401c17503102c4008513000035103500301885d1055840aa40c02904202d001d481e49902c4154800d4559501305030b000034441c04c1e140d02c0c0281008502e10000d04402c41484262841c801280f0240500c80003061044000602d40e0726090001640e400040d0070003cdd03580000585445680d00c80700c103071000c10f40403502d0482c90015403801500030036440e00001d4040c002d24882c1c080da011074448070303111010190020f1100e5501d010003207594404000d000f400841030a54240030514210004110042040c01154007040d11045040c1c6040c4851412003c100c02c000f845c9016a503002d0f007000b000708a92401010745c608 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 315190413 1250 315189163 315189179
    0x1020d29010e041a060a0f08130b04111f090f0503032706070519110103150b030603010b0316030c05090405030a080a020d1517070f03080306121c0315 66
    0x1468000c01e0321070b0f51507a401e80c440d01c150b130398542d03043d400040c4441c0e6034081c0440054080b5400740f20160204008a0015024070740345002c90010355440801e02100e80e41d10754640c0c40320040d0100841d0840d440e8112007621050381d6070b00b00c520306101e8039450003da19000b42c07070350008c00700d4111f140070380c0050103100c0803140106d0450710002c02141c01d80703003518a081c001c90f445014000c0c000c2c2c55031191182219001c8100081c00d82110300822081403c00c4101006400b9290114001d040101c04c2e01d508004603180d100286801080c018000b0130903400354800a440c1880205c42d58401e07140310703581002000301a001c4c503001040f0644904400e45013980b20b854880c081d02007040305106807040021002e03045641102d09549485000f04030800800302d03c1d0710300d4070b118082d1014070528150b0079080a000000d14000b1580d04140c1c55071413600719601c01c025900041c1c0602c6d0404481443c52010700c00078000f050041030028406681d5854802c00102603404280c1c526030750010840c0d0901c070640b = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 315191663 1250 315190413 315190427
    0x20c0114010e16020c060d150308040603060f0b121b220806040506040b070c021002010c111b01050f070203372a17030406030b04050705030121020301020d2901 70
    0x40d60491b00c1503210151113a54070040c040c400d0100c0e041c03800c2441c010041024101c060020ba46480d074080020a844040900540c1628061402d0800707080c030030f04c0d0342e00e05500c0d03030700e43d001500e8807140585000c91958000c0036003080102409415041e404081201900c130b00302d500500c040710041c0b02e58103107a11101d440302009071000c0c110100d4440061106030040350103201181c1c0c090202d01090f540c9050003802011084a1000000d80300209040d980c1c200141d1044080800d036070f2a8905513042c401551247c1c010484036803013200501c5502d0140e0390900a043d20710000541a40701c03076501e903410041c111038011000d000000840d81c1040030072840c000c0110041c44956440c10402110382d05a000c402c030582c0642c03141c0c00b00480742d42c601e620100107801241c240e610f05000e210744c00f4041109448048490000080003400100003000c0c596207020000702d0106034441c04138210740c021900b6039002e1444200403944441d03404210036620401c442840488610702c0207044050000203241c0 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 315192913 1250 315191663 315191683
    0x3030b0a0614070f120e1c0321060b0a050307090605070803010504020a0516050106180e060703090206040f030605011802090a0603050c1213032c04020d020c0114010e1602 75
    0x203050204003942008403180d2002c41c0a600010b021a06428403000200170b01038100c000390040d440300004282c0c02c01500511100d05506449d940c03101c002d11070218941c0380d52444600d4003581c9a89000174804940350040517190b03119600c030340d070703920b44070740043d01040d52a84058200300c4104120317004101040142c0c0d054038021100540d807031040c0c8104807000c0c015021240c00d85900341001c00f041020542c011000c580c01005c007019600c283c039040308c048580800c9008020b81020300007924152295000c244218801000355043ca034a5116041406655400440c1c0c1640c0e1800140014501207411051010a090b4103501c0c1281d90302c040761000c4214840e220a0549450108001984003401c0c1c4541010307203070040350507140910090134401d88001c1c082c0c1c00300f8150b0856192213140701c40d410380c2c10084400524180c0c02c810003440001e60010200c00c120b1a801d00811090f00310a0080e001c0001d80241001400d50600ea001401102c010344461005180320f00504040c0d078011614190b0 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 315194163 1250 315192913 315192947
    0xf060a0f0b090103320106110703020f0307080d020d02010b0406210311030a0519030e060f06061306080405120a1d0310020f1803010b010c020d05070b031303030b0a06 73
    0x1261840b034010780142501040e600c07a50441101038800b020041c4180701402c8900710514610340c3da0700e41d01503405000544801c0010380000c0342c20f1004d420f1010542002a5010382203c10b1180d482c815541403444103d00f80c40107070010104010142d03824050030001c1401100d003004580c3c41e000e0004e008071018148140650484074611040c903029543c1240450002c0c0252a42e49a42c05801403e03548820302c00071840d02c01c0900d49501901c244120180c0b200204018011502d804003d040369150040030280d20500810054641c440102c25200060559443e803810300d05041ca00941405019a081d0034011801d00c80c42182c40d034005c0740455501d418051800030864501e01003030074410301614207003503140002580301001c3c070300ca001006207022820702100508501c0c8205400c2c1c0d020b40c2d4801d80050051161a0054078100002000ca98403840884844036901d61580d0402e4104645040401d070800e4840018503406008840e003c840841d42008902e051000140004100e1500906 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 315195413 1250 315194163 315194167
    0x60e011b06050a11040f03061103040f081b030a0e0306250c06060819020a09050103030806090a1404050f0f011b260103150b040504050c060307031805060f060a0f0b 72
    0x56545042c4c0c40030106000001c4c0e15550fa0f501d44c0003210100c145440119001440c11002e000290401402e503805560701071642140e10b5802e44408180750400034a00d240c0794640c1401c6040c5910400c020300c410080764640c0b1030f05a600904042c00c241000b0100c0d000910622241245454183d0108550b0100d50074003088204903410328070004d06451b04140003520503032000300000e10500082c40c41042c42143c030300711600d0702c45c0c091301e05541080c44004c02003907444d008680c4514005260a60181001c640020388100c0c890407018100000e58040c0c3d540d070440500c1c182c0c84c0006121441c001c6802400a00030110360750001003403c45003540a4080140082c6038541c980144a407888400303040016941c85943c403402c00740d0384454603400c0c500109281c0410b80b04241081c1c028548926000405010075240040030f02901303920050840d002c240c1c1e61042a01e9514103100d80c0094a80960000d11142c50b00c3d1454007000103000d443c440c400c00e81c0d89010000106c3c010420025254440d006a07 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 315196663 1250 315195413 315195421
    0x42030c131d0f0609010b0102150a05040f050303040b01050102060c090f1513090b030c0d030f110304050a140306060301200d0f02030a140705091e0307090c09060e011b0605 75
    0x956100c0505941d07072950301645100c1c0c070250800250281c003e240030002007118105040040e42d0b960380205c504403503446020700103a03180503558004c0d0f034414000c13011a140e01540c5e43c0c0e441d041d54030032281281c640c40c3d148014820365034100106603001c404041c0b11481c081c4d0700000600b14002410956200d441100451a0021104c400361100880c004403d0429103484410010260940d410410301900c140300c04c12505103040d903407640c07600e6019254001c45040c402c0c0110f40815001d64071440511040000054549407400041c00508038801d10b030a040e14004105070a081e00a80343c140b01e40e05003030004820720488a00d21071fa0300c1034081c0090385c2d0140c0c1070420024000700da8444c1850341c0f000c402c1246e0354080380c1003c0d10707030308441d00720a0040c4e40e001c0c000d4860340a2003100a8100d03100e40d49201c08064100c0050250510040c21920b18564405514007aa24074903980c100144880c40304100040c2c001c0f015008440090800c0901011498055081122441409006651110302003 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 315197913 1250 315196663 315196691
    0x91404110f040e01031110080601050c0a0b09160509010518040507030b04080a08091f0c05091905180106080c0304020f0a03060c090602011104090542030c13 69
    0x4034041c05100e400c00340c071180c0d500e0000056100901c41030300e01c000f02180c0004640b030b00c0d03020b200a04849032100d03050f94680314011078054000e1f441656440c030442550501160304102110320503d1180000e100b00e4086441d07005420300340354400c500411200005100c0c0f13540c1d00d1045e40303000d810044401c8655582c0e041c41032504010f984090807040a0105100a02c0005002061170201c4d9031161010f0f0f440d20514156543d5042c41c0645482c5515a00d04040b554030380c00a0a1484040c50b10030308000b14030000a091178200040914200e10000c1c080041d803c01c017018481c1081c180c40030308460341c500240984542001011480900c000000141c04c56031011400100c00b28050640d440c81d50b00d03403400400511034400450b0208108040009803503105005048200300d10182c2d0074100380c50121118050b02300a03007c0005040700c2055038400c0003142502450725520274042c01c595203d0703901080b4038040d4050344230703010340c2020001c0590b035102c4950f81100314940395000503402907400c40c0c0f = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 315199163 1250 315197913 315197917
    0xc370b0a1803081206010807230307030e030324120a08210f0702060a06060e090a060b18151611010e0402130302040e06010807060302030a0f0c0f02070609140411 71
    0x4001d00c500c0f8046180c4821514100c4498800d20013a241c4030501e8403030318825a4507240140c6105031803a0400c5600b402009003030081c6070401c50034100803d10f00e851400705401d64004449020802c807110007414045484440500980c0d5001c0c0e07a565200421030510320f4641610300b001801070040000c01d010350041100014103105100301c110704d20f5041c00c403141c039401d0318150b601400501c110303400314920b036030203206400032113503940c8400d04080501ea0a00035004001807510950b40d030349100004011003030b40004d203162595140c804107080c0c01d0500f003140e80b11012160614180c000d2003046080f8202c141c2102c0451303008042d40c80075041a2004840040368410800d801c50700220b050903e00d0f01d04620301d020b40780708443c02d0180280001c43d250391001c09218407480759201c1030040000d2402540110703084810018041446982c0700c03c000c00b03a4000201c103600054807849085030656041c0b183e20302520040c6006251245003c10b002c0c29480c03020f448a101d00e580c0e101110303400b030000302 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 315200413 1250 315199163 315199169
    0x170f0c1303030f0306150c060f0b04110c01060609050a050402221805010909030503040f030903021906080f270a140a0b1803031302030c370b0a18 64
    0xca0340000e9141d00d0010482d2440b16440c0020904012011400c5003a03845510401c56041e0f561814800003511002c025048446154896594803030151030380e602c0d41d0080b84500d0708d60145041d65002155212402c4030038590101007000260503090110355a235820010403600e00300c90250b211980c11441c0d41511040d05160700030501c0041001880322284070364000842d0102c0d8080007aaa6070750a020203644001d4002000140c0420008002552814640c02c3c218082c0c46c02c80840c2da141c0c1d020440ca414200b6103d80c2a07072500208100c0d807039004058660007000c090000301107080c01c102d03c070047d050510b001002000021328010514404008030a41a604075003864048510814002d454681200050354142004000980040e800c0e24202c9510004070b8020342c515a02c2c6020828804100304040703a142c01900d42410999130f505042400c00d8080044401c072989100c0b0030b90b41d04040b40307890400c14214488040000d00000000d0b100d20b00102e09181c0e080703038414120241d480e04a50 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 315201663 1250 315200413 315200437
    0x60106110f06100503010f020c0c09100905011823041403090a0b0a0201061d0604090804030503070606090e070b1206030304030f03121505030604030c0821100501170f0c 74
    0x42c040082404240b03100b84103c0b00107600030030008440d41711030401da20544015440b9940414082c0d28141090b900d981e52040c031760004803802544401c019410b984003a8000100c2ca81000800610501c9900c150950209000340094183e0801010164a06002031010b40131912600969a42c0402071003124002070005003805c08441c0c80e165048259000030252400562078070304040760100807242866012a940020380c1c280340c4d5a44104005004d142d1400c0390990744c14000000001e604002401202c0e1080c000802c10703508016250040b03a401400343d00d00f40e030001c2400c010074000641100d04551909030109007a076140c502080c690700c100c0d4802800a8032080601e4241548080e660b901602c131100b00380010b58584490307400740d910310300802da0300d40c204001160019018030100f000080c0f00304101410004000308000509980750210f0209405078001c00602c50810404500603203c24244040300c1c140d121000000c1c030701e0090440308401c5003c00481c588098480a9170b200315241 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 315202913 1250 315201663 315201673
    0x3180906080303090609010606020318061e030603060f150d06111b0c0603010303090504020d1d0708060f04030503061012110c0d090315090212030a09060f080702060106110f 76
    0x9112450b5482c0d2084816200a02404000c039641d43c02c180103401c1100d8896004505045004801d200310680141c1c880d80c1c469410052204400705003840b00b924042c01150150316460424149400d226004141c400380212040811070900120305445464510645224101e2101843e140c001041540c080448100b400300b00115119a10460b0345000d8070424284d4404001c40401c0c040d1030700083c0002004500c488006101c503041c02e502814109007489400708494048080c0300c40403c03054151404075422a24041c8010700040110759002034a104021181e17207040e4600034024000900640c2c8211400c581c50703c4068802e03c003821011610002c10040203040001c1c21003150300005540c007940c05400381190825005851000841e03800003a50003c480d9032088540003881424402c80c0e1000713901c8000a481c0d1b90420280a10081700e1f120088a07a08005001e054185288801002c214030042040081c40e804683c46046800c5030034144040700d003200000e8241030800505013a24494 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 315204163 1250 315202913 315202919
    0x30e012d1a0a031110031506030e01020d0501090f14041505280212090307030815031603050a0201020111031e04080c010c020a0b09010c05031b0c06090d1b0b0403180906 74
    0x80f644030080e80d14411603075454408441703030081d410313944581c42c0800e40070880c1204012060013500115561840718000514107072010100c64100ca8082c1c2108100c0d9503128003440b08a06a44113a0405c600b8007102c00300d551800780d85000304000e40324555645192203802045809100c1c1e610641421450b205100740800070741031040003500308404113903c101c03c0700c020525070303030022017119092a010f83c1e030300b01c40c2e59910200100003901440789039007601c19880c1043c642d0301e031102d004d00513500c104040d00038000d40740002801c0d540351620350045140c2c1042840700c20b2194407407641030705d8580e00c07400d05d5a68132400e1141d85802000007100c03240d400c01c8260141a680030070881c074580c0c80382d0b01d0305580c7c1e00c0f0350f0403140c02c17200b1300c00252010404c100b001c10101707829a2600a000664902c1c0c803843c204100610311300303142d000d45200000385d2200f48086003503a000080054401400c080c1120440000c2d2030305d8118500151020301400110341e24408810652201e00001d080141018000d843d5 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 315205413 1250 315204163 315204173
    0x803040b07031b11040b010c0503091002161e08060601020d0e010507080415030e030c1905070f0602070623160311010c0c03020c09040b0402060d1b030e012d1a0a03 72
    0x501d01302403d00c1607180403401d490b0381d0b015010603034002d41c0250055040921b10010300600c2400004040c0542c032945403004000180030f08454080d021100c06030496441d280c1e0740d440403a0b810b400802c019000780d4100902c07a68001030903985510700d46400c2c403150305078000503a11481015009041c2c000e0006001c205a080d0051200750070002d80d90421000c40e1584280e5200d00a803200300c04690451454164554000d241048049000c0c3c400e40d0b92007955410103401c002095482000580c002c003604120032a0030401011002d107200012190412100c20803191500c22014840c100d03454100086044c94881c0300320092004000c0020409480c00010160a84680460440041c89001c2100d01c550078442102030203242d010352140e100b80c9440d03080040580000c01a41d080c0d0780d8a0002c2d2074142c0c55103504962945194800103140128403032081d003501c2400f0091500c50400b4007840111860721090340300c650000b0000000c100e01507001003400ca4501843c86c0e54000310000010007801 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 315206663 1250 315205413 315205433
    0xf0c0507330c1101060b09120c09130b090309010504090e1938070e03190b040c1203120203090a020a140415060c02130609091b0902040803040b07031b 66
    0x403410788035900700303c40780d0003007a00382c03016406500c4001105000803212030402d001c0e9007855072108000d9419a510843c085003d03840121848040c01c5010281c070340c240681400c134580c00c1600c440155240086401c000b0b0716502c141c4c4034001c49199036940c4500d0102c4c060200c103a82c0d4410342c0100181e900702e41400d64801c205401842c0c00007000080030320340f922903681141e0040c0b07a0800b402000b03983d03020b0300751404e14a03003001d01d8140c028141b46240c2040810854850148640140342207800c0c603040070b41c58144150441d1000700310460302d4802294225000e203040d0301d8007800160b40c0703a84000f9030900b8209050402508480304200100311054004200d4280c04000d640802000e504403040d045803081910a00e000b1502d007400d2540542404100301c10200400034010036a26030751030b4008100c1e8103111040e20040079400381442d5015000e40c010004004070107013582400d00304201c041c0c60b0f11071407140494060f000110300c0105801102840c106554002c0d411981c800300d410018408 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 315207913 1250 315206663 315206681
    0x1404050d03052a0d0213080f060c0304030203070f0c0b04030309050306060609010903111f0320031501050d0e1207140102070b0403120b04020415030f0c050733 70
    0x100e8106000144040003608200403060b00462019070a100305074500074003680480305190084e502005808403040d41c1206680080144038010408400e88040b164140f80000d0003204203644104103000c003003030340041a600c0e00e0f40c104600d00c2100f2141d1070050020145540302c0c2c0e6030500301103000014140c02c4011803003200e005070240c030310300e5490303030204031051081400f100d000c42c240500c14804909114110000d84001501420200351105811303000000000c1c3e100b40065218051040003848101c1a00760300b6014034a02c908501340072155603854123002000754100072020030060301e0702c2407581140c0e44007030b01070040d40c48903841c1c00000750a0f0390204005440d1001d69904842c6004014400c80d02d00070303001000c0314415241c40d43c0c100d070840c0002402440131503c80c42c07485030594961000740000d01d001075107080880840301014043d5440d4101603405a0f180110410840c0e0308501285e001c0e41c1e100442540c014045040c0d1024801184007146901354142d03851045500184c0c03242001c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 315209163 1250 315207913 315207917
    0x1271d06010b0403030206010b0d06051302042102031009030210020a02070620030a0e040f050a021e1612050409050c04240f030e010f050a02120112050606010e041404050d 75
    0xc41c0e8a94980c1e20301841240320060050303000380c004104203010f49005d0485050068800324440c1c1d07503040041c1a000d0b10301440400e00340e000a040000101c05280010140e0b190203540b002602c0710380010303031201041c11100c2e0b885529240030307200305032080c400580b065003e100d00710340300c0245d0000296110005d0080b0f4000c5410f482c800758101c2054412500b0501100004510346021080e0884622102806254106481e9851000100414014140303d50a410070041c0c903034070382d0103483c0701c000071074005101500030030010001e20b03e07680d01018084540004607038080c0340300030408071000d22803540400b888a190034107018060082c80d000700215100900902000070301110f125501034000c96507040442d5044c0c5c240040240250080c0046c002040d0000a81000c81c011500c25254122407811080d80d0004044003c2c1b007020b20200c3c058014200882c0107131060342d8666550701d501900860511217480c64440130350340d03240c214200240d510101d081c0c460925240c2195518180002500 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 315210413 1250 315209163 315209173
    0x170706091a0c070c0329190c030e060f0408070f05010516050405090f060a0f0609081501060807051e0f190f050a08041502041e1a0301271d 61
    0x40c024650141c4140c203070031010a036440c0e85181d9420380f044031009800e48404000c4c0e828030399881904942c02c0e00c80e1490300c090303047c1c824028034108122800c07481c440303051601d4843c02402004000544c55440480781c4545480da403501c1c1030821560103410002008440b8040455040240c1908041e0107299600c504404521960005845900440c01555007000710400010700351241c1e5080c2e5074010b103015190940b07035611120744614060042d08054045050707107904200c0c81000f04040007188a4480b540f00d229418240c0c020300880c1c0c098044c8040000101d0082102080d142d901401d10162110300c03507450f807102e2444082030300b10b407018a09040030501c1182c0014065040d1a4200925941d0302d0f20b40383c40c1c040c040d24440c0c40a04107862543d0f0440e032000016003244000d002a11b807035000c1303140c0126070200381301e40200682c00c8041d1500b25540c0300310a02c05590180da066901400408040040c050041c0d58015900c080d003005032030402d0801c241c6102c8041d1040f0362318140d0004d61f0 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 315211663 1250 315210413 315210421
    0x507060e0118080a094703130b0606040605041221080708090a050c04090807020306070c0b0a150603020702060903070e06120a1e020d17030a0506030a0f170706091a 72
    0x680081201e20407a4407510940170104d107521440003e10250a00c581b002801d550342c2035016040d4000f241c201d04c0e414243c1a80209006d00c40c01d0782d40d8080c0b812902c092405080803001801c0703000700d1040050424200e80c2c81c10070070224140b00e4945544980e00c1140740010418006c1495070103499140118008801003400d005005c152000b2684d0880c0003080e002c600c038410f101c01040100000d0740e042c1e1042c000d40c40180c2d03041c0003181c040d101a40d218500100c1038204114540d0703005e029820440d26000980d00e00d6140310780740784103c0f811400c0c0140c94860341d00100e8410f204400340300354103000d2500c020502c1c0a0400009001e2502034440b01006030315103c0380c0e55680e00003075010b44981440d28401610040b00e0754090043e500c05041405e2112042c0c0e914662110749040082c1940400305c100402c4030140c0c8151640518100c0080840403961384401d41d140c0c034200400b92008480c0b440220079400201d007282c1825601000c00c108107403640c14a4600c0c10000301c0018440c1b11500081 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 315212913 1250 315211663 315211679
    0xa09020703020a0b15090a051b0403051f0f02030a0c0917071208090d030e0306070e0916030e03040f0906050102030a120903090e0a020a02060c03070507060e0118080a09 74
    0x14900c440d81c03640061601c074125445072803201100810038009903041101c04411a2901030f40c5074010302c2d245402080f01c1c1000c2047c000044c81d1350184c0c2e2510740e030a000c200b02050300010100729540d240c151150080724040001005450010100c0070114000800d205101c545a4021100201c0703a039220140d960702c0d40500003503045c1c40c0758051502e5100300c005018442040344a000039511804400e031a140955010a16584100d101030b0042400600c003100181000e100107540a0f400c1d141104075010302c03c002a12500000c0e00300b502406074a4007544103680039622050718048000100c035110343c0d03030704007100c0f50b0b6046010300d80041c0c0c01c0550004d800d500001c10340b00401110344130f03e00581c42418540c4000c180d0a070b025000c005080d9400101640d0036290980503c00310f182c007594514500c180030707103002006884a510220200104075410307a201054556040e0b0080c404101031003100c002a001d4400309944460000907980c000c400c10840c40c0003030000d840c0e00d8035560b103243c0c4e5840e44 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 315214163 1250 315212913 315212917
    0x603011407200102031b0306060d0e100e07060c030507151d120408030a1d0d1a060f012001060b030f0702060f0106050f0a0201021b01051e040c0e10080a0c050a0902 72
    0x6c0b042d40010700c030700d105490750090400b443e486800900520f0070482d1600c1004182d1313481c040703225984c0c0c200d0201852140c02c02d001c0ca48419030080010241146010801005550320003405420004081000300c10030140703980c103040d601444001031010107185440686c0316544041080b01741d00c640d40c6007182807038035801910708036408031010703500300501124142e0700c80ea031444100a402d03c401040c40c1076669003170101146a4081c01388079407003030360000101440490250400744103004a60030116141e030300c030a0741d0000d039040707080f9501d41c90079810215014245a1b001100c0c0c0318404420402d41207045040c07248102125802c42c0e1240e20340c003800340e81d588001e00403600024410800f0071541d801d40e0740140341c481c1303561000502e8445030f2480149110401000f4024a9455000b40403401c502e140624091042d84035140c10141000d58a000305240031744514140c44000e1400501d1030701c00c0c1e490100040410900740c0d41d0440b1907240015681e015030003828841c034405d00340480c141803d482 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 315215413 1250 315214163 315214171
    0x150f0614010306030c031101021f02030601030c0e030c060f0405060f0703022103011e1806050321070f0501090803040b0f010f03050d081005040f02090306011e0e060301140720010203 80
    0x41328507500b03095441e101f034000d80c0c50400e01d05501c1403a03841500f0b6002c26000c1840010000350040e101e0900300c0006054440300c6040508000c0c003a40280255a408201c2440b90402104c045944000d216081d034028010340d40701039404800810920785040000c00200b010710710950076207065820020042400c0740389101c0f07010501c101840113205000d07126401c00c2c0a00d030a902c80c0c129259944080760140444101c002c0080d68a8510801290901708106261181080a495145003119082c181c1c540100100039203429920161441030100a40c04107100d41d0f0400300503550380c40c2c03c1c109a8844039064800d54030700120700e0000680d504c20781e0b20b40c0c0c09503540580940400034071640304030340c036500140031000006d9400328002010b5880744038544120a5600300507840f100344104246c10040140c1c0a40101d07107845804992a405414045050781e8901e042010242c403602c020034010089060176214210305502800501034105681224071a0180003010100c40c40700042401d03400140c0b = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 315216663 1250 315215413 315215423
    0xb041107031b020f040504111003380402031e160e040507090803040909110609010221041a030f090d0503070c140a06152709150f061401030603 63
    0x40015140102e0408010140740020072820301c84038400e0024084078800d80301100c504800b28100a664101082801480801c070300307080200c01e0011000400c0e03000c80030700480ca1281d1882d039070103034448081e4100c0340484001e8800c549901c1d103600d40c207101034138140c06c01c100b8080340000110704020804124a4440c2c03242c0e242c5044059000078040503010140a038401d002500602050b048402c001920080c400c09801081ca034656040849145c20134020460060004020081c071590b0002400c2001d001b20804800402c100900d50520500494100241c44030060030030520720010040a18055401c445041d07595496a04a40e0b41c0c58040c1c582d4400850014000107554901644500b00000d008452220003030110008583c14141441c1e42201d803182d555084554040792100f0210190507060000d040c1151a80d40302c00701465240750301404642c95040040803c210381112240b241d04000c0e0500c11170307021041100150030203015100c060003100c1030811045d8400d000700e4040b243c001c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 315217913 1250 315216663 315216677
    0xe0a27020a0302041e0513050c0d0504110109050f0a0b1b1911010503040c0504180f0b0a0e06040b0a0b0402070f1a33030307080415020601050409030f08090c030304090b04110703 78
    0x28006001c09400010000274800d9130034000d000c2c151300a40501446684116071080d2004c0000c00090440f51298102074001c09488140e10310340d44a0030a290181d411100c0b50340c2d11a405500745440340f01c00d00b003040700c0b1401101d484022011031907401681d228841c4140c00021603c4000444203400100c1c1d010341040d4400c9420451810998040090b0300c10030038041d00018156120039086010740041242e240c0200c03010020070304414810041d030242c60401401542c00c0c103440c2c00c48008000b402210009588009404003981c50354112102180e2022680300702992034109005920380c00e020010f02d00380c01100207665940c07007000c00c040c0769800c4401e10b02201c034070044421643c1c25440c071058040c401009040c0100d0707041c0d00a8001010301100a44403403000b2113000f4205030703041e80818060350816021780300083c0c0200e922080020345241c00c2c461992900425032400d200c1903940b0740c040c0000280412103615540140100010648040c402009414040d440912407540050005030328 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 315219163 1250 315217913 315217939
    0x8090a0b12071101020f0406080109050a020301080a03111c0815011b0303020304060902120d030608010507050301031b0e01090f060b07080a080c0405031501090c0e0a27020a0302041e05 81
    0x4203a0804030680c3e5000060500d8906546400113501540186000c1615803004014003042c500850b54000c0041d007041d415940740401503655002c09200090501228408903041d0741c01c200411701c80303181203854034402143e5078030003c0c00c0c150081d0384c1105401c1074442d00d8482d5500a011810000d0801c06c202d407000345554408070000d410207401100c40b55158989003015a0365034030501c600d4680017000e40078903559018041c0884006900240c1c290b4100030401108030f411405503811650810f21002040000d003030800740e20008ac1d084003046080e10303000441c011011b03900403415103205003000c02a90743c54610106541c02180390042c1080010017184000b14401c0442503000111458100e040c1515000000c0c02d082941c2c203070700001e220420041103403010074000c5144100d10340c1000743e16602c0c4000890001c09290144016000c0180080701c079042c81c01c0d540142e01d11008400f1911801c02000090285d8480d218101d041800303008a540d01105261001c0308448000f400745080c880c0c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 315220413 1250 315219163 315219167
    0xc101401050d03030e030d1b0314060f0d05010504232b1110050403030b0105090a0308090d0204020301080a02010e061309050c07080c070e0901090503091c0f08090a0b1207 75
    0x414440c0c00c42c101501c896030100688800c01c00340c00b81085203c8023190218012410300a0320022003d4542090304040009280b41e00c0407034416005241650700054010348080820030129040703100130034542c0313400100000d00c240c0f81e00100116081001500011401044580d035407822410b44850720140300d9008840c03850640c00754840003156081a0a405050040e40c50524107107018200d207042e04c50007000101503040c030900003071740c0b024201241400004c2c130100c0c0050201e070000919858001410b05015582d15410242d41d9900500c1035650b1340c0c54850341501c3d20250482240403914601541c3c0052078440283c1d941c4000b180c0410b42d4403440c001c01040603040c081c20005428500f0030170708010070098001800060700e58001007004500d4424401c80b10313a002045141540d140641c88170015002004413183d81130101c818050290402c00c12004040c00d00c0700042009071101d0b048820403a0040c043c0c28502e0b800c031514010303d65651642030b890303c141d22112001031401d10000d84114 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 315221663 1250 315220413 315220429
    0x40f02150a1b0201030b10020d17041505040203031e1b0102032e0909030e030d18030206091207120501050603070f06050c0a0605010803040f0b0c1e01020d090303020c10140105 77
    0xf40145804203100c0c0546000c540300d41c1060305aa001a00500c50022207241c00100a15502134903084003055480c03c0d0b1a0b24903c00440d0300c0540d1505d44440c041401c1d0364041080e00e40800881c0106030a400b030040207100e0507400014107801070ba00c041c000d4119003606100b0340c0c1c460b00392010801040c000300c02600600030122600a40e882d48400d03030210b02c3d00c065100707500c4868801d407074034442d40da1450f04241c503002000880030100541600c1c270041ea00100d08041303084071390541c0c906031510307103400004031103100100341d2140b180b14800e00083c070500e80102041c841c0d4042c0000b002247c440105040d1540014081e5078946240b81d002040400d00c14001001c100980302e054610014142d1b80e102c0a880003070f03101c0a0250700c046400d0095502e110a440d00a02e441004585808442c01080b52200c9150030740b11050030318500740003c025400c0d0116511003500d503c04000400d00d52402500a420941c070300c000ca80306403400d0621021051141d010f01e003600102c0e0710b000760301c1c11040000700c0c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 315222913 1250 315221663 315221717
    0x40b1605030706051005120a02060f0c0a021206040c0609080c0904030e10091e080706030b030f060a2003070c1203090f14060f0c0307050d06030209040f02150a 70
    0x3a1104004250206506103d16030140c42e1001d81c04000d940350608004c002c00725200c400e85180c00c0205503100682d0b840c421600c0000c0030202950320307001a919094100141000040d4004d001054403007200200410a103118030706c500d074610343c450307244c1004070341c412203034082c074040c541c8590005e51030f51400d480860341c441c2c401c0c40d1501880c20b519000c80c200304a000681c07408690381c0e403018001240c1150a0307440b000d12003209514211700d40500203664a205101c0c0c502490341d2507a00311031070b4405010502e19031030007200716991801e007e04100010040045030342c0642e11110b1210741c8203000c40007200d0103028aa030f03901c40760842c00e8480c1e007160f001c0721000005141e92464900000303400342c07041c8600c02e409120700080151400d1800c0e0300b492401040c40c5540c4150608105681541c801507a07041005490000d031034020b04844d0f00000c0060380c00c040e5022440720300700410402503100e01d0400702c0c400d4405901c1c40d00a0620300320b0030f0084180074804280c209607420b0f94092984100c4c400 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 315224163 1250 315222913 315222923
    0x1060507080a232701030b1c0f05070b09040c0912030e0604080d05030910092004060f090e2503020f060f030c0a030c020601051c050c0a0b0702010207080102040b16 72
    0x3811041ca03003260951044803620491300b1488907542d903d20681d80b481181d82c000b8241884800100e00002d101c0c0101c041441107042070801c09407080c44140c2c41e4401840ba802012284030303907150104c1c0449900712031034080c404d6003000c640c140c07e903110700d02c40d03804c0b15009000302c01083c1403030382d06541000040900c1a00581c0901c03001a07511410040c0e07161030901138607010380e28285500100d00f00110324601c8040341e030070100c000300041c210760404000c0b844500f291000c18055503002901502881d030240311031071041c0402250024581d030011034806a40403c03101100c00c200d500b007004440c601c0c011503d00380c1e0500c08001509061400021522008104524210020055004940081d100320340d000b84040384842d04660148203101d42404240000c0c00150716060005207034240c022111010f200f26400050100f00041104000050005020144903516484840203c1d0020b0105a0061041290000d6082c0043c0300322410350b044202c140d45042100b014081921251442c1210 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 315225413 1250 315224163 315224207
    0x117010311030f120d140603031204060f1b020607080405060106050f0702092815090e03070210021011031003120504080a030302030a0e0c010f080a06030b0901020a0801060507080a 79
    0x9541d61090040d801c64410a044290316420f41e82220030407076106c1c072140e0700d240008034180101c80d07030f0000903101c1d20050042410300ca40c3e164503086025040c012051030388a404c3c101040585920105111091000f540c04c850890f59610307012125860181c8000c0e000c0d400a10044c0102c500c0b9030b000b040c1c6032034000799a6280032140d502140c0414003c03600090f200320008080d800d24007100050683c0940c41c40c005000207451180c1041d070035152403255001071a580c200386c2440900134411340300c416800400f00041040c1a800213911001c02009010b003481c03400e55081041c01230304054a0160f04100da035103c8503411b43c0e8818110026400700c6c4010b01105000002e074403501042129480c03842039901603143d0515059010681c1c00500360540144c10009030881e503640d025007010358107419440c092a068850f2640b50380240786a8102030900794901c4101300450340d0540041c060301920b991070a2090382d07a182d00312258024503c1c010320303070381007000b03582403442c482c0284205106010b00840 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 315226663 1250 315225413 315225433
    0x20703090e010b04331b0803101a0f180103060e09101503200409080d1b080c030a0b040f0e0102070506150303070602130f030609020a140d080d1d10050105011701031103 74
    0x1400ca400480303086505100c0e101c800e010120b1b900000f03864100c501d12b141c90401c12616103a0925004441180240400800b940d04c0540c1c46074010000030300000c030f444c400a082215500751103200031500440941d0600f0580c5140c0c1c00200004001c4030303040314038282291004048408070803c0146101d921a8548000300081503240000306908103e00c100000c040c1c182e00b41d02008080d84804002c03d0040e10740c00c200c00d450356501240d922000721a070008a40390401c00140041c1204200b044403249010310500071107805600a1151502801c111510745c3d075040341e640302540c0ba1590168054200784407071000501c280d0042d10380c88029a0040c024680c0780c000448805000303910035114592118003040640c2402032480010303120308003c0030300448004020030880007020394001c00402d40080e00c50000358407540010007949001d06005000390b51000307080da0710040c1c0b90840d4082841e1800000b515801038121044001c00010482000d070f00e1a1545101e81e0030b04c01c07905030180108010070b = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 315227913 1250 315226663 315226673
    0x5090613080a03110a03080609060d050f010c0e0904030c031d090c27091602120f1b0309010c0807030e03070303030f0606030506060d020703090e010b04331b 69
    0xd48040d101100007845a020541002080c1c011101d40002076904151010404650b20400c0c082d0b000780290f0b100e40e4507481d0b040100e640002c01100c0030740640580c12002050303240640100c02e4480c0143c0d03442498a080c40e0800c1040401518024003113050100c82400290045d001010042c0b9103104400c1c0400700c0074086400d010b401ca944040700500014004506802c080f410032034074003d040510016030096010940190000d045041115400ca000d2411244200003086803d80e0b100d08480c5c0300c0c1c0a446c01c0c0710103500a260904e6554200d481c84105000c0c00005551015030141d45040c0c0e184010745400c8130a6011a4080e010041110b0100407a074808200e100d004510070b46e40000e000b00d161012008403440f640012082508040034400190381d14001c1d81c0019420740c1005981b03003a585400d4868410700c0c1e01071000f194803400001102c02800c0d028108407000480c0004815418210f8640000c209181502500003c0010080310600c544001c4040001412a010340160b05071a5 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 315229163 1250 315227913 315227947
    0x3120d051b0a0906030e0109020102151306020d050105040606050a050a0c15180506130c0b180a08030901090e072f01020d0527030706020901020717300a050906 70
    0xa120105076a0307441001416410f1140020303808460000b000241102e07070000307403a074120290b51084cc2c0071034004a140d4080ea10108484558055011903680140d00c0316500500024400c60b44210b2402a00003071a900903001c0310b41a1a955907118038101482c001900c540c10000000d84480500324141d04c0b035030120340701b683c40e1600d441005140000390351030310505d0108010000c2c0307000b40c043e81440001401034500c0800717441c180c110080d00c45003281658617103000390181e0598803c14480d00002c4505010006201c5124281e0f14a2600381d200c0b441e95403100c0043e0b8407080084c04403801c0455440080e5421040d080d1142107a038218800c03141190b00ba6040480d0320507205a50340103100050340c903003007038452000f10308030a01000405d0550700c41d00d030b0042e8900600303d150001140500d50b8405d202180c00b810240c2c800021017448000b00d03544d104614011a12180041c3c1c1c1c0944c40c51110080d5140520707801c031007139403910180d20401c65040c1c110090040d0003800a2281201c00854015 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 315230413 1250 315229163 315229177
    0x30302090409231b01081905010303410706060e011805011706180a0b131a06030d1b02090a020703120506090604050718030c1403120d051b 61
    0x500216102450720380507159400381c0c0c0710f2942c1d544046041c1d004a1004884400d40b0130090030000a25a611111000c08843d09040031003003e18000000c4101134028000001c01140340c10a840c0f1410f51103044010326030580d444920060b1001464212981084024a0340720721032000450b0315581d44407101007004080c0c100d800c807100f8501594840d907410380b040a00601084070000110090000707a640c48100c041c1c085001507152001a40c0118030400c48900d031a68441c00d6600280340800c03003518082d600315811038218000030041e445a2051803c12409541e0003009458020030640c0262104c0e4094900305540000c1c042e40c10340540d5440d11280d2044101d088003595444492070000c0980d00f00c0c0c040031034114905401e10000351211051a40c2c030034410764001a19855504e410780798003c590705c140401180c914000300070001541254000c0354910070080403000d0010041503207403071400040955407071040c001c09034401801e03000a6003080410800c1c406d80001c9411300480741c0e02c442 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 315231663 1250 315230413 315230423
    0x80c07080106060f0201060b0906030c040b0c010c090611150a0e06090a1101020a0f080a0512040c080d14030a020a0c0206040f1e050f090a1e270b010b07030302090409 73
    0x94410050035400003200b40291340c2510003002041d090040c0a2058060544a280148404400240700c520490700b16400740c10200c00c21610f80305d501070602c0c0030305003201003c40080e854010008800f070046030920b281c015810b02401062101e2401e000e10010004e0420741800d451701c2d1087d204410a1000c58046c80140d005000000340c50704000202d00552440c2604551140542c0d1010403000c60a26401560141d0074541da0509071408072818002d10a03000386403032840c030510003080b43c0d02001c901203a000005032440803586910a4070b6005600c01000e14181007040050710140341c41c1d00901c1604114140f01c03e00c98940e402144458000760000c07040321030411014030410854500c80c1c41102d101c01c07080320144d400d1001144040784120130550103081c00c1310215600c03c6d051b400010312400d90910000c2d510b104214a940908641d205014848046500040b490805207004d45c400607000300811519920341206091030358403071a4280d08040d828444000c907651280162403c5034020 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 315232913 1250 315231663 315231671
    0x60906060903020a080606011b030e06030106030f0509011a041d071502060901020906040e07031e0b21190f0c14040516140a0504030606030303020a02060f100e04080c070801 76
    0x600c140403481c802c4d0742120000341c3c4060200b2a00343ea002d01d03484d910007c1c1490100c040b100e1850241c0740e6000000145900803008000482e4241c0e05a10003650001600000c2c06641c440b00680c07422184c03072901e1424038851481000603541800d0f00900490322481c80164a4a480440d82508191103a04065800c1c002c4420142c2c0c1a0b81c10040c180c0c220280300000c515010750040040c1041c8540c1c4510700a1040c03030400104030314001e602c406103014034440d20000a810080c0150700500c24404024400e404c0548036083d41847c9007080034501d84484010001d16034103601880210700d19150407039003c1072030134651700028004070b45000200312101c00e041c0048110001c100c00d80358010202074a0301c060b50840007066a204c000c05283e048035064243d45e0baa284441251140709903040501121300b4894000101a419401400044a07a6095070600d884407007501400303540941e1300c24113240100205020030b0880c00c044580103449162000d2804451400c140d0401c0c2480d400b000c102e9640b = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 315234163 1250 315232913 315232919
    0x60e09071d0d080d05010603020a1106360f0304030c060e1003020a141207082503020f0d150305190510090303020f0c0303060a0b0304020d0b0405010609060609 70
    0xa2000d400286504050503400c0400310001480015000224442d044034452001030080c00800c6034604104080144880c1da1140070180195000200704030000b40c818114202e180d1000c981640900d401502440132056201601d00c20500c19048040344035001c0c90f0082c41c41c1a04009080840e080783c0050754480f0b1460034200e010840e15402a03040c061202201b441a580d403140400c1400b01d02c1c140141c036070b030481030102e03510400ea08070b901e003081c030004d0009502d080100d4028808d4009585101c01541c4408504003500248140c0c00c02c2068840a9020100e02030b0300540140598500941e050180024101c8255801800303030520089003110180240070040c050042a4116040c0f4580d1800059682603a114001c804daa170741a543e509003036040500c00c0c3c041ba80b00d03626100d0001e0f101c0c02290211901d1b0342c010368042d4450074004400062605582c016039110380c0c0c004008105210301038070ba4200c40c1400400803149950398280115603400180b04950180a8603075850600b282 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 315235413 1250 315234163 315234169
    0x30c1f0b090c0706092a031106130e0a020f030a0902150c07170f01020a020d0914011d1f050c060609010807060f1718100507020304061b020307060e 65
    0x25446403124000ca2401040200da4214482102d6009900c43d60009920300d60b41001c140c0403c3ea1400410910107052411005200985c0643c2c00c3e42e00603180d00d07040c101c5403401c000c82403051040024103808036032000c02000c52352001c4c00d98401401c40b80945042d6009449031101d074402c5a07800603041d990320446040d42400032013811078010f1808914504000e800a00c1d035120154400c0620203080000d515400540c1807040d01c00301c1400380f00030342d03c820b09488069281d14a1040500000324036000000720f041d41d1216204140c481a191210341d00741c8ad035500c1e4a00d4070309131900fa40080416003a4080181501002004101c055582540780c110215076a400c001e0041c061a115550384001403001542c0418160102c40d080d0070044002e059541e0191214408002e0718403004814504200c0104546401000d01c224858107035103000850040b220120b030429a14040180e20a1105000403409480c8544121580090300d0529021700d500181c540704140e04001c000614400040899003 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 315236663 1250 315235413 315235421
    0x60c321b0a1707050409060c08070512010605030c071a0109141e18010213050f010315090506010210090807140703030c112106101a03060f03030c1f 65
    0x80180d800c101400500380004062102a02980b5441220498010041c44041102c14003c0501810078402c005003070400400500050001c00003043c0482c00041c5824450b07011100559000403000c2403607400c01c04200c1b400d800041115914035801c105120108180890400c1c03040700c10002c401d0550f050084104c11b0b42e0500c0d0110032002c040358140f05c01c0f45407200c0003083e540d6001c84243d5282d9100102d150501d0382d101e644290070352000400c412020b83d440014400d43d40251790420b200b000c100011811114082c0300c40919030ba98207000d10844160780c0080f070700700b401441140e52601d43e6283e10030444501140c222145100001c3d11402c02c10110f504c591211144400b90807851f03d10784000d00b01900002000b49001d1100005c14241d40e40c005140d80c0900b1800707050000245a0910640d45407c10b80b80354141d2141e29200081c101841422202d02e00c201c1d400c11030a644455040c84952550a80002d50600040c00b01c804c1ca51810007020a48405924480030070710051000c0318111 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 315237913 1250 315236663 315236683
    0x4060c0c140d1112040b0304020a0308040b03060109210f0201120e0304080705010c020105030c0307090e0106080a0b030102092101060b0c100e0318060c07030510090c05090907060c32 80
    0xf9410980010003458134980a46044803441241c0c15643c0d87d47e440021400d04941d003009025090204000c51017603000c0c1c024502c03a1400f81c862022064407a00c3d900c5d45e00c032006c0e40984104c4200c00010703000946c90696404090710605001d002d00d1040080130040d119061048140780e40080b8040201d5001001040028074003824070100240d072540000f000d0b07200042400031041400000300d40001e04c1070144a00810640c414081e40707584601e0001c08411056440020f42c03800c06031b4402da2480d044c8200d4080480c014041000743d0b800b9000c6aa0042d080502001155030381d841c00207894551400a100c0034000c500900b035469007098056042301d0409208110b19401880885544448002c605100c0c010840d90561100b2345c4c64102e601d40100394000420303900600001941c0c52245801090070207102d2220300300c01c651240c080c4800003004444010042d8002c00d01017140c01d002d00c04000c0340901034054603104502006098240c0100300a0301040c24190003041600220103211009c80 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 315239163 1250 315237913 315237947
    0x901050907080c0c1f0c17010e01050d02060d0c170f01080318030c120601050406211121030403022d0f040605030106090605040b1002030304060c0c140d 67
    0x30034100500c0040005a004021441e075000001d460050110304100b0b0000600c15845141d10360f064114100005e0868100740c18041080ca200c19282c0f90350144800d8183c8042e140c200429038030340b10070452514100c81e03003660805800c100d000c1000415000d20704d4600181e8442414050255140180b5144020525000190350354014041c03a00b01100b1a4009003a0a030092850160880080d080205203807143e9808000c3d804846112030011582c14100c60080340c040221690754100444401c00c0424442504525801a20000342e4400b4100074135000c060321041c0885070485260104401d000d00f003940766840490304200314070b4229254840e02c0e00c10707060480310b4002a0754210454410524003449561031805010840d103c0e503101c00002d10380100280b00050707403019000000c1c080b900500b030046050035501c003000c5c28020801030840009500031407856032551140380080c00c5c4810803004104001d24440e0205448420620f00c081e004800341001030310b0140c000c1c008400d154140f031070f = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 315240413 1250 315239163 315239179
    0x40f020a0f1b030311040b0a1806030b0d080a23070501050601050c0d0f1806030516020c0604030b0a200a090e090a15020c070305070303020105090703021c020f130b090105 75
    0x111491001964482c5a00d402c1c04100484a4603050310315001e00c0d00720007812030002c10007101c4941e201031410b02d60000d0784040d44026407200c40480a03204c0c8102c18a800106000c07090000560aa0081c01d8021151400d540c071005220590750407044402002d0380410f84c0415044148002885041d07040039090a21500c2d00c03c4810348141c580302c44010000c10700c65581c450213211070040f50004035542914a5100040e911141d014009040c01e80e00e006821000388411166613000250719202c1e070200800c8207081900c1d541c1e8601040000401c06440e00d0340b0341d11600c08892800307580341c5401a0268082c0d4841c070310154010304040a640c00130108505900038001d4140011034180600b54100160441105460fa1824017a1050514400c064443d000c030020030f021000c80e0040540c0d01c241e000340116200c8845869403428103001c00b0750702400e41c00039007007070354904104181c003a0f102a1049041c1580e0000082165203004041e040341600d0f101c400340036242c0448028050101118054 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 315241663 1250 315240413 315240437
    0x9030503090c180604050403020a1203140c0a02030906131a0909060919090303090f05030301080f010c0e010309031101050c2a1b0307030b13170304050a170405040f020a0f 75
    0x81c03800c02c060213080c01240e551001c2400c5c1442442039480640d002100130080b8060060003c2c0203140358030320012004000408108a841c008044420000903a03000310b045c614004100a9103900540940c8108188820700140c90362a200120295444910400340c5880d050001d015103480d0052116119050500c204444001d14040c0e02c100c400c3c98440000e0005e0207440c090700148441080941542c81c00ca034203104201d000001141a030b181c0030305450203a40c41da40f00e1401c0e11580d201840c041044001e80c00030a5120ba03111010301d40c02468641c1d01c43d9010b2400342e007105d03029640e810202c4000640c3d0302c0280c00c0100c5200c0e04500784442e601c421040d2039003150300c0b00c0c091450300c0060044080007920300d6a08020460241d0b030030048680840c2017107a48070a0f45a208542255000c624110740c0c20619554419280303e0764000c00a0108501c5640d0b03505950395508600350545e0344240303c0891183c64030b00c900e00e810640c5000042e0307252405030740a0007000e900d540500410032580d50807 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 315242913 1250 315241663 315241699
    0x30a080c130317070b09010207020102161d06010c1506031b060c140a02090a020304050c1002031b030f041404112d070b2d0603030a0e120109030503090c 67
    0x8894011120191003d5000d50340045442403040c00b502051a00701440042ea0040d401401018400d80803078480f0800780070401c00340d40350391048840c0441b07280b602030f411800361410280d2000c03052400350803242c060f54802900c5800740ca100b0412640c1e5039801e0040041c10f5044c101320564403c0a81c02c0c8510b03081000308903400d103001c0200b80341c40e00301d18005000410454904581d07402044841c8510300180c041000350011101902d9504ca442c00c80001030902062250300c0b00c04a5020b14a86115000d045d0448050140d540645100c200650780014a04030003800c09455003000724510244c1c034904000c2075a43c50b54280c07450500401200c8209450708208110301e2403180d0030b000407855013192080880c01285c0c0003130315403030f0520b0800c817406100c580141c20501868044011591509909001c210390442e8641c2e0194000c1080c000382900030340006120030001000b0100000307143c0c001c1820344804207000c4000c1440402402070030071050081d400ea80b6026036820506466508803 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 315244163 1250 315242913 315242947
    0x108010519090807050105010b0d060902090112090f051c031505091f03122105010510110111160b010e040309050f24040f08030c2d06010305030a080c 66
    0x42003070309030761a41c900080001c218141c5190701d400800030440d82d0394030407400d0881d601900480152616060000c0b89102840c400c3d2281d082d03040c1d50707200b4403201100880c3c0040c10320500070f4485030f4003140c9081c001030301081071010700c01202e80f0303006600181110150070b81c1e42d501c40e0500c1a0340900400c0c42282c8076104d8031030744462619000740314a05840f00500203c121508090710800007030b40c0381b0103030540252422000c0c5103550041225400d290b0200320407140c2c00e006030f03079001100701d111050662054038880000c0d14003600000750a51810545040c0c1c0d4040803803005c040c65502c42444c10b0000050281d8010915005074581d82d1409540c0149000c90700c0c01001d21840386034050181c0d5849210086858030103109404003503d000d5021401c840d0018440d025a001d001000031542d140048169100650080d005003402420881c04090682c4000244050208284107036151844200800c80c000c60056014607a59042424000c018801c0140403210440c410811010b0740003030150 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 315245413 1250 315244163 315244201
    0x50903220305120306121b0a171b0a0906031208130c03080d06090c0c1506120f0218070306050a05180a0c02030c03040f080705090603030f0a051303061401080105 71
    0x1000c16580e580b0a40007803807404030001c2c030015500c01c407011f030180d08001400b4a0003901003110020385090b92440a03a034403072400c3c4402c05d229041450300309840d6200d41c1c00071955800040070a9071490319805030104079155644207450410581c00380c4481e2581046080d0340001540b048040c100c030b40c1741c0f0b5800c204107140c80010904100050803050b0802140d02c0034020341520340342401644c042410040a1384c080c62019510b18090040009061041340314410440b200d2400309150540e4a84490403c050220426a00f100e1300b030418039420440007400f14840c21446d1000503480342001c060084445040e004a07014403e07100c611224024504200c5a1281c403000003c034040d42612005c07800c5025070000c0d80300600c00820080344620844c030301c120903100d8420071036442075980d000304003603c00240c1d40103400d5001001141c001c03007135010040400d40c1203420000d10b040001c1807801d030308070ba441d441601c8032a5036450b04221901ca03810381900500030b0100030b120904004517001230602d1124 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 315246663 1250 315245413 315245443
    0x2090a0b010c030e0105190206040c081917070813180618023403081620160f030302060718050d050a0f0b060109060504152001050903220305 62
    0x8050344d1001d038498021034210740e00425100d4400030200e48040d44d1528292421503183c1b600d80c802080b5103100003540150103580004c02054018951030b110010416601c070003010031420010103000c216000d004100007100161034656951030201c0094004d286501d03445c0b0201e0800c0001c0144004030800c031419045107410060b541c0c0c0000f0720000003c0039030108050450041e883d40c02100300d0100002c00c64a00948410616541791603901602020b0800c490740840c0d14070031080d001602d80d9901d5072203944400b003203070414401c9004018090305540d00020600282500500426a05104058020743d15050288089540c0c91941c1110782c0e0a008050081031011068010702500708a40c2044580044414803400442d08003840b01074401c44444d0301060030035100054451251040354101c0340300c8007041113a43c0d444c0c5801c4a01c1040100d4100c08107040c81c89181b6100401c3c801c0500400707041c0d008543d07600c540c0710703120580d0015255400c2d541d4020360081010580208030541070103101c0c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 315247913 1250 315246663 315246677
    0x140105121627060324180803370908120a020406120903080f0a0b060705070501020111070b0a1815060306061403070b0f070507060e03070b0c2509021602090a0b010c03 73
    0x20000c0301c0003041c00b801891b44803241140c00b10144003104000b1030040780d03010b44041c903c101c41d000e24a846480081d480c04990124140c500984603144e1010401034400c4004d00c0c9080c0d06400b20485805040e40d1130555242c0c00201004580c2d0045950107040c102414140100d018a4130003400b40c50000b014841c003c1c8000c40000c0c003207034150740580d010540c02402240c131550f01d801d02c48e5503200320b401080e0140d0318040b20a01914003c209650801e030b4000c03c1c00c42950340d500b5481d00a0000850a501c48245025688c00040d100d0740d5500407414001c14000385a51031410300d603090711003961080a082480759500401e41d2008513401056401c1c00c5500c0d41e84448a003030a102ca4880d1b554081c00358000c82c2400305646900906441840200310304581c2e61035182c0c0000155403085089600659100c6803040845920041c00601140c43c518620904959524100b07001d9900100c41e010704030b014078050104501e88041026002071034010f003044040100d4001070402111220060188010 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 315249163 1250 315247913 315247973
    0xf0b0d1d01060b030f01060806090403180e0103030c06050601030c050a030905070317040603110a050a0c030e060d0c03111e030a0f09060e0f011401051216270603 71
    0x40c4036104400d802040020821281d076040d6072035554209a682c01000700b031140000445030310440560b4010303840180641c985480300d5406548003901ca000c005450f400c1000005604207200c2140303030086000f500e6140c01500305180450495400901c007138141490200f410b801c21343d00609035084200d00381000564106941800c41c40d100060380002c003408000d0405000380a0068050720490321652818007000b00300036100d410714021004801e0000d0414000000242d10802d402100c05000e400c0051b14214050301240c403591211205a10f100d886003081008107625214000e00450310060700c1d81802d040d444404061040c800119402d0384000c03012581400880e070001103005a8000e042080f01014078240c00681004c00811145004458031005a040b0600400e66862804103020800d682028200408900c0c407400c04a0079100760704a24013008004038420002e0309614a00b00c054038441e006425680c0e850024a4040b2814080108005215044403038001c2c0e60541100c030141d11 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 315250413 1250 315249163 315249191
    0x60f0617130209070c030219121d10112e0b12010f0608150405071527230d02150c0a0506010f0501051806030601110d0c2105040315021902160f0b0d 65
    0xd42c01601950001c0041034202f10a6000219420f18004540a85c0e03040b40e144150319060911002074190743e118040c00d80303480c103180b030f0784820b4a8201c001e20204100d00340113800d0b421600302c0c000900c00c40d0f0303030780b001484080030412181c40c9540301540c40003518646503840c1c541301c1e889480340c000d201c0003142041c401180220f10f002c1a259285910700300c04503003040040e4083c03095102d25135203030f1189501c4028803200241402c850407000ba01001c51040d8179400d00182d11489000c01a100e01c091156500c0710f81c00f40f000142c2e0714001d400808065041c035005000301581940010b040c85010420800d5500e4034034034040c0c02003001c030358490303c0f65142401070300d0750581e44040f45801d001e0413242c81c640b2a00301075010002401800b9140c1c044845602c030110300040c40d1300e554040f69080c081000040e001201c10590160940005420319490541c0401075a818000010140e00180038484140c60480c0d582d000510b0541c01c2c201001e80b51544500441c41075501c17841055456020010b4a10 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 315251663 1250 315250413 315250457
    0x2060f0703091d070f030c051e160f120c02011b050a08030a02121501020a02040f090215031602070e0103030c0309030b070f0201060f0617130209070c03021912 70
    0xc00055043d007501c0400302e01010b44002d003124910017080c940c03502c0030106413003445154034400e03841e00d0f201d1900d0111024091910110102d19442c07107401c011003109500549040c5407014032410a8141305c66142c60842d81040791030244200b080094418640940ea11810911030030101c0f003003030503640d42c550909070f04200020902030000c02e07000080c055440506d9005080e1714008003450000360710b58410000c0070483c41c0013254010303403058020300c0c05031038681d1001e003029146000009282c10240d002c10381c030f5041001e0317010440d040030080003041c02441c50403011604461000e00b046504184154603138220600001e410000c240a89104050060380ca54028503003206e400040e61800c81c000811201240c0c2c81280154208100021041e0322400b001e0156800381d2070b50300510801c0040c41314034400003486105841c140c000030102589401540d1801071605a503503041ca40d03900e080c06407130808120000c0c561800d15001c40c0022900d02507842c031740201c41d490300c4001c51624000c08242c1c8 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 315252913 1250 315251663 315251669
    0x10e03012c12030403050c160b030a11040f030309030b010e06030d031a030f0f07060c050c010c030c0b0702010b090c0307090303080a0e010e060412050f03010902130e130c08010902060f070309 84
    0xc0c02c0004180800d141e04080034029941c20101220480c200400b0780e420b18805500c10040458010300200f4514200c6402c8008a02d4001c42d8260805680d9100c603d5243c5983d4801d03404924141d00a1007413040c0085018050900c0b0b580707003c031500340003000c290740c0c400c08160b00b4100750ba0b1b002c4a400d0002000601900b0703420060803140108240c4807010b48403254a01e00c0b528601c00d080001a80e0740c01110102ca100e908000944001910040155904061410224100000000c1d200700141c3ca02e455175004541a60001886c03464110911080040244c809180d1410078810890021342c042c804005070b9500d0b04c2c00b031009031903038052240541628030103043c0301d500300019184c48000009866100304e002c1ca07141003400000b10010360301d0384202d4184c0c0c80060003c000501104400d500140003490080340062012552001e803840280d0054400390328415801010000f0311004210007005040c110000300300090007079001900c41c0c0309103d500c45076a240840c0e42e9080c1801500f1900007 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 315254163 1250 315252913 315252943
    0x9060403021806010e01030b030a060c090509070f02011d0a0327030602030a0b090708040308040f060c02060603010f051009090204060f17010f0c050403060e070906090209010e03012c 80
    0x200c68031420b160114204803a0b060029000c1904481c40b90320a020b10052004003030060701c103281c03054075030710007600000d500b12044c46940a0001240d448840c0c00511803c00c0d943c1c1c600c42900c1c0c2090003829180468164000c050085ca070001c0200c81c086010200c180d45400d02c80011141811090410215424103c954041551000050107003940066104184107403040042a48560420281101c281c40d080c002400c80c800290000c1e0148003aa0341041c065890b034140c281c403550340d020541344540c1c2d40000507000342051111a00382402503d2911108000900c80c0740b0b0480302c0e203800d01801d4400c1701c03050b0ba21a141c0368103540301d50b0301407030140c03200001070000540c030b40ca10200c204048802c9800c0940c81c209007480c01c48110700c542030044403959174540c5000c0c5581c44200240c12902c400141500440d0000070b00b16000b4400d00c3c00800b40e100c4056100e03100f110014005401ca41400c81c0a6414000350101c10f54041c0048800c020f0611008210060103c0c0034508d4200c0007031158103 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 315255413 1250 315254163 315254179
    0x180c03061302160201031d190302150112022706040c030608030f12010b1602040f02090a06121d0604060c090306050406061401110606210313080d090b0a03020906040302 74
    0x4881081d0180b010b044d000382c0b01071060100c41032400030008030143d20282d0540006101204100c0c0c0401c000d03003a140a0710440d5500c80140c102d04019410030303841801d00302d80d405100c00440c20204e81204584a840558100502d00c495140202c800c0c000c4c07403284140c1e5100d00d940c0b40035010390f1210b4041c281c14000c0300d44aa09076a8508103581c00003207014241c0c10000000107005400c00c0c00c4030850100c501d40c0d410516001c5c0e00b40000b03046a03001144c10740d50207004090b000d8588490b8800100080e942d66400c0700c07550240b100448041401c04003100d003086a011f0441a0002619504030354007000c0000c800102e00012200300049800082015080109110900c01140c0000040e200348200b0800f085d4200070042d00d4070b0000509020240e00824000380540c90000805440050903d81844072130380f0700c10004d0700f140d10103444039080d0003c02000b80701c0d040b010480398040781c001d418080d0285062800300e403c1405141d04074020160005510103542c6c960b28265070045502400c500 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 315256663 1250 315255413 315255427
    0x1e09050706020105090a1101030b040f1b110d02150a02070506070306050117090d0e0a05031e0118020303120901020d050c0a11010c050f1303080307020a0b06180c03061302 75
    0x56221000c41c410240150b0810020034240080030503507100300c95210300300c441d24075401801900030f0f000c1811080d52041c4d40e19a242401c682600600d03000355080014803500060143e809003da8244880c2000b140e8064000d410a4580014120305003140f040d003400d881e80d44110340c01010307100300074004000340902001d0111240d09504070340305070f8100740c03620080c16010083c50748030140c04440b01c40140c1c2c807414460004900911038009115000703402620441c0c0c036100840d00c0d00c0394088581070b000c0c03000d90140c50208420b10a1050301001c2421040742ea50031600065524000d03d03c2d114418007809000c05c0780071009504072045042420820311851900f00703080c0301260405440e2401080403450352075028035041c803a940d04420b003a03c40d6400d101001050810b25004030180d140c13941c18150001c40401c5585010b18401c1d05c40e90700501c040d19a5240580c075007017015100f280102d03202162a10342c0c0c200b604841c0e038450a900c1c801510395031100d0001341d19a282c07052400d000d0348001884 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 315257913 1250 315256663 315256673
    0x40306021806160b09160618080318041112040210020a171c05060604120303060b0f070c0f0303080c0904180302060a060519090c14041202040e0102070b07031e09 71
    0x3d0110340600b009030510b0b035a980750b141c2c1340d0481900c500c42c80b031440b4000303228007401902840520201c0a81c10421652030b198268919407201c01c0c01d00f07045403800301450791460a800b07040cc0a03040c021348142041000c01c4411000303e006400203200c0d40c0720b03401003000c003072003000100c2515420054480b00a14104109005540410b03402e458001c00407414051034000e50044a004035030261885103018644480145100050401103007050b495510024816045c10080c0085101001e80d45540350741c54a402c0d51008031030ba00c031001c04110540108003194001d42c015601500f0441d42d1030b50b414a1400040040c411303501c1e400b078004a0110103200f4141e00243d440d00c501c3c401c4100300301c1161034104001e844036811680410b0b482c0c00b140c0c20311002e003640d0010444480c581c01e142c0c4545580c466040401d40040c0c1000d15040c1a01044806500c1d00b4082d4400ca40c5a090003189400855250390070580c02c000d0610060503111b20b003550064103c041e620300d280703070000810400b41c6128500 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 315259163 1250 315257913 315257947
    0xc191e1406040803191a0918060906010603150803091c05010c021510030b0a020a1701090209090a0903081b0f0a02031206010206130303050a1d060702100b06040306021806 75
    0x480c45ca0201c03403607403420f841040d51003a406010141c0c07103d11a00c0c000f400c100300c80404000c1c08075a0180e1103900d988134000381001054000d0b250782014200350341c1403500050031240c5503e0f080004010030302082050b0900482292406041501c000c041164040692284140c580c0d0000b0320079880c0c101005142c59001c00c13641040d0b00380301c0400342c09444405c001446039200b80000b0344014818008582c4462490340200038400460400000480e4003050880d841c0b0002da02289038603800054203100c074503200050585c030042c00c0000704001982d0b507c004008001c003c04103200303c401044000410074101d030a07141034160070480a83e84050112009440f9080508800300d5907940c00082081c030760010030f500340306801c0108000800400307514103d000c0e040150408140c180d494040f041c01e82281500c100e66008040e00030034080c140014028600822041e25004103480c0040d010070503a00d0004550072650460350141e150420001c2c101d50b10050456481e078003950001d0581052010081 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 315260413 1250 315259163 315259171
    0xa1503050f0a05090d0302070c0503070b07050d03020a050901050c01140112020f1e0105030703090b0106031a010c020a061103040504090b040209011a0901081312050c191e1406040803 80
    0xc65040ca40710900e18606507641904c14100a4220540d2244950b100c0d5010303000e014080c000114500e80e907000841d044c071070550001c01803031200046040a0000401c4110500222480d04501c2c140e17501d48001d240d4052000b000d03040060000ea50910b00c842504201145d40b41d0f82c130b109200d0b50395401c42c140d003600e0360312041340030300c010706903090301c2d40f912650b484880d85d604904516a040301c10011507a5500041c0b501c000c0c141c0d40c00c520b0300401d01c00542d26010b031180361800150611203103109c5401880480e400c1c0e04001c400406500140c0303072069004115001401c00d4800c04100c0210b46056014a40282c0d801924100c07002007072059200003e8042d5000f0f42d800c18460342c8039451851400341c2403149016040d4104070b00c081030351054201c0d90b030102840c1c0b41201540015520014641103280000000a50105114180d208240100360103410a181e1b0b44e9000603803643c0c0d041400d007911000d604d0075811000c3c0103080c0011781d0321204001d00100140c40003850146403025150b0000e907 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 315261663 1250 315260413 315260431
    0x108070e06060304020d23010c090512070e071704120809061b0702011e110601050f03070b030702010b060d230f13050c13050402090906010b0d0b0a150305 68
    0x80006003440c5042480d90041e08007900c2289141e465030240a0042000b0000f19a038007202d54004c0020618a401c0c1d0300d00b041c1041c00482d104550310401001c12440d0341000c3d100d0001d801400e20380400000d8017004135402c48032600200d40d00d5550980b0104400c90b452170f06030741c1c05030403c0108030380c0c0d240507000c00007162980541c0e916200011543c490302103c0305e0b800702264040004034a204540540071162051419a03040700f0100d2000c0246a00950f80030081044900510306815003400390601400e01518800038900d400400240d0383d401e288928020003000102081c00b01d403003074000244404024209503910001e00080d00020000d0510410901ca0b0007441c0148600f00c0140440c090401c02e22092203070703250411800e02991140c1011601031040d00030521f00d079103407003564030605103642100090900d042c0c010300281c041d000305060702d6038104500600c41103a40700142c5280410303191002600f404400c4c0425084602d640080000c61500841e002c0d102e68550003092060b0340b06 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 315262913 1250 315261663 315261673
    0x50604111e09031609060e060d030e03010b100c021f020a06090c0e012402060c12100f080a06141608070203040e0a1a0d02010f0e0a05060a08071709060415020d0c03050108 75
    0xc3c3d54021460300288c1e8a940e110300040e401102291080c0b0101c0c1550700c0c002c000003105403001c400943d1113071a11900e040854201d41c102019458100700010181090841c80e401650060100a444c2d610740a802000d860b40d41c450301d07043c08006841c0002070201050820140d507101c14003081d4200911202e41141039401230b01d0301c52144081400da0058450486d1642030401e810405080e0311002013070780020691001c030002c2c6906a010058000706a030710081d01e811511420084141d1b2020192017584001035030912106100c20f0101c128078021600c2c000704070341c0300c081c2c0484c1507204030384c001481d0300c0581c028401028401e030302462800300e0041780c03000d00c002e482c1c040c0044100011000787c08500c52003642c4031814002e8441c002d03500c07c02032021009a80f950001f4584e41c11410b9000300040c0c0e518200060540c009039a00710b1180618103610352450f002c001503a135004020801404258801503000c2458280d030141c0ba024105004180580390216400070b0050000744a60441803003a = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 315264163 1250 315262913 315262919
    0x30614090a0f060203040813030c060908012307021504050c01030c0816030e01020d020c0708070b070804091d0f0a210806040e0c0d03080406050604111e0903160906 72
    0x210101c08603480480b69a000c44140c072084000e402c000c100356a030910401140074855400c801c214042c0d4440c1341d540701d1882c240b0800414844098100c1d450070b0b854550340070f02e000400d030001030400d0400d80e1950410f0342c0310a0304900744203041c9280d800321219403003888200000410502c8004400307a80401c0407860501045a01d40300540f6400b6001c034020460701183c5110307801c02c00b5030700b40c05000540381c1055840ea034822a0301c5a0b2070611660030210040c000c081d81400b4900081c403a818055080c98503d4660400c10321480c400c0801c5180d5a29034103108002c82c402090515a030f80c4141d810040b803814085840d050302c0c283c02c03141050880e1030503010440600e24500e4810b01980c541c4c00703070f80d20882400014401c0840440e03e6100320031043d100e503998112110040c0340719607070f480c84030304040c94000191000900740a01c41d40c2004003d0b182c04221a050b50f80e00c9114a505a607100030641c288000e500c29107450343e0300b5008030b800032044030110704280340c00c0b200071050400940d55 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 315265413 1250 315264163 315264181
    0x30a0c0c02011b03020f030708040e090a15180206180306070305072703050607230720151305090907060f11032a0c030c0f040f0e0106030614 62
    0x2080d0340000d001c12510541c00c034002102c081850b109620a0044424622980030070310b14540150008580c1d0710b00009043c00356200f64076070750b90850ba441004122103405981d0b482c1201e006601d03010744d000d0352707010040028042444600000f64000c2d0103950b503402100101c401c5101103101c0a8081e104070b1002c60311702c0d882807041e00d200314074503501ca000301c0447d0050407101908441d1840304050320f0f01030210200e10240110f0340121411384807409440c5020206206021808605920580d014480d0703002042118405031406880301c2004900143c0342030001d02720381c003103041e800034485010610080c0b0348031500c02101030311030071200c041c12582c401078016591446400396a00107040d0202c1d020700107001c0e031030208003100c020040e00d042c08038480050200307014003074032942030f41c0c03409982001010003400340903042103090b0068030b480720802011580e050101c5980700d0003035540c1c1a01c600c26080543c8501d5100b41c20740c0090001e65540d080800c0a4000800303404005a41400401d010351 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 315266663 1250 315265413 315265427
    0x10501140d1b1701180308060f01120c0302090a0b0307051b1603060b1507080904110d0e0106050f040e0d0f0212040320100c080f04090912031a09011226030a0c 70
    0x65041c0d1f140c00c2c0596a080a0100052200c2c079a80e041c0031118001000781e99481c00343da11900c1c01a50f005813902824020406116919030080e00805002c00074411201d9000d011203184241648607003011030306801501d80303007960100380310f24043d11003507000c802c00000b60014804484122201c0241240b14182810795200c7c0c07490091543d082000340d030f0300904254026695504002103a82c4c02c03e800c450103101500c0c016400b07000d0603596184284620b140413103080c407620130103450411101416051707050303490045030300140c01c3c0007044010842040c420403004800501f000601034607140d40e41b50086c2000550010300c152061902c4058103581414218202c6c1980b450762000030030080380d02c0744c1825500c041a45240e0180030400460824070b1406021b1a9501c61603441035030000303100c4001c04450403141d036002c41c2000161900020360ba00440c40741914002d4401c0003502d8030307914084048810815900a42d00b4a020b091140041c0e035030051031182902940a024240b41118225019 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 315267913 1250 315266663 315266711
    0xe06030f01081605030c1315080c0114090d030819090507050307061b08031f03080d0507030203060d02010e1f18090c08042604081e010501140d1b1701 66
    0x1540440c020100387c0c640050940c001c0241544001141c54450403040b5040507180c0100c00c203a8000c0c0784142c11035900000341226284446800f60421500000045910116840207002c00c0000c00100d0890060035001d420303408541c6100300200c200601d0030a031102c4184c400c103423190044400c0060201d00614201100d05c20a40e04c102d030740c98003070b580d020080d04041c0041c50209803002c1d4003502852441c44210103140900121500c91150b4190107003034039002001d4004150042c0709201160300d4884d490040301e07909080900d850343e02c200100381034004c6208160b40300c500c1d0034100d100c0301da00840c810502c516160109844a1307280c07886c0d00196800c4401d03c41c001020f035030000b00030900002008034035400c0290000f0b407841400d0003000340c40c3c016802052040d08151f40c8006c060000040048100340c090000780102e41c90700c40355456004412030900d018454217140082000305400180c03420b000c18010a51985840d60315080442e603c00d09000180d61070255880304034503201540381c0780 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 315269163 1250 315267913 315267919
    0x61104030c0b0a030605040c1101050619050d0201030f0f0606020d0c0804061d0a03030203041403070f03060209011e09090e01050f010b16080f03060a1715070e06030f01081605 77
    0x50525108000c0b50581c40821464200345e603030b42010030555a1801a07200030a1a5900c004110056907185401c4072070142030903200f9a6a810094440284180017400f155411a8a20b4900005000680107802415001c02107149481000c400140d0b1581c0b0000a4858603070864401d90711340740c400d4070010845240900907900920040000701d1246015441200150340741080031070702e11001c80c1d010400f0b60030440142e0004201030290082800d0075580051003200104201450191014011800d03400041c00c850740002c1c4140180c0d01031a100c029000d042208500b13407558182d401460740c90140100d90215041c40b40f850704448050185c68010701c0c103c13900c0c542c00e03481c0802c06140e9030301c00668450648070ba50100c00c00311305420003900340c0190303040606540b898403404101e0b940380c2c03d4000802907069031314030140412000a40d165295071030925800141c549541c103441c82910010f54641c0a42d00004214444000300c0c0305038100e8081c102103034403211945280003010000d5011b00c0350 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 315270413 1250 315269163 315269183
    0x90c030f0a020d020d02131a06041d07031e05010602010c0512150102100608060a0e06010605040e1b0c010f0b090c090603250c0516031e0c08010e0a06110403 69
    0x589454145802c81c1c5100516170b101d00c1c89690301084080c0104a07845841c03d81e00d0748001c454144240c054a802c031b800700c031000c0c03410b402c00035128a08114062606401409840060305041c002e50100e0410340102c900840c0624040c4400400303400240a580015400c16180c0c7d201c1038010400e56200c0384640c00203900c41e994509504050710158061941184101c03035201c036100040307205100207001e981000d48014a480c00005044d14070061400d0401e912a40042203d80d0740401902c081c0e8014503049030a0340c1760003009464a22805c0109a4000c0000801c0e8168000560007646c1100180740f0038043d0002c14010001c0d51042210108401601007008048600d001e800441d070150060210407281340b07040721441d401401d1100c0c4140801c4100700c002043c8441080843c0f0061112105c410030141103584001110710b0480c1420108447d4400312000c010742522040050b100701e60003004401c5204401a42d24a540c220542e0842e1411200c4480710005100703e4040d81e810841c009 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 315271663 1250 315270413 315270433
    0xc0b190c080405092509053f1c050711030105010e1602030c0d020a0b010b030c1b2401140409020d02010503060a0f0602070e06040b01020d0f020a080304050303090c030f 74
    0x201c0e41004080a0540b910b424049904003003d400180c1018210307690600c4090803c400d00008aa41c540355080822504e00345020901100c8802003d12050400520003450002034032031a0407201000800c027a084c1242d80440e240d1b1001c05025003500a900c40d82c0c2001501301410b007207880078010042498104400030b480b0305000d82085101e900d203441200d24140040030000d09005880041d140185c00c8000307114113000150307100b240034001c100b221900d0360a00506100462248800201c92120a00400b003006081442280305060200550241c44800c03148044108442400758000100c00c00e030101304203092074880d20301c509a014011b8112105503800568603a0401082a40d0040900a020800c95040c01e41d4100400c1650002c1203014201070582114001c002d050034040c0b440c01a03080b02981c0c1c0001c00d200c6c01056030601002c00d010561040b4240700d6100005403900e000001800104034000004520600303004041c0c1e000e04240600700b644605c400d031400106540017001803 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 315272913 1250 315271663 315271669
    0xa0f0302101a09150609030a06140c0a02210408010c09080708030405010c113c040e0d08040303020903011109090121060506060909041208060111030d020d090c0b190c080405 76
    0x50000c00c4c10040001d0f041c220700d00002460140e8407001202e0050300c48010700e546817a590305e80390708075140000440c01c0020052001750340e07410340e40c04100f014180c0c1e01600300c1407190208540203040c0d2078000340101801568003030054900340c4250b491074859440009800b480100554007502c5e016034030000320766102d8890140048000010641c01030040031640e14034554500380110b240c50020f40d250301d200c120704203410700c484a106054002c0c0d0a04c00165041103020900b140f440c3d84900b0030700b081d83ca036820220028020f40340100d0709076103081e2804c95541c100a003d0320141d9800c44120b28207a8880c60b0088003003200109034584181b5040d200c5001030502d80100d030780800007400340e60a0a10031400140c09c4030b0b003a24151407070507520200380c500503030090910b64000402e007800c0801ca644d40100c0d96480c40741c210010b441a40c045140c40300c1d0851f54005040d05c5400c40a0b10041c6610303202c08044507030150340203041e1721030003200030704015010b0403070340205540102d500e5040c54505424 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 315274163 1250 315272913 315272941
    0x150607140c1522090207030206180601030f06020c0f07081510120213090f03081f05210f0307140d09030510090602070b010b030907051e10020a0f0302101a09 69
    0x5108900800f40c03800700394850f040c806001c200f8040d50040c569814868140d4261100500c6c1401c071b40c2d041003005002041001544842095200f0001a0384150392040c060030500f00710803200f101c1c05011000036104400003150205044c14061004280e07e13041c220404065261055148a46101007807901503e000c85c0da5180c0340c0202080819600d05a544100051071540421000700e9102014451803100828402e448210300e45044a1903d080800040c0302c05140b012210401c940302150521b804410320005415000103012a41c450205161a442c0d007018031041c400030344100602c28a2240c85462804203da4000d400380400e030301180801805008810401d50300c4940811100b00083c50448429000340001c3c0d0390241c80e810840103a03400d0030903990142d0302c503d0801440031452507040c580441c103000e00b1a01c0100810202d1410b13410096076480c05801005042c01c428141a0041400c040ba003061002c108000c01642c858841c3d0f50b00c5101c545500100240300041c164042038403 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 315275413 1250 315274163 315274207
    0x5030c0d05011806050d0c091e06080303061813061d100902010219080418061503020309070f03080a030510050d08040503010b0901080303040b150607140c15 69
    0x95280c00544940c4109440c000e80c04400411094003041c01080700701d10850003d4076013119140b41d4040c5a4464000c415030300c3c0151004c00d03540d414100b031107400010b07000311202a2034605100c20743e6208000c0c1d1b101d40085034014012488400b0106a00c0c50b640d21301482402e602101d40708808041d1260001042c0c1e20303c400380f0381428510340700340c0300d1820440000042c91a00000c81d92014a10009081034402d40140701c980700b4141c4690002011903059a058a01c1e901030040307181071441c045409001d190b804401c41e8600b000030984507941c190015441899440102d07a209541e500400224034030303074440036044400501c81c81c00018400e80080350083c10f1154a11200b43c1c4130000100b00340010308003214640030005040026040a0040c1c5584943c12210704080e5071511100940340d03c00140000e01d84121134000a1400c14104016440f01c58003400081d12801c1600e00310040307000910780040544584042400342e403410700200d000040715800c8017410508081e00359050304c80101 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 315276663 1250 315275413 315275431
    0x10305121303020a17010609020c0a02150f040b03010e06030307030530130516051804060f020d050411031204090e0a122309100e010309050601030501052d0402010503 73
    0x700c000001d61380d49000724002d80050444804040400340c40d69003115801c1c0c0c0451007032401844801e00b2000045541ca0403e0780584000404400c00b002c2c005541c8a100113410f65080c01080100e400010040035505071048000100701c0d9407650810140c2c0ca0180100080020f00c0402070b185a24590f5050140c2d004285102d4001e000000203101c001c15804507840c0041c40c02c080080414403404100d860054104610300c656514140b10110300c00d011100001100c09429a010070704001d1160720128510380800b60854035082c4451409024140c1554181c814884040c1304000c40d02d800716805101a80d0344807000e282625111300100984014640107034540070345401100030607441c4140d0a41d002150343c5111424400b4160740007100100b88070b1006124052044d00500e0321107441d052a14002c1e428030701d030103491240048015100e2132900810358068403000100f08a4150000741c0103e0145640d002085c08503603541c2a580001c02c030303c83e000d505d40404603016502400007990880142 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 315277913 1250 315276663 315276697
    0x10f180902120d2d030c020f010903020a0c080c21070302060c030304021807210603061d070911042907050615040504111e13060f0e01030512 62
    0x80d00040c1503031800c02c0d882e9515400c825024020154000c0300f1110303400c140b0218001c410a05030414034000a003039984020315a4495420342c14900070042c2c840034001250007444000f1140c0ba0081d01c800f16000e045134030440445010400c0740c800304035001044009072084181c40500320303680810126148000090f4080c0003408805a101c20300140080d11607400103642d40e04041c414490300e580c88d03020061400c541e01091210140d03205105000c003050548289941070710983c080c0c002081fa1344c1c07004010340d16248910003e01d10640c00404280c0c116130544680d540e80307403d0001600d0703011604a2fa08002000305001d1712070f045801c2c6051a150365035445080c101100080d4140d0b0182000355159400541048401d01164045d05451507054400780030a007001e90302d507c0e240f5149080c0c00d00c103074070548500b039407c03c1d07440018044600c01000301045c581101007042c028903240c001c410b070300b0040d11004100100c0c010300c524122a0301100a1002c4101d40100002542080b9640100483c503 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 315279163 1250 315277913 315277931
    0x30406110c030a2001050c0706090c0e010306051807050a0b030408040e0c0d0605010215060f030c060a030e0c040204060516030e0a0e09010f09050c2e0206041a010f18 73
    0x4100040e100000042c4c94900c02e407a521410116140c03c2491a100a60704010402c0101421142610407c0da070203c0007103000c42c4075207420261980260000c010345176488000006020b01c80e00a580560049075103540c050012155903511083e2a01030590824041c3c80308015100011006650107401a90210304007600c481d03000c03080e10020f44080700b6020b0040303121b0344da20707035184100b0000f403400340010810041c2c0c1040c04100610700034002c9101c0c070104699002180c60034000f00e0100d90b4010015a540e141c0248082c006101c0703103071141c01034403481d40706c2140b0782002c1c400c030f409448007521441e04040d003040d24058480070508044040100c4014039a44648502c0b1038040a0200c040c10a0000d1800401c0c0d2802c4451401e1689440d5040012030808030b2404a05043c52450a84cc2c03080c0140e041c90048240464811803080c1e0340001400381180240c1c042505030003944181c020940c256000303903500b8007000c000e014110700001c03900c60401038072011f0404d40c89103034031201c408180700311 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 315280413 1250 315279163 315279187
    0x20603010b07261b03120613021e040602010e0303040812190f0f050703021305060d09021201050f011a1606090501050f0402010905030307200a0806010312120e0303040611 75
    0x4048010800b91040201d10307225a182c0144c0854890b103210002942040981d0407075168084010b40418025400700007074a42001c00c9404884040e031002e8500307080b400c4d03500700c506069480b900c90b040065192000038000368001104590040d50000c1040e814000f0b004175800050350090080e4021340d03050350203002e20034020b00544a041019070030020311441c1740f00d008019180010000801c1510401000c88813481c00b925102c26a030301076804030f80364400700711020001c21808201941c17200c00c98501c004801415044603125100c2c2d950751132aa0703680d400b119815010b170045000e180020a112009122015280010301070f8055000456a81c1040e11404e0844005503121341d00603400e03808001c103658000546c81c00511094000310b1501d402901c0ba032000c11000101c2d5207c0300d042000360221552591034000c050150030082d01c126503902d107041c2050264403102c400214402d55814002d0203254070402150040300c10195217143daa0380e0320207000700185421030140c50f01c18003200c500f0786 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 315281663 1250 315280413 315280463
    0x130f060c020a23011a130b031e010603020a05040c02060403030b03030403200a06020c0f13090c06120b09160c030c05071418010f060c111005090108060904020603010b07 74
    0x10048210001d4103d038030a0754600350352040b40c6280c02c0c03860102502a00761112510f407040d44d049900c0c0002d00c0c5401e0f00003e41422410304000401e41c070001c130740c07a25401046d07000c2000c40c0d20896054503080d03611410300055402007802140941c00c030000140119001e504035001d840402029245030544a41c2c2e060640014660f050b0601c05c10f0301003446036401c1c5006101e000d09680e000426003000d103100014600b80f00b41c10f0b100d005040c550f1f03603c610132905421461540358020000448117850320380080500543c801e04911080c100803a1040504102041501035a5805110b864040740c51b07030155003180e03503801c048040050801803940030480620042020b4406200d0413600c4502440420101058440e1030f001912000b10041280c0c28090040d0001c480c064181a520074505d1300b03116800081460143c0e4000100a020380f1055030300000421920100b40c884060030340396803042c0507007000203e034001c1d0088010001402102c0120b4040c11000e4032860a411807522911100304c1d40c2 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 315282913 1250 315281663 315281693
    0x3120207050915040b03120d020c0309120f0d0e030a060915050a0b01020f03033607080a020a0e09070932040302010516080601030b121501030605130f060c020a 70
    0x409040103e4895624281c051101000c1c0100c0041914078810405514188904a5465000daa00041d480e200b100c00b0f0041c1d8000310b00c002c0019050a004501a40d00e4482c40e4040040c640100071803c100e141c05103c00302c0405101030000d25083c0d81c20394130000140400c1900b502c01241e2184030f64407094172809454862000f4010120740505090000787c076041401c903640c04541c0003481002400380107007590100964581034403d01031200e0044110b80c02c280384480d800d590185003000f01b289100040c609000c1803007600c401150f142d8513501c001d00c0581c207507244595034115580800c0f03016182e8001d41040101d00035500c980c20310300c001040050a0030880f10034ac0190704410402459028071905074000084010001510b14014000b091540003e00741418181d031480c00c08802d803281403519a0251825007103030b9441424140308090660244001c559a900b040c0014a80030300034800788814076440b9404e2000c810003551603c0180c03144000c7e041c1140729603403801e00031540d03c1e1108614 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 315284163 1250 315282913 315282931
    0x806010e060d15080309030307110a0308040b0306010f030608100f060f060e092203050703020102040e0f1501050a020c15090a061701050a050a030303050403140d02041e03080301031202070509 84
    0x40401e01042c03c400402a4800d100c660401d00c01b10030700e52804011113020f298802c145082001c4880d00184001d40c00c0e80010b04100c401007004541414948011030040100f602c84440c2c40c421040c0440c142d80040c059500682c0001100c4000016280c02a075003008800c0c80118005440c0e100003031000040340e200000085180119010314240142c4c0290080d29480d5407110f1030741e034440c940b44104000f0310010108100001c003207042c14030039410756016051a00c40e5075a541001d5110b814502800d40d42c0002080e0365524015540d0301a4045800580090700604800340750700c0d041210106104030012a44001001a410039031340710b6180c100544126103607903036a6040b04011411510058100c5406402500d0080c0229030391500c00c0012281d0514020a82d55910315013103405001c0d00c0006842c1080215601c0c40400032500940240c810320810b06010140303564403210003201512025224060800041c00030131548405c05580041d01e00403204400c0c1c1d1007010400c00c82d0100c0d25107103 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 315285413 1250 315284163 315284171
    0x1c020d090b0a0e120f07050a0c0501020c09070e0d020a1e1e14060a0c06060e0601120b060406180806010608010504051812090f0603010e180604120806010e060d 70
    0x410803000160050b00100c60800c00c00c0003240207100e05039541962150102d41820105081280b200020b084035600d43e0b221040d90505002846d025a140e83d041c0242e038050300501d0b08110150610f114030a20070040c0d0b5441c0007200c4d24800c284a044928000241d0304951001e81c04519040083d100c50004400c01640300304881ca82040c8101c0c0003a190012018100002003c200c1a800303640c034256900001c80e1080ea0321441d21800baa01d14805610041181d0b082401c0001c0710280031208a01c00c600c00e886500700c02542c00c95840440390304c0d07904660302203400d1100b408424441c0c51805492145092000e20541c1c4441025107080826030080b800921414014002800c1901a26401020b80007804450405082901d038031405119281e61640c0000b20f03071342c05540d4402c40404801a030142c0056681d5031594200b1007114811503031038010b00c1c20740b402c01e2030464001074090b11458104045101032582803000320313401000641401c1c1000780408601c55207946000040441c0115030034001 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 315286663 1250 315285413 315285431
    0x60c02100e0d0b0c0d1d121305040c12050703060f0b16080c0c0a05040b0d0308092802030610050102030406110705090a150605210a1d060106031515051c020d 69
    0x42c0560704909040f1401619021a1601040c40080c050151b005011500c94491108080300110208c1d640c2c0190f6202d400c181c0b10a40142c2c03c1a080c4204070b42a1074280001d80d500710080e0f007501c040d0300c00c682005080070f008000c0082000060514032034140383d43d940d52140ca4403130101903007003018009100d42020b0640e4006181c00346040005100607101030003140e1b14200040c01c04001400301400307001d102c6000501d04282032015103191202140a0b8030781d00c1c411111824900399590b4101d000b48940d2001c180e242088d1000c030011030388140e00952415042500448135050010807082e00c030301c030340030000c6269a07130400d99a21503040070800041031042950140c12418155010500380038080101021520300342c440e0100c014400002c04030583c8031490420000c00311036038401044202c00400200254000c68000c2c100c4506540038800b051010040b050041c085c0e00c110720441691804000109001d2006008061030701542d0500513000001c26109a078025403031702d40b640359140555 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 315287769 1106 315286663 315286687
    0xe16090e130c080f03090f03032503120606080921030a090f021e1f080703050621031b0303060a09020c16080313060c02100e0d0b0c 58
    0x4c90302c4441902ca1152030350031980d9030354866561021840c49602c1e00005503a140c00000c01003096a041c1c2008035002c0325007035401203082c8400341e040700300c0d0f060145c440c0c0f00c01003e807603c1c0c8443da4500803240a080001d0340d1800c6070040844103210b01c81d4855682625489940580e0004e8032a009040c803541c000751140000394062105000383d01d84404080da070b1080740300c00707641c41c00d14664001c150b1441e1a181c640c4040024001d000000d4404e4401c0d040360342c201c0340c0a0040847c1041900301c00c21040b0340405480d440303500006094904005001c0e85105015000c00518190304001e00007440292242c41007418a64011a40701e103417480030f0006102c080f48110359001e05507550101031740ca0b034003c1000c840080c61801c000041250003800c3d220300341c1c3e03401031096100d141c1440040d20310340e0210030314a4028a49000b00c000007401d64260b10b002d00883e151072900c46c000142c40c = true := by decide +kernel

theorem cover : BRFrame.Cov 315107913 315287769 := by
  have h0 := BRFrame.cov_init 315107913
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315107913 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315107913 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315107913 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315107913 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315107913 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315107913 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315107913 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315107913 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315107913 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315107913 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315107913 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315107913 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315107913 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315107913 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315107913 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315107913 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315107913 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315107913 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315107913 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315107913 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315107913 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315107913 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315107913 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315107913 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315107913 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315107913 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315107913 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315107913 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315107913 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315107913 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315107913 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315107913 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315107913 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315107913 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315107913 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315107913 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315107913 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315107913 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315107913 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315107913 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315107913 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315107913 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315107913 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315107913 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315107913 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315107913 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315107913 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315107913 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315107913 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315107913 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315107913 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315107913 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315107913 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315107913 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315107913 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315107913 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315107913 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315107913 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315107913 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315107913 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315107913 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315107913 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315107913 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315107913 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315107913 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315107913 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315107913 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315107913 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315107913 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315107913 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315107913 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315107913 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315107913 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315107913 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315107913 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315107913 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315107913 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315107913 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315107913 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315107913 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315107913 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315107913 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315107913 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315107913 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315107913 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315107913 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315107913 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315107913 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315107913 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315107913 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315107913 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315107913 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315107913 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315107913 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315107913 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315107913 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315107913 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315107913 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315107913 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315107913 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315107913 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315107913 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315107913 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315107913 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315107913 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315107913 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315107913 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315107913 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315107913 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315107913 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315107913 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315107913 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315107913 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315107913 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315107913 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315107913 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315107913 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315107913 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315107913 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315107913 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315107913 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315107913 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315107913 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315107913 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315107913 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315107913 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315107913 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315107913 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315107913 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315107913 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315107913 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315107913 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315107913 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315107913 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315107913 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315107913 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315107913 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315107913 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315107913 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315107913 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315107913 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315107913 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315107913 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315107913 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 315107913 ≤ n) (h2 : n < 315287769) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
