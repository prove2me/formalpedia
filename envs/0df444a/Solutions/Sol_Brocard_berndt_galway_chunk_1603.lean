-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1603
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T03:48:38.550389+00:00
-- url     : https://prove2.me/submissions/6abaa485-d514-4a27-9871-5086d68fb583

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 288129496 ≤ n < 288309352 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 288130746 1250 288129496 288129539
    0x21201150e0a0c020c0315071803030201061814061003110c03210c180f1305040b071701030807020d0c06090602240720100504020a050402121302030106 67
    0x208020010503a0b4030b441071880d00e0140c1d01c054001700c0349900c002641ca012101c3c5203940322031f100b0081540300e80150070304102e1828401c1a20142581ea00f00a4020801b03071041e01c1000c50714080248078003000740b2510b91761407030b0820ba4550544910040c8400d1445e407406e100b044c0750b41c035000c4440c14404000605000a034240c0195a1907440010101c030b6034242408040600c240354085c0100500100140c86805210902d01014694000001454422040b44003500030a029800d140300f140a07400141c407c82c051540e10485444000c011104901c541da11404a5540b210040c0000b03041400217040702c500043c6907400c0c0c10ba5640f2002451031003a44204041a4010780400c503281d01400ba01e241040c1c883c11031920707010f1241d10480c2250004200c60704000300760305c6141410030031285140c1102c1e1510102c445881c10306c0310040040ca01600c00707070311071541c50200103a5843d00740201ca100c20420503012040d0340310407000920443d55500b040b80d05540b00c520115201c8008907101c0c001c1180b = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 288131996 1250 288130746 288130769
    0x3090201090902040b0c1011160f0c030f05010e030406091202040b0429040207020a030b190501080106170a08270301050703020409050601031b0f1e1e0302090d02120115 74
    0x4070b61ba42442d0215080801035418100700843d22126500026142d004142030300c242c010403c0741c6030140c8550785d080002040130703c04980c088180800c030b00f40b440c0401c2c0700310020401405482c404950302d000c1c510400b070010388008014400403c10068500400e48080d0000c1000e14240d400602a03600e10f4803450004040005900341c00c002200b880d0014640640e021071500c0c41503000318481e020701340406042c0740d490001207034001d20440b44541003280343c203c00700a40e50b102e08820780a44414440c0c0030665081900c000d6840201046581c2200d5201c8034035441c08030105a9001143e51002d40d00f040920210f046c4007142d01c0c2030050070700c6154241d0700160386500b0701080c0022150301600003810035181813900704114100202c15101c41c3c5403800c1410102c1144001240e4400100c2c411040c120992102401665000349a80c1c0140420f00003c00c1560001d00c0c00700c040307001c0e44e030500740d02601d400710000c090b052503004103080c0300176a0300100b9280010b445c0104034004980c8215960f07034 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 288133246 1250 288131996 288132007
    0xd020f0702030709020f0f07240e07060509030d0e150403060504200d0308061203041409010e0405030906070c050d0b071115060603180703080904050109021903090201090902040b 78
    0x10b01840450054603903442e0450a00c04004402c6030305000d511081000d00f0b0000902c90103020030001c5a41c0025000e81c0301550f808180380c0803902800c2e40400698807403154200c04141c080c0280300f940d1500310060028443c034900b0541c11514018410040c68002684080041c0b800355040020000303507015030004140350500d840c0000502a9081e040780c1714541280c60350080c0c0d5200c00744481507d40510341080c190f200c40e07000403504140312910440601c00002c0c000b501b80e19581520300c4241c0101e442c042182c1ea40c05601700c0803402154000c01c15003040103c2c034010f2400741c0142400d9806810983e0100d9140c501040307113404440301c240c40d0600d00404128000341c0c04a50000718619280c0907004c4507901e60003a5080a6020340b10901c1070b000800045c4079049054200d030303004030702002290000359a9080c400309542c4a0368015014030300346030001c070b1012810300840da901444491180c0b240445003008800800441604074104204824000340f000c002d40090000303010301c104070b2580c3e01c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 288134496 1250 288133246 288133249
    0xf081207020103061805100e0408090f03010b0a08010510062d092612040f05090a020904090c060e0d0201080718030501020f1c05070f1803050d08040b060f0a0909080d020f0702 77
    0x2c455003d4144290001c0409c800200c5007019655900d000f42c1e546601f82d0103440009000d0506c0c907407402e41219a1040c00244076505400c818040e068044172100384542b01d0000b10341c0a51603005a000c20302d5191030020f08000e014000030070818903403034541c9146d0f07182c601100503100d86210908c8280c1c0840f000a607121810b1180c03420000c40340702228582841c001c044450121188200c1d84100707280800144810840d40440e098070b50002c00c20010300a01d403400d0303005101d05014600c0002c464044440d214281a03d0308a0155016180d050081c0d84020045500711050900300041000380800000082c0090004d2300c458109215541d0700d808283c041c401001d10b500b001200f40f1403d00c01400302e15600401400407604445c5410100c9601031500890180443e41c8014402d1044022001c0d00c1a884040c00d0b014a20030070782240d42c2d0319500c04110b05544c18210381640a01900e0f000c0100034015400800e00301d1085120500780b06803036146000301e8026600c400d140d65400504681107 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 288135746 1250 288134496 288134521
    0x1c02180402011b0c0b0c010204031401051b040b0d0203061c03030e0c0301110a030504050a0b01080a020901090c0215071b0c050a060810140a03060c11070f081207020103061805 77
    0x3900a20902c3e0a6403e403151200140c0d030300b00e44220200d18000188000c0842001e404640c0a1600403102c24483c0c11030051150007000d04a4441e4040e1102d4a01400013102a10888040350120500707541004002400e040003076002400e0507601c1703003480a040c04500490740581c100f540c081d44000600b500800002800c05401065061190b45089843c0c40003012010035505505190b00d00002c5a5030385240c06450404801c42c05007048100a000040c0203500203500d000d824400d40300d9891503613131503640805403130f0703040b5100c809a00007035801d48041d4000304103141c0c41801303443c00b11044031041c85241d09000c220081070b60035500102d001d00240c206180d10400420f0f883c039050300343c0d00d4401000e0000c00030342e0040304103c1d2b40d0100300510b5a07030b810b29150702031608030400f000100d8010318044c10301c81503040121914002c00300001440011a210f8608030381043d8080d10048540b0060001c823503015143c200d0525644203008180c1505080c10560b0140154000186e2810243e040e44e24 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 288136996 1250 288135746 288135767
    0x3280903080a03020d1b090605070b1b0c031903060501030207261e07020909070503071502070b03011214010213030213061a070327061107050301052a0909061c0218040201 75
    0x242700d000c00c9103000103090f064090364040e0140c2031401c202c416002a482036445103c2c04507007244008142e464262002e803107954076102c519102000030550780c00c0194107034000c0306409444010f41215203400321040c20485020741000b0340d199450180c803101605481e0741140d04030481c07003101240403011030400002c010b400214000090405c6490840003950b925450b0241240a400b041244500117008002c410b01420304500116120340e1122400104180443c0b42590904034103100c3c2c800307000b0180f08480400d1051555061658210740a0240c0d041c0c0800310b1811071595a100000e03440041b02c580c46c09005481d010694800c118240100300007084030b408000c0096078021915080340c502c00c400304941140c2030241c411060000880d042003841e5001680650038041041b84422040310760721507003c03902004484c04c0c049110440c1d00341c0a0381e1031540c1c20240c2c0d10b01050451511100e088000d10307803080b8500d841c00103170b400315584410110300c0062951500080c4011582c10140070700 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 288138246 1250 288136996 288137009
    0x1061209020627240a020f032809151d03030d0c090b160b0a0b030a08040609080f060106030207141501140d0f260c03280903080a03020d1b09 62
    0x3808080b0f22810500040030261904d400040d002070320069450003481a0107130b06000c6015240c41c2c40d2404880d0001c101407940b44a8038821901901900300d000380064009e41c0c0c031007140d03540c0d042018101641c94030038140324100c0d01e1003003039110521030b075081008061480d40c99001250b64040f521014141c0303c0942c1100c83c601d00203204103520303007a11200d40701c20b107074000c50510304946030010003000501d40015165050b00941000b01d05008a450051040307628580d44c0600581d900c4181681b1464100c0d289030040e00100c0040243e1031003038014101c840d014242c03003504200c8a1503807e1804925051000d0640010f100400488818189070205984182c1700c071001e503030032aa11141400e900d440d009142c0e101440c90000420340d0b400d80074680b01c7c0720411082c3d031000a08412035898121000c4860307581e0f60007803055a500c968005212480d655511401c41903419591140c4403030f08031000b84010103500b484001e254000714002c50b03101441002c048051103003c450011f000310360540201 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 288139496 1250 288138246 288138259
    0x13091a1602060708181e120a081302190f05012a14070f060309060b03010902060a03021c02040902090f0f0612100b03070801140102060c0301061209020627 68
    0x20280c20341c020910992000041c03510390740d0b40d6030b4a00c01200441c44800e04034800c3c0304d01844c0444400d20031051131003009a64040300e04842011006c0035403449164400000254200003091a01446402807168244010321800d203030b01c208070600d420220310390b005100031184040100321650300b0451449212100003c000c1d000229a041c0780094078413610024000d032107010301d40d0040c090501c402d03005007035049a401c3c80d096403500700902400400b80e0a5603074030321f0301466100e40c0c5014440c81b0b550700c0e405490035041100b018000d50003908103029075108000c0254103c401c1c50310701d100420142031040001601d038107200c0c080c0501000300411035402080c0070302481d0200d50391007069807050030510702424240e0365900300d9080d8941e00e560140c070500c0804414032075503a070011465410394029445407110b601d901d40049036950816982d55071b0420003000188003c5200307990000e45028401070200e8203200704c0d40821265802a05140d10100122038400c40700c07503008140405010003114007 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 288140746 1250 288139496 288139531
    0x25080105070f05071502030106050409050a0b030a02120c040525020105060f0f0406030501111e0f070f032d0306081209010509010215010b13080109030c0201080613091a 74
    0x9410000702240d0b4505028001c1581c0c0d080020403e11485840040b81e425074595070b581d10302404980050194911030707810440020403070308540c03140305081d600090060134506095000d100b502c3d550154000300c0c0b40211f04038a0f2264680740585405429590500d022440824183c9555141000000c000310390411084c44640d99418461a00e01403040740c02192030000c0e0350010b801081103034801402c65003814128800c0717252401c06400c00210400c02c4007007407041100340510620400d112805031000601103040400c0403412604100d601c241030248a070740000107030001c203d4040d065a01e00000e49107002007560741c140100e400400f404001821b400091340c100340700c0c0e80506214581004804688800681c1c400c001020a802031400c5924055071260b001d01e0540e4400c44c151070f0006240880010113450520452003000d0705a1740b0105518803a40c0111071895020700030b030741d0000e0741e400e45072007000c402d11034403400b0791180c9194071b82da000d01c001d510b0303410070006c202d5681810000c2c1c5 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 288141996 1250 288140746 288140761
    0x3050105040b270a12050403150504170a050708090a0803120601180e0f1506190201051302130506060d0e0c040c090518091c0f03060b0c0c0d110325080105 68
    0x1004e429407580b1141102045040200840e038a0103143d1000c2c00c60201c1940c40740d0410115030010740158002d0008209404402455400b6440b560b401d5a0008108000390b01c08100030f10702400070200000c140b005015074505c96140355400a401d10b02c840c0d900c45080c08250341e08074000b41e1014083c03941140120f45000148102c0c1c90000b810b11001c420b98800046a443d41056500c4440100a0078640c50381d4400c28050313510394942d44410095841c28011403c2d03026601d4416030403550090591030041403081c00e03100507020240009400140602950741210202d009040d44900090300411102c2054030810041e1032843c11107c091140c0703a0400d001c01c2c1c41e10074003052090f0140d80b0211403038990012452078848880500841021841c0d140020958060026481000c1559090008c95100e0921801610401d0b503400b43c550701c464000082410310141010300103000b078654490101001011030300f0302e80c501c0c04200c21550134a8042081d00480aaa038001e040404002c001c140341866 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 288143246 1250 288141996 288142003
    0xc01020c010c110d030f11370c120506012102091b0a03090506070206010810110405090406020703080702030c0a0b06060d06030305090406080f0c010f050403050105040b27 75
    0x481807410081090249028031071101021000440003800c04120013003a418024442d1b10100c1d8050006090744500b00c01c018000108a20915802c61030000d07105400210340442c0c541040904807500000c40702040810f00300803a0a00503d500c1c03407014981110383c9442d030705201058021000044c0743d10a1403040b0b0100381c000000050b415504000c0d0703078503181c05024043c43d4014842d0485400000d0500d0071035416001260710768032071412240c0c2c40d03c5d00b0405a03215042401046603950225580e11103103485600510081048410307e49d20345900c41001c1190200221020303600540c000908104059202c0382459220096102960622242c850680d84808500d04003030300d03981c03204004c1802c9640e400c08689402001000801c03240d81c2ea031070082e11a8102c0c0102c90f110303928143c400aa00c000100c5c0c01044000b60750050041c8030700c040019030b0b041906081031001c0040611020000683c04d10449000d03c0c081c400701c11903443c0070035400d10028015401114028216207030742d0350151001 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 288144496 1250 288143246 288143263
    0x12030109060f120620070f060c0c0302102d090c080307030c0209180a0507050301060b04051305070c150f0b0f090a1a03030a03150503030307091a0906041d090c0102 72
    0x2c200170440041c03000f2440f94020140001c04298400061007804000384441c9061139a480b4290522284d03038211400d540138a1540d5000d405038003300146044099203038000c500c81c1c080c000c0080c84094400c0528145603001d18000a0059a1618043c1c10701074001040c2c0003c1c2072640081d80b414401e81e40080c0314940042c0024000c84402010070503540f441d0220215050629003141c8041055085c182d985005074840c0602035442e01c4001704142804504580030b03150b01521484420410030300e4180104030080c50001000b9105600750001602d2401528141040c044040342c0682540042406c94400f00314880c800c0c165243d90300d100e034945c0031b1090f5010364001d100045003100c040c81626443e00e24a0415418000015401520340d00b43e0b01020400005040413411903440e00285552840107807203a00104d01004010441c910182d00540201045e07204018141002d80000c107001c0d801c0303034000b100601c0d01128014410b800d50010303194800c1070440108031041120b0300107901da0441c0b = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 288145746 1250 288144496 288144503
    0x140f0a0809010507060c260c1204060b030d112a0105211e01080a08040522060b0d0b0a030209060d020f060f071b030c0e04050a0512030109060f12 64
    0x101d000c03181680910300781c0d84103640256003031101c28038129004286000410b1043c07200c501c0d015414448942081d00d4500c6820010350141ca07041031080038860a00c0e00400898805480d2004610b031510144842c0d007101c2c9590301c91a4080c2c914a02050821119011641400d0640303140e0000210100710460311707198081c01c2c0303140d0f075000d000d009030440041525a0340d5030710600400d1058900c0300d01144049840c204c0310390181d590f281c418980e10f4201c0008050481c040a00c8203011614003085806241c2100c40036401f01412141105400c0d5111540080e800060100e41c0080882c09802a00d044030310849072402124215800600741880c05080b69000d900c40d03503049001c54456401c018013440000f06416211142c100c04030030b0a602ca100216500f10840b9280000c81a10485c80710a0f02d03400000c00c440c240c10f0005110081c00028800d40e211320038405140c01007001032015585100c44451410769075030510600c8800da4143e54000384d105c0d03103440070801000c604011450f046503030 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 288146996 1250 288145746 288145763
    0x80a051002361206040c05060309070e070e01030b09040213020c0102070818010207050616030e1302070b010e0c0f12100302030708010603030305100303020303150402040f080a140f0a 80
    0xd001ca032240300c007000300c0a04541e40007802c1041e080362440050340d1000d220200d460900c45070031110100e031100400e44000f071910411901c107002502d0900301070359029828600b1180820345e41c0c40412584030003039400c1e1001c1207014034084041d503030601801e001c501c1c1c241e071030760043d04103503011405400c40943c0040780150302140300d03e00c2c80420f4044500350354108a155450b020f0030340000c5151807005035854054450440000b419060050540d0f41d100000c2c42d03850002415074805983c0501080c0318a90310a04031001901c001ea400d00c007400c8541d0007210314846541c100501c0307001070b1001900c403907e00c0c1c00c10312600304854400411074400d4049100d810b030681d00c440560b0315403480c484d0002540350080010105170480150f2102045070700a5401344003540341d03503d210030541514023020b001a042000040d03021a40c046604003d0700c40a440140791030b65903207001078a00c82c5604800002d0304684045024407003501d41e8000168240c0c00540b04840441e03003100e550340c02c2c0d030a0040c83d640 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 288148246 1250 288146996 288147007
    0x212070807030615020601091508100c0c0b01030f060b19090b0a0e0708090d0e060315010c05011a0f0301062904090218100905030607140712030c09080a051002 70
    0x14403e8214100500124850760510034010030007a46980090007101581c1d85014046566121020442002c0b00d03642070251443c00040544140a0f156806548040c400680d04d4030f000210340f12510381c02507024020085100c0b200b4500141039405804145100e081d00d07081200001c00700040510440b009941c0000d0300341106c5000c1100ca60315179116a24040b80700c2c3c200300c080e0b900159201d00c01e11405003580c20302d41d262039081e40c14000f400c20181d001001400000c3d5100c4003841040300440c01414035000c0c50a659442500f5500300d140c940e11001c20f8049241c11a040c0150101d52159080380240401402c003980e110422504a00400408200b1000d08451000e44401c80e006003c1540e42990b640c4100e004820361040080f5400d8001d40d1003410750303160705100c0c0e4604030030f4510040190000c0e031107041c000c44501454421070f2001410811013240022143c0d2000406152603480102d82d0140d10340d006040007405034000480754011800c0c010000f000405c40298101c0b801c000103846d107 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 288149496 1250 288148246 288148261
    0x905130c2123010f06090b0a050a0201090f030914120c0d03050c07081f0203270102210f010b0c030708070f140f0708010b1f0e03030703050310050402120708 69
    0x240078248501c51140c2c40ea01070301c2ca014180b102410b041c2e0b04240041d2540d10f6443c001200c241d03a6500c1140e0a910b1700f4800101c00c3c62003500204105142840045255451500c074052048021441180030940003403040080000b00103d181980c142256940c1a0755110310950361036208410100b48104010541c0000b014007410945141d4080700c4121344142e501d940195a48110128425098883d0401c07000b8403001c03a030007104d1084601c050407800e005284070407026105428035810703c1954080c820161550300340702c940c1610a140c10f000340003501f0000f601052092040c0c0020750200d000700314403086010004101c80c038956015450a517a40e40c1da080c54100300f150010020550108a07100c10000d00f0000342c180000025041036039035080c0c0d2904180c0c00c032048002d009030410081c4402844070071000003001048195824015000000c41d80000e0441e44644400c0340456008018080c9805440403a01d001d0482502c04503d000d06807420a102c40e00010884410400840c0004808 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 288150746 1250 288149496 288149501
    0xc0c07120f08030a0f05060f100c050c061305040615020a11040f06080a14030c0d0e120f250302130218040e030c0f070b0702090c040e04030905130c21 66
    0x1003070b0451500c07900c030706002c007404000c2e020070300f0b16410407424440424003074a09803a03580c100884c014400e4001c0c49004a054542d03158202042e203290081c1c5c40c0d482c400740c840000409545140f04040f03540390341010708100444401d074000314422884082c0a28079260001500900d80da0400209140e1426010004010b00300c0403c480e0f001c142420310005c0e8441c0000b8014500398401c02c106484d44c18102a49503890050103020180d952110484503c00e030300442e5111150352000d049400e503011420315191070490300d04540f07110f6900c582109542c42a01c5059040700d00c80c1401ea60a4080c40d64001a480780e0300205050b25165001480491150444140003103c42d0090000d00c6843c628000c0151070f81c0048181068500540981441210002c100042542d9400340802c0c00d0030241c0d004d2080d042c40041860b104400c003040040385c03d200002c0c0a0380301e50320a66402c00c0b018100303018003070884041c80400b58000d042c9400390040302e802400082a4031005002c044a03007044013001c00c003 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 288151996 1250 288150746 288150773
    0x702060715090c03060608010b0d021c0305070b01171023070e0301060b0915090a03062316090e070c0314160b060f0312030c130522050c0c0712 63
    0x103080e42d000f200004000c140d4109400312240407000b0441800c842050040c00c0d600d44900940c015080103075145074004030042e0140060291a0090901410381c2d11644c02032003e812504103201d10b00801240818100300301641070017481c01c144081805441d405041080c0507540c0d100d2040c183d000034810500c11584441c4400703005009000543e030740e0448101c1d65014006070350207200720071480000500d20804464416002a058400291031030700d03108002c00c400702c1c4121038100035001100e072038808002c006000d00c08880828201d44003500c400b8040183d194450303501402d50740c0c2041510344d0001d841c00c0d052601400e1201298080a08440d00c80c0725003d661029004034820030030034010400882485281c0a5883c1c41d0303018520780415603600c5024620304003500f400c00c00110410205005040c00c2c0d242071407895803039601d1300c0000d084070406850103005130031081c29041e00450203004075500086c50f002c205180c001803625440e100c20060040c3d07981141c103049800d08210300710810f00b8 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 288153246 1250 288151996 288152003
    0x60f040f200f0103020a05070f020402090d05010c120c02210408010f0501080c011704030c02060d060902130509070c020d05070f0305070603200403021905060c0102070b010803070206071509 83
    0x4040e414000705054240d185101032801032821040d120043d502a100320303840901c0d107071142d44c20b0900c280d5424a0842103104200d07001a020b1000c86c41a44550031710400c454440d00000c00e525411308002003101440c107c4008540b0304290890b624a60049801d2003000400701010151b01a40f021f03440c850b115590100d81d5540c81c4c04441d200d2100c036544242d06803611642a18601000d41d001107594802c044101484101010042000207005074102e000c500c2c80a40103030706103100c01c142682102e0382daa02540100d0380005404500107060101440500b60466640100d4100200d00622038030a050000740518415001c0500703003c1d0400080008150200d0300c0203000d1740f0f81c44c3c61a180c0d240d61144002182c1801480161003015220503011074550424003070400349150200031b014812444200c1c0107040d1200d010407642c49140c01041e40200c803078005a5261404e15110703100440580c05854141c0061004c00016500e007802c840c0203c1e00300249203075a802032410304005010900004 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 288154496 1250 288153246 288153263
    0x30807140a0c02010909020a0512040515040309090b1909020c0c09180d11031c0e1510050a05100324030f20180a0914030405030c1002060f040f 63
    0x350051940181c20300b01c028400c0c0c2e2401c454540d24075581007607014190b0600c004c10303014020201e09441062000e07500500640c04c0360051640031424148581d425503040c0d0000e040b40c4000d1107090814011606468019980483c2c0ca0141e040240c0301c01180740103030b1400d150006820072400500f00981022244014a0120107091030350040018071808100039030715004542001c10042e000d200310035104002503018510b0007800004140c400900890703c03a038403503a00c40500031598001c218805e074051108080d041a414008181d500030402c590280740304500d141014041034032079015200e0306c3c40741d40c00c003c81e6088447c01811181203100400d5188005006000028484000d51b0700c40120300507107500003048900129901ca42c07816440054024081c8451640103c1310881110780c064020036000500e2031182e13458050051100c242002e40364000b0030140b00c1c03481d050281d100d5000048039a624200201180651034035001000728650400400001d0107000c210000c0f408034942c00541d0 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 288155746 1250 288154496 288154507
    0x10b031003050f0a03020f06040308010b03040c030b1f080f03040b0d0209031f0b0d020105070209180714040506010503010f0b07030c020909030a0809060105130e030c161401080105090403080714 85
    0x290f1340d180c0c4d428003900103200c2c90000c44c04d0044041015800b954055542c6501ca03801c0c03200390111030b0300180046800640000d8004089a22002150702a481c0c0c002d4210807010301c0213120308041c2c1c140d0080542a00580007104442c80004125001c40e006480703584d46803100c0752001e01c024001d80c8086605400b84082014400c002d485026400071901d200c2041301490b04d0050010a4040b00d000a0205004001c640d000d440c1000590368455422a84500b160020160440c07c0c5140c0c0d80c40138880407036244040000d80303480e02074658000000e01e0411304541c58600e080260441d640300f400b10b070560000300c040c14148a1071085540a0b0090059411803c082c1c0d9660343da980400e0b5998009503060004c91003200340810070a04036500142240c100350803504031440282406010840c00d444200641e605180c02071010411707140c0300b410401011442d141c00070a1101a4030071403810001c100005026036076644c52125005905868660030340ea807884c0054506c0c00444003007050781d280c081403 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 288156996 1250 288155746 288155773
    0x330604050307030c090609060609170705040c11012007030c0503190e090a1b03150815191803050d0207200312190309080d060b0406081e010b03100305 66
    0x281c07004807070070b013642004001d5407001f0032411070b9854002c00303000800c1400100301c1f1030800003e0200481c004025a01070560302c0002a04036941d5280f0b0341c0125402086450307404030300b81b04444a60f0030440c8268071070b2280100000701c62040c20381c002e0500c1903e03000801400420402c2d511803a0800d003450710b20400043c0054101c6441c0303070420707100c1d444100010b44081d100b409150300f841200060b9200c402c9841c1420340207001881d900240085428030006142c9508000f60014000781e004240c00b2410140800414001c5507412217040c0c90a00c200c0da100c0e010440c0c1b00c107519680515180c0d88500500b007802002c4e01c5021000f0313259240295021074102a1040d403034040c20700c01c44c21903190022061480001d4001e90b07603842ca40301e10502111400602a40010100a01c998a1f8510700050345c0641811120280c204050707580000c54107100e02500700e040c4d141c0241c030004500d51031049071074200c494140c0c140900001d0f19404800304041c01e506c1c042d6940030b5a80902a6013035441d8001 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 288158246 1250 288156996 288157013
    0x30c01050406060602030c0709050604020f1908091912051204050d0305070c0f060c0e0907050a17010b0d0b0102070b070f050601060e03060a05091005070f0833060405030703 76
    0xd07400d45695240c200006401800003088130411003048000d03003401844e0400f0100200001000103402a80030030420100418500040c0902509101c54800daa4001140141901801407003012190b00040d140081103600d0070b21202c1e80c690140c005290352004c40400c450f80e00032080c0820416001800f03001c100b181c04038070380886101c5590100015640c4240c22a90712109420107081c4080c0c40100d20045800c40e04030085a4000d4100134402290318004610701000850300100000c0d0041110721002c3d911130000460705118034106032a035410141c0d48404c9104418034000d240d1b650b160305018590090150310018200f03144071a454001c0d60825489032140035004480c03e0042100220300f460044c0a000c040c000007a008018a613a400c054130300800300941080c51074410380741480000762090103081d01c205100d84e03601119881c001c60150141d800545004244400c2300074104460120f044400c6040b5441080c1544050300500410036601ca51b800c0707903416002d141404800e009005 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 288159496 1250 288158246 288158251
    0x509030309100c0c02190503030403081201060503190b0f10050418051509040c050d0f02040506090c0919030203010f0204050112201c140106030c05070c05091008030c0105 75
    0x4609850803400c02181090449200c0040d40001c134400e408038801509105401580103100720303020a02c20740d12500082d1460308140d208494005000480c88031400c207404086d4010511401d05a045040c00071241ca005184604030b40380c0d2070f5a8140e040c58070f903500c0210300790300e03040907003030b08003083d4101002411036005000701c0c0140c00b01d141d0807012180170761144078803070404400c52070f50740d1282008100703c0a0015109035942441e940001c641640c0b01c0f06c0040f185846084132501c6040e2910510041e00d000074441807296002a00b001140c04c410000ca801c1034004031501d45413904c81d8a0000400121900043c0d01507181a0100013403100f075500801c02e82c1c500762981010300c2e02c8014540c080d2040426040c0840290900d61480011141d01070801030745a540d0440c460b40b001d81c0110200c030b4820600f144142203032401009503540520070450241c0d11482c140c4d24020305034070b801800c3c6036507200751350081c9030307500000e8800e5004210003805040f6544c1035a540e241c802032814040d1070207 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 288160746 1250 288159496 288159511
    0x3151003151a030c030417040801091401090f120908060f01170d05070605060a031a100909020a0e0c07080d09030e0a060e01030b0a080f011410060504090f02090405090303 75
    0x22000854120010b0451100c2d516551007400d01d9582c0d0580c00080d50b810190003100c1c0030010310158900708281d01d010f00054685000005a4031080d0f0402c0c80741409428031507001e99141c01c02c0c16010442d5400100400d6402c100c82d02403800d5505000c95610140d540040c01e180551024401801020200c4504036603541e50a0705014240d030110070348803886070340d1500214104101000c0042c5061704059400b1400400ca00e52040c2d4030f0f1541d40261500c0051440e010005004108480074014030110152888440422401c2c4455020030303290407042c000c14582c00d500a00013105585010100e41e8015070241409841e140014001405046010b07012400f0820000c20024641451030490040300e07a10303641c08044400640064004001580240380c04c100e07884404140c08408000a08455015000010f01008000905c00c2003603c042c10b031030203103618860300b00201680041a64151003080780c00181342d071031090b4404024070072641800d4004d03042208000c0003420100185114151 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 288161996 1250 288160746 288160781
    0x11090c03071e1e0c0605250815090403030510080304050604090f09061b03060602030307091e0b0a0f12020a02120307030204080d08070f0306030c0b070204022703120415030203151003 80
    0x1184c5d17140c2803200c201c031504100b1026a40405074147c500c1045803a0f0003241110b6008031230305100c80400c865400840b0190007090b107400902070b9140c1c400381e81c02c0c02880b02002840c2020705000002d0441d120b54800c1146c540c0d1600614017822900d68049964958030403810001e5001c4441c40d00d9030400b100440c840424605403000601e140080b0031207100794401c0c0d64018516084c02d415200d1614403842c00c40e036910200101140d10702d0007000800c040c078001e80385c030511034a007004000d104c5521840050b071828018040792001c981c000035030700d684c0c00c90446803a80329542c24800714028010340c0e0001c8100c0c410301d0120710100c0d40112140b40600055507411043d0701d0300c24010b4040e070b811484010000085203000b001001d0780c210281003007900c000d0000d032514600c55020224007619a90150b82d2100a0050001a10f810050000b05800e5450a10305052500140840442c04206c8180503d80c000000840700c1d030303080000ca20b480c0c90007424030425107005074000313004212020b504070303e00300d = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 288163246 1250 288161996 288162001
    0xd02040b0a02210403030912060e0d02030417161518140a05121f330617162a02090c07050309270411090c03071e1e0c0605 54
    0x311208440643c0e0701038492440d01c88c0b80943c01c40700090348a509070b0f022a5201480200008180105942811254001c40d11281424031008285954030400c108543c0210304110b01044c3e895160811902c1e4030595460203071001d002521440b85a100311120345880980101d116400845c503848040e005a070345444043e02c80060100301d0b1207981803c007251340242401d07885030001003414200000c00c0035010410003c0300c140320281e148585c014506c0311030b10b08202c0c040e416026241c84c0c010002845c1c2928403020035a281600c101c0c016011801080304000f20650f07035402002c200340318680107400401036107050707020f04a11030f41d451004c80c41440203d000c60070060040050b0f0700700d40d0304203016518060301c110401c1030200c0c4c0150524003411400366608150400e000078180f089000e042e491182d8010b440c01c010b01103100402500c9820014814443c001c0d6018805221015042d2200b4028100808098502c414170500400c0c1100d6074000c46450280d0000d200440d1030300ca00010702458 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 288164496 1250 288163246 288163303
    0xe0405160b09011d040213080a1e02011d010e0d0303140a0c2f0a080304050f0106030b1915260102040312080a090b0115020f0607020607050d02040b0a02 67
    0xa02c6a40000790006000341d042402c201d90280e8112140503004100620b001c03110050944406a6680310040c940c1244003000c0a000c0070300c407135a40c81d80900404815071540c940c000780000f80d0711103014a9032192110098003690007060a500c610342c0040c0445480f07540c51070000c0c041c0170301d01400080070b550100840c91400c080e0040040300482034403103c03e460440845100c0426503000b51508100800203000070702c181c00c2c05114110340c010414599241b505080082ca014210301580c282a03141100400204c0c2c07071182e90755000040c0c01584012080c4036401400a0074000c8441d060191074543c00242d00e44505120042c15140c40d00503c1302209500b05041c202d026034480a406030401a008440c642d00c5044030a900c40510800060f0702411070b1208405844240c0000c50701c030380310032506011aa010403031080c55801c190003d103e14079201600039110754018200300140500800c1005040d080da40554000d88202261140c680d40d0205009580c2c40c18640442da1040b640580c3d421507 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 288165746 1250 288164496 288164519
    0x60c260f03070f0206040309090209030a080c031306090b161103061513090b010b0306060705030304030f0809061b0a031d0625020a030e06040b070c050301050903040302030a12090e040516 82
    0x40787c254030780c01c030f005182481950180d8480c20100d40d00d405441c1c01900041c8005001c4d05201003090000c1d07803600c1d400d00e044580e19070b40360461024030100304030030010f010803039045601c0046812003054a034842ca182040107440002105a414055031080046400d528103034910424411110780d03501d0194143c00c0c0c81200c005e01d8019000c58210740061040207882001960080c0c40505a13038a030444030b4582c542140c00684e400c0b00002c950300c0c4a1441180d01400503904118903001034000e604000103803d80800d800d000800344084046407080b0030754025070002d0794620b0684070441c00064003203540350702c03840304603143d055a0301e601d010349111000458a0a000200c250001d10f1600c000b40c5003560030a258074055a4404004c12001c5010303d0114060030a5a105200351080d20f03090008142c00d41d10010300c0030180b035005010410140c2d6000504000c1e00c1d82064500c80c01700750916003105c2d035071a1a00440064558841440700304100040c0300084103d03e01040825243c484110845 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 288166996 1250 288165746 288165751
    0x12024b010c0506061c0b010807050a090209030a03080c0f31060f2304060305090f030a0516020f1c0c0602010c140a110f0f010b0307060c260f03070f0206 67
    0x69407006000400c03d00340307400a0f100d581010285c00316051241d9580742901c1d0f00036040801a600310500410040c2405008000940b0400c401581003e02420202e83d5800d131020001d81008000000310ba1007086403030807200126480c4071466503c25050381a50143c081c0582c08820f1040c5500d07140c8110341c407070844e15040e1840d075511007980c4105484200c0315040b05220031000021500c4e0304111241d0400001c20040071952000303d11403901309419400c12500b00003982058000b002036404440c1e101c401c885500e213146060388014001400800d031022181d46209401c410035040265011040454444800e4841c40e00b02141039180e0400702c0c26203010403800404a010103102d490a0950f01e4003912011340300f8600300c04032081d0403254a1a0008106584040d034001c8820885414000c1c00340000c0404181c004060326454564002c082d60348446000d1b01b5032841c0b80c1c000300c0075540002c440b0200c596250440d031b206e0785284100300ca00c0e0301c145d0b404000714112107518510070b4000b0500d20b1 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 288168246 1250 288166996 288167003
    0xb04060813020f060d02090306041a16020d05070609150203240a06030b030309030d050a02100519020901020709050a0204050f0103090b180c19080105010f12024b010c 73
    0x441c603070f440c0180a090b4202c01c10711044680c00b4410405607803010003016100d24019035aa04508030079141daa41544005024010103480c603130050403015400048164900d43d851030140d0b034412460404000400c501c0300001d107240c28138104c004160710190080d40c000d5180d04410300f0180003400c03a22500e02030150607250000c1c440c131020481d241c02540204040b007000340540707241442c0c500c00241032240c022070400103c0e5000c6161900f41d40c1c104540c0c013200302d0824040100303041c0403082c1012080c2d028070b0482115000508040240d10900180300200603c4500303000d18101001154043c0d0003e00a96000e040c64411881c520340c46405007a80c42500078841d100b91b80c880d0000260407002040031103a00d803040302c0c0c44044603100c1404064540c048604682038990078440c485094135010b81c0041c0034450100b000b1302ca41103017103040380410343c1e04039500083c50540b4849000500b04080300203d048503403090100114503403840c8841400e103c0c0c00005503c00d0004010356401480c0c04024 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 288169496 1250 288168246 288168259
    0x106080304140123030f0f07031413030504080312041502090d0b0406060b0c0303061e2d0913060609200f07050303100602070b0f0304080d0f060b0406081302 69
    0x610340c2e54003a04e5a500607104204a940030698820111a00340d40b0550741901140d1215042002d443c07181754605401035081d00e82480388501c3c0c04c8400d0041d81c000f4180d10705044c002c203031260815003d80225001403003038070709481d11400d8030f013049034507154200ea05903100100e481c0c01488603c85442103401000004043ca500302c182c580341c40441d4900184101c07000c66071032102059001704a0043e02e07604500380011a0b49140c20310038042c1c1843c40400600c00b032040e44201c90030a541c1c81c610550b84480304060341c0082c50201541901c21905e082800c1c2d000000841481115420141e1010074180640c0c1d09000081e940d03484403044401081003d981225094104c10f07400700010002c003c4101003500c3c00f4200421a00c506c3d055038000d44110405d0780061504001041d01400490024003002c085182000c1380388020300c6281c07000030401443e0540004400b4150781c902d51110481410302c000400003d034a800c1d81c510746a10900071480460303c00300c00103403428141d8002280c9290b018004 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 288170746 1250 288169496 288169529
    0x601031b1d06011701080307020f0f22020712090e0709080c0f01020c042c0712021002010e150a0b0306091c091e03030f2d1206080607020106080304 65
    0x701140c6a8054105410420206003044090320701c4400d55018080fa0005150795144910401010444085103903000b680c481502d00165501c04281c0c04031b0403501141580e081e499403030741000a210b0102c0007048200200d220b42c07801c0da1320041031307000e0700c1401050480c3c60320360620980b5100ca040c03041d800c0a5000310400d541d0b80c2481c0d1079901802034107004071412201c001c00020191004056101e00b04d0201c640f0900e049410440148030303000240010305002da090080a0714091146c0d08082c0c042c0e01403010b0040c1d514400d5100420804080080e240100800500d002d400344041e50401c40d902d0414210f00124903011500d20f000d81142c50061240641580e9100058540f04a000782807000e40d0034001800351140c002c80204050714a04410014110f1038040d185442d24516001001180d03d0790060301c0e22801e0910b42290888414803125a240c40c1c0104c502d81070fa80c00d0b14145501b080c3c00091011000503050b805040f0319002440202d4031020420790700d0256120710070f00008034004 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 288171996 1250 288170746 288170789
    0x30705010e0112020412120f1205061c0311010c0e0a03120e13090215030705033411070b030903030a05060f0406181109060d0f140106020601031b 64
    0x11440070003141810080041c1c0c05914180c07080307070010340c416003200c0300c0c08120b034080100c2e543c008880441d007800c101d625551200300003400001c4510006090554960104a1940c0c5607142c0c4256500d08500100c1c4e920454500102308030b900c0400e8900e15030a2500b030111082c09080d0100c0704540140081c6499403039500c2c0c48224400c4400c003a002c0c8404801c0b41a01c90700d4038120038070003410f010808101420544140f0990300034404240d0b032004010302c18840015440411640c11907007081c0c4c400c00c24188031841a2181501318000c181001000209246540d0807412000842c0401c1041c0c03100743d540d4109403507462004031400d03030325904100005000404254001904010301411400e9500c014001040803280607803c0f504010030101950044c2080c1409a600260141a0041c0c14202100007141c2540150b56010304166100c1c0340c58070032034041e50700c013404a6844802d10b000e9941d54020281d150042800242d52460488200d20070384601410800100d03100b00f074111628400e0540c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 288173246 1250 288171996 288172007
    0xf0f060b0109091a0919090b180102030c07021201060902130e01090b01080408070f02060d021206031f0e0a1e0c090b0a03060902011106011431020304020d0b07020a1a0603070501 78
    0xb09a044c15400364001c1603825000c074801c01c00ca0030711424100b600b43c1800789a0340314080c5070901c0a44240cbc01081089510030a000c1554001e5038103860117204000041e1075503015000c25089030154600c04101890401c140d9403640c411a03002e41d03440300d15640c980110343d060707074088460140451038240c041070004101d07070300a00032903000d035681380c4502c4010340c00918241e01a03d00c204100f0707004210251411a003240c03803508807400701c00520100513103400001a491898006210091b56403a00314441103040c48003003035499201c002d803c61541d4101621560303403c2c0d15003e0302d222098400105010340302e442005440f0500400305104c141c555541e540c0034280e8101d049042140710480344002c03000c104002e50103032244140c0841450350280c00e001c240845210106480c0e03060b0708420103107280b4070520303034800c100080016a4a07691400418103400034040c00a10304860710040028043e07006c62880c2401d0721a015031000700c201c903001400640809e0354429815000010104065802803 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 288174496 1250 288173246 288173251
    0x1b020f0904020d0b0112060b010c0b01030201080c0408010e03041706070504090c030603060903020615061e0901110f1005072a05013c02040608130f0f060b0109091a09 73
    0x8118560307078500c2d44c0e81c0c2040b4800c00c0c0e000352220041c0c0d0089100b00030190040c15000402860b1003600c402040d00d03444107400040c8400f0f8180940701e40810b0000d0b040b14102c50261040340d00901060300501c110983d80d40c000d21481e2442d00015800c4101c0e20000300e10240202102e6440e10b040a0a00d440d003001072008810034814140d8400c400030004d030300c3e406021451406500a40120300d0075189200403004c454070224451b020411030416a49680c2e2007503030a22100704056a1a006100010780d94840750418074002c40c0f20b18a5504d0740c40341c00056413440c80720495828000c40d12414415100c0e848041c8425000915124140b0a01605003030b40003840c41c084d100110300110311103020701648200b101951840030b403418100f280540404500521070141d007904501e881d10b414001403c3c00c1000e0414800d07989666103510500c4003c06001100d0344e0010402400c000e417503d00440140720340c200842c00710301519070000700d104451040801032119800c2d411408d0740b08004200d0541d900 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 288175746 1250 288174496 288174499
    0x210e190812270604120f020310020a0c03080414120c0d0201020a1d031e070807080a030e0904050f010501090501060810151808070b0c0f030c0d0c0f05010f020306011b020f090402 78
    0x5100020341700052000d0041841c1c0100b210000d2032506005050803c4c0b560251001c10a0042100300d4186a01804581b282a01840c0070030440e1514941110681e1042e00650380307a114030390350380ca40c0740f405400407d0100c0b2980102c410224080742c09030b00340d00507203e220003c038400d042084503e1402c2068114507000c01402e5030040015818a40c480070b420810b2000a903114030340900070038400b006410007034072001008100d000b581d95801003400a85018490040b05880d004c1810001d0070803580c0c0003003901100a00103076031a414500e000386824815000050340000228882c0c02e10900404161410350b00050a0030001c194203032081301c5002d4605580341c0c08200001040c40090102e0030140090b900300c140e03900380500300549015803546910f003054004001c03034101200300043c0e140035401542060003c0300030b1401c040c10054055840500300d5420b052a02c1a90302c20f50f030045100f034400b62512002072a604900c0c4071a0010070070025000522003040042c140750104200754094030 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 288176996 1250 288175746 288175759
    0x306040c031e0b03010f14180a05120706050105010c0b24040609050703050c1306140d0e010c0f02150f041403070302150c07210e19081227 61
    0x440100a600742950400d103000c115030364100203c0203240a01810b000400c081c1000c3c08120b240c440e20017a2040702500540040280413042c800d5807406001c035a004541080c1074420b8104607214108540d0712550007124042c1c60b24002088941c080c2c1403c1020310342000c003104072541e89608880c40341c40000000800b104401280204c035640d10302504c00641040d11002c41c460404e0740019050b01c0020b42030000e048410700c40340c030752633403d030310401c04407205403829003201d1a0400500c1002d1186a641c040100d040001c20360103c54150014002d03840d0380d64480c03000405007070040382c44503001d43c030303150304c2c4130a0501180c030b03420700c404a903508a801141542c41740c15503602c1c45071130350b031016008402603040b00e4282c00051001d0b41c24154484008100585420b0311039546240b540001e0745a102183c0400304000c80f00c85c840c5c0000c00c200000500a140b00d244504a0484294414821200e0707600c02c0b0a45610800e07100d60984103048c0c00c3c2100c00079111200f0074000c01c40c280140e0115040f52 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 288178246 1250 288176996 288177011
    0x3130302160b0c0c0105030c1e040b040801050403020c061c1d25060c020a0303054b190809010e011d1504020109290403030512010e07050306040c03 65
    0xd10340e6812008002240c80d541d51024900f45940c24801c4801c07001d4140103080c001c02c50603003400400c55203951f0182c00c0904450701441500784560046401500790b540020a01041d9518150302540c010f40c02502182c200145500c100701a602c02e1603200e2078900021a55100e0108080c0c0150b0035416514101d454008403100b82c403483c10702c40f900030144c0040b50000d1000e030000c000300300302c0c09400c0a00e070840030207030590041000700006201c0241009000542c0307900c090200d91840c8018001a0030742d08845209030405100600d1010002080c0704880c0007910a112100302100c110740030303041029040701c01c4200d003900d64620091403040306540303c0307081ca560100c003841240c1720040718080c6030213100c42c80c03600d02e8500090700038080c01e40900303071041c0000760f81c010413244100d4a103c3c845a02000d1035001c00200c9103c2031404000c154408540802010f811401510a01c0807880940c04c45a0340c6201484044c1801d4800001103041000400c0713040c28550400a03c00c1c459040105078503 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 288179496 1250 288178246 288178273
    0xc100e0124090b0102070e090106030c06050f030f0619140a050117340c0c0e041104050705090d0510050907030b0a0203041a090a05011a01080c07030228061503030503130302 76
    0x20282203e2460308c99545900600400c20005030000207400da030b14042d820558200001104d0b4480a08406d007024182800580d06a45161340b03208062042d03041c0c40c40036a5182d0300c130404201507a441510034000c2107000f00d00c65100d00030707500350b402003c449540c1a860307610301d84030110703c13600b00c89020f4403c04068451600e01c00310b5895505285ea07903640300005440c10703c0c503054500398115000d6079145600f8400460b54144010401800c12100040d0640350f80200b650a40728031081950000d03140c5005600b8003001258150074078565500c01d01842c0d548240454440b2811f0000800c082102d00204405203401d60103564071600c9101e240f0003ca030841d50b1407990300d030101d44180850f4441e0780741da410408207028000785000b00420003906100c1010028109241c000c00b076151400340401d01c5420315208018040d00d8102e565403000010302d041c0040d80e441203282c1c800352082c0d4100b003044d440818008004100310381d0180d80705070445c2ca5040902c1e0600e25030080903021880307800c8040c440e2 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 288180746 1250 288179496 288179519
    0x1180f1115041401030f02030601022d0d02100f060501050a2105130210110d0503100308030c2212030c020d0c080d020f0705010207051201020c100e0124090b010207 72
    0x380400c02000d040d86929000010165210071014006d01401413080c8441e9980000303c00d5402c600c0c000c3c01c0c035459550440188040d02c11000038042d1403094003021048280c01283c1c2d04d081c4240140300784020310010503400c0586a0612603940007500802501d0b403460b00c0307030100401c188820082d01103145002c440360010358100707403045401140c56151010451511801c0c5000c0030045003051308140c201101d0240d2110b001074451001c0c0701c000400108110004e5292101460f17000c020540c0ba0308104098084680001040090074001c80700e1540041c0302440d010000c40c8d62465401442291655080b607004100060490304003103039401010015400761000c0b400340245500400c11400702c014003d14028480060040765041301c5002e00440e42c1c0445c402003900c2c015681c03101d400307900c801d0342802840f81d00740e801000c0c050141d00714003010180d00320740c14011142c0000c0c0050741d00f0340c803100103040755810040c4d0010800881008150180d1300101c1c50800140155044a40c1c3c03000d10320340 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 288181996 1250 288180746 288180749
    0x1b03060606030b0316151d0307030b07080c1201060e0303093c06040302041e140103030801170d030b040e191217040f11030a03020f01180f111504 64
    0x1c20b0f00c03070600300600c1c01d08001202200f4030f031201103400305d4900b482020081c0b02440071a410040c505480d03980415010300c1d501440c6001070116072005540741014020310100351400c0002405920211f01d0960412065801c002512840800b041e480c01c0400e49210fa10744034640c0d05800240301280d2203a031204240c014420b000a29414200b0034028410001e2040254903824001c20b001401869101c800c2034900756a81a207000801050407182507d018421045000800d404c4c1540803000050302554141207a220752070b841c6160341c80300c03802d41c90303002400f10104651707000d2070030345000c21711a800c402c4030101c002c6e000081110707800e0021400c2506070f00300d04862002c003010480400900540b11a06688940b404a171072040308230b80b00450303001c058406410368290b41c44190600906c54a803081c1402c000301102c0b03901c85039280203500c80196041458180d482c0400602e540072001171a0f5a0060344286040544400d56032050002001800c070590012041001d10361019180d000500 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 288183246 1250 288181996 288182009
    0xe040c03021003060e0c12040f08090a08010f0c0302040501020607142520030613051204090c030b1e04020c01020f0c030705070803041a0c0a0b130b060901030c031b030606 75
    0x2840d0f6082080c0840d9050b4050304e00c106d0058108600c540b009611190300b80c0060380060480448001410005a00d0107070304910b42e44000224000941408150700ca5900c04a80807410302c0384001c1d900c07054003240214070601e400b50300304000046200d881000325402000070388060504101e001070710308a15440d141d44100161840f40624020b1008803000360b129040184041e606400803240800d07110341000d491842050f525500c03080c104002031104044072205c00ca240350316660f40b120240090420b40c2c4036940468030b401c3d03035000305080054184014419111742c0d000f81c805c10006000003036004420a411555080c0070f00400420104014000b5500580055440340c20500b001400c003504e81d070055120750f104200030002d0b84424101528601d0780c40c0308072511440b02081c01810f02c2e0b082c0c02d00810756100c8408002d81420450510b0b2001030103095551100d40d900d2040c0641d00d6820700010703082d1580d0060800004021082c007185600d181805100110b42d6940c6217000d6440582101 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 288184496 1250 288183246 288183251
    0xa06050c0a05070914100b0f1318330b0f040e070504061101021c0e0102070611030930090316080a03110303070c020f190e04140312010e040c03021003 66
    0x3440d400708446035407500020048111b181540c0f5001c05e0082e140700d507520890464501089260110300000303003050091035407441b400410120a01004000d1a50791640d1000240e43c00c1c441d5011010403000c0020078402401660f0400d080c02030a0340d150b0401070107505610350800020881210180e1094026031107919403d4659050001c007030030040b501407071190b20303030703c1404140a0b05480d40410103402406a10014010700030031520b501a12a1450140040b41015540c003105076024004511419000c07080d10801144820040803020742d13044041c070000030032681110090780d498020003070528020212038036244000e0240d020b410381603111070300641000009205150f001810740020300050400345181d4500350f10040c045001036440680107030800c103082c0200e9282e1540614a510f40300c404a003032181c1c0c6038500d150035481280d0441e810010101800d120784030000c180c949032135818654500580c2000801c07038403408010030568103269015000800340e1074009201ca03d062a50303801 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 288185746 1250 288184496 288184511
    0xf0301020d0e0f0607080c0703030603120c170c06040803150904030c02041404050307060e01200c07050604030f1101020a0f050102031501021c0509040f020406090305060a05060a06050c0a050709 85
    0x11810100700a007410740f04d801000030489020350224800f6404526000c02d80d4891446040403402085030740c200803e00752201c03148061240e0000b544e0411a8454595120b04401581c0c20785110f003c0d4602c00344169101001141c0020400d401541d4403110380301010262045500004403c99400c1c0c0342500803c5444182905606103401a6044515240b03440012801e265403130700e640f0f1180c070401500a1341d81d9040c82e07092010a4002c0f0071000c42c0030790031400442c24080c0c0c0c1010395020049810043c4101c107000034103401c2a80a580c1181c0d00001c6140400c0030303548580d581c030303194440c40f1030450141d16114000500760340c5c070550b1528010b500050b201e240c101d52444954525400035815075008410140002103820140395180c8064500745490b100d150011401503c1001b0001d900c00f400458041801544003d003001168068811583c09407220380200301100c000303841550304203000d00b409010041c046c0e001080798045141c1129201155500c80a04044954004005054030b4070310 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 288186996 1250 288185746 288185771
    0xc1216271118060406050403140a0212070603051b0403080a0e060a030902100e130c09030b01240f0c02010503071205180c03190303050618040b0f07020f0705040b0f0301020d 76
    0xb950b100b2030803d580b00781c0b070315061541c0580349015511004010112807184d8402e141c0b014041c2020a43c0c1c042c15100409a43c0c42801d038031915280a054002440c240005a000320a80e81525200c070b030400b0001d1800d41142c40301592a8407508410052002980c08040246c503003600405002d03889950000c1c92030700034410441e000c8003480200c4104003085484d04190b503120644c03c8203000000f0400200d50016400c250348103611540b02070407810070310000003502640f1903210f91030603600e6059001c40313000185090ba4401c130350303880510004078120210300c01035028100650b003001460516041d550700014140c0295101212511102c04041013007441c039010800601e901113800300c1c090403115000e1000380c220700c1042000a8109074540c4041040358507400508010107050176100c0c096482d003810000c0740d8120542e100d110400480c0000f80c142840030902c1610039042070007030000c540c030b010100800f0300350030340c90b055005111a400c0c0d0380a503424401000540c0d400580850400420403 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 288188246 1250 288186996 288187027
    0x21206010602062403060a0b0d02031e240c071e1b0b0405060d050423010b0a0f05060a0f0e06040602241303030203090c0603090c12162711 61
    0x30301a10780b104c0e03860641c0800390340110346141d0040201c20001000086c100015480317030f003032000c00303034040c081c0d904003450310009603418842c9034400350708032a030f50350039000d0700d40e64903002210240e0400343c40c07004a102c0c1c0311100000d10f0b21f0b501460507402d042120114648803541000011110400c408000450b000ca0520003117000348030345140a8180703854100407622520618a201006941e500002000c010344885030b00c00c1100d08884a60015102c500b40300e00804404d00014070a003105d080001300f180500f0700740000e80c0c901400860038100750390030582c1c02d0a049003141c0148034245200e51a96110b52000d00000c02c03295008142000001c0d5824900c100e1410000340361400800402029508aa1507503102c0382d414500160f032a0703a483c5985080507000f840702035105000005000c924400002c40b1011710301d04482ea110100540c07040143c1c2c54013503510381801c10307072200002c0188207005103034810500100c050f00c81c00c090010402004488400c103103290300c0d4001182103480f0041d030301c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 288189496 1250 288188246 288188281
    0xd0c081e01050a0b0c0f0a0308010e0a020f090409060905160f0819020d03020a170306210c12030f0304080a02071d0c160f0606061209120c02120601060206 68
    0x1400c9400d00d50420000c10704020b058043c030031401d60000303001100d858003000300780303403101685040d1986440030307240c02070000c0020300c50b003001d4000d102d0200b1000c09a600c02c49104540c0180001e103060381d01c60a00020741040b0303400303440d00340d0f666000001090f0140701518407500880c00000031607080c002800c1e000c0e00150007000c8540d103c40c0c060800700b07100302904403030301d50100d80c0d000c0104954030741280341c1000c041c8002c0400700c684140c000ca40007c034010b1402900200d070200c1c8002d100208161b421140e03001d0004950f4403030000001641052121500c0000c0c0d150b0689140c0346070b03c40c844c4000e510542d01103503015000a01c101c1d003540d05200b45c8020f04041040414105074407201c4883c5101f01034400300001200041c4464003400100040d83c60755840001181a4001c60512030000c003018420040450326000c910480c1200d00d2080c580120b074071142404528180c03003000c641d0300300d8501e0100d800138004c00c00e101c00520204101402445258000c01c0189040b10200f5440e0401 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 288190746 1250 288189496 288189541
    0x3111504150c172806060c03031a0f0f0307091a010809061003080a030b1c050d1407060b030a080c060103023f07050d030302030f090a02010906030905030d0c08 70
    0x10814403003074004566000340590016141e84d0062110302900007005031401d0340a1032804900003601c81d008400c2c807060030b0007500e0412500009046400c022030504482c4d03988826101d80e40d0640345040340681c0300c000000780441e445591160300d0001169400030081800c0d40304410802c00039a808058594060000c0000d0700441c108183c219102156500004002200102705014180c0c03080d4000c0540301001848007a015008503483c1071a0440184103030703a035008881500c50001d003c0d078855101d611030f0410f002d2601000d42ca0f1032009103e44860b89926000758003203900070409040150002605d00740c0a850307a0751440c4100261400808118068080039007108440302d13012901d0031050601901142010004200318107081c40140d0f0001c030741c8407006590100525915901840c840c003044030110740251215690f00e0b80c1c032120440020b0019808010610041e8400e403c1204407910901c00c9134180450041d40e0320a941d144010342d00019200000c025070f10700300c03c0c050808601c1 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 288191996 1250 288190746 288190757
    0x10e0702010b03100b15030a05160306180e0102040518091009020108010302190b0c01020c100b03030f070609080f07110108090712170307050304020a0b090d03111504150c 75
    0x2034502290700c071012550b039098056605c421602090310740c26001c00380969505c810f10b60346e02d400c1030902d00624065450280400d0f45c1c0c0c10301d8111354003a116010a0742c280b0820107038100c0c550140c00016188100c1039840a5400b4040024252100741c5202040070011805650920304540000e02d44152000701c0020503003040c501201503604000c02c01c0c19a5019103006900520340d040510201e286940155100c04000031440034410065003e84540c6a4150541d501a55607030100741c183c0d0004a1a1540f41d04100007107000040c0640003803204500c10708020843c0792a0752a403031060b404c0a200080103000014004007000341e04403c1014408090034a21840d0400001441d6901e415003d40c102c1900c99030450010b00442007281d86c12040944180c981c2d91800c1840184950400d603000c0f4000c00c0d0840000c5082e482e0070080d924a010050040d1590402c0d070b8504860a1020144000040c00341c0388016030480d80074a8090b02c581d0023410745108480c00105c2d0202240c0412050004100303 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 288193246 1250 288191996 288192011
    0xf0702011b0213050702030c0a1401230a02090325141e04020d090c0f0f08030301080d03020a2c010e0301060f030f020a0e04050a03021c050319060b0a0305010e070201 73
    0x281c1d4143c120114907102c03040020207580e40e1a05a19610030060800c40620504200301c0400c60341501c03a440d00110130b4000d00c0400b80c03101042d90360010250700c0318400304452002030416040e95001c2c04c1d04080003400c4644818900240d020700d00794014196000c11319414050080c0b1100c500c009000d075600741ca4072049104405e025620f04804016064401c43e00050725203003c0d0102d400c1411400c3d004a9031080081c0d0301c0c01c030540140d040b07100340c04078544a0750000440e1a00441a207048400a030064051174161000c1100298021104074040c840008803000750340e14035411070302031030242c40c0d285412984c414002401c0c428800b1140b510a0b8140380003481000c2d12442600c0c11a54842c2a0840003000e03840010841e2006810440350300510703108000604c074001511282190194095a8511034200140c41070003110240210101d9420401300e044100c0d111411003101c81110400904c00d40c49000b030030340c654040407817600080c2e100d0f001882226804803080da00111103000030080007 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 288194496 1250 288193246 288193249
    0x2060f01030809010f030609020f0702040506010c0302071202060d0501090e060109060510030b0d05030c1e0127150609020d0605060306010801060503090705030a03030c1d01080a020c0c060f0702011b02 88
    0x340f160790300d201c0c100851460750680d641e00a420000103804048020354031070001d240707101d0030b82d0031100c1d00b03900c202d0420000c03500c6035015249140c01c09805901510b03010b42416030540c0010240c0600300d0b0864000c100000c0028858812940a442e0f00c000c0411110b840d40703492072a00b40d06800500015241100070030596661b0500c0801c08d4040b4200458000c04520000ea0444084100a0081c3c080082d0f01e01400d24081443d09503078030420080003242d448503c0c1682290061800a02a2a001400300b2020ac01e03e110703640c950f0348070b4003003445894841103c042c25240ca680c0103401c0785401068101104150f405141d0140401b5a085802d5240c0000001c1403e80180b0034401403050001c04100700710800d100e400060000941103880c0050213240090061111542c0b0400190150508d440b0745422402e041001e08416035807505180c4070303000308034025030044000051511a0b078280c15500d44801c40505a2603d8400f40991100b80314000500500402c01c45070b20040700d02e00402005 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 288195746 1250 288194496 288194513
    0xb0f03280516021617031c0509071406030c0d0902030a0b060307050402031603020f070b07050406090b09090103030f03091406040209011e120c0302090f0405010606170610021e03040602060f0103 85
    0x11103450300c0e4009000000d180c0705c2e80c1188500855800f6524588001c0100b0400325046180038001040c200c60a4075950325250700c42400c0d5030911903025204001150515800c0130140554480000c000690076206070f0000c2e140036071401080780d0040b0800100000d03450140400700c01004255019455460700031800e80586480308859800e160b40030588812144a180985010b16440040c1c2d503014204508003070000e4019128035400503100c10b001048408010b0140c0e0340407200501040216421070350192082030704440e41030304041c0c0c4d4010150110b260018121807040501000e0900d508160040c01601c5034142c001400c2140e11900d0600195810b002c1401241d290600e00e20542c112440c0000b400c0c601940b01942c003840c2a010f1000340c801c2158120301552081000b007100550b0780b0000c1d14451440c0c1d0307640c1c51907101d9000041c2d042c1045140710340d6100303091050310b03240c00d5880602e91f030016100041c803c040c0d02c042021300640d501000510313046000142d40090541c91695034180 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 288196996 1250 288195746 288195749
    0x30c010503041211030a0503010e010b0712270f0311030c010c081c060806090708060601050409020c0f010603080714120a0c15052e0b0f032805160216 66
    0x7260b1007003010440352074418404101e011304c075031040e269103000700386d00103000b03801c203000b844005103040c40000784a0040c40c0031035045586c003034070750410b201d5034100c240c508005140c04102c40740e4041d214003146c4c0c41034100c0c51014102c4030303110320043c60179820001903c1e1600d42034140258030040b103030305140e0b8000d070312216540e40c0041050358070314035890101b01d1001240c2001091506204000c1041c440100d4006c0c8103414100441d0300c031503951484203907a6141a101a03012850400c02031000684c650018003200001400f160503169017581803e00319000c0394019a0f4100001c610441048a2510001c00001c4840c2c01080358619118259415200b40005101849481d400900402c100c01c00c03240c1641012090800451170b00f813889003c8a40210750700701c00001a480c06405112518100c1400e803052000c0c0d15003010003181c0c00c42ca00c1d60002e420002400840c3c4c007480400b014078402c6903d07071218a800460142012900c08c03100301c412400b40410354024490340d01841a1240c038000 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 288198246 1250 288196996 288197003
    0x1150504140c16120e0306070306140613050904061d010507051801020c0916030c050f0301030f0201090b0a030204030212240709080a061a01050a0203192c010806030c01050304 77
    0xf69510001d40540505400c0400700811288546141c80b05a5800ca0740e81c07618507a00b41c080d03410300d540b404e20450031140c80f03015400300415003da20040c3e07424080d024011100004052541c82520707040056032034a0111801c4900503141e4082913002617040d1061070b40ba141950080c4002d0500c01c5c4054075034092842d506001441070342450300e8170780c07003001007616903200602202d560707040404041c03041003030a2060201103030401c0ea055603441c0c4258101d5200f22104680c090442e42166200d10500540034401e9040044164010800312801c60041c0385131945074400507620740c510720520000100c0602841c1c2c85400ca0320700c00c4203240342d02e2032042c010300d10070007480d03110340e0b0380b80003651105041e40101040e8401d18002400300700b66540156652007402404c0740c1c00c50788090044415201c0e1208032401a04284044030382801200d5602000d2200350500d0b902d0710b0440c03681035823486042d00d8006146800b2401c4182c95503040004960450001d4000e003552020210020780103101c040c0004 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 288199496 1250 288198246 288198271
    0x70f0206070c170c190e040206090303040b0307090f0906030b040f06020f0c2802010512091e01380d02040603022d01080105090a0213170115050414 65
    0x7007001800c2e01e40c00c0c090200210070501000311120b089690790381000c40240103d40c20013005c00c03200d5000d895074007260720302904982d0340c0e600d42d8207200a03500103102c4240c2600c4140808140c80380c042c000307107220302c82d80e60710b4104103031a04601c8504922198030540325a460020103201051042c004070354811340121842e100c0d484540350401c001d100b0b40080c07004107400803410702c06140c00800c5500d984280315407050a4010044010117011650900090200c2d00401452200c48803c2030703c1c1d80d100c240d06082d0f0700680800001070072800031a101d50403160355140c00c1c0708a1b4103030005410288421040d541880380242e246600c5002e01a50304552145d0000045170046640c1c6820410207158050090b00e1017a10020308111104a620101000c0425080310108076520a080480c100c650091440c0b5490319000101d2000794011020101e10640420000c10008614a0205000c0303101c83c000080088040c1c0641d00d40001e140c100b28801c03070401508030400b400c40d603c003175000130040b5940c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 288200746 1250 288199496 288199507
    0xd0801150807021f06060914010813150c0e0102150705090d05012004030209011202091302010c020a17011404020a0302010503071803050105010e1602070618050d0b1803070f0206 78
    0x83e031501501e4110b144812481606214a4101c01d400000c11145540ca544c2c09440c0c465218400c452840d507051400140c0740700014142298040594207881e00910310074030500b141350141001e840310710001a0100307011120f0007a40703583c10860240e00c07400002e070000c8182410300c0010150b10070584000d01c45c4889541c0c1074280320085d440303010180515020031003100c0018100905a4206100a03440b03010408000140c07410040030a0030380c5a030050100003640e551172800644a0310100c800d034108911403800500503161040000080c007540c0b141000e00b107921407486400e54041c1c42d601e8500000c404140070044c0c90300b84110b0140c0303a0900713080da00c1c1d0762094000c55440c80d10540da0481c8401149001051203810751080b1305903500a03910780002e0f65800150b4030f685110510080059000f034000300105407107441c03003046544080282d203881075076400c0001d00030700042c0b43c280c4140015100340814600c00214508510240708051428016540c540290101345410060b0040354005007 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 288201996 1250 288200746 288200761
    0x10030b071404081c0f09050402030c0c1906150302030613050f0a11010909270c0810050a140103020307170111070b311e02210d08011508 60
    0x40c07070303880003480d03503503694440d9510703841c541d95050714600c112440001c402c48000140e101e003020850034003c540718a4a550700d05820b2000039400104101d1b84814180050f0348480380034007550803245105074440ea0b150b90f050505c03904a41c2e03a544132000c030340c02000e800c100603107002c100c040e4000f080007254a058255800d1040c241803035400d0070b40e002d0140902c0b550410080c09840110001c00380d86182c031940e2030b0200c5d08201c0c1c2142d95040c26800b0809030304030004031b5410800450078070403c60b103414517a075440210701c0c1c08003180b41c040e050b0f40c40300d0812002075031a20814145a07011018040305514503008079407104060301850301159003280310170440321000d4010540c0c4007180c103842e039600d0304c0c00d007004418440b0030b8074031219880860401c40c1c1100818403d8000f0300305c880c581251111015541c8200d015008982d80f00c400c001000c2d040d026a49881011070903000e10550364004034002d92a007030600301840d88034410301042100500150b520a4142404121103040940302030b2201d03003 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 288203246 1250 288201996 288202007
    0x6120b030309040501030f0303050c0a200a062c0111071b0b0301090207030e03010b1e04060b0c1f0c0e040c0e040e0c040c02070819020a0e0903090906010810030b07 72
    0x481d0b90308541844d000008101c80310b0650200c003230081e94100b0141e2200400700301d1038450403607020b00190850110511030035819030800078a4035030744122203540c0c20315907030780e003c1d40c2030f008603822011100028200c02618a401405486120800811401d42680209034180c02030020180c025080381c3c1c900e0b800388a100084202415048480036100d603901c14445001e9884601d045002612030040c0c180700341014000c00d0100d2000820060b80c00c070710006547c03520b002103088a5402a16641c001410540d042c004007040301055002e03004030200c4c0c060f94052103c28403080d00031039107000c2c03546c0c440b558000306100300d0500803500416802007002d001c41c2d940d8a400362030342d40640317021104003400c080055450541902540c0500c00d04240e00e5090f80c607590745120300d4041d9003000c0400d1a0403045180e00c003001d030b480106a45107041d103505402604040803a450003699000052103409484d05103041607100c1f50034608801c49140585003481d86901d42d100060a0800c81004100145e000b075 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 288204496 1250 288203246 288203257
    0x2070608090325050106090f06150f030c0201060b030103060b0102011407050301030b04150212010816180b011b0b040b060d1a06010e0d2003010203041208071404060f080105030706120b0303 83
    0x1000a0180c140c55921f81001032801d00c4030a4003141c5030801c0007a0060341c84401d14000100c07a150109441d1000c201900030706101c1e1108011950384002c041290240c54014501070343c002e034070001c1c2c0044500c00190856403030b0f00c04182403e40c01c4d810043c800b9800710443c0d0550354070031080c4070581c0b120710340300042402c5496141502400407514603425500305260314103c03120b4074102d400b450740c4882d0603842400a4040c050005140101103203540310341c0d03000f01c800500189442c140c100c2106015905036080700d003040b1448405c8400340300910060042e80d941003241258015030741c000694460540145417403900310040038280004515038024481c580300010b010f00600442e6405240003a01c41d019400181205100c070b1941c15054101442a0381c415544034001f070300d000740d04c140c05455250000f00340004003d20102401d144c12603440242008000c691030b90174500881c4000508504d1050301b1540c020f40c00740e03100b00007080e80404030b482001310422300010b040001401290071803055 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 288205746 1250 288204496 288204503
    0x10e04020a0c05160b07020d022103041a0918041104020c070305060c030c0306330a030b0d050303060d0311070602071706070801030213021909050102070608090325 72
    0x4103807038501c1900030382141281445401900c0b00340140b10400c280807001402000b04500043c00818010709026080f100040e0004000c4030030a130494010441c103108503403d4680982020400704290600e80f00601000c100049038641401c0d942c0c400703d1540300301a503080440c0d02200300441c06128000b240742c90714041c09441035581d01184000d10703655050500c812034251158400048103a180c007015240501c00b00702e00c00303286443c1d5404000c07250360b40010004c0310090703086140d00845000c00201405404c10100c080e1140f4010f00c0c00380840e060407190034019289104400001100071045a80c019011240070b207050405003012240098000e080300b0161041510114510b07400051071003c80341030100411582c18040a80b54a0365000d5550901041c00040140010b1038a0502d8003020384104070014149000c01004246a80c0c0422a020115410300130912003564140040c001070102810326441504005100c955280300384140700c50040c4881c2200201e2403030b0440c000c00c0543c0c2 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 288206996 1250 288205746 288205751
    0x4030f030e010c051305010c0c1509080d09090b011b0b0901111201030b22060c0512040b040b090706080105210708061f0605070b0a06150819020306060a0e010e04 71
    0x700300f0001c1d1007a440b00c44054982e0090000c0001c0c0c9621540002c00d880354019940303800346240c007100c1e440141c20700706000c2c00d0010000010454a600b007240f215940495940c000c04246002860021640b010590f03504000f5880780c081164260120344411040e0702c01d01c400c4242d80c6140c0c0c120f00514040046130034201c0c00040740c41c280140701020340d05076402401c0c8a0301c1c0744c440c6941090082000e080305c00c0f011202030f280502081203684860404e69140c106503182c142c2c4158002c0825004590440780c550031171061109001c00071342c0c1359911000204c02403890314104200540148814814503208048605c0003002c1548001140103865022008403500c0584941c01d058079140c044030800b03181c06110600c4100348680340c1e040d80845505440d0640703013000135240c140d00184020680114a900d0300d6000038a0b9041d9000c956449086540d80c180500b0034501503540d044000b060703000b2030303801801800510360b03800b822074010b02c0e00c0c3d00381080c49448600040c1c0d0014413103034800d0760107403 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 288208246 1250 288206996 288207011
    0x3070503120d050105010305060321120408071203020a021b0d0c03051b06180f01090e0a021e090f0d050708060c030603160f090209040b100c1b05010804030f030e01 72
    0x108401501441540c08001d100d0f41c2e80b40e0004400f1141c04540e455415441001c0d407070b156121079112104808401902c075450401040701001d003822068804a480c500300180e40d030b06100600388120b070282d06a00d004d5190074100c58000307503126012400e070804010100c84610b41c641c1e0f0751000d02c5940740d0090600a455959080c5651160240c07107014030300c0e06084802803a0352030714004541d28000c41c1c6840d030040300c00c81e4090041c403040540240c1d0500108800c0070401c51301d8070700d11034880d1040d07a00150741d6030042150785e10440320b490803800e0154024003054186580303d842004480c9001c1d0340032034851000703007000d030300e4480107a107c400c4034052041480315121003800118421394094086400f5040c155041c0500c44036a0310850042007002042031045000c2c6400070401108024000700b4000b07010000240c4682c2090f120602040908490200b0802c00f000d500c40301800e01da040d41d0340180b4060001c2c250b100014070040070000200740c1424110b0286d40891409038001008001c0d01c1e = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 288209496 1250 288208246 288208273
    0x60a0324060801110301080d08060a030b090a0f0503031614090402032e150f0827030f03060f060304050c040c350903040503030f1e030c120609160c0203070503 70
    0x340d00a0103800981e00641404001149c00f68140a000d00d101602104603e85161101410384402030040b4413a8011504441c0110b4a0481500b46242c00f81d4040c40e9642888224003e000c64000414024094043d103200e403101340803420740e0400380043d03c0140c0d40c0e80c0c0e2154000c4141c01c0780b005800d190103600d050f43c0003140d40d441101094038400454020f80642004041c1c552500e014140c10004130303802c3c00200748000f8907580e5042c801858034403100d80b040284200d03003190405151501000d0000c0200721451800b1a46074500c4c01066900c58a141003035250203880b080d2901c900c9001d43e8940d0404000c0c40d01c9100801e4002800d200101525100d5410403071a02030f90f201b0744032000942d84041104090301000322821500010000c0d071a0240c40d0038040456000100034403000d1a180c0c4070007842204050003140b16407140540d140d0b0301c0c0003d5624507500071014010b94001c1c0b40203070812203c02c080c0e84950804014030304140080c3c125a1002a190030000d411032501070140218010f41c0 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 288210746 1250 288209496 288209531
    0x204030309090203040f060b0f0411030a060f031e0c030c090f0506010305010609030f080d0c091502010207110112090507140102150601050405010c060f0c1205060a0324060801 77
    0x1500d00c640da81c409082d0340c5900300c5090307010545003d400e580d4556484070008602d64800c40e034011000d800d8801480b0410002004c5500b0345007855203a807400420001e030090306218407070180c00c0700781e964514603085880381c02d94052906549207480070010003030420702c51060303001c000440e800b2041404082d250307081e000c00340213902c100210090902002c200503600034000c10703042e1281680c1d0342c0f03600e40c65611008039442d4081e0060380c518000300424004034040340114819441540c1341c10380f00b5071502c0765542e214419890031070110791040c000720002403003003003510310400400d02e007010295480210410041110050081480c070030760400040f43c0090104448d5801000d8003900c0310800d0000201c0c01c03404049032490700050003000113025641c02901c640e21000d00450000942420740200541165420840000800c1a0154a044158640c01410b50080c0191030602c159440c6688103501d1246844030b4000e801c2c1c11501c0130b003060700a980481e0042803030300024800c41c00b8907040c4004 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 288211996 1250 288210746 288210749
    0xa120f020a0915090b0d0f23060102060a060305070501110f011e0e0613030807020f0601080618010c0801051509030106140f1c0308070e0907030f05060a050a03020603070e0904060204 80
    0x41140320202d01a082074094412a002c036000d00b540355280c004941a00d800500d811440e241940f079032400d110907008d801d01003568503190b0313140205e005418000006858000024075442c42e00d800d14409100042001c69090304449003806c240e01541d850513040e03410441074000d81d0138658a0204042d000842e00c5507010841408400d04111080c04151181d1302c4000440d220300750a1244c3d4a6800001d10558075207900440390301c19038580c0c540c02c04071241454400c0e403288050354040410300641e04100964250045c001030020096101410005000060140b0403644078068001d84250805a008102c03181910b00038000c0252070348071591400814204170310513000b004010350b030300c00c00d003021038503007422481d10540303501c401da5656011184010b0040045081201100c441d100702c1c0ca901ca0010b0040c0d4080c0c030042080c0b1140c018450449200420361031042c100000c00700036903110101d06009484d015143d80d40d80c1e42d01c041060f22000200008240c04c680038000300300c1480803d601400 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 288213246 1250 288211996 288212009
    0x807201b12030301030b060406080703030207090f020412020f190b0d060503010917070609020901030b041110050a0c050f03130e010504110d1a0415030303110705030a120f020a09 78
    0x1150300d4a2041401414000d1642200c0194000c00051002c110480041e9501c0440140041075103030b11100390905000c050740c81100964805181403041d00f800317018078804100d0681003181041d1400c030000000416250002c2c0c041c14211042010f2912810940000e40d1942039010850ba03a41d401b0040195109918612000c0d14040011440e4034060051145c61038200d0a200654100301c02c0b10901c1e40d000e41d0049035150760f03664220005844880ea4940258095a480c0c00c040c07401d810081c1002a840c0e0303400b4403070892001600c0b41e2075001802c1d501c581220749007038622000c1900d07045103400b0070021420454800820015001d41c42a91084240d84a0f451780054ada40d9800030310080d42c13100002d12058076801c0c046c00504e018150300c6400122342941d100d88103400c0c4d0b000440e01b107800d01241030021242e020380500615425010b903103000c8021610342480e049103a15195264082c905088040003d46a10782181840c150090009001502c0d4115030700c000030350014000d440b0a00c642d4 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 288214496 1250 288213246 288213283
    0x15030714120a170307020a060f020403060e0109120507020303040f0803040312110c011b06090605012912091c020d030501060f0e0613030c4101080720 66
    0x4144607400b181c00c0d541503501c410003144086030701c070785003805800040ca098118400c0300028004610f5034002c40e0300e044c400c0040140e8031411810300e84240c442e08000c1d55481ea041074001000180010510185001c440ca081c0e5181e41080c0f001074114412039000200c00003041401007280b01010004004692041801f420400c00604003134a400d00607030134a110b2a00048240d80d115405076403004c51210f03160406004e000003075511307003085950006081d2205ca40d100d005002e5400310000e60942d1032030040f03050024010420b280200c0b40b00c1c03c0c441c0c1000c0920040800c0b60071b030301005048002c85c8095100034640c0b041c21002903843e5140d500100000382080000500706005800207070a2480d540c2c1c5520010010406001440d4056811121a04813441d00000800c0c4091551405050303690160280d154248451290046402d40303290411404009010b20340b282c1500d84070807201c030a007010307003407696074200c00e031780c0c030800d00c4010b5030804c1c0c0780640498020000f003002c7c4515042c44056 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 288215746 1250 288214496 288214519
    0x603010e07081e061005040314060403021902060301170304170c0f0f0607020d11030703060608070b120a1a09040614010803131e1a030106030b06160b15030714 70
    0x300440d10400343c3d040200c803041c1c0c0c400f0503454185100b0070840c80080e400e040e840e10b580c07580c501c00e803400315490707450994104e0020b1008141d814045d15251140b0340007440c40b55000360b0000ba0061106101e0301d174162900d00721000e061072040c01039400030001404440b4200350001090740c0c403400c50800382481b4100c2c81010b00704a10b040c100c0e6141c44030010308800e0410406909024403c8880740059602c00300060340c080445d40c0c100a0000a980300380e80105e1502d1926880c07514101c187e4101881222091181600d8003880003207030341d8003164903940484d0440c01c4504524645540000490304487c4080403c02440101d400c04a00c0040301400100e841e0313612020540c8902401440050b40002058204420350300d206207440d1082d0045100d071040e1f0368901449403c0080c0100780b01d0310590110041103242d4041c030403003245070fa054450924110200c0c543c54442441400024200f000c0c0101060b10100301280213202800064100c503042c0da1034900c0c0d03c49155480c1c08641c1320390280001c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 288216996 1250 288215746 288215761
    0x1b07081f050c071e0c08100515091b040305031219050c16050f030c0d110c030a062309011a01050c070509130503030708070906032003060105090603010e0708 69
    0x10301c1c1c4030740b41000341503081c0342107556030701d90a29810b8400e0724002c0e00d4251328004590204002e4009103803000041c90990102c04440040d18002404d0030b00d442d01e07a810f6001e6540340c080304154030800d10001c824120711032022003ea1030040d604050700e584004907440041c0340032100b13400d0003503c008481200e5880e41e5540d00064640403a00300d025140d0a1040c1000104015452442a032140c015208001c110002103455500203444002499018031540328210781c22890000700381c00802c000d80240c0c14090040303546d41c0551800240999910b100c200601d4a04110800280301410310a041c503048c005220342c003800c02c0105400141c4c11115202c0101e42c02801181d221440324030180c02d289107410200020450300800743c5480b00c002d103641b5000680c01b80002c40c0f064429458265803030400c2d04004146144070740208081c98641403120923107803004403080c00003014141d0125074035902d120040752640602d45d0829001000440040b03092000009218450189560f031500c2554642c035 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 288218246 1250 288216996 288217001
    0x90618020313110a0905130b060d03021c0e03030c0a020f0307060e041802100815010f02031b07080703030507020f1f1b14010c020c1f03021b07081f 65
    0xca14080c408400b0b446400010060388014030441c10081903100c10300da5440b0108269481143c4008503000c491900104000c030000d0b1254001d4400e64240003882495500a0368075001d03010640c0104d6000d582d6860b1907803040c410907030500d001605880c0c440c0b9008103515502c0380054400c034461400350981802c603003000980740e002c644c05903444454a90100c1c0a20009102c020a0290901541d03007151740940c030781c2050046400b0042c3e0303070f0311000d00d4086007900752542c49500b03150400004080d0034250a50000a176068811040c56641c14105940619840c190f40d5602c40c07042c5001c0d01c4000414581c05c00c0140c80c0d40341c004e0f5480346000c4000d80030000841040f64010441c42c41d98141e680d00300384a01c0090b805000000d80b60019150503840300041c0407989204940140e4583c1030b15200c45a040c0803000ca8103001303464200c0f6030081344d00c40603495004135035840c1c209540481c11881d1a602d01e9014990003007001e040d200794607101e0000917119928250080d601d000102140d400300c0c0e03100c0c03 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 288219496 1250 288218246 288218251
    0xa030f060f02090d081e03040b10050409080304060b0a0314010204090b040506210c060d02030717161b020a060201140c090d030309080702101e0e1011160906180203 72
    0x504690403500319994000240c2c100c01c1d401c046c0b54090000440325156802c00860085001e5003840700a880c0c82c0c4851340840602e50816401982001c2c1102c000074400c1056a4100c0c0c1e005001041d00440300c0c020840800155202501040b00680f03180c28104040d801003041d0313101e00c8014000c440400d814402550342c151011500585181c0b5100031080e0844c00d1000c9480f000c0d0103885068400000080d02030300500d5001c06070a03800014003c401c0c0e044030307030564800701c00c0c1007900c158644100c038072120701c40d240d403520144140f1350040550323803041c1c03050400052303801030900c03460302d803940c200900900d5029840990a03511030080b071840e16800d81507400c02074000303000040301e0080d542c044000c2e044010045655484c203000440040c5c0c1c6003544000e03000d005503580c1a500f5082c145c40e00704000034a00a43c01d0001003801070100c0c0c1c441c05d0000c0402e08540c18085218081149414600030a45542884035801800041f6180d03081c0c1e08100304880f16110032070902a01c10041c0022803109 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 288220746 1250 288219496 288219499
    0x6131e050406080d0f050408060406061508060d0611040509040c0e180307080f0c240703231e130209010e090619020c01020433021e0c0a030f060f0209 66
    0x4d0740003056028402c01e50425814854500300741000d540700922890701c4829501110b48640707031902404092035000010a43d02494074183e0498181000440c402c0c13284030b100940603684034100c5c20184020340301190010107021700101480d10305810b020001c08160b01a10042840c8500414000000c50481c10f8900e0717400402386150030351607902d16603e0391040d0811100340b9424807202c1e20300e1006122981088008003007800417801407225841200400602000c01c0c14030b01007800200c0c1c020480011965400940060340c2d548503207100d002251742c3c25100044038401201007000f044140091501c0b81803081d6080ea1469884518010420004a90b07008036079004900041c020321a11407201c88281103a880107241144001d80c05081e40c2c0150450114144c003860410041c0142109220300c1001044001c6080e44020f24000e48400d40c480c1c00d000c21001001c119210310344180044225080010660480d40c0d5032460b00c0c400052404400350340c1645440341c801d170311001c2402181c10b085030 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 288221996 1250 288220746 288220753
    0x50405090a02100e04060b0417010f02030c0a0c060216151112040b150a170f160302010503220b0f06010804030801120503271003060803030109020906131e05040608 72
    0x3400f210031038141070744441c0c03a90300540301c1d680028441e5580d0000d0003d00b00c0904480760f203110064140f82510342251524013110701c1001040750100200068543c2009540741180b10041107042c440043e0003410120305420b151450420104003001c6c0301c100388100c200310280022680d40c20b101041d4003c170010040c4200e09000014005045007080940c4801c0d2040380704201189072001c03568101c4140c01c0b2070070080da19078402124460420140746103624590007400500a030290240019070207100081c184500400031801e06d0b140082486102c07840116910946a41e074103080c603102c60203842090340fa40c03041c8007245c0710f0351040c4840c512454168594510503482c00e030742c20304196409036058443d40814031680118408003a0b1001c000c620603485000074407414010003030b060b0602c4007650141480e002e410008440080180e0b41103629117100142c03203441d45404030714107100306014442c010740c0f40200802c01c102000e00c14499007440305050703800c0300d440380c09000440740d0500031042540d0 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 288223246 1250 288221996 288222019
    0x3050106080a020d0e0604030504081b10030e0307051c0f0302030907030201140c0609060403020613050d0f050405090702060a061418040203032b14071e03061d01050405090a02 77
    0x20307590f001018a0007008500186400301d0200407801c5c144141c07030440028000083c204181d80007000120000d4040e20100700010320044005202803400607100b500340364465590f065941401d0080d185c0391034011003580c203601030444d00004882c03880455100402d24400110070000c0c400c0c400c0c0d0b4400c001542c02800340da8110307001910307900036642564421801c200029034581e40103001040c007800b6040c00500300c0d070400d4a0041d0504030008c0038220000704400c0000c001c91000aa06c41c5030704c1540c1800d940740711b01744204943d0380c0b0603600f0481d008110035045c00180381e400135446100703425080d81080401e49480100d12254081c5d255603034001500c80c038140d80c0c039514078015904907200400b160b16100381c101c0070a003d181a81d09900310305107040b1102c901c800c0140226188080141610005490030380005003000746006040c480611005e14541c1030140070f0703446840545086239038001310a10700525860b604800340140c0e80186d05100120312244400a0205101d83e0300404401700103 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 288224496 1250 288223246 288223261
    0x30f140a03090c181401080d020703031812080a020601052706040204080d020616050304200a0305010f020c120708030c0304050a0b0c070b0906040b0105060706110d0209100305010608 80
    0x100529502076804111012000800f0403458a5164030402e10138800301d200c505151042e00203943c141d200c5c441176000b00703044028242d8003080712415a645424040d402c0054048007140b03010b000d801400c035422140d0f03810380a002c1740c080a019540d619500b118001c0ea02d881c00d01500c40740380030940184c0942d2940030040c500200d01519031000c005040141095031318008503141c00c10b0b90f043c20015800034030034040425400c101452132001c150134484e1540c1807503901c5106443c100d206c0100700914091003450340359203821494004641120080c8840c0710f00d0001e110095124006004003403242d02000e4403030310307020403e0340d076419000a003950440e81c4168249215030310080c0308503010700548402d90001801d404015019880081070b044d122111846c01507004280580a1001540201e04200000351315045940c1560b40555000e6103810143c600701002c4d11101000941c400d001146189a41c00660301500c3c00c19400c0302d208030380c10010102a42215020700992002070411030008101 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 288225746 1250 288224496 288224501
    0xa060e1f1404111b0d080f04030804020117041202070501030509120903120d020711060316030c120615140f03060609010e030d0306080f0318191809030f140a03 70
    0x354078040c1001c6100744100c020b44000d44d0107546451110185401410300380309041060001d50307081c0f0304000c6d905040541400901c031900a2004040082c45800201164420600301c030a841104a1100d511308103482c10760b40100303c114400c001031060fa1030000e11584680a950700409000c006081000c44600701c200c401d50007a203200382c1501c0b60b8401a10751110a500a00400401e600c0060b110300b1285011580c40c0d09424180344620018000d1200c1d581c0e00f5043c1d0654100385040005162904880950700d4240346020150300500d014000103404010400c0c044a1b0f607140d64500043e4650301210110324010f00f10011015070081c00080c1351400c1c240300500030b4441c14103100a0f96651500040d10307129000210600081e100e51040100712410003c090554803031901450a100c1024110b00f0362884020134503104520111800000b904022050009410180601e00e42c684000c4554006802251422000901c00d00d0850795500c0c070600054241102140c805c1e4581404150f04901 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 288226996 1250 288225746 288225779
    0x50a0b0609040b0d0506040606060329010305070e0a0b04080f011812021002030a09060c030501080c15130602160603062d0b16110906180c0904050a060e1f 68
    0x4008101c40250f0005c282c1c10004248154410703080445d01c6814400d000f015940305000e5003e04001d501110494405c229800001d020001e20b80020696250721044441c41d01c000d03000c9030460086040810321030041030042003a2101c403001c491740c00d1010702c031240c01ca0f0003010102c20428070360b00c001000148241000360075034800b841210079281d20364110a080f6070060b40c402c00790b182e40d8209a002c0105030301401c2050025810204002d625059140d510340b0301100a0701c1c4101c542c5500711010349140c00c15191407800f4a8500110349403101d80203035640701c43c815071014803002540d000940038800c0c000c184c1514121541c00180b80c2c2ea010150800d076464a403800b0042000d00b001003011088100601106401030302c400000f81003038102041010541810f07640605c0024042242c1c0340c80300300da01442c01d8005491a01d4542d10b002581540c2d01038420090350103800e201c140020a079035a088042650642c00006002c3e45036000026611401c801d907010802d0600301d000c0142001040741e11a = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 288228246 1250 288226996 288226999
    0x11040806071103090901150f0f092108070c030308180c13201b0106050306060d0309030510020d0c0c1a10030f0503030106090608100e10030f15050a0b0609040b 70
    0x3811301c10241c000a00b82c40e4240c20042003070b4110f20b1007a2003594446410041c1000c1801c00400c0d08201007001482d000c1c03a4028990300c0361119050502d5085061258004140c200610546070025481e06801c01d00b2184026000151500081640f890390b26544074000d0034048003c008008100e41441b00c81e00024000048460740c0f0100200e5144402c800840320300086045a60b40d104030540240300040c4022007418240e1400105000b1611b0000f441a007105d07045680046003d11841e0884941c0b00680004207140180c0c03e82103603000072074000c0d2000e08010541841280781c03160040700d01c484054001741c04403070008510343e0b900c10703801c1074550840c281d484600030042d240e4075034001c1d0200d4520304840503807002004101a50740070002c8809040c0c03a15202026040811040f040155640500784401805401180000300010580402103a000b0a02c2c0c1c1c103407006003026041c007000240c40840785030500000840d01c203600d01c039902d403030370008211a041108860910000301480003529 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 288229496 1250 288228246 288228253
    0x503070b0a08070918240807030f3f050901020307031206080714100e01090306020d0204050a0305010209010314070903080306030109050109120e090c04090507020703170d110408060711 81
    0x416144d220703400034203c43d0030008002c1014846424a602c40e12640d800c040c114000c0c0420500c19036101003400002c503a000f014048070841581403400395244218505062510403681140380101202c4bc03061b49581504101d0700507440b070000c20f07981441451305690058008011041c0000d01402d06c41030000d4452100040254844982c18a0500e0700d400c85516071051074100b05251400d80c0d84d0b05c041c4a02d92034071240c041018000030f4503286d52400018005a0049000e0314101195030540e070041030000c004450180d03487c10160700030350015080c80d00080c2400c83c445060f156401c0c605016001654800b9a8107265494070045038201514082d4155250180c0a0103c0d20900480003118092a0300544c07094211030094201814815001d000e4805503041002c42c0041405882c01c90b0700425000c500c66030344180803030811031745170002442d240102c80091341070301202e000b5005044208208101030003000241080d00c0c01613110340c020b83e07841034000440e034500c80d040811074418040c084 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 288230746 1250 288229496 288229499
    0xf060c0b070c1106030901200f04050603040303091b15030c0806010315050a061115040b0c0d1e060906060203130302040e071701140f06010e01030c0507050f03130503070b0a080709 79
    0x55000c5c1e0080e1000e0708180c0d1242c0680710001c0041c109100d6000d64507220520703108140010050900030f03441028400d00d40440041c00b810b029400240d03800354052000c070100003201c050801031314610f00404810800091a24030464000d1003190607914181d210303100396688034401180502100410b01c1c0c10010200e00001e500d032180002d20000e816152141c04602c00c2c2a401c42d032801081061042512001e48148400324080c0800355422070741600da115554000040d0001c080c1042104401440c070100100614001c0c0c5540800f06540c40c21200303102031a901c49080303a032070140750304070030a003144482d013000103150541c401e00050340c0300b00554140540d150000c6180d2004151400f200d07035102c0301404a4190708503942e617840b802561003ca52800d12400090502d051a00814145a591040d0058590040c07040c3c1324442d0340f050861384210300000116849030800001c101c0303500c82e1008049002d00d0b02052007010740c0c9a40b2501400c02c0003d80b01258082c4e0050000010b00000040 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 288231996 1250 288230746 288230749
    0xf04020c07080d020111031303031d061905160210020c0115120b07050f090f220207050c0a0e0718051002031201060302040503030d0e010e0f070f060c0b070c11 70
    0x35002007035503501070703c1d90b00107080019094903a4400c8484a00408104004850f1080703001c4885a90f05450300240c2003000d200b50f164003106e00d00100c45548941401c100b20420100c41c0f4050091400d030080c801d98480c507400650119034035800704c0141c1c0000c3d03800d2021345055406440242020400442d0024100d4101c05843c1403d03005000f140c3c040c10441c20900c024840030035049091450300a28003413080d008404103000304401d6600ca00348140c00f04100746d444600d10b80107880c44804041d00061204044c000a511810048820b402880114052491b000910b002200c9940e2142002a6078500080b506e001c0100c0c0c4d03e0310746c80001e4101207030680300c112002c41204010f0300150b640f000299100025030300c05070b104408040c010841404075483c08400c2d07507036201c4c42c0032010a0b0100300c000380c03138094034006910103a28812030340100b030141c1001404a00302c801c0301194521a45e20362030102c6a5401150002d413100940a01082c0254803803810140300700d0044a161601111040 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 288233246 1250 288231996 288232003
    0xd020a0e07050a090614030604020a02010e0304270b01021e0703080a0801180b100e030304120b0105100810150e0a180605030a050604020f0613120311010212060f04020c 74
    0x841c0d8030002071001ca1940c1c120794000390304130050080d9080012241d091025007003403501c40100b215001d03540108210455034000d4100040e400f4404082e240c4454950b4100550150101c0d05508500b040e0080d001c210701b81407203a100115070603809480c1c0e410300c01c035138400031003038560322580365110344040007001c9074256014140800300740d40d51101d5549881400e1400f10003030b500b10041181b0701a900080c81e40d5020301e00307103010203030b08007100709007105400642540a1544040882c920307501d00346042104020754541660003c445200043c2c500780000c0791040d03000c580303801d20511040700034080682d080c80c014038081411b20342000d188001c000481c08030710a1764050440c840c820760f072102c46010940035690180c8010b80080051f46010340712243e0762403000e000130f4083c0d4240b51045ca400d45400c0704031a90740d45400c05c24940d0b96640c0f481e40445100601c8140d0000b01070a55a1a0300201030007102d42001410082c0b501c40d4640508000c0800704c0b01030b159511560802c00c1c40341021052 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 288234496 1250 288233246 288233251
    0x7050406080606211005070921020909010b120a1b06090506070606050d06150b1309020c0a020307030c030201020c0f0609010f1223010f030b070e030120030a060e0c07020d020a0e 78
    0x5c04140fa051040e400380c44c4000c80e40003102c59001a103420006806403010070106913404a03550031458561f00b5800f0b0050402d05203903504003400749840205810000b601c5044075100d00c403c06800d070002c01032242005003c1c01802d000800091003000540303040340c0540607a034019000044c02d9070b995000100c0b0080e071a28100c884c07a440e8a60000c000081440030320051403100d60641c034203440c10138400101041c500a03074502c10f41c0820582d100782c43c104001d84075030b03901a04842105490b820580c1c03800a00c0d00c000c90040c803410f62070f0182c6060441041e00e035004064480760820340800019286807446203200c401b040421032403050400441c2c0076280360645100359162060321402c0c601242410143c024171400441d941040001594004500d039000d026032814000c80d60140b40003a000d403100c0c0e441c0165a007503910b014110a00c104c0019030180d00080b60411005650300341e0354041a00888803425a400e0620030302025050810440040701d100900c03001646882d52603004c0c842c0d505 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 288235746 1250 288234496 288234523
    0xc1206071b05120414030f210d3c0c0c0b13060f06060e19031403070209100503060a0605010503071b0f030801180504050a30050c0705040608060621 65
    0x2482171428060400b030114040486110000d032500e8081007142c00380404000004240c0385c000050941000b4606510484c4001c59130241c9805651303603442403940c1020210110000c08011007000300d0141e0043c8624054500d15031180c91f181072480e143e002840c0c0000b4a51120080070311028400188980b25043c04c1c4881c3d20400143d090074502c0c01040f040450081a0240070246010100c1c1c132200000c5101b02c0754011006100c201142c0c500c03500318014000c0c0250896030350414080d1503000c003040381c015a03000b9000c8407415900c1d01070840540301e4610a6070301047c000c03c04620076504c0b400c802d0790052007412008202e05c3e4280d03601c03048a000c0b1a4190002205007006200042c000c0210606001d81c1c038505100c18200354890030f844408440008291014a03034100c0101031464001e00703030441c1e40240e51071210361081c0004e80241e210341c8840880f801081d40c0400c40d40340c14800c00c410348000340010101d036a640320030701030b5070b13410042c80003820200c0e11600c2007503d20402071030211008 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 288236996 1250 288235746 288235769
    0x1406100602070503070f05101101020d1a03190303020906040308040b04030203010c170a050402011b0c050f06070302060604020901050c0727020702101218050c1206071b051204 77
    0x1038910020306140c0700c1e0700514403075088098200095030041c3c64550548408641181088021038400e444180b441c00381c00940d54004078400c2c00381d01c0306030300c01e22050100000c422100b80c051010541c9540d16548540b050350003151000000c03d104c0c1e8042c02400c0030161210b40380c1a01c03600c0d03021003900964819001004001030034400c6007002c0c0241c00c0c00306524200078071501c0c910410040a00801403110349a566140001020341e841490ba4100410b02d2a0b400c0824242c1d5042040c0121214068039020b020805c041000c0d85c2484001c07107034074a070187e014000a403581e01c04c01c000396208415042c104442840442ca0f6a8800d0210308000c0100c4022521031840e0143c0f0448030405114211104504c140461030140e00c40c989841801c20691401c0b40c0d400c01402d00709002003402413101d0348810b1585040ca42000300c000b460449021007205c034001b84603100118295110011102c280c00100d201c2d202281021102888501040c0f2640544ac0111041180310034250020b41c00004441c1 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 288238246 1250 288236996 288236999
    0xa0b040324020712050901020c091e011e061b02031c02060a02072109030501050709030314090307262a010914061b030304110109151407140610 63
    0x7003800000e00c604010010035810312200d51645840003d100080609108000a200410340e1080c0310420040e54024011400e608103001e040000c489402030009a0200d0180049000741ba810365006c5110640070842c1031150414008880310000748032a03e50504410b940c08005030b03001d200042000c001841c0310010840c0270340e0028907051028000384141707441004404042202404207502d0859181b039a20764245145008641e034180d0b41e80060030b10b520f000c041c80602503110307040c901101d000342d8542404d860350090841341c0d403041013041c5505901c0080c0070072a901c40522116511684140c80507581441d09800a040400c80c103801244068081e100d130000a000d80e01c140e034810710030f28200302c680b0b080040c001c61280400307144511401c804074100c402c0100e8040f411280d0f0a4100640e9124106458085e003242c41500205000c142e00c040d0208030505207114401b41501c2698502e610310f04800c0741c0711110741c011041a0741c0060801c0322041d01c0c401c1040198040d02006107001e0015 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 288239496 1250 288238246 288238283
    0x90206040b1b0a050307030212030103030f08150312030105180f18100606090314030307090e0c070213062103020307030c0812070e01020706030b0906060903031210140406060f0804020a0b0403 84
    0x44481041c9ca2406800740010301c0882d512074088032030a1414100841941c54000001003400000030300b613a41413040082c0d00803900c2d00680a14101d480980388490401ca84250721100c140e0200c8402121003c142d001441c080c1142d0401c80c07402e81c041c0c041d580710b02e205905a6060b10629000301011514041d0100200b040111403100540000f0f80514118101008000c0c544c3d6038a10541e240d01c031040c40070840003500c510442e1800c0c4c2e40107040010300c50180c0a00c001400c075910510800c003030900e0043d0b54102020480f4036a05900d0fa029514203000d83d40c007640e021801da2410384842d0301c18004844040c815401250117001e0a4452609400c04000020b140c131603260440b00415080c841c0001c0c82d0745811041c10303017024044a03000d03119081500424a140184041c002400c2d072140c061004e14601319050005071042034121000c102a01d800344804d0b0f600300c1c821140060116034454031074034414131003190031a100800b000c420503a16280c01001d03400c9600152000754040029240d503 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 288240746 1250 288239496 288239503
    0x2030f070302030405060402040e030d0c120e0102070503120411040507030b0f030f0d27170705093d090e011d0304060c0503090d0609110301090206040b1b0a0503070302 74
    0xc038a1405610f03610709540c40507290030b400340000f0300441d21054000c402c1e038000c0c0700b900d00401012004100420188000800200028104100c1c039464400c6048501406000b194405c5030000001c602d88841c41d040d4030940e00c000ac2003924480391032200a1129940c1d8040c0d207006a00030f59004c12080d0110080181a0944076440b61290b40100c0100c01401c8011540401d0024503050091200035990031034080840325050306041c02c5c00c0c7c21401f1507901c1001c082070040788c2c0c01008548600340c8440900101000640b500b200105486001d400c602d40d1490f5407010300300321103590b952003140144042c140383e10960807007096517403503030302d400004802481405c00b1000c8004860b0394144440a00c0703601c2c0d2040380110410040750f46080c1c0d040c0a010004c076860100301418600303041d50b45081590003000c1104048441480c5040c83c200580b50502034a5042600100100e10301490a0b40100c0c175684010010b01004030322190b041480d40c414450b034000c4500a20165980d40b0071860700906 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 288241996 1250 288240746 288240751
    0xf030b090a0f2109050f1c05010c17070f05040b0306010e0315011e0f0e040f20100f090506090a0306110c01110406020c01083c06030a0201120b01050403140102030f 72
    0x8210000f11308000320f585610a01e20b2140782552080c1c0c107040071144401032144e00c1c58000e4215801e10b40706150b83e941c45050b00080413100980c605240d01e0b089001c0300c2c2c0d41c81010041c00042c00501050280902150065400540505003201e460381210046410b103000c6c0300e5140d21116640004110065101030140221000e021400c5800e60400c490010305110310b000d807000810f441d000040400024250200b05c0036000000c031b4070070a1151780d107114515901c40855010b41e801340340d0803c002e8000c500c014030303405568403030103405400c1c00c003400b400d46c00940d28564047c054650000108001e44140b00e025002c0a116540e03403083d000340315080d295840d999603000c0804100c02c11003184e010602c517034503801c24070300202e06886d1078020380c0c86165101c02c3c00899210f4035a46440e2401c004991404082c2200001c02d440d40d541010036485641003040680410007625110540202da50f1002c1503603907050500c01e041a44a4581044c08403450511000c1070307600005011800b124440b2559 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 288243246 1250 288241996 288242063
    0xa060605010e060903030d150509090a03020d050901021b030102190305010f0f030308040f06110f0903010f0e070302121501170c041a0f0f040c0c03180f030b090a0f 72
    0x113291a0b0b00101103070341d1307120700030131824510794920310710310b0403208642c1000061400611a0700d1070b0804040080e2036280168007200580324500f0000302d903e002e0f6040d034228200503006029400c49039462507041020f80e2316456490f5508001d212034040840c085008006240d50f00000c0640c100781c950b480c948000d81040288400c81c0c0c00410000f940300d0380940c0e000d64004040000340366245042c1018180c600c044404901d00450140884002d480203040107650440003444525020100c050841e01003440040300b0f1340120500b400941011801c00880e514840f0480c0c036596104040300c4c1c0400e500303800c40b8440700c152845841c420b01307040010901c43c01045408104607240110105003001020548a01500d02c040581040c0c0c1d031044480002600050000d015a07010400014072a00780c00c0700840114400c09038000104252041c0c44003075546d045110f900c92800c2d500d070250001c0000700400303441d04c0350604150005280d203182e02d15461080140c02c10084503003400c048004400549003 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 288244496 1250 288243246 288243259
    0x9010501030b07051e030112020910030809040c020304050315010e1f05040b120607030204080111040305060402010c17070c030b01171213050901031a16080a11040302030a060605010e 80
    0x61021802000480390030a005040c21035403660810850301760002c5034140c55042640c04130000811040e4505944100752007241ca5084039038518200281c5108103000c0030b40110030902011000e800d00d603012200c501c03001d0044034240303541c0c0e800091a00c1d25850b140001c600089004000c115071070654603030441c41d54004100a01c1c1c6c05a0410041055813041600c600d84400080291740c170354800480e405902035003510b20a1402000140103513000f84214042c0390f28100040d034a0110b041e017a1026694002d01420309a140ca0b00112110740200c00c06a440c60034000200881140a500030030000388155008500c0502e1410160b20468050b40a101e1403041d00c04804400c980109602280511070040c02e512800c011042c0f4101d00c1464100d075400a110400220500402003c1c82812a00514441a240c1d0b100d27000c03204e04615003010f100204a00c3d9002c10003000e000e800040301d2280000204d41420750f250002032401640180c16201d44c0d94610080c821540d01c801c181700e50808c04d0315078 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 288245746 1250 288244496 288244499
    0xc0a0201081e01091410031a0a091a010807061407170f030f0a0b010306050609042c0309101b0b190207030e0103110f25060e06070306050a0f050d0501141302010809010501 75
    0x802c1c0c09441c07200c188c00b0038515050700152081060f980031204d010f41001105044c1c1043e017000c2e11134580d00b030184403954400c40f40f00144040c4a000d426503031180c03a40c45681050500e40c2c0e06180700b11400340300d0710120750501103101d03a01d1601c005588221440084042c0350300b0010b90304022100f0081041d41003600b0b202c0d0510103030b100c1074201c9034001025600000c18031031140c0d402c3d1142d0140041605001b410001021950710300201510083e4400c0311084402c0c42d169030140c0303100380052292070510300a810248007046505442540c060305404007070303154241e03258407002203a002c03141c00c9020500007042d241c00f55030b1501c1fa01c4102d2008264107481c10060300040b441700c1c0102e241c445140715000c45440c407540d80034065500b540743c1c08002800b00c162083e0102d9110303d021100b4400103441d1250000381840c008242c0303000c4032102104076048038104402c0c04904030040308240c0b0300e99280c0440300c885010718502c09204602600d0030a0103021540700042c200d041c05801d60046a060000 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 288246996 1250 288245746 288245753
    0x605030a02093d1701150b0c010204150306090c09081c03090b0f0103030815010e090424061d040c0501180f0305030904110c0a0201081e0109141003 65
    0x1c2a5402840f500034040440b1440009040c0c240703080010046483c001030a1640700a9100c0c0d5001c0980d03128840f804400340c0850749490803183c80d43c0058540459400b81084203406030340003805500e04050025103080e031201c8002481010506000000036070700d85041004a183d0b1140404801036440c1215406140c49100d80e0b898902c2d070244105d18031001c040d4003046000398415075409610401380c0740d19281c0344d010030103452801d100650208040d000082c451144820300c00002200586a6580350206882401030341c1c64003c2c006c0324040d11240356219801c43c2940c000d581410741d82400f19a560030000051100031a4011640500004030f0030301001410980320072098800130301e8210201181441007042649880e03200d40e00300980c40794003009002020000300a4a0410755040c03211000709400c1c45024400e080c20000c05420026120b40103610528039950010101c0f40760003006841ca00700f1280d00102a441100145c0c0d45258400094041e12a00c0c1c2d84911012905100c1034a581c4 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 288248246 1250 288246996 288247009
    0xf0f010f030e010f0603200d1203020d020405060d0b042007080a030b060d0c0201050c0702030d0f02010f0e0a020301051506030106110313060c031806020d030b04060b1c0605030a02 79
    0x6008000341502c550904103a08425032000d415604840428840d044d9a410502210710140240c06d6083d030010030349014605110000031200b41e031019200c0c144010340101203009400c015000c0c0380c1c1c0307a0204400105550380d540a071400c025a03020000f40a000d031001c00c41110b00d800c107200b0809521075142d400b5101c204003034655490300b00e83ca030380d070700c0183c05ca0031002071030744488507a803149000c00c502c1c80a492070b45c02031411000715002040035803543c1c2d005070000e01810f540203616512400c80b880103d40700d809940b809031582e000101d02e250240000340240c1e0a80c290344002580901d10840c103600d400d00415410040155490010040500105000f440140500700c244447ca01c01012005410800c8070311030f07100410562003450312f40e0300080000c00d00c1d40c0c0c141e0000f010304050004a42c2004031140440b0540c0d00100201c0d84424415805811484255175000d80c2ea52000201c58807520002d10344072a00030603204e40c4040d02d09802c41120401c0d0496406540070444820043e100e00 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 288249496 1250 288248246 288248267
    0x6032a06020d030e1006061805040204050d061d06131e0317100306050f04050c09070e150c0307140f030406080103020108180111030a113117030304020f0f01 69
    0x614020a848040c0302c0600e10f070900c4418400003d46c900300000829a038413802440200c0d00660791403280e0f90b950000c01003a80114094136500804079244480018140d41c4061100400480c14541d220301000200c0e06049003210024620080d0500c042c0400c10703d036a0320269460b4054000034000402e40b4020288441102c260744c1640c91b246c007007182c4030502d944800c01903a00a0050100b81b800310024510400305843c1201c0ca0b204201da216900c1c5441210580b0840442c0d0383d09010610394402c2010710030b20844442c0c080c2c9800c200b44003144909000828420b80030300f401c0034004407080c940c140b419600c40f140001a8006200920102c1e0340b20b0000c50440b902464440d007a0b03182c40f650048101c51600408180f9882d1202003442c00b0200e0019510170b00b8500003c1041c5820704d40840018410b0b40c0761500d02821404040c81c0b0805c4000b003500051400305503404010340c8404801d14809540b10040e0625440801040114604401980700c01c2c0e02c1a1804920884e030385d400a8800c0400 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 288250746 1250 288249496 288249523
    0xb010909060e01121e05150a0b090411130213060207050109080d0e04060b0c0d20070b0708160308010503060a0c2f070315110712050307050d06032a0602 67
    0x4e03207480e10a00c01e50452010042c909000f0000c009206840c1141e51140b40d2600f0020341400d120004400c4017140c458881101e802a000c0c417802d50780d1744d0324002501082e401050b4001d1200c80a400c004000c2e101070030318100060100c410355818004042e2500003241c3c030050400c07160120a00030300c00c01058003245c00c50f403070402d5412892250f0020b0040d15180c0c020301369226010600b458113000c001410114024152200b43c0d2840c0c040c03040c40e08001b00760b26022210340c08a4030400070107083c5401400150300500d070303c905040b0100110210b080c280882600001c50400043c403440c90244082500081043d100b00b20302c44588002805032410000c07803081c3e0140c014450020080048640701c80008043d040c9c9101945a113042c44d5000040300c6000c11013854620102091b102401c1200c60072500301c0e4105104e46d28030b030700440d041d6200808003001c021082c0001220300e03c40c0c3c0991406548540d203140d0303c2c00c50012400c0c515844154421100d1441490100b14040d00410302c0c9440905 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 288251996 1250 288250746 288250769
    0x3010c271205010c1d010e061e04081e010209010e0907090503100c08010504110313080c1218030c10110307080a03020403170405132309010b010909060e01 68
    0x100644640e000c51180d44075801d04110090080100300c419403101e2898056615850010071860030342d244a03a60454095000c64100741c1160600d1419038054010184402002003168101ea4100c8050307030000e07480034542e50b20641059004203000d5241000f10b4508030021820124440002007000300b11510890003903140b02d0224000794403d201201c00f5000140845d003100c410055030304003e1207161550b80000380014004112490b003400740c000c1000112680c10308581b112403464503000343e2800e0441c3c2c5c41400b04002e1075405c10038040d1443c02318984402135160814241950701c12100c40b00034500c0fa410415840c0c0c2c45964009407805545142d1402c00700b0901100340c0d00d403941c496000f0151130020f000c41c0404034180d25400800991f8811500078814400f0000c1001d214040c6008035648441b9089041c481c0c2c80075079010421088010000e000d03401c0d80306180c681800025184844580d441e48401441960084000c80c000c20301c03180c0070011300f803401c9170b0314011410601980c2440c05 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 288253246 1250 288251996 288252047
    0x2060714031e0414120f0301031e17040e07170c0d1e06060e010207030b01050907030b0d03081b09090115050915030702061e040f15060303050d0b03010c 67
    0x1100c4684039240780e440c2c00e0151180e0304050501d0702103102650b81c2c6004511441d00c5840740c419002c01950fa000c00d00c1c4c1001411a400c40c1c2c3e600071040c00c004a9211390045443c2d9040210309444400e110585d4640e24031651039080050784a44901c0040c40c00c03003405101d0320140d1445280600c0c03035034803c14000242d81c8460640c034019001d05580500290700400a00d00320b8058003955012504441d1030b91103100b1020003007001a42c41b4407240c800604901d500c0b10040005081011005601050500d00042c183c41503c0004189a04c1940250005265281008060a25001c3e00460081080c4a403400e003502c00740064000c0c03205004580203602003012a4403124050030994085107001802550310844008001d0a00d420440d103400042c82224046044800600040c90340603a9601c903501c3d050b43e40d9110a940b901285100301d0300e62a0022400c00042114440c0c800950303c030b6901c85980329862542941030710301c0803540d02c3c840c1c1d261a00c042034098104e65003141440c00d0110303800c20603 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 288254496 1250 288253246 288253261
    0x30504051b040209130f0b01080c0d2003071e1d2103120a0b01050426150106020c01020f0303270f0d050703021c080109020f16051c0206071403 63
    0xc0c0038901c4415000602c008000c1711100d1a90801458240007030020040c940d000c0740112030300e0344103458550a0300e02c2006809400d50054100d1180d240403060365101c052180300d004d01d980d5008649c2000020710b00343e081c03546140207803188034102c14540f500313180b200e541680c640305503080e0f466020b01c120204e10700e049001103076031140d5402282c0401a02d0f200c8215440c0340c800c01c001194403503940c0389000b101c0410f960017042658141d803400e15001ca418001c5402060b144601d1281c5c02c08144100498004d1000200c07500a010f00305c20b034040c11100e0a20f200180c5003901058030481a50000d000300080806502c0c80d02052031814030064000803114a40070342094201c0312002f50900403082c80c8410b10b03030800020040c0500c69070840310b11240c07410f00207104034545501000054032800c010444c0e6a141e0300502038201c0d4020030145080b00d17064005d0100c0003028800c84140d0024940301c00140748040110200030324a002410040c501540000c1c200d5000c6590074888200203c0402d0b440d = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 288255746 1250 288254496 288254501
    0x619081f0906021207020607320c0d1808120f0f0d06030f1103010b0f040f0209031c090602030301300218100b070201080f1506070309080d030504051b04 67
    0x1c15003100c1c0c00c541d203400d203842d258190201142e05501510a440101ea6158030941c40d43c240540324030032146000703194201c0450040d020b0b0f010030384000414001c038040114140300d1002c043c1c44a44861514000444990f80100129030118a194212030700d0800005411412035003041801c3d00d103039035140c0c1080481e50050288c4161b0400840c50968003008106800101d4027040b4001d901907080781401400301401c0e2400f54240581007035540c0742c000410309040e00240480000c00402505215002e4003280c40c2850b10403e580340043c09106042e015600130108070042e0110784051840c541c10f0070310000c000055155081103544036030038141a04804800da5081c81580204040840c0c50440100c5d02101c40503180f2409400400000045a1080c0003c4440980c2d06131501c11141d61482d081c011040350007015500c100382d07085172041059803102c0041c540c161180e01c41c00c0010f410f0540d800d10380300c60a0004418546800c007070101049001903100d095a5075103000100e100001400b0801 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 288256996 1250 288255746 288255761
    0x504090e16080309091320120a0302070905060108040209070c06060308030703050601020c0406050a27050103030c0506010503010b09010306020a140a0c02090a0b151b12030619081f 79
    0xd03141c603852004540710b80702000078000e24008640e50541a103d1180c111244120722800030025441d5080303a0100c0c5228180704102444000c10390084003800107285400d0409080c0100c0051f080300320140300f05403003446100d4100b8020318003801a8a8117a005c0341c854a000790100061003201402c800c10085c180d00078802450340040c6107504da0408400240c060241501d055015020750928200213090038400c200c1201c2c8000c1001842c2c03450301c4020002640e450007000310a11a0b16480b008809030350264900851080c2c0e01c56112042c1820400d007050010382065119904046c285407941e5900c03040c0e03038190780c2c000f40c0060f0307201d601e000c06451041030841d046000d03801c00308003004110303000004005014020b40c0c1041c460360721450703200215000d507022554000781214141e004044184c02610945840e4034000304058101e501203880c040c602400c00c0c0300504d00000300015400c043d441c0c14411500040e07241e80e52800c1503000380e100d007110a00240d04560442040b010510320703402554 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 288258246 1250 288256996 288257023
    0x1835030d05011406072d0303060305100504050c0f03120307020313140d03030203070c0507030b0105130b09010b0c0a0b01030804150503070e063007020d020601060f030b0d060f0f0b0d030504090e 85
    0x20b00c00c46c94a00500641003501c07041c0c901d806014111505030b046801500d11590380080034012400300c000811203602c00d048c0b1559054403900103842c0b807030500f0a0096010310300540003180c55410742103096030180caa542201c0104082c20348480c0782a1102400d008102c0e616040158a81c2e072004011150702519420203001c0381b00c0e540000040c4000c2c62015070503202c0c142c80240702c2103000045d0030142c51101240c1504112003c0c01080030510400160585d00400000d076880c2082c282c030b5800700f40c10701380c10940d103003500001c0800003070590001c06404140d00d07081c0f42c0c2c25883c10030009018031041d220000d000d0100000c2e000788110040c482440c403c5100061504040d0948e2003918104100b00d035000c000d44104500000b5807400016040e0403288617079500d56048a42c1074048028100c80c42045402c00e0f50184200300182c2d450244c404000801e82000880c00d0002881205480846210074000c8208034641408260720504840580d4642d07074010419503c10304115107844580070209 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 288259496 1250 288258246 288258323
    0xc03030a1107211409180604140117100b01080f04080408030d0e010b030a0510090809120a2001140f04170a0c061835030d0501140607 59
    0x780b280409001043c2c14440d0307290303507440604001201c00985403142114265105001c003880e0440400300417242c0d0ba0251018201040c0c007500c03506e01003541d80c020b800c6601000401c8500306011581000708a00c101c06950080c4400000d400000c1c3c0401009058030400c01085400141070001e4801290000c1401c1c2c405c132951040d03103026140007403030190544000e0b5420038102a41a2500040f8441c040341c02c40068001070a106009034000c1140741400c44212201b408024079560b00ca2100d44410300c0030001400b20100c440c9880c2200b4054902018062540d401e502003c0340d901c55050008000010885070b038a40c80744040045900444c0c2c0200d00748070401038030003a00c1a01140c00310102d0710420340d01e14a03641f540303001e030307100c0d004c2071440d050012381d4a81c2044004196040302404200b401895400d15204840341101000000c540c48541d070700006200d0b40e030220354401d081c0140160400610442c2203000007400600c201c0c0c0014190703002d201072003c1d00e40c546c030b184011920101c0003007 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 288260746 1250 288259496 288259523
    0x207180207060b1e040b06031506030403020a0204180501050702070b030c0a091229040201020606011d130608071e06080601050d0212061215391305060c03030a1107 72
    0x604c08261181404c2c041d0342450350030383e01810401e0a5a004d040b1b0b0403010304582ea603500030710480303810040c025070451181c4d0b410f1a000d41c849101f004510300075400700d0000c05006003449400c0d241c02074044070456201d03000801c4059440000d5a400024481d44103035103480400b021104074803203800209496801070001020801c0e580c02c060907500c00b181c2c6203000d403c640112101e02d40320413100031740940c0040c0002a00b40d0302c101d522081400303010125602d81107107000441d1b001503640c00c4500c0c0040e03992009110009080208400a1080c2d01d01e46007400c10f08940c0050004442c4034500c1844820404108542e004401740c458003001000b04645440300c000266041820580e03107070313019423120340c21805c0710f03071012032141d0030388004c00241081a100c0c208050984480c416800c81c4c004800380c8101014040c00701010401045e11403184c1d280c5807055030007409503c0c0d592000e880f074402000204000700c0048292035109545020008051003403402499148c824841d000b170811080d03804 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 288261996 1250 288260746 288260779
    0xd031d03010e0f0615010903050a06110c03070506041b0f03080c1e011b0509011b0602210a0b03060708070e0a032f042304021201020c0a120207180207060b 68
    0x24140e102d017000c40c020303500170300e402c0e40151100500d5000142c51034001d06101004160700c0e401c2300d130030f6034150000b06291008100242d421b5400c00002103a85800c103806000a003e01741401003020a9420030b000c07001c6244c01051984a00305120091041c4804500000085410311411a03c49001d040c2c12102e400d0780340300035000b0800205143d00d60040030905902b04ea1088090310b000030010b03180e140c0c0354014141c0c000461142200c0c201c5000342c00b040601d0080000c00d070002041103c07411694013509202e0810401d69403d142c01c0c0e402648840b0410101c55403013150355400c8040e07820012296640700c0b0100d03614002c0c50f080900040300e8000682864805810101124004100c0038a94020840c0070030003603e072100c0c41c0407051000c640941d81c0341c103444c6070380b59000b600c02400c0b0700c409007000d0180d90070390f00603000380f00c01038001109541c148601d0b4410409179155510207032864900302800c240032102d1140d14010210350104000303040102545c800303001c400004205140c100784050 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 288263246 1250 288261996 288262003
    0x90705071e02091e0c13050d062c07080a020d0b04050c060301061706030a05100f1805010510060201050408030112150e0c0a1409040201050a0c2f0d031d03010e0f 71
    0x101d034000e18007980004a40440384002e07150500c0206c01d11015940c03400013000342034102c1d20750a840155a0f440c0e50241180b02140c5a01101c82e448071100292240c485e80700d041c12900c0d880266650003075504200180d40702c1140389403403580b00e8039015040d155410300c10700c0c0665010303203d508180004000f144d07241c0c108100c408400c03168000c1c0103032541c0360301c00c3c5030711601d601d4002045a4003105007104095415040090021840100055100703005d002d451108074200d9019600d59548005110701182c1007041c000113800180000d001c242425610401644014401c1890b42a0481c02040130010039800700b1500581c000028003428030201c1e101c40d1640451071207588180d4185000003a40e0035074600c0b08003200d4000b00198115591500150355aa0201e410401001700c420254000200107441014088a90200d44c4880190b10303102c1c684031954030140740341310303044c90421400004d500003541d00b60404401c00c1a2a51840000400d025000300300d10000140680c0314030b02c801c1e16000 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 288264496 1250 288263246 288263281
    0x3120c151a040e0c03070303050307050d020d0b0306010f0609050f0109051206091e060a020a180b030601140304052a1e0f0105070503030f0601050d111206090705071e0209 75
    0x21a01001010103003160140d940ea10300c3e04041d01504006c0c41000481c3c01070003c2e543c008410304060345000300c070490740e4003268040e200c024411070b070392450b0481900341040030501402911115005032420f0110150110751944119481a0545840c040503a4400c405000051070040c3c40b240c2843c44208049446440c1124003401c0741c45001202c104410210483d10380d4420315502518a030349076003800702e000c0d6100510f41c1e424010071681891040341065115402054208410750300d906144000402150079940c403141d0341502802404045140442c02070040c10700c880241d030041600e10b8a1741811003400e1403c80e0320040c60320881032101712140c800628001d080741c02060744400140151014081c00001034421f5009000080810a0301c41c50a0380161050500500b45400d500d011002c2e69280040030859060101c9c074840615059503015400c41c1003100c1c210703002d00c0c001400400501460801400e0004502c045900d031464140014240c00d0300a41040d0075407510340000c02c030340b00a0 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 288265746 1250 288264496 288264499
    0x1e030207021c020f0a0515090a03140609060106080c0d050714030901090204060b161e060c030b040b0109050105032d09071805041a0603160f06020709020403120c151a 73
    0x440c0d0f01c0d05991401440c2c0b001543c200401c1e1041247d40c8180300c24640d040f1401050b0440208140440866460741120408600c4507004002501c3d04620300703400d10406a120b0b00620030040d041c000c1c49100c00c4250383c2550380c003890002e802d580c0c804044981c0000224031418030180041070128a00041d001002030303a00a1760309002c2070b56191030f011250300c1003c040d054500202080140050454140041d01d0704003169010b5003a141e5484030300c01c0701e080031074a501180e50303201d40c82510705060042d14030743c2c1002d09000341490300d0140060020311005000001c00012030b07480800e40422007007030140021881c0c030072520515203d960295601c000380039481e24601d6804500e03060008601030710b441141e1000d00450900444016000c034040c01400707555041c01215001d950020030081c4030802004002c010040061030440044e040683c5500301001c014010071052012401400b10442c10000a241a80c3e500405081c40010000769405e107800843c1003043e801452401060b100188220 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 288266996 1250 288265746 288265759
    0x14150114101805120f030a0e0a050904020916020102040b0d05420103110c011a030a030203250c03030305010306150e06090705090a0b030a0614011e030207021c02 71
    0x101c0280c1070b1070340c9400a9909122401860042c84075042c8003080124104003c3e0490342c4e541e202e0039015096801c1032003a0000143c20041990130343ca0b0001001004105c1907881901500707164003c604401300040ca058014041520f001150314401d504540080c81a844003644900200307021a01601050b204480e6500d0142c0251049818200c030154140301011145e4440301120680740004100401703c09051556484240100c40444402000c02c248080c00000340c0c541031780390032190f00c40300744129030003035211240f00c5002a40010031640581a44000750f0314051030800302c01070ba4001000010411541da40c070001c205900f54000078140c0f031242c401400800c03000014100021164800c032415812106c0106640c0e05010a003190028030f10f207065071510b05200c0105503094040d41c002d94501c00c00000b0030000c0c0c2c0c9030744944000f80c85441c400c260b01807103280000340036000400c1401249000d40409121143c000e50451300d0b000d40c00303054280d200040a040140941d240403040e4003855 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 288268246 1250 288266996 288267019
    0x2102120916061d091e0c09030a060506120304030305130b07020609090a0b061602011206140120012d060e190b0409050303090d02010605060714150114 66
    0x18000700307509030031200c0c0e55440301c4960701d0402d0840c2c07003222000168986074500c4041c10160344070407414910603044503080d030000f00d16014413404aa10300405028941a040c004c1c0c480c1350f940851041c45c1c864210402080d1500c0d00c200003011440080e66440319840006000810507401201034585002d11000c0703d2146590b9000a610920414034001d5019500304154a0740e460a48212a00310b081e20030b0000f001303812840070448a41c004501e0f409c0510308100e200046691180ca0342c818400c94171f0050041514202840e0f5420704a40c103414103000441c803051691a03400c0000c4c04042912000034014030249220700160901748480e42c1c0d902a41202c5142e000b44003d0140f0000c4a10440c1c80c9811952000b2034617056490b840a165041920f4000c004030a41d1580070701315015000d403002e1075a03820b001c10f80603e0160111801825a410102c0c200016520030701030b6001e080c7c05c80c11a082113091826014180a40907051108001e100b10000c02c1025140c0c00031a40603000b510909500d0 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 288269496 1250 288268246 288268261
    0x602030a02030f03070302070f060b150c12070302150703090c0e070207060f0908030304080d05090f030301030204050a0b10020d02010c1107090f15030b06030613020d0f03210212 78
    0x91040c01040009a80204a5842103000768001158052a645001810300c1020b035198040f0246030a029144d6076200c55035000c003171812120803e031103029034210310300c4d002e824403c0c0d03521841c1601c101e035500d400100b08a401d0600a00400700780300580d13488860503151281d0060010442c104041c0e03400c03109002c0119058810003562401425540c00500005107070132011261020340510401c104000550001209001080650700032403280c0d9040303480d60b54454400d4200c0b5030040c9030a0b42a401000140900000401120b042d00e4041d180460307582d4460301c0c2140070740b030699200307600f110720200f60803d1942d020172400280602da50081c080440480c0c0700321040005500c1c0540d503604443e50800040c0709a81c4038813070080c0c004801003442c0020001103007039084644c0c82a201d0260039000c009151405028190f0301142c50950b206c2c20101e650003090381c07aa0140c000031b1658400d45061400e041c0611541200154140c1d45d420f214200c40c140310002e90444948a04a244500e021a022 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 288270746 1250 288269496 288269503
    0x20d022214011a0910091503270b0a02070611121f150507020a2d1a0703110705090106050705071505120c1c061401090501080126030307020a0506010602 67
    0xe285151101d60300b010715200400180e001400010f07006d21410500000d1146000c0d15860380602c580d460015a02825103444c024000301010750b0040303120745008210024007203844554000610940040e00d900c078038a40f0f00020504c840d00291071a8001c02d40b18031080c140501a4400e402d0141078011500c0030072460b007968440e078001c0c901024034400030158000e1040014281450004086000c1c2540d0740510f812454020111035581c418445118007508404040990040038481000400c2c0b410362601c61032140243c0302c0080403c5140316458400200400040019200007040d401c02945d44820140140e4003850080711070380680c10002074400c611801c601c1358240d83d502d0311894540d070800001b48010009040340b4450205008002d0000031810740580406203910000484604101440290302c0030182c2d11030405c55100000d00580c0da10a89080c1140c040042070130803080281c14200d0300401e81d007100030300c3c0d00c404000c00c03d10641c005500c80d485402802502d13006d90300c40d030701283c8 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 288271996 1250 288270746 288270779
    0x30f050903030624160209090304080d0503041401060806060a08031801140705011112010e1b0c03160c0f15080c070f1e030e0303090d020d02221401 65
    0x250303a0028400a40241041160b0a00b40d0103604131407400e94001c0318030a485034010b200301400e1030341020030110460401310300540d085503c040003036041c540303054189a500e140c507107250010000040049020000f9040d820034040f20080001d01035541c41d800701d00c0e603032203013114101d105104106002581000100403612b0681020540340720254400006603109200700c008141e903414200104004250300784159104c04001940c010381c1d841840301c20003010a410f8000703e100200050520000c0760071032243d516030001240c3c880361911a500030b12030071070107500440000f076581d1445110401c03121200031015101c034101c1801c0b071907480300e0108040d000c884a4103808a045240030030480003131040500441881907517001d040c0d0748142d95401c000b4040100c06070040b0030a00c80c810406422401c0804505c0042d401542424103140c00034081508400e0080e015089481d215001e40d103841a81d0303211081c0403c0910402c151004001e0010a010064035450310150800860303101d1524042c501d = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 288273246 1250 288271996 288272011
    0x70b070e010e13200310060201110921070f0803030115050703050409090203010902060d05090f0f070e09070510050406030c05040f090203070e040c020304030b0921181c03030f05 78
    0x11468588503800401000c80680d0030b198510400400b20a00041301c005520684802880d510f420340f4082010342554403200140603a0b44003488290b07050b86582d501c400380407600d044075085030b2000100b81400c1141341d40185c0946941c074480461040800001141210b8042841c004462040c0c0e1007100c0d10f00840c03c00600150741048100155200e0f0380081442c01e000400006400640d40e00203141c50340902c18800d03d0700e4a903002c00945160a00c8001d10554540b0050b04558036600d004030303120100303402182c501a100c400801c07174001e07041003814080c2401404010100f5a41c14000d800c58025214810001c3e042411559140b449003050390304442030482c10024660a012800c1c0c003079000289241308104030341c0b05620b0690340d5070244500400c2d01c2d802840da1182142000c680b002d80c005d0020900b03511404149005699100c6014445032030a00500e445034818050401846480780105602410350b0380f69064402100e90b20002aa22a80382084500b01181124040e01c1080300c40b034 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 288274496 1250 288273246 288273259
    0x270a032303011e050414040209060414190f051315060b0412080705010c0302041508010b0d05180601030303060608130f080c011409011b1b020f0f06070b070e010e 71
    0x411003541c401060210000f00da00115070283c2d00c0c2c002103000c481c42d01c000b6044800040d0144801d43c1030940c60f80e23800000c1540c0c20302c00c00111140d008080c4602070000041e20701e4600625000d03c038550302002e0101052082071000341451011034040100c490000d803204c0f41c140400c1011803400d40703d468102d0302c07602c090a0a0030319290001140d0300c003041060302c003d2030030458040020070a21900f06031006d00d440040c1c072107041003a01c1102c2c0c03040c04001414004908014000d00e03180000791103460000390408100c1e40e45031180600090520108401580b044034001310405800d90449010b4a00c0d48c1d580901b142e0391400c06510b440010301c8090080a640400f000128407001c004011540c581000820003004a82c020710000c074040301c60135140d940d100d00aa04840948011184680d040d160400c004c02c010a00012031172001ea03002482a0f800b1049180036446400c908045a200181450b84841160a0401707101c00120359103070004000910100c0d00f58011070b203e40700c2c07035006440c0 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 288275746 1250 288274496 288274499
    0x2120906130b1308030a051501140d0b0402041d04060b0a120219150903020a0e010303081305150405010c031103011805090f1c0e0103060e060405270a03230301 70
    0xd11220181c0504821010b07010f031880c07200461078220055000d00c201c04000540c0c0c0c0703401710915a6100c1c011415904109427641074024103100001034075030301c02030340c0c030002602243d080000b0000c1c03282d03a1104020080b4800044401003146200c544180c0c018013007406402036220030441c00900070300031401c00c7c0311440c00304009410004600c2204091001e180f0101685652412400c5044101d9840004950800c10f0045003080d0000b64014441522000c13030a50440c0d8015150390740042c201001c04105030200d1051140c200400c40824519288808940c2054280340d8040c00701a4504404a400e03d801031748169200c5044904850040c1d1688040705800341c2000040c21029000c240b043c815100b4044d1840006d0281c1c0e8861110600030800205101d01c0c043c12041044410385d0600d46411010040400c000010070740c000c00448001402c0ea64440c80450240c01c1d03100118040740c6070104403400b0010002d01c2c1a41c8600a03201c0d60141d2002c685080151800c4030099131000005000 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 288276996 1250 288275746 288275753
    0x1e030c06090201110105130314030127020708070b0109050f01031101030207052401030c0602010e0318130f0e0c0f1f050c0d03060603060501020a020f091012060212090613 75
    0x100404142c41450300f0342e400c00308822141d00390b46080e506001503050148441041540140046d0309006420400600319031405c4580c44505210000078584441300328401700c41e10446034115068194010300003038559840d81400c403644d480034000d07400c801c3e1903c00400c4036400403401d6141241c0c0c2c080c0c021042c0c2800350004501039044007000b1202c91152000301c69080c803841100d00d11b0202e800c54001c402d98550708040c0b00c03220459002105591500910031208a0040300b2230302030091460509500440c46800720303c43c00c240e4035042031043e28242c00b0345465040f6400100450482c4812680504041002c001c05c1510f03410145501502c000400b003002c00341c040c40b0344284801c034202241050000340c8090b040c160400f0540340002e984400a02c540b0f6058440c40015100a00c024804000280d000c240c11009198080c2d1103443e82c0c1e000640c0d888412002c10010740350000d10030005104070701d06803001c1c0d04001c101180d44001d28000861003c40058940d10072440410001c14141c42610b = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 288278246 1250 288276996 288277001
    0x1e04050a03140d050a020c15070f0c1104020304060e07050102010b010e0907021e06040302190203060a050c09060408011a060c071206020d1a1503071403060d06181e030c06 75
    0x80c0c481514007024030000d40f1840551050354810780e0f92500141c3e549403020480c1d41030101d540500d145031102c0707005204813035a00ca2904042c484a5080071a0701c4050360070031318030f04014449000d41c07180c0000100000c000c07040d00042500c02c0d46034200e681c4140c56800581c203032110b07007400f03c1c0081c01000c1d10040514140304066041001401a1802ca41c0520000c003480b81042101c107266a010388184420180e04010030b10340c0010a92056010711086c0d40005e0301c6000203810103c100380c841c2c0129603c2c0900600715403185200401d00c581e00c0d40e840d2852400780c00c00102c0500c0510243c0300400e82800c4c0801240e821840c004060100c003802d010251040203c5000d0640c0c1080d0300b0300550102500030300c40c0800300c00103a00a44d0008004c44100035102c2d00f44680c58403195010700034014400c1d040161a0002402080c07400e0303ca50303802001c95036001c0d000c400074241c80e062030301c02d650220740c9270302c041c2626005410001d100d0349812a500ad42d00040c440042c0050101c9034070380c002c1600356 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 288279496 1250 288278246 288278267
    0x30c0f010219180e070507050d0807050a050a030605030709060303091208040314010f0207060204140f0a140f0d060204150f0f03230403021023040305030402010909141e04050a03 78
    0x30040407001c0f038031085540d14800017103171154013160b400100e031418804c0800280040c02d0750f03450325440d94541100010009c1c003603000b800c01270020108a6014007402900a400600000f604481c40681e81e0350446018000600c803e4000c200c40510100341102044000e103019070300140c126190626580d02c00e11202162203108006543e61480d103406404513000070b0090314001d807800345c1c4840c206000090f00800c0340156611542c2d0050888525440b86641d0310221804111401c0c000300600c00030134821414145044d6000384c040003a0410400c031279018000340c9103d03c80000d840e070340506054440ba002d504852010954203102821032a200750031883c0000c0d0700720f111050000030000500c1c800401590120b025800288000360b0f520796034401d0315003101e451850900d505108040100c80d41c00c0282c40501082000030000d01507900a405800043c50b2070102007002000041e204141d100094813840c062402d8030a44110141000380381c6070040b500240070740f113048040e940075928420308 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 288280746 1250 288279496 288279527
    0x60903120403121a09070c0201080103170f16060e0a030915091e051e1309050111040f030b0c28090b0a02011d0607021c0903060905030c0f010219 64
    0xc01d09010f401d4458051002003050441540c980756012004006034000004e0907001041030322001c103400742c4c2c0c1c41140c060450b03070011400c0c000100041ca007441944120300c0b0900c130b240000a0501d8180c2a010340042c1080c0c055001000100341800d45a9260064181c0140000c0ca00784403c0c44041545400d00410003c42e0401805140e9104806c02c8210140d110005940082d640f00700f04901340b15a01c2021000021400b50050500c0c40c00502c1e0103000001c0010400e47d111501006c000b02507111081c0c2034a0310031010b4803143e490780c50154000b0030780021a55561580089000e0784a40815030b030b18240300c01d407034540d00d00540c1703000781005074000a01400c2142503900010481024030082011685076800881c074425440740c000e0040303468414180c1e00d41e000104100d90766601068405544502803111728404811a5003161750807450742014101d5441c11800e101045000001000048001c20607500300402c088007543c00c03030007402c04c3d511160a081d4144809a0b2140c0c0c42d080d0700881 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 288281996 1250 288280746 288280757
    0xa050f0412021c11070501050a0210150f0e071e080106030e1509010f0b1203041511070f06021e0d0e150a0522050a051c120503070f02060903120403 65
    0x1140441c0300103d0321150001e000724001ea1041e43c800d90080c03000b540600002c0c02d185141800d042002552104507450280301e0543e6a11501c400711500844680140380034409100403a4031001e080345640c00c16070314480420241c401e0608410903450040409143e99100c003641c0340e00e0800300394098038401500019a00504001a109140100c8594051052540006030350652000084112903c0c0c40f01d40303100382080862030030034000000032a026100c06401d08a01800406030036140311002030208010b0307002d0138502103207003d8001d102004a500d107500701c80b0a1818160950301050110a54019030782008944124103401a00c4000310b12201134101005421001c40d80c1689800034034158000420004d880b00c03140c64003220b0140102c507454000d0002d14036200008229428511845001e07510140d00320042902480d49402859082503034010042d006640091039540100d5070180803030504440811010700c0007c0b00d501c50a551002949806407002d805d45071110002e104404020 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 288283246 1250 288281996 288282013
    0x11d030a170a0e0a0f14030304090e1005061f0806030c1c02101706100302040302060703080103060515030a0215040807080a05011b0e100509180a050a050f041202 71
    0x100101c0c1e088580310540c00d40c141d11052050b40052201c4401c1c080c0754480c0e000381809100c0140700868030300481d044240c2280410030190003007401d50055030700005910b0314000b4240001c240c08905c1d40c2c10302106840400250307603480e0800c84500c17140031419041454005191200500440c6443c2e0003800c01800c440c1100700300e10015440701d00c841c0080e2202d01c3c81da030101d4118100340e65248079404980c10981040c0e00443d05845401c070f4000c01944c410000b0010050505000b58115009950050031407a5200250b09001d42455028401241c0c3e4a2500d00090302140001c0b2491a486d4401005041d5218894080003401010000090f42e806401c00c00040d85032030400c01c103030080c0032140c00380001030002e040c8103003150042d0840011100c60302085106450340310245040804049070881070304100c0c11003c0300c540c01281000da400041b07808409e5414144140c7c401c0c403582100c28284416510100b0500a951003036422004580605000c02c0009421001500000e44a0720440b1541e4 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 288284496 1250 288283246 288283253
    0x81314030f21090d02030316090509150a050307120f06020f030414010b041a130608060702070305071703030f040f060f141003080409090309050a091d0705011d030a 72
    0x1640141ca01c840080c21246a1000071421080055030282c120f4000c0d00035000505000781d00c0f0f01c4014800a03030012800d1702d031001580600c140601600c00035244080707515010b03544440d018038454445110340414a000202450000b40c01c00c26070341205072a60621503140e4543c0c6c0e040150703010031a845902889548000445031000d50f105a0180d00c0c003004120b26083c0310350841d0b45100705103014a0400780c9820300e80da94041001144ca40940e4140320304400031a29900422440e0030003840e43c000c50007030106035680099802c041da8084d000b5508129501e881440b240c041402c900310030f6401c00d10009003003411034030070154440e024502c0d440e038080d40b903664642104d1444411003035050b41c82d2401e0402061005e1025400881190550503a90543d160340340c10f8040c0380300b01944c540d02c6034414402c051182013031000070500907280c2110643c8410500c0b014020080c1030710550400d120242001640004078141110703010307140c000100e06942000c200c410000d20500c0d81500c07542d051003000 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 288285746 1250 288284496 288284527
    0x115180c11030a08220c060e0d050a030305010f0501090f050d0807050105040f1514040204020c0106050d08030601140a0c11060f2101050102010c02060f07090b0c0105010e060108131403 81
    0x7410f2103076940d5402460b111038016000303002c4204c49000591a10500c40001e9a002d030b000c5e00f65034043c24200f00c610514000034500e04110900101b02d4040d03a9840c00405401d60000ac1c1030317440181c1039404090b103131001181c43c0c1c0d0a512036141d2043c002c140404c5103040103440100c01c03a004403502c1c0d180c01e6441d162142522000d4904654201d103045c1090140300c6000c501c56192100b2035400c0c4035044003403001d040080000380010748030b594001030200341e4020962010f4005c140c00741032201044260300f001055078008a40648c00f15918100e8000ca1168080807141030300e0142d00ca00890200700d46030600400c3c4800ea6064120004011070300c048481d450107400b52403000c2d4003058100500c2c02c0708010006041e44468150782c108080300c0c01b03054001c610113900c004c007184044210740d41c41504507139030760f20740d44908903444d000100c2c07045024064010b103059a42914000d2025104d001c01120f4521341250264030180c0b60203243d80015070700c012050040c200c40422203003818002407480030b5 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 288286996 1250 288285746 288285757
    0x30a0902030a02031f1d030307030c051e0d05070e0a06140723070905060a0b07020d080301060c031713200901090c0e040204030f14010e030307030209030115180c1103 73
    0x2803540b1111003034505000340c01034000000705014001b020712400700303080b581c038000030f0b0500041c1a2242c0300c02c0308591003034041e01e45442c441c1e9680001c020701d00125440b1603100d072034200581790600e8005415140102402d82400e100a00b902d00f80303919101088601005088034044204010008000403074103040c2c000342c5148507035600c00728090091140350715119850740600403c41c01c0204010b03503a900c0008800407a0442c44889a030f4502500c00140101c1c02403800414001c804400070881662204580c000c83d442500c034800c2510f8900549180c94030100da1002c40100100f0342480054800d03000d400d103680c0f8801c0d1418070700c540100060701e8050245c1240ca061f60380c8004100c51194001c01000040c601580d0442c038260558840d816181c03403900001d81100211035104000c800254481282d140709101540e4803030500f00d5000b4040c0d4444000c05201c0c0d801c3c4800703e1500107411a125085481000c00403901009403405400501381800d2443e013801640010134204400034001444c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 288288246 1250 288286996 288287023
    0x60b1e0c072c040b06010c020a0509010609061b20010c050109030e0307090e03041406120a09021002012d0605030a0812070801061d040603140a0b06040b0105030a0902030a0203 77
    0x510030b00d0700200a105107080c0c1e0030b03103201c280480184004190300c4031400d82c01c1002031814840000150000c611596881e030320042d082085040000740c1c203540042c0d04d4041c0c034050f90711580c40d0a0b00b40005e001b15048064003030011079843c0c0710484540301001d01c41c0c1c070b200c1042c14054241c00d43c41c0c43d4207007114007281e002e8000c1003040c190003900349024018a00500b805640811900844805a9540c0c0c000e50080300b4107601180c2070315000d95545800da5002e0340d240360746070b0980e00c1c2c40c5950001500401001301d003d00e6000305240c96050060080c41c003046906500e5128100d0080c0c1e02e030420010440380c02c000d1070b40d1003101140d141c4045c000d10815a01031400580d46030b00c40c9454411071b4074000c00b0041045006401032102c694080040c0b8501d80030300c400d60184410b0600081c1c01000a6440200901c0044041561310000440d0301c00206001300e0b4170000c00d54840091000ba6804043c005000403802c0000606400082c0d018541090015080313500520450b40807030b04d859020540c49 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 288289496 1250 288288246 288288269
    0xa0b0402031608070f08150301140901020405010923212e090803040b0405031620010219020904170c06011e1203050901030908040b07020310060b1e0c07 67
    0x2c0160b41124189402c01c4240c9030031140c200c40703441d00a01d04c0001412001d210740c501031541d0b2441e0b6094025900c000944080c00340c26041100c06103000b0340c8244103007400314410380400182038080142c07225002440c402c070100c00710002d008000c3c8020780c800502000c5442a0301e1100300320000c20102803000c243c03c0f00c0b4840030040312000c40c0b0141c400d00b50004254249501e06000544903020703203401a84c031814807171440e01c480c03405500b18010705801d0074420381605590000d028001c034105803c1c0750100008502020040700480e280e20240078601390810710b4100560060a2030002940e01074001c01e042d20013500500d1900c4445c2d441404450741c9030340604018004000c440c0340780300d101c405412500b8041440d1000010501032010000303420b115011034403110340e0740139401a0510580c460b0500b81d8454a0700d001c2c10040d00078080580c0a84124584008014000d108140a8603101030120342081c0c40300301622456041c0720305c119004030051281c0307800b40c501044a80068015000031 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 288290746 1250 288289496 288289531
    0x100c1d010309060f02181e0607141915060b19020102040803030f061206011401030509190503041404061d04020d0f0c0302150726040308070c0515041d0a0b040203 71
    0xa0312400d00098819110b80c1c0b45800e48032103054070602190340d640702035403c8c0783c031111142407000b4800c03001140340b00140650105003407103c1f002428880428416140a0716400c04003036800c0440c3d015010301c10924408109541c2c04d0b075911194600302510520000d0301d490786882c0460308540081e80d080049004100130b00140d46003040989510f080c004009025541c5010f115510300203120300780506150360f8601152254806000c8404007484145402160150b50b00d0700030740c2d0350300c2031003101c0c000180398640340030f6450a07000d20001c6403600001e08a06c803a03003c22614020070050800c0380e01c44600c8052400040c905510665214043c106180e01c0a11b540140060452404500355602c18100510300008600045000c103006407544008030700a22501c614603140f09981010748150800f00e08002045800c0f801002030302c02c2540e080405035441c80c41c400c21030190340680141c6003106030303a0341010400350401550101b030a50005c19545840004503003280d0040e04e450340348076090b211 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 288291996 1250 288290746 288290767
    0xe061e040f05030609120d090209130501051810050c120a0c140708030f0907090e0606040608070303080a05060109050a08030324060d090807020a17100c1d010309060f02 74
    0x1220042ca000e501800c0c052529031003c94840400300c080740d21650010072410075a40440d40714105042d40a060007045080c1504105c1d40f00300c20070000c5070305600b0840090a0702c1e01100c04840f46c4007014006000c07041202c0c0549002d01802001d070065144144a0f08002010000e5000d00441c0d10800c001007000d5803c400801c030143d151840c0103030640400c052400622104112640b040e0424600112503e6480c001814a2043e61140e8812402c0010103011410045100da00030030040704c2c100907031607440c4095a26404280b20240c040745030035000039001d00d42900210f90005051404030081500c580c0040e545030240c3c2c10a505a80c004010869041540d100450080d40003c65001e0070b011040005100f62140814020b0b925884010301010404144184c072852940109001542600c4803840c000410a1070012450352145801c603446469680c8600700783d000c515036a1010201c28640019042c051404466041650780d540403808204280315402203480400000750f07480752103aa = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 288293246 1250 288291996 288292019
    0xf03060605030105060702011110050a02040504060f0e070c140303010b040e2a070314040b030f01121203090201020f07060e0135061908031c140105010e061e04 70
    0x400080c103000c0200700600059681c0e20503280d65603824601010b8405601070701c58241000070b0845503029050100780880190a9000350060ba0b9054600b08800ca0341c038000d0032483d0420384194040c1100d92004203022a00c01c40303103007249a0140d81c0c041100d0003c0f26146182d0b6009a010041290780030600b44803213400c010209801020702480f00c0d4000c031031045100c004080c1440107000c0c1040c0040c1c81020107000341d09100801c01c070003d425032a940d584485a646078011902c40389104251400822003011300c03a0000c25403901308034079220340400742d44140e00138400510103a0551090040301d2440b00b0007000410b004c0d0005948280c00d1040c0e00b8000351904000f58a411443c00540161100030038801c00c4007642c03c809400e0103400e685400003c90031a940d1f012030000d02406103200400e44080020050a2074420221000f5049568a4007442201c1410400702c46800340c51b401005951701c00c5510218410f0010700c114504500407a440017008540b84003c02c0c0d045010030300300320001ca41b8 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 288294496 1250 288293246 288293249
    0x60402040605010e0f0108190501090b270a0c2d020607020307210306030f0c0f0e060303090f040b03011a100201061505070c0506040914090f03040b07020d0b04030f0306 74
    0xa00b01390256035070210000d40d1421840c0302140c10481600c0003c0d00b240040440d02143c0c61488200304899610341c01513102604013400058021300c2c0c40e0f505040c0c02c60340c12042d048005040c4615403042e481d069035620142208907103010401500490140e4102c81039480640192024400b80040d030712000d00190404400801107029504288280740102c0d0a03030b45141c8058030b685428440010301c01d00190010007071500040d00d801c01074101101004502030420082d40c1c1c1e28014510180c1d0303034183c14810110100c4101f41c05401c10f0040b80b103907080500c11030002410051002c6040c54805002c40d0855068020159102c07403c4072241c40c0a041c5880d0456041f0128402804800d0511100d0405030029046c0103003000303000102e450600101b40d1021001e48402070103103903a40c0d40c034210f01300900812261005801b02d140302041b07108030700098071840b0103a80c102550030545080001b00c2250091170060b6008158903103214001524032030098401c0d4442e845071441a020210014115483c6 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 288295746 1250 288294496 288294499
    0x20601031e080432060f03060a0305030f180406030812040f060e0309040b100e010f0e0907090e0a151e090606021e0106030506010e0c070501050f010617060609041508060702060402040605 82
    0x5009000745a101c5d03004403a20741d50111285c5d9a20740316800410816aa0341e4006400c500000c94885d4916405c1002000d09c035a110075040f00b041e4200c003c010884815102c0141a4641040280c400c0d052003107045501c58007d45111041d65810b88501c0140d0b41c0b0399988400e10303000010300c0d194604d0f1910468518813002e41e04003510490110018214050708054541400f6810381c044600e140305070300e003140094019184054608201c035001d0324400680c0280d02c0f4018030708001900b2001c180c4a50710701321a0295802101a2402d9000000441e03040711140d180b003a260b201080b508000d000d1840140601d0f8010b00c01d03818192403180400303108245c41d52007641405020404106c00040e041e05580e801d452400c3c2c1521246901400c51059100081c4103509100070030400030300c01e00d1214106d44140d2145202214090103d82c1759942c100c900e9079002d2070030f01c1480396a0420394402e01070003402c0e182c80004983c4884115190480440e800b8005030700c1901000218206400f1b044000c140 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 288296996 1250 288295746 288295829
    0x721030329100827120a170108060907090b011803050606090c03010e0a0209121606081303090902070f1401020703090e0c0d0b0f0a0e06030f030a020601031e0804 71
    0x51031260081c02c040c00d032940002c42e20881308031984001e8140180d13181c528100c00c465548880111026142500b030702c0341000900006000000c59842c04100207108a06c44805000401e0411611314000c0c00621140c50401603900f040040f80c007508000342001d14000c0b801800380346007240c2040f54800b4003c0c10004004003c0c001000344041341c40342660419050348016860742c90810114502000800c42c16226108020303101ca940c0184040321404d580b441d9581040558400d00c5490317600ca007001c00100040c001c0c520030884d40c03000794090000d091140d6814000c0806c2030f210204d140c40c810300c614581340d500058480416070060210002001c0046100103d841d01c020b840c3c6c07443c01030340400d001d96510780c03500060a0b0b4485445140ca0740000341280380d401d49403014014111000c907141402407040d007014010400d40002664a0b150303056000b81156805c503918480d0280355000e007400c16840300051500002c1804d400b034005000800040c8440d00306412030402c08060b4540c001009a0 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 288298246 1250 288296996 288297001
    0x3010305012d1109061c060b0a0e0111070503060903030a1802060a0f0c14070e060402030f06010c05030c01050c0307170903091519020d0f0207210303291008 69
    0x10307020b680703024011688900c0021118292500000a4130440300003c1c4c2c00000011420004100c41001c2003100c0e503044401c211468581549160501c25695410040703035000c01e06807401d612074450311385020072032019100030320f80d1100428a01003098502080c0d0341c10200030000d5444203803144003c2c007807a201c0014074520341c41c0c01017506440361442c81d40800460203141c840c070038015004140c82c0c95015202c00c0d684808a1040f5450b08642d000c1c40e41103016500100303a1138605402075034040c44801c49048030640304c9000540324032039a054100c41d1404148500103002c01c013803146034400d140c426201d65491410740d0000707240184007014100d0740a040024044017070000000d40358214402d8071510950707481c403114410540076114a20301c02160708031a0031485a03000c100712140c0901d98860150500c18a402661550081d02452611000d005141c550340c01c03800802020b83c50280c10f0009101c0a040301400d41c81c5840c03446021014003111010780c0c00e0910080ca2650540d45180c8800340c1d0 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 288299496 1250 288298246 288298301
    0x13091e03080a020c160b0310050109031203050603100204030506060901060c030801170106050424050607030815040914070e070203090916030b030304060e0a0f030803190608120301030501 82
    0x100000e0702e08005282e010601c5210804100203040d10b610031080864038032607480007030543c150310440d00d000101440400000d5a54010074050055991120f003605545401a0084004000040c18075516119111484401030001c0c4010b00155010300042c140c1031601409108105c40306910860030040304111100100b54003030203043c1524500c2c40264807107000c00d050309024051580200350302c1841e00c0341c00081c454908200810700845403800280f22641da10401032540200640a40401d0000000801c4c00380302050f03180040c080240002140e50b103645a9011360100c0b204005080da0044005004500d080042e0300e03401140c47c4004c0d481c0100d01d601142c400a0090300b0100001034402a400c5410b000382c100d40c0100d1000750403030342c03030b9590381c50001c0450010303050070fa00460454401044403d48505d095040c4d81d00820024a55112504600c44206980840b0000c0c40c0d07440d42e000c6801c00041c803110810002c1d01c52480c1e100c1d4150305100707084400c0c510a0400146114000300350b074 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 288300746 1250 288299496 288299507
    0x3060606051c0e030c070e09120c12030402130501060302120a020306030712080408030a080a0b03070302090c07140708012310030b041e06021b0604080d09030c0213091e03 75
    0x120b18801d000450300307103c140180c3e465401014000d05041c000e2680114001d0803500034903104080c0101144e900e1b915200c500722180c4502c41f80a0847d2b0407030341303151111039070b43c500440e00300d84090b200b1250014281c4007241103960a801a0001030740001e4030f000c0a0300480e821342e42244000d0821465401c1490009554507600d00c100161318402c5040c2c1014400b0305010355004042d0001500d40d22514144010320045084810480d20361400181510a080014404040da5400f030301c91180d50712000303c00c1d40030790451102150130074070000c04204550020700000000300b01c2e860000c603203401f428008001040c401150050b140d121a0101701c9518652004241125008902c00303443ea180c0d4140020f04414a0f00d01c1e91405940359110f204001d001c0c0e004007290104175080c43c0d100120300701403d45690064034040c2820b1003e11034108960a0340c0d0081059074401d00b081c1c0021130303107a408034040c401d0440081d6002a84c424440040c403040c14880c1c07001201081600c0c0c451503156502415 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 288301996 1250 288300746 288300787
    0x9030301050f010e0307031112030304230c040c02100b0d080304290c030a1a100509190e04060b060a050a1b080705011b0507020a0509090a08040b040306060605 70
    0x2150104107180d4010303134001c415402c0c0d404000b8040c0c80c01183c8034202612408610300e6118000c2038075062602c4158408000d4a004950101c540c1d0340c8680005101e14501e0101282c5940074015005509420b80c0c85110354108858290060111445269503040131180e220308072502807492a4024400142030101301c0e54090380c030100522507492070208200d101c00c1d01d00111140c0c890b42005000b0000b0b04040a184644103441080c40b01070080d0303562400600d09951415001403c0701c81241b031403402000a004451006410321180e01c0000240f40580740050340030039284140c2d80203100034880c850254002e40c0100399400d500c7d28801410081c000e00c071b1306615070204010070f42803000b80c0181000c800c0c1c1c0940c1180b151038a0351103504210b80203040340140b4904d125070181c02003640301c0c0180103603031035250001c0034820341d18a0281803083c851401003941442d03020720085200022030220162014081c41c510503620b490a5180c01d10454500c0c1c0c005006011042c4504d111000341c8010303e00 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 288303246 1250 288301996 288301999
    0x5030a0b0a0203040c03170702100327060f0216060b0a12141002070503030f0603011a0d1a01080f151003140c03060a0b24070305160c090207060b04050903030105 71
    0x10382d070343d1303542c1441c04401c5803541005104003044c229029590388040302510f2064000c44900e21103000d040c0f415001c4859004413040d248031041210050486002e4012441d2409840081100b4003140c4400d4201c6e40425924248400001c2325103040c40090310840c220850180e80050100b82001200e009007140c01c0c1004120001c1082d20a401d0201806840307040d00411000b07640318040c51421949940046415080b003150310f10000700c2d1b40c40c0c14010820440c1c40303c2400d80010b500d590070b2189440691a0a9a100312024840c8043e054060881750007062003002402441580000340c50a012100000e50784a08040c010b02141d031a00c401c2c2c0c2d00450b6400100b20060012500f200c0d410039204882840d40b5008800c100003001685421010964170201c070b050841c2c54905041862041c56030300c403040034200a000803800680110001c05540300c0060045496007aa17136985040c1307140b0340e002036020903004070b44a0104542030080c0381014504450511140c502100140e55174001482200d = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 288304496 1250 288303246 288303251
    0x1203210f100b0f0f0a27050a0b0a0c0506040b0601080a1a0d030e13020c012a26010609030c2c0c0904060902070302061e07080c09040914060105030a0b0a 67
    0x204004080c400413280740c030140c154142e40f0340c0f611480162110f084142413240b01c07640c9005960848001010140590f4030003446031012504000d9015000d8101303182840030700c424500c004000c40c1c020003090b072155100703003140034041c035114000400c09031014040c020082e00f00f03002070394a541c0380301c0c081014070400d1b900c010240c0b50906045841d60803062540d90030841610030b041c40040940c00410091070b006001b402500c4015030a0882e5801040c07503918000700454042074424070032140d580c850340c0041030303a2074a1000103170070340191a02030b881a0302103400b5480030030411141d900c000b0001e07c421820600300c005038202c138441c0d40452042250040c100040002c00040c0d0b02815180300107400740082082d00c0e00c0d81c8802009511564094015105d0100000c84290304030b03440c00e41341e1001003114025901c5041c0c054400460103486034460010034448400d041d103452080c82d0f112402187c41496103101c041c1414108401a04014000d070408286c2c03001080454000784d4122940c441d00 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 288305746 1250 288304496 288304507
    0x20a020f0409080a080a0b0a0b0702040209060702090c0d0c0c1a2203020313141e01030618090210050a0203040b0f0724060603140f061203210f100b 65
    0x5000b0810990000d0800d600410040120343e403060985109003811202008448000c0c030420104a0303103440f403200c010608100700c50050030160041d100b80d150207041e03982003605581c001500c12000316800c000301c1d000461200c032854401d0081e100d902c0f5160800304041c003601d44a850440711110740010001c8551400300c2d40d10403912000c6050480c45103400004a945880c0094503540130920b25180250b16070b00215191034203078400c001c028001400c009455088100491a4982003040b240c140340e6100300025890b40e00c0c1d6118405c290441d000044d840590344100a0000c407000880030800030241f04078800d05800204982c00c2c0c482d44903a1a40316144041921918403c505006080c080503074961034102d0484240c1002003031526400b8081e080c0c9075402141201c5070a5071b94242c070720410000c40e1054543c001050b0b00500040c0c00c007450119056019451076010000c0b6504900c4288800c1c0410300b180c1482c0c1d60443c40e042210221130810300071030302410036940159030320000e00050 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 288306996 1250 288305746 288305749
    0x203060d1e0203010c0e040f02030c0403290f0402090a0e060604020706090c060201020c060a2a121104050a090902030a0b0c04030b0108010f0c1701030308071407050f0f060106020a020f 81
    0x8150300d107164001c0c004d20000c911010b004215006d0041c100c0d000e2801c1c10042c4901c6035040c0203403440b4040c0e01d16a1401d0900d1502c4a1812418030310310014107844415000d80102c14800d205807152130145040200c80c20a44184028281c008200744003481c0741420b12642908049074450300101c04403005a152081030422070020290f1400040088030080000102660103402502c0c4540c29442034032140e541741c40c0c4400554040035400f0490308040b034107640340d022420200c0032846001d0b142c330054413030044e5911411034130054104550344d40f001c9400c01861400114542c05071401d188144154015980400d64811500e44005d044c480100d000034200c03a0890103903001540c004413144440e50f034a6100380d000301103421100c1699410502010300c800d0185488040d5854440c407102e030103a295407811a080440585120200040342c40c090380d4200d000b4018246941c0140041c00c0003000b07000341145021403410780091a5040380004001903500442c807242c03500e0701642c1c0031308803200c0c0070b0 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 288308246 1250 288306996 288307043
    0x1b020d080708090c1e01091e0510091707030c05041503060b1c0b0105180405030d0b01090902070c050f040b0a06032c0a02010e01081501110109060504030203030709090203060d 77
    0x21501c51700850403450016140c40d03600c40944207014281c840101c1c05403a00f40951038089044160200600094001c220030304080915041c07200707881c606100510380310107400242d1b041041c4020120361081101348144003808210038010302e07044800700184449121000c500100034400602102da49014500140e11002105c0c022003100380f0720302128082c40c1c03601c030351084401c0c09064001c40960542d407682c81d5483c082640504d030008029803c1c8020b444400c0003400300e90381d0590402c020114005456030560001d0703c10079119809220085003000700b401480e001703004099102e14106004130f006601c80c404824291181c529012603030304281c1c8170050500f11011440703100d008020161740118540480c042001c24400d0f43c8040f11410458011100c01c0700588021104c0241d51901010b070307600405202908000030307000030516000c90740300e14044981c201d0f015005a04000b0030031203400da04c044c58202502e401c50046042d4100305002c14640303219040006c24551403000f404036842c2d41c84 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 288309352 1106 288308246 288308263
    0x2060609040206090d082704020901090b0304061107290405030313050a1a01051306080a0209040201030b040e010f0b010201020403050a081b101b020d08070809 70
    0x5408100c0e03d0740c00248001c3c0e20040c003070050000540180050501960041001d11409083d240c112a0680020b41c3e0144601d01c1080640c4090b030b00000b190b410f454848000d0303a01c0351350b103180c6074006120091804042180c0401c10f2010820b1940c038132244d61448401800d215840a840c04081c4501500c0092840d08148005419814469a03440aa90050048a10303990050702c5c0c0d0704ca1104d04452181c80e8071180d034014041410025591401d00c4980c00c0c0030800103141c80e0826449000c480d000910400b05003000c901907a101e038000303039010700008008200800000704864000d000417a03001e40d405050401002041d0f0040c03081d43c085980007800351200350b0066803100e41c15403040ca41522040c00d01c06d0030ba10040000c000e100d0f40c0149103180000c40c2c0d24100c280305003002c0c1400744001103512840c03196114075440703003241c0d40003442410b02100c00c0c2c0301c4101941c2805a10f = true := by decide +kernel

theorem cover : BRFrame.Cov 288129496 288309352 := by
  have h0 := BRFrame.cov_init 288129496
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288129496 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288129496 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288129496 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288129496 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288129496 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288129496 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288129496 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288129496 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288129496 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288129496 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288129496 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288129496 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288129496 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288129496 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288129496 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288129496 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288129496 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288129496 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288129496 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288129496 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288129496 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288129496 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288129496 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288129496 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288129496 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288129496 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288129496 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288129496 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288129496 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288129496 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288129496 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288129496 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288129496 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288129496 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288129496 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288129496 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288129496 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288129496 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288129496 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288129496 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288129496 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288129496 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288129496 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288129496 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288129496 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288129496 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288129496 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288129496 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288129496 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288129496 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288129496 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288129496 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288129496 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288129496 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288129496 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288129496 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288129496 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288129496 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288129496 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288129496 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288129496 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288129496 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288129496 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288129496 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288129496 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288129496 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288129496 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288129496 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288129496 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288129496 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288129496 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288129496 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288129496 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288129496 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288129496 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288129496 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288129496 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288129496 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288129496 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288129496 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288129496 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288129496 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288129496 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288129496 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288129496 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288129496 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288129496 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288129496 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288129496 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288129496 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288129496 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288129496 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288129496 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288129496 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288129496 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288129496 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288129496 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288129496 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288129496 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288129496 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288129496 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288129496 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288129496 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288129496 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288129496 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288129496 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288129496 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288129496 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288129496 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288129496 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288129496 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288129496 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288129496 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288129496 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288129496 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288129496 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288129496 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288129496 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288129496 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288129496 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288129496 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288129496 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288129496 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288129496 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288129496 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288129496 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288129496 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288129496 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288129496 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288129496 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288129496 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288129496 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288129496 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288129496 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288129496 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288129496 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288129496 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288129496 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288129496 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288129496 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288129496 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288129496 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288129496 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 288129496 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 288129496 ≤ n) (h2 : n < 288309352) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
