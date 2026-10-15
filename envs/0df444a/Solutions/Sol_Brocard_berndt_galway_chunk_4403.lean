-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4403
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:30:01.722522+00:00
-- url     : https://prove2.me/submissions/afdd4b44-8eb0-4724-a8ef-ca3044717fa0

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 791726618 ≤ n < 791906474 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 791727868 1250 791726618 791726627
    0x110303060612090a02030a03020a0507060c02130f09060213080c04020a0509060d0e1006030605100608011701140414071d0112081c0b12030c0c010323011d0702060403 73
    0x2881c4100c0b12492140e07102c030071007113003050042c80d00290702d07200742c1d0018801c15030042600b100c6540540b060ba01f80c0d42e511042520b82c010844002540b1110034000c9800144d00e66129003442000510001203014860752140203c1c4d020040320b110056a105d000c2010200c1080002e00b0410180d0301503040c803c00e0032010b44940a0284102d100d4903000c9915003000c0303002c0c0d002c030b4521034884046950443c5071110b44002860640010341c0c0395800c05c0c0015054544124084048558907680c01d00603a21700780d513040e0544100c910841655403500c4110004200c0c041009d0302580c0a0341052207524900500a480d18089030300140300c1b0b001501d00d04481c04420300c90f1504444404041c0458080c3ca80b5050b492445074080c14075200b6425800f40c501e28445600055030b012094510010041500742d1050b81d078002d40780780d0f0119601804107141d95501c82d80024001640c0c0341e031402c450202484c4c824603ca0401d0f00032643c1c8001c41c418820000790f4a900c0c5540000d0340e070014102c9402c10707450050 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 791729118 1250 791727868 791727877
    0xc0f040216060504080706020a09090b04020a080105190308030108060618090607050d092012070302091b070b0f040605060a08191113020c060c030c0d0f021c0b011103030606 76
    0x50038941d4880000b000d00c2203102c100c81b0610b034440350443d82c1c1d82000c0300c0a07040080c18094840300ea49030402c07403130f000d090602c00c40da60700703129403a0003805a01c0c0904001d102e4200c0603004820443d00d01c400400201a030018501074aa1140904240d00d080070503c240002d0352007800d929803404c00b0900c11218008a1600d800c4021460304a0751040030726040400b0342004a4001c180101c0e100c072500d01000b03242e84416070b209007254181044002960310030390310701072404040d610407200b801084c80e01052034031001d03840d14070340041400c15845444481e0300402c03c942075022072443c0b0b4204010070480d4822150701803030841c2d1030100e1a0424a40325a80c2401c0e0101c83d000003410075801c020321002000c49018030b440104000c04a01d040ba4590010b50451100030f8010f12030b08001c102100380e40c9050301e128610360b0300424148084000c03030380090200311011840c020307400c014070400429244011007080403206800b05d1000c800c07034001428180380301714203100e6410510600c03102e0b6503030104a4 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 791730368 1250 791729118 791729123
    0x604060308040b070219060f020606060c0c04090f021018081203010306020a02010906051503071502030313080405040f0b030d0801050f040c0306082409010605030706121401080c0f040216 82
    0x3071380301e158034808110050180203d40c60800c0e078440000a00942c40040443c0f80b00042c0d0030f0b91003c0e203900c003c1c00460300132604040242e400c242c0302d00b003050509034413048525004040e03400000b000c1d9000305a540c2c600c007542c0d1700001d21a00000c0444607460704042c0c010103c0c5070040c600f085120740e0701d2402e07000c180401080c55400041c0648101c2c801d4114007115500b080041107035007072820388040c490f0403080b030890003402080f41c00103240b1200002100d91202c250050740c91a0b40d90344411010ba100004100c0b241c9100341700114064031170b8812200c4501c1040c2002404e041c24404140ca001c0e600941d0b0403c01101e54014030403510390008160040000765800f2604c625082005e13070240440d40c106161511840310101000e0b12030184559109410600152443e21076810181c240e504502400350503903c05030080103d207100d6404030006d40c10010002074070482403c90a050381d20280d110a031580e020782c940c81c04e1490122422144008126000c40c5030003014901050040d1070600301 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 791731618 1250 791730368 791730389
    0x11a0313080705160501030e03120c090d1a0403031109010e0f03010906240e04110907052701020118111002030c0a08030106020c180411120d0203070209060406030804 73
    0x388081000c490191802a076020050364440c0b0368003555034442d001c4c24422240040d042c00c200441c0c40381c001c0100c0d400031207451941c255580c1ea5502911540d40038211903904500040d42001c0810807042c00c001200d031100c00030198034101810000c040d81c41c03a28100c07000f07080404c00078181e43e03040140c0c028050b600383d40342083d440d00c0b6000a8010803584070b010300020305110002403402d50f469903003054080c102035032079000b50311140c0b48400020700701d034004c00e042045e507840240c502e00b01040e283c0c0283e56150403032502926031310b0604450740381040b101201003c88101c5081c1e680a00070441e95400e4110601080c08035900e9100040c0a01c0140500a180c0004544090352081c002c4419540c101403c48040c00c11034540040c076680248a4400140075403071484d40c1d6403030801e40d108006a0114400207181c1ca07140c0310461003030009012168800151032490002880500c1141814129074002d19141c000500511200340402001c07a8880c038544801840040c4400c4160317410b80300030145 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 791732868 1250 791731618 791731651
    0x30106021e1e030702091f120204020403020a0e270c1e060423040603121b02120a0605010902030403020a140705091914150d0c050607030215011a03 65
    0x720905000c000d079481030400d0482090b46400c0314000000b000e515100382c9182c00c40b5900c0905c0b43c03008806401c1213420b4900914820440c00801d140c2a95203940001c0c0014649503072640040c1018003160300c180b030000340070000c004030701c2203414450044580254810800ea486070340e07103a03142c00048083c1841403200c400c010304103400002c10070041000141c4001e83d21520b44481002d0210721507040d40b0f83d104040c0031300015080500480701102d81c869280c4024009046040c0c0e410301e075650540c182030902d08007c130090b07a40c0d00150b102e00413514010705010246401c11900f40c801c16004508828010814000000e500145540c01c5a41007420b460b01d000a00e241c80f418100598401c1b50300402c01000d101005542d1200719140100c1d22104001c0b622913180d16201030710088a1003610000010a400d2440c00d2100b1014601031040d80074030000f0351650009030750360700801c3c0c0913001a44111603d280c02002003c0203030140900c50126005501c591107024018072000f840101400c803d0b00703 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 791734118 1250 791732868 791732923
    0x1c030b03010c1e2a0c0b0a02120c03091e0112140a0e0304170d0e04090b0402150417160e040f15060909030c050d03110d0b010e0a08150c03010602 64
    0x4c00e07804070b00c01c01a02c0002c40455200300c071001500103050a581d068420540060721408141c200c41c0b080c14140c0240111911401841e81590800908a91180010486140182d460030076031410341c500c04016840c414544e030700051665002c0c1d07100000c0c20f880d00401192410150310116480741e0401404500820b1040d512800d5010301e038040000c403000c2e4000c0c4620100081408080b442040d074800040b210458100410b9a6404070040d0403444890003042c050305080980011214400e501c1d145495507a018400c01c0c00004c034085045a0000001d001c49915460380e01002003101071031040050500d07849a507001d40d10040028241d010505100325541710f903400440c002c00c000f000401c8001c00c6410050314500c80d01d4800c40381405181c8000c2141d9010340301740e046ca1641c1c0550300341803001031000c840040c0041d1510038103201d51000702c01740941c0ea8404280241c60b00201428112a036401031540c079190203401c145001c9814001841900d0740050904280b0010700c1c2c08080449112 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 791735368 1250 791734118 791734127
    0x140706120b01021c09030b0f010b0a140f0f0408013c0605060c1f0c0c080711060301170c040209010f0c021906020708120a090b07060e1c030b03010c1e 66
    0x420080413075580920790410340342e0004ca010044900a041010130355540121104a0801c00d0241450090061110f0310b100f9220b0100039043d04400480b06140000c100003030074054021801807004614005024461804d0038003c03103810b1820302e041d29048012500101095020410014101900380b9803140c21401d019002000100740c0a06150b40d030f41d4003281f560b1703282c0342c01c0594022000280e1031210a1101540304480c0b1540300366403505d84008441d41c0d06e4007a0350060000f550340ca982810503100e20750b10380300194000c04204a1840141c0c4210345040d041054004596124030b10600c0105200d9822141c039041d69040c07498020321241092000070156035104003e0405100146d40210300c030f6400140b62001d44804600b2126400c02c051010600c80c8103034000350002070170b20031301002000f0048000d00319051080201165468450000602d85011240102c24404a26035400101901441400138101041e4002c1c499003140740c001900c0c9204602001c80440c070702100b101440c0303224 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 791736618 1250 791735368 791735383
    0x40609080409020a081b0306010518040507030b03070b040b09060a110111040914040c090513050307031706061603050f0c0303010f0e0609160f050408031303140706120b0102 76
    0xa860381d48640c0c6a0410301d00030f41040d6101c102003099103000c1080079034810035680e10501400786c4c4a16654400c030045506030002292400104e2000f005401d55a80714010b280c403810443e900014411200b80805141080383c0e0f022f500c40020070003080c80303903494240844100c44400d0304d103107556007440b070404c580d20480d850f80d940c11540703480d468030403a095840041c0304480501e2001e0140304104c650814400206440051081c68012010010380509401840e840640711151605c074110f141c49403070071035000080440029044204d5284031010424034550007860aa4505081201180440a0340c4860040240610901007032151660701c1e000200c0e01c0029001c010b0f00e0720395a4544040f03542a5150044410b2503242100060340b9003410b05805100e404250254645050700220554103000018420810801c0400000c80d80d40700400003400c00c901e030307801c02c8000507144d4100514841101c171644250f50304600010005141d0011484540078041100002c4694007040184d290406 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 791737868 1250 791736618 791736623
    0xf16021b010509060706050103110307051315030c0306020d0501061d013209030c01020606010203030703180c081005060102010c0927050708041b0e0c0a170c041d0c12040609 76
    0x40045e0850401c55960461390403280304000d45803001d0b00c2070342019240c18140c001d0b80d13001134000c0d21840700010b03241c0141010742c0f940c41c090902070382c41c3d4607280c018004a4106940352a000203210025003090305c58203006003d03a2030f10485030300ea0540003400b43e1a4800c4042c3c1049440ca45051494002000d58241440b113900400b80d002d0f00e41c4039080d003d40012007094460701030010030350015400440d020781300307000580c0594559581e40000354010441404046a215541c0d10303d6400a004001d40c000508000e400034401d042c00c2001d034500f0740340700a1100d811641030600b00c00482d9041302140003602c000c1c40150043d05003c0c00002c689080e48040180f5542c01e01080c403600700d810915003401503009181540c0e05401d801000b42801c49a4868010f40c0380c00380d40000c3c400c5039490b029121320701040c0b50030021185000c0360404860740903a40c4201c0d240d000582084503560002650801c5208500d1501580c600b100244c07600780103090034000e50560020020341040311991102e02c0e8107a = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 791739118 1250 791737868 791737879
    0xa09090204080a1502030402060304020909011e05160e030d03110c0a0305040312081303200607030527030d0e1501030f020a0b031b180301140f16021b010509 69
    0x9550b0101c00355600c0c40010103640a4010b008880340d001424001c45e840745401a01c2c0c0f603d5500c8980c00d0161074070004001c1c0085540c0d8100e240e800c80045078507510300005207107000c0343d43d00b02018802003c1c02c036210101c7c240b2007030841d00b030300d9602d0204400c07824030680d05001400800c1c98640602c207101e00320200100d80030b078003100d008064110024100b030340d020303000000c1c200205401c181d43c80c6405803840300140c0c0804d0342e483e0000e48210504a0018440d03480345880071550803107540352444c10349801007c640c4502c20031184902e41003c50060080000710702c4071010701d50303008613142c0c0b140611284c4100c0d2540380c0c080f1050300401048060005000d0150482c1da0740c0e06000e001c00c10050000c900c203a8008100103040800802500c0c0a00e80b14402c51100075040060b800da00c0d8442c01041c1c500e40560031392041c142d80d0a204104030750003840394046807494005940107079403600601d404100c11807505a495050360006200400e4480d00030302084c284003c0c001a10702d03000da80842a40103 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 791740368 1250 791739118 791739127
    0x20f1204141e010e15132d030b06040f021c111611030c060a03050603010507050a1e272409061107091a0411040b0d0f3201050f010c03050a090902 64
    0x950080a11044612803107030087c0b10203050001c008540d440c43c0600c03288000c2c03030105102041c00991481e41105000300006064021001c0d03e0041e070300310249242c60341c182c01101e42c0c1e0052050059141850001005901c4d090140d046505a4040d07650003030100c00c0101c00d60106503d04101c0c2c0780c1c0017000100080d4640a880340028003608041350070707901950901020500c0c0794014810360301504010380320b01040c0781c402d91204c00580e107182402010000040245010400880c41650035140040304058a00341000014914010560041540c2d40002d41983c1701842d4048000000d2b140d0526003442c100b9014015546003a420360414885a03241c205030340c000300e054441c0f40300414002e50f000e02210300c0c03e5024004a004900c1414a004420400b40300889555808416082e0181100003400c16000400715424605c180c008291361050120180e40316004041c410b0040c0300c00c86807507050f0755008000801200d49140000e05002020440b14001401628184080c0034100c000b1504d5 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 791741618 1250 791740368 791740387
    0xe090102090d2306060112020a140a050909010e010b03061201092f04050103030905012f07180207020102070611010b10020c0a0603150b0a020f1204141e010e15 70
    0x1d40041c56800c00c02400f00c00c00c5400c240c03202151081c401d00c0141c640c2e0480307140881c05c05000c3d501c15003e030b80c10030030403a271700c07642c8441c450025090042c8180e85640d10b81449409008400c441a0080d4200b28180d20042108c060a0310440758000300a9840c90118010100c42c14054441280b005100d030a80c2d01d080c003a00c3d9861000800d1902d99041c1c0d10340200e04590030f01007180c00c05e010140010703844180038040e0794003800714160f18500b880e86205000f01c1c094070586040310b102d80f800d4441d0b00003020402000041e1550b801c01107034a000114545182a40042d550f152184515800c0c01101d000e0600801003c4d0301400025102500d00449030000e418002d44403030b200506180305000c0204045103080c864450034100802100c02c01400301d003040e101000300e42049014104505c04e02c206000b450505000c294800303440090495265410103c03040c610040301e00d20f03a8010080e000d220300c1e20892010012002c0c503402e080c443c03940d51480d0049000700321414103072030041d4130000b40b40760b4 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 791742868 1250 791741618 791741633
    0x20a1404091505090f041e0b1f051219030512070c0201020f0304080a0807170d020c0d3204081f050702060708040b100509013c0e090102090d 62
    0xd00321000010580d036850f032080015030b41042d610440b1045291001a000520740d80300b003203585403003100c425200d95241d619110074205c22034001c0b000040d1101c8003009000c201c0800c1c00600f0303080f89c0c908015000e41810070780d82d240319013400442c004141581d03014503016108691071000000c00c285400d24104c80302900700c0303912003000c0340144254404000c581c100031068909444402020745841015519002400e401c1003500b40d0b06103500820082018007010002d02c00300305200e001580703494442e41c14500b40340000040d04140050a500c0030341407010707000001c24000400600c01d00d41e40e210090b0081c03070b005a400c090340314070441001801c1c15100c81c6442000d50106001400190754000d02240c803035000750350b06e8001c100d40c0c0003c100041e0b440c1a8155002d54040c5000e00c01c66540c800040c000002070303000c014100c0c0d10a010703103207000c210080d800c800151411417a21200781566400507030b500c0d074440d0032a403400302c4000c200001401c3d01110728100c0d00500808103107050381040704 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 791744118 1250 791742868 791742881
    0x105040b0711041e15210803150d0b220314070309030c0609090501120f150b100f110705030316020a0914010f0f1a071a1906080c0f04020a140409 64
    0x45403145c0c00001994103003c00755018035400c05d06100700a81e00c0c5603240c8000e0340024114004c01c0100e046050003984074141d8100780280102c1072980242081100c4014401e00f005101c0c05030042c138807003c00440c0d0001075940c040815696503903685c00a07420100e658455641000b0084100d890300003400310b80c0500701405460700b40300c003045140d07070340c081800c1c0711100e9500c000d19901d0f000c10300e540400c5203180106d10070040100b0201d11908000e00149800104401440100f607502e42c00e850015440082c1c0d4038044e010380e0007400034504200000c2e40c0d0b4000e0b00505d06403e00c6000700c4204640315215104000c0c494940c00380f02000d0070003a1200001400d006100409210038070026501403080b8841e41283c0e00300c442d40c8410681c00d2011740c01a0b10202c010789100c040300c40002d250110301240e551085000040c0640e20009000410341a18080c0c1c1c0810011340c03051040700c3c00fa0380c64008000420204490040e034483d1011029034a400e611420305401c1140401c0000c4c1c0d0041c01d40000 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 791745368 1250 791744118 791744141
    0xf0709050907050301060f0306051f081e060708010e0a0f050108030301061404030305040b07060915090c17070915080706090503010c170402040b0301020f070609050105060105040b0711041e 83
    0x102d001a46840a050803201180710b0040b508600000401c0800d0301e5901203604401020400d07006c04840000904040001d544690303620707031117002d0030750400500039440c1c4207200c000d802034000c2c1c2c288046c00070040e13601070040c94884c1e04420040f4182680992000b001608400c030203000960f5244400c1c0d4481e01301348070b03000215010300d00c08815900004110790550380d00d9104c40d42400d04100380b00b40c150300410b07030407540c0c144d444a410012030345080c41444002e4805c440031954014501e881945140d10358002c14081051402c03000205d04040703a5031003501d004920010380000c0840700d103117407141a43c0c000c2c256409009408240298410301103010b6130801e400902c180401c4002c00c94205036009440b4081801a101040040c41d041d0048003500000174009400c0000020403044d165102000490f1714641d20800002000800e00480764888400d080843c00c0c585414605030719403044c2e40005020140d030101443d06a550b60f400f07a4500d1145503803940b0980c0b400a110030003444110241c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 791746618 1250 791745368 791745373
    0x221a0a18030918060e1302011803060f14060d080f0909190e0d0503070e010905090709050307242624030706140702040b09090a0b0a0c1b0201020f07090509 68
    0x3800140805406644129441114039094503a900c02e46c0444c0303240c01c2403040381007003200104150440c0214483c0d00c017541c0038040016801c10501220002c8610480002c98000e0582e020480035030340750004495496007040d04155660140d03c0d00e0040c3c1d2148240c500d9011142d1000d01603524092107160f644442c066204209500509c2c1015940f40324180e51000008c10400004000d10b1150040c080c2e12881030500740305043d1100005414013108840312030000c0d0000324104010f00d0b040080f10020100b41c020504102181c810641ca948200d60800083c000c1107491020490145003010301c0383c1440c00d80140f803504210950700e03488e08200180030850010440341d10401e01d80410082d044800b591940c1ea40c0f002c0d0300c000c0d50310030f4120b18026613010740c0d50000b1102c01d03140e9106a603c00d000880180c9000407103460900c40504002d00b000791400e2401c43c40035a420341014003080b481a003000300141d03440c41440102e00d0400c01441145c003e01540e80c0000e2150001e410950050244006 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 791747868 1250 791746618 791746649
    0x2010905120405030c010e03100f0c090f0506030c0309120304050c0f01030c020a0b100b070602040819030801050f041b0c0b0105060a02060a0209040e0f06221a0a180309 74
    0x1200e040c81c0290f01070745038903070030904440c04c00b50300412061718450405010b0316505034405d00700c0c008554040e4450b4000329100c0408090f0160700404c100080c0051460074101d250a250100b145c902005054481e054400030209045200403c0651407401d070700e01d035a583d2443c0600d082034a51a00f41511800380c2949105071115601030700494942494503801804013140c1521106008400600b0000f081c101d40c0d071001c81d50100e142c009114460241c000940e42e10729092007070786400c010b04180d091510b28940141c0000c0d40c442c1030207044980071510842850000c0001030003c0680c0b2941002080010b101c449007150401c1c0c0e0582e5040c09203840c940103a0b80d40c03041c080c61f84284180ea1005800c0703030740011403401c03050303001c1e01040703801070400299214003809482ca13242402030388044503800003040115803030710352541801940760101c020099900542e980c040c2e80001c042c0280d0003019050004005000c82e81c00a820488c00c0d2031303040c1441c0120f003030107068404c0078002c82d41101002c91 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 791749118 1250 791747868 791747893
    0xa02130903080a0e0c040c030e010624020c0d030530060f1c030c17040b03091603021305040302122208060c040312050d1109030f070b09040f020904060602010905 71
    0x414001c0c84c182100c0a00462410301040000804010621005043d0741e4694980b15210074841c8202801148000b03802032075003010f89000d82c0d112820101c00319031004409000075200c614840007000c1d85410456241c81c22481181044003840d40c03030102d14813013410021554a50446058000c20096500590f80c2180005203c82200d0040c03e829450700e0158036400064850710450b186140611701c04405895980300726409a071083d449454503050100900c07428241c00d20080008440300f00c50407448501d141e0110322100f00c4120074401071603070fa1001605140c001c0c03080d02202948030188640d980c0101541c43d110041c2c0307030b003d10000d5081c04000f190401c03000401c6230280058216490600d0f141d980d900b6600041c2400400c10000700384443c9600f44418000c4480c41d4010700741940c0c880c80041c090528058540944440c03030340c001202080111206400c407244404155004100c1480c0645440044c0c8501a01c2c0358220786010b10014400e5030640c06559110b01c100b050701c48040421 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 791750368 1250 791749118 791749121
    0x60510030201120506090106050f13121e02030a0818040905010c030f090c2108031923070f021f0e1510051c1e0c0501020d090b0c0a02130903080a 64
    0x46030f0a9400001000050003014028800340c4203044030990030ac0c0c0381120342c2001700050002d0b54450b200040907485a0000c02c078100700c0e00850703036400c0e401c03110b041d40c0c02e500000c0d9180707801080500807400019070000c2080303100032100d2258074013a109214949081c90003074000d050084561001901c0d08501c0910182240a4038041940161030049294205018014406841d401c040040340a50146000280110000c0e41c460208aa801d281104464101009a45900c11854140181841078000601c5854503032078100001d4601488049040c10080e46006049000204a03096100c9000c09682c0c00c0d030059109100254180c482c2c640d0001042c082c6a07405865066103289140024003081c14480280c80b59407449e81505a001150741d125220130000149241500302d54030180e40c02400071042402c0000e2200384003e090044002c03400901d0007140d4003a180c3c5038440041c2c400041c41c410400009010b4004050b14400005002603000a2a50400483c082030070000080c6903130450703 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 791751618 1250 791750368 791750371
    0x3100b0a1238010e27070306090f0e0307060507091a190c081b19050a050d0e0a120804051207150302190503040f151a030f15130605100302011205 64
    0x1071311098075546180d000c214139890425460188031074811200c3d030b2400200c0c6a007034040c50350f9441c00141c03941040403003000e84540319404000c10341003050106e55840008225090203410a00c0010b20707440c0c085084880f03802c07550140401e1140d44645200c140d1804d001008845d25000c0c3c898840134400505907a0f55201d036030301800f495030510900c4512400043e0303000722050402d09983c03e40d100c810108500090445041e43c1c0f0f5030000141c1c000300304003000f00003003010043c18040d0854a14000142d070f80d803054050360f0032008010480108108003001658042d100040c40d402c43e06071645c02c069a03c6031140f0803004985035850001481c28024400c135000f41d80360901081d41c0c040d2100c07060300ca6030300251041300c0f2900c0130307803e0801084440603007000c2c205500d0808240010240c1c02d20100311000b41c20b1030311130f4002042180c00303600d0008010b0b140c04e0540d040c806007607407010700030001000034000143c181d07070800701002241c500910300401134a1007600c0d00c07000d03880d5104864080301c80 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 791752868 1250 791751618 791751731
    0xc0924030a240609061d0a170d03090b0a02090109080102030703090c06081e09100614040b0916200703030c0b0f1513090c080d0806030303100b0a12 65
    0x20148018001140701e0305024076408203001400070420402000b050302c03042c20358071881e00e960354401c41c8490742c8c20a10450480c00358a02d41401071241d40d0716400c030200c602a202d440c119a00044030000c41c0d010302c06400042000e00d00840d120302d0710582c05000740c01801c10444452509130804180580600c40042c00703101c0280240740c1c00c505141d03402040c490302622500403441080083c0f0150200b80c001d0101500900400528441280c420b21081d1500210100e102d071241404001005001c5451440203000515010302224110301d0a8070a42e0b060160044450207184804010306801c9070385141e50ba4401c51f80c0d0130940e03480740c00500d140701068400c520040320601c08446949090810306e40b034004005070005a0b03150030b03070340c8806101d0030342e00c140300b241c0002901c00f26041c0c009060541c4a1030a42c055461441c12074225084400c2c2c90058100c0581c000c541030b07012501c110003807403c0d009402d00030000d00c14401b07801c0f46009100c0c200b024003d41d80c00c250f450078900100c88860ba070300 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 791754118 1250 791752868 791752877
    0x118060e07081b101b0c061202071104181b030203060a09020618030f0a050c040c020d0c03031e0e01091203020c070e250f02070902030c0924030a2406 66
    0x112800f0401124800721480d9000300040d4102c010b00c00c042c45241200f240303104450a00005140134000381410010924201002c0e01c1400440d010031301c4020002040d0390110b41c00694200d41c640d800f00d0065402e00b000e4059101009084a00c41c010245076095030f0084048524594440c0400400c0d6808403000a402c40b41c03d025241d040e01c00703091204044007004060721044003445412924140400c80c0595041d0b0040340700f404941860b200d95180d4104501c040c0148102d10310015001007001c0c03000600701a902d0425550204180004244401043c0424800c0b04509003e540c043c200c10f05060700d6201c00246100391640c000d2080320760b9400c80c80064940f030f41c944000d00c0c4556200422411540e04410f0041c8804200c0036071105d83d16000d0b48510340b07001020380d0000e240000316000050081d00c1042485291901441500d025003c00c0b240c03600d03110341091030010801802401c08401c80c1c4040b06024481c20070350440c000c0003d40401c04402000300340300030030310b03203495115160218 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 791755368 1250 791754118 791754163
    0x1d030a270f0b0306030715020c010806061318090c060e0928021b070e16022803050d05040b190b13180b0408040e010b030f011401020118060e0708 64
    0x1d1142c2409940e220000806981e01565181aa0030408081000d40b00060300015600e102c03e680011405400c603406035111030030007440c400410f1520502e13004503840100c2100100c25091300365002a0407040d40081407905880e130381c4c00b0280041500d8a0701d00d10030400240050040900103181c058803411224020071800e0030f1500142c000c2d807000105d82c40b0030402c1e035103001c64480b00700048001031203403014140071840c1010801109061241c0711104541150401d000803403203240d07010301002d01d6201c181544c448545001d80e01c52003810700384001d80f03007081c0810003030160350300d0041d12138120340c42c40514520000014504860b550409194032140c809421114840030364048800c640b44030301d44204103c01a2500001d004048030122a10740e800182803103860002d60b4100c1c010700440f0045810343c10b00440b0400700540c140140c90b40704034a0403400f4000c0e80300350013000000303100c08124030502800c0d040000150140100c46202481542d070001070360f000008200e44a5013940300c0c0705080 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 791756618 1250 791755368 791755379
    0x60106030f02070c0614070204020f090f100c0308071b030e0102060702010207050613030302070b010902031e1e0c04180e0d080103020306040308151201020309071509091d030a270f 79
    0x11405581b001514100d070500007800140c40c0d0344002c0c031004541d509065100cad030f041360811000001e0a40001c0c021000e8024840791a9048404a0a03941d13050502410540c3c1d030000441c0c4204052070340c2c82160f90b0386d01440040c180c0110038403403004070aa00ba500e180e034a60006901b0703845540300c02421644030301f000506205001034034414030351192801504c0c00603103480b800d0098401b81c00040c4c14550000501c001952115175045282e096804141b42a2424501c0305400d401038103c84071921100e20001264644400c080341c0160010001119146050352080310007011481c195620901c20b00c0d0b48805081e0080500c181200c3c2d0040042010b0782e07842c0c2c0c049501c9400036001690740301d000040d040c0f4a58400207140020701c4d405000580301e00d08800f245140051a0344681d000f01d41c00d082015405500115400c140c410345075000c9034491030b40e014110000602c03101c0300c041d400007061503583e241d031220200340341c1d4481d40301c006550001c1c5408600c81d42c980f48554441456618410000c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 791757868 1250 791756618 791756627
    0x20325020c061812070b1c110301052e020a030e030a1112100603030c0b0a060503030306040e0a0c0f060f0203030f0403030f020d0f020319141f0b0c060106030f02070c06 74
    0x1d809a02074050300080341c2000110f898410300d0307081401b084401207901311750340100e41084185455103182c21300c44841180c016402511060003014010307080c01d110702e0500043d04900e455510020184c40c1a11010120000d4941c01c05420413800650780405441461600090b500c05407030b0415442c0000803070003003c0004076844450010305a02998120402049942c0304403401103001351a4840c80080c80d00c0c0145050800420f0503441d6031400c1c1c0c0620694a000041c1d80c0d11101c2a10001101c1c1c1d002e01050b4907060700100c0c0145508501314011801d00c24145030070003100e2458039284030b80c15420b50160303201d000840c1d5000d0034094410000c2c0200740300b80c01002100203800001868011918041416500b040c3c07104148950004140100804516961144c1c0d648422080084801300c2d101d206a80d800500120b600f00e5180c6140c25841040710701803c0200400ca034000d0f0740f888240441904c42009200d420080b03450070101e051988102e008864020342e11080800c5950b04003034040c0d5 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 791759118 1250 791757868 791757907
    0x1b33020711040e0f010606020c0a05030a05123a0b2b0f0b0f1909050714060408030c0a2607120302091002070e0619180f020325020c06 59
    0x1c00c1441a044040f44644c070a1080c04082e000a038090200c0c070100b00c6c2132061222099005034080c1d400740c1c250001140300030907110a402220060980d13599071040700d4065180076418030203015051030a601c9601d0741d403251040c50046010f08140124040c1e0170070020f03807030b40e50841c1c1d030108580303070250110811031440718000542c440c41242d05650019100c0003041c00040360310070300791140300c0c0502c0703455010710b5047e241c600d04c840420f12484900340d6555440b00ca040c8140040b112104c4000d520903551442a40c026212600031292103d240e54021030352008860f100791811202100e02d030940420140d0a4804080c500903e01d1518006540361254000c2441102082550a20000741c280e0b90384445a400340781c01d64018004c017401c080034154410780103030103140b04036420014225450000c00c0c0c141e0848070038000b041a64aa040172070001b81c611250601400d40c8000b08000c01e0714900d40e90021031240103102a80f0300c034041700042e070391110420b1410b5032040051007031f85034040701c0c047d00c41e = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 791760368 1250 791759118 791759141
    0x5210c0a0e01142706211509012009120a0f060e0c0105071101020f06010f0302090a0e0706120b0306040c0e100602030f0904110a03050103120504050f011b3302071104 73
    0x2803585640e00d0591120410060040090f42c0052400c9a0000ea070705800b1500b1a2070b2200030415080000c2013040380344c658414001d243c0ea030225680c44103a40ccc005c0758250029806041d10b1403483c03640b80003803144101000880b00c09280900c101202280001c0b580d44010042c0c4480f85480c0c000d80341c01c04510f0441d4132550462003a0314540283c000180a00c500808020380320b07011003801e40c070410803424002084042090329000c4a010040400100d0b081200d0356030600c942d510107900c0003c40a080b00c266103a03014803072a4248030401020f040640215112a100088540c403403400c1c41030a01c540e8814680164402d102900300d00b18900c0051002d08001000010301e00081c9250030383ca508030f0004400866503800c01003050000340300020b500700302c1625200c1c0c606814000000e0281c070140d007034141040142c6010403c0d40c0c2c0049094809660400c45100803100500306c800c108c9600882c11500c4131780144009689150640280d074612584042881070015408007130000405822145 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 791761618 1250 791760368 791760379
    0x204020d3207051c06082a10080601140301080a02120a240b0405010311120f06071d041e0605030706080f0408070206030903030103020f090105210c0a0e01142706 71
    0xc00c0d1044e4203c0c82250300a05071b010141017010600d901c4000401c80e0140d000c19603500600342d41000d43d480d0210080010041c4c00c2c50041c58440000480d04001e41c0c04610036814000070011862480004e8a0030034035100b00c030002c00c410034005166440f40340364400140700342119201240703203500e5001d007880c6200003400000f441101800024082d241c00b0b81c03080d03072034481845501c403076030074200505102007040c0001004c00c140350030600c541d515030051003841082481c10030800b02c0c844900081181c800020801d07c42d601348081c000051404100c416525107140c0100010b0508001c0f0301c1d8421a4110f8442c0030399903403041350907055800001c000701e82000c0100311072001642d4030720243d402901d000000716161360645c4140202020142c010074801d6007044c004010381e55494131101241c86079074a180507910300c80d00c41ca92030000c4030703018682c4c032002819012540701041c10a09040382c6c900b032120020807421b10103003c001c14420030342d01403042140054402645000c40e09a030805405000c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 791762868 1250 791761618 791761657
    0x11150f06061c090809060a2601030201080a05070c0f0812010602070b0703031505040c050d20161b0801090501061502032b0603080909090c2103070204020d320705 71
    0x4031b080d4885428100414200040701005442d6040324011800100400fa500381d4119000a8000700b002000c01002d1038480d000904414400d044000045900090700d039401c01051a2880f080d401c101041d02c031114210f00002012440040c01000b15804030303034950f180540301c2c1c404401a181c03010032124114800000011262101d200d4001d505415588154a41072201c4d4084255041494182004a030a0402031428603141088404003c01302021100366406840c045402e82481040358460f4580c50301d002480f02c40642104030b2080c4190020007206840f03e48039021a03045070103400c0160700504c8080d060031007454100d5500c81d29040d950107030018041c0440c1c00d4405680044a0b640f801155248490805901080d04000040b0150005c40300d075901203648048181c240c21500d142c041662090780b2030a20880d910113270050025907442c000c1441600181000120b69500c0d011110b00308002403c0c103d241410340400c2402c03886283d100d00320129020380203c5030070341c040d80c005103 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 791764118 1250 791762868 791762887
    0x30b3001090b0a1d0c100815042a141b3c2116020d050604030905060f07080318100501030506130f08030711150f06061c0908 55
    0x780018070483e0898404504000448800003958010940c0314441c1e501000c814419a9901a800b0001d03954515202045645264690000007400070f0312503000b920b004030407064506820740c003015448100032028810303000d204044950003400c003200600c98a040c05818010707200134203510327854100704080300d07030200c000004001d070300800081507485030110040d440c21201406462800c0c40302104040d10080038ae08850401e41491071400c04aa00000681d107803460b40c810000c2c403c410b4001c1d00050640456180141c2d450405031002d5010072520513001500d80b501c04229802d9152101e001070610256079981000e54101800c821071541c01031600b5440b4402c100035030f8005040855010402c4c0d407560424500f007003c003400e5501030b100c0103107008020075880c04d0a001182d1340f150b5a1640c996800c4411240c4440e0580101c140d4002c043c041070010041e0f0804074081c481709039490740d803074071003004200407442003150840144c070f0b50316840722100c0031561141c1c10381e902400c212443e204600 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 791765368 1250 791764118 791764133
    0x9010c05150f3d08010903120e030307021903260a0f06060e09130b1311010203030f011502250f0801060b0f0a05040504050a050403030b300109 63
    0x8007991400d030502442044214080090056001584049411210210448091003a0503803002c1001e04030101c0f081400d200c03042014850040c1050402008110b403503140080041c10074049a0381803600303120a5040540300407048902443c010f4008085070426810380d0b54483c008580c050301030201241905d403040791320300c60341c00201311048000e000314a010000c40e001c85100700b8803080d2540c6040301c144509504aa0b5440c40c06404440c095055625401500900101d28000500b0360b0212000c1c005001070403407503041c16900c0784046e0180c040c144001244c0d00d002c212905642c0c440603c0c0100320440408044412207012881541c0031040c07202c1c0c145400100e2020181707403800e10140200a55803a0f100b18001400c1408001e200c2186400700160b164051596041e400140c005030007540180208200c0d002410041d100740402d00e81240f800740141400c43e01a0701090910010741030b5890a001010403581e1b40300d0501020f491701c0d501144400b001d1072400644c07507599a0b040d0000ca0000e = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 791766618 1250 791765368 791765383
    0xc0c05030d0f1d1302071e0606030302071a090d060f0e030c1219181e03060c08042006090d0501061a0a0503010b090406090504060b09090d080c09010c05 67
    0x240c0b20803041c5900850018001140c2c08108194001011121801d80e030315490009010038010b4000b5071204690b0800600c5031541b26104c0c1051910103100c0c4040000903089a000c89000380c0075210040c2c2c0da403110200743c01d40e00e140d03090300c100e00f084451503d00e031400310004414080c060010780300200e0700030b060440f844481990290350020621601c590400c024408040402d64102400e260300318ad8404884184540014240040c000c41c001c54032000e401c81c00700404811061420401c11124520541822030109480041c00d003841403807624003d00301c841c040c640c40004c001800061070700c0440c00d150940e80d8651f01942c1080100c082d0740d1200031510800c0d0144000281da1850006a550001041c00038004020024404c41c104550002d00303881c112072081d010182d0310108100090014001c6030811035400703180500f0b100920080c1d500c81c440c140000d07900300e00c04d40c48103400310381e545198402000000320b5500c000396000f080c0b000500140e00c0f060501d10710760216596450b080504 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 791767868 1250 791766618 791766643
    0x110301050106050a1e05040b1611031b10210501060201140106050a08070210090507080d0311070f0c05060a02011505060c07121e0b31020d0201140a031a0a080a02010c0c0503 76
    0x600c03a0010b000070300084080f0302b10220700034000d01c14074108035000b20303841514040c4a03c100350a54041c403800790958200407600c0148407070300841c0c0c2c00e02c0e10009140c20b0203804010f42c0380031b0008540242c00700e5414103071050750b1607075810b100d02c1300c10450726904000e090300c1c21409038101e02608a40203018a21b01c4520400207000f80c1c50410300b21900d44100901c03002c080604000c000c1045500040071180401d800043d540705264140c1070840140d0070691200c0d400c07100c0000e00f82e80f0154107502141100c0200842100d6090755241040141d0003101441e00460700810010050402590061000300d480344030031044d408030345000c6480150103003106982c07412001040200c1c1c1e15004c1c4840f200c40000542c550001c8100741039002d00b85a440b08024069149410030400307580c0100324841c4e0400512100b2603544d01c1c2a00024003410a058840703ca40d594002446428688000f92005036000c04000709120f800e50340045940c40302d04001603030f1a103030881d000710701620103100b07c040484 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 791769118 1250 791767868 791767897
    0x9010522050a06170111040e04170d09021008060303030a0c020f07030c0f0f03080406120b130e07091e150902040e18010c0212130e04110301050106050a1e05040b 71
    0x4c1c42c0104000c0d4040700f82140700000c0c0d141c404400c840000c8a0165820344040010300c0c20715989070f2030080e8250080c629800340344080070481108032901d40d00240f880d40c1c400d81c0e00205076036074608141d0348240196000c2c1e6161b001400011000d004507441004070740020f10459410084510071242800165042500e80d00001803023805125040111340005006858108500078034541f2001120b00442c0146000c0184c8028000407602c0c0c0d5400c030010200000f410a00109030424100d0b0013804840b440c00c04d1802000c3c03001948820074800c40b00707444501210010980351260200c4014040085420441456110081042c01b460720140001d0aa208038102d11410301c0c0d0400409088030b0b1100c115543c8c149005800441d9001c50b80b41c5203c3d0111003640e843c1ea000c18640040e100ca50f4102d081c4040b82c40c030801050040c09101c03007041442c02d40007080030b0390302c82c1c00484485c444d0780d182e500450038a5283d404400b0040c0000021180d01d8506075003050303262802da0005078020ba011002d00b0 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 791770368 1250 791769118 791769131
    0xb0603160323030703050a0e01050912061012030912140f010204060306140607060506041d0102091315060810170105041101050a17040f0804060503070206130209010522050a 76
    0x206000c071400c0b2020040c60045040000a035001803442c46098101400c11013851103140640e405401641c0e5041001440c6448100b00c904c1950b07a2101d08855132044081c034810001040c0d48810201001ca94243c2d480702a02c6041c28800c4501d500068001c840c07210942d007284038014070520441c00002000400541d50b41d190000c0141511070365008084200d06480f12020140e540750115969113a1000002c1500c0c1d840c44000b600400c1d4014150202944a02e984107940d003042d4003c010044c000c803241206580c2000c880011284034183c041107541529006205090045503401c1d80034201c00a440c0d12103842c0d00d403401c00480b0030000b000881e9100c206200400c8460414442060020305c0c01c5400e20004100051141c40004000340c0b04105000125051084100c03190604c240c102c00c0e0240c0e42e9035500d90003007155204031080b03001801281e0114919018888101142a40041c0001103590a050402001230101e207070004540001da8030b6044040320602030030b4481d6528941c009100d = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 791771618 1250 791770368 791770403
    0x9030a0302030712141801020a060f02040504140c09060715141e07020c01031104030b0702070e0c040b09040e010b030a1b0602010b030604030509030f06101d0402030a0b06031603 78
    0x3c0b8100300c44c2c04044c040c2d0b141c42c0502000c401e00035070301aa10a0702001c07420494000040c3d060808204010700000d080c400200b6185055070001c004917807040e5030030081c4192011850001c0c0600b42c40d000180c030003c011a085a141c22030140c188140159a04006800d6440003034040f10169050800c01001840c1040400d030f0640d220701116104016110129151814000b500da20f1001a01418950b80e020003444a024080941d409943e104036800d0b0981402034010f55180c400b8880e0a041e0460b8500007084407042d0380540f800c0364114110103042500399001c1101501c0c80000d81c0c0020744d81c90240c621147d5040000304c001d01e0040c9141003151000d00f80c2e051001c0c1e81a041314040d603040914020140c0c42c00540a81c1c00780d0149490707900d4881a1000900f071502800c81c070500b510400c1c00b8400d400650040700d004441d0070092410300a1404154118080c40845001c0d505030420410b1801140d02660103170740c003050040c01d54040340d00a401a028503019600107135143d02030450480c80 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 791772868 1250 791771618 791771633
    0x30d09050d030609020a080a110f0708030f060d0c1a070b13020306060a1a09010903080f0405015d05090c010216150318051c08060a0b03040809030a03020307 69
    0x4e407001420561a1034280d031030180540c2409003802c0303181a5a00e2400380900c0d0385078140c408201003680f041d590b5010900300324200d03400c15903070400860060304c0031403406d28001401010050340a0312108040e40b404860b0300810080b116602030303c0c403041280c0000990140c4500d031049011008540200000d801030500e0481c0060450380943d01203e010311112000800c0c0351210703043c0c840c500d81d403024007a00481d1070310341d00d030b02c01080c103423002c0340c08d03950640180c018100760386080e46d40086005411003814440c1d0b81405500000c83c00192504100c0d626041e40c0a800e007000351106000025040105041c48161807003903103049a4440521000841c203009140d120b4400348002c00500f456480d6800822400748070f1580700c5403440042c420030038041d8011b88004009030000d411a10a5414469241c844208161003000380c0310b0410075070fa5000e070135240e0007a00d028008200003420640c0750300e980d50001c0d04c283c1e8144824862480c051307904000241d4000d1080c1c0c051502c400340e52600d44d0 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 791774118 1250 791772868 791772881
    0x211005060906090d0213090b0937061113030c05100822020907053c0d06030203100b030708060702060705071e05030c0f1605040905030d09050d03 64
    0x288508400c00c01c48180d40d584900307540c1e030f02c4002c03a0142d10400c61480080c10260100114200c0103040a4150080c80441d0304c0e8144110001c81c15140c0000c1019050407140c19001c0003294101c2204124400030751001c08921207051080000044080c02184606003540015000c20103406400c0d20a02c02c000c0b0619688005080a550700c4105240303001d4080c22031000203210a0303107049400390200d207070140c0d50324201155401900d038030720904105c1802460f5502c020f004d000d50107804211450b213681c8180e4a8402c08504042044c1000c00f0036072131b056194406090008803d8883c4000310250b5001d000040700c0b8800e004000503680c07004030034941480c401c3d0740a1122030300b0600c20002c903141c02281c10fa52040c01803411954841803403501940030880480c0300c1c0c030440c0440041c0005c100300007005051a19202084607041038840b0503440d92403920120502c00700385a45d004211508080e04030300340051180d800c1c3c80c02c00b800d0504180840d4407030300080d21903503c8000c40b4148280c00d03104e044c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 791775368 1250 791774118 791774129
    0x91a25021f0c1218020f0603091b0409051515010504060909020f0712170a1e0f0b0d030f03050a0b09040b0723040807140d15022110 58
    0x30101d100400a418498110455040118940b20382d800103206108140c074000d00650301d48108000800c038903200c00d0062003030750120301030500000307a000141340000aa07841120743c0d03402420b8010442d4a101070b00c00c009032429070080c0c0c452440d10700050041c41902e110480e42102e103400f920384446440f03c2545011140e0b810b0102c02c00c03040c46000d0f0f003c94500d003960080c16015942d40c800c0b5002043c42d01c5a0000074056101c400702c10002c15034000b0207040803011401b03141c074a546488107400100d0b1125031640040c8079500c514502642c6c429046400c040b0790f0304c03a002844650100119448400d4030100b20002050542000c0c14150903128143d0403201003102000940c507980f020130200d02001c0c01c081c180054100008004901c10f905140740e101c14a00650364003d040c2202030342503003103070246407064014504081405110350040300c3e0158001414055080881d413900d9113003400d038954401c10b00d5020450a10302960b07000380c1c0008080d01c062a042c16146c90008590f42c000180c000d03 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 791776618 1250 791775368 791775373
    0xa03060b240a031e1b18080c0909010917030412090608180a020402210a0c0c0201121404210801080d18090e03250b0109091a2502 57
    0x50304851084441550b4401109040000c0e00c2c0507070300102e070110100000445601410000050003150307002c0c1803404a001d0342c0c1c90700c034403a0902c00f0031846011582d000301b11301680100c0c6190098030341007102ca80c0098580d0000964103c06031900840400e100303041e142001000400c0c003041215180800d54040180d01c0e00c1c04d01c0fa070402100810000019003401003000041c41c411000b5001400f55450305a40180110b5840d00917109942e400e14200000790200c84802001440c414528040d40070241e100f50303617903000341003d40d005444005410b052040440ea44095014904810346030950140e4081c070b00d19040d00c2c0e00c408134a14482030149200081114000c01004103681c00981d11102614600303281c19044d081c0c05441d9804205688541042d90400380c0303c0c552000c000c4010b048101c000421040381c1102d8211264600840ba10000c3c151002c0700010489440242d2040b500203100d0040f00e103811038034284031010b00d40151000b44880c0f8110f0544510700041455401085455002 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 791777868 1250 791776618 791776669
    0x110a050417010e1203040204021c0c02240f090a0b0106031509090c09020a02010f111801081e060609040e070807050a051f0201020c07032001050304051e0c0a03060b 72
    0x20203480304021184150a0100800030404550f00d503010f071100d00f5450b00340c1d4816100ac10032000058040a0300000160180c1003124040035485040c000d00260850642c00c21510343d11440350b03600b90000e04020fa0f9001716030909002800a445e164020a23031540d01003040c00d1125152181d4038490341c0302003440c2d85031081c080d000034241a80c00045130b124000060310343e07120090917400f400044060070121494184000c09204140024080b021302d121a05210262154015a8284410751f1640c65081003c640c1a0541c0280c144440d48664040d0880d400c2400030fa0205040e10800d120b050556000030101380300700c010030803486004000860343e20f41c1d000d18110101b07130404003422405c000b070920080200042c1e4001d404807103034414420101c40760340ba66410020700203940e40161301060792601001b0202c540c400c109030790083d501300000d4000000c241c1840010740c81c6a481e124418090401451160340c2c550035410003c0d8094040031903010724840401c0302c0070040c5001c01103e0f292004 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 791779118 1250 791777868 791777891
    0x1030f020406022104260106090606020303010b0f09040c20031809042a060908010b1f0215010801140f070f0c0804050603040809011b0203030a030906110a05041701 72
    0x1440a21180d0f264090100c010b04981d0800c2d5912a94008140c01000c6c60400c6016a9490040280c9064104000c11459413525103001c00d5411901c560304c0181c2c010710060068950401c01003124120300c1000c1c914041c03e20021600350382c03004400b400403560904110b1240180c05040c6282c04800f0130141d80f0700218418019010720103011004c0c000d40350358000408003d103100304040b60038555002c1c0ca2914a08610300c000c1448a07008040010b0542c80f000141c5100502415a10340300080a458061010f00100805982018a9082184510900e030743d202240c50f5000c034081c0c2a04400820034106040482e100c18034040c02038030180c0400010080915400070810081c05450315105580090300d0419100c24082da0308600e6008034004140000c02403004000c0c070446c10282ca0303241482c00014a000d020000c41d120294040d0000c10078181e1281c460740c022a142446504001403110000c0c408070681e401103541d12010880001d02404003c3d1f001940c84c042c81c54441c0203110401c0d021 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 791780368 1250 791779118 791779123
    0x103020301151811090409050c12160303210911030d090515031306140f0f060a031103070b0d02120c04030503090112020f0a0305070f05130506070501061503050601030f02040602 78
    0x50000194540d258580138491002108450780400700030024405071601d400c110342c4412005c84c400e4403c5082d40308071342c0300000110b541c042c48400401c0c04d0f54440d10310345050b0b0f110125100004441030103002580f140c40400e22034159000d0280703019140c03030a4014141807a0040c080c0c150428400040c1c01000b50390707128038282d41840e8482e2951a180e80b01e000a88000341e480c0c6600a12403800d00c10060301d0400d45400c9240718041222200d0701640390f21320420982d0400703440c42c036008802d140c000d10100d8410800c280c520300d0045c0464803078666400051a0340e800111034880a60380000d40410750918480301c180e08083d100403480c0c074140c0f0310390314941e84c0d00c1075408880c14000300840121160000d60706031804002084907850341ca220341035005000b07240c1122401c0200352128464032480c0e22800c151503500075031540c9044c50505040c1001000e81241404071803940d21214049807140c0456821640380c0055103022855050540014050b122481161848988180310400029900 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 791781618 1250 791780368 791780399
    0x2010b031c021903110105010b03190c090b0412050601080d09030f080f0d1b1404050d0203030f1c2306040c17130302010e0712121e08010302030115 65
    0x140407a2000000401e10281e0400c0042d03d01c3c2800301c1000320242040c1900040e0072121000802d00800c403907030700c2c0c05009030b80e400705803520440c40d900c2c0407080e03104034525408090540c55509002080da84c2e900034010603035005030071494a41034004141c10400004014440c0500030321000362461101d64040280b912045110207070941a40f0311001080c0b003612011103d1301a071703110b00641c4e141c5090103140041d041940c200710291203600d035607002c20782c81200d10070020180d24503650310b89440c041c00c11400402d5142c00340d030700d03000c100031104500e151317000107101c07500781040c00002481c0410103272001c460704498100c10781d0b554280601c183e0403100e8041d60340440e040b1000030b640342c4401030840b50090300041c54068060940c050040d446410b0038601c078a03034800d034028482305ca6181011520b0b10381700d105a190b910501d55540b0f00090380405011200c955a00c0c02400c9101402040e440080d1090a8030001c03803800c80040c02075080a0040000c0000010b552000180c500400c1244400c1c4 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 791782868 1250 791781618 791781643
    0x106080705030c190f2d180b010e0907080402010f0203070c090c0c020d0302031e0906090d02010522030c0605130b1804061d01080f100b131401030b0702010b03 70
    0x4603011910b10713607241c4403024010301290800076045a44038071602051541e107000c00b4007a2944100c586820014001c03072001035030300802d4210320600039035030301d01c2c0175144801d506410322100141444081e124009002c1c401c0c1c80380d988450712803c0c21300008d84600c00a540502c110b4000b00b1260303000c141a603e0040032503181040014819805880464503049848002580881c40c1200c8100703040d80040501130440b01c60359810303805041c240c1e02c078001c1d00c200b104a0b60446424030642d1102d15010522070001070060424514009400c0d5800c186400d50009186604038841020310a100c2c9000c044405014907003841482c094100e86184800e98041c403540c0c88280300000c00c1003290008180c1c0f0f40450138068070902c982912a0642c0414a5409002c200c511b060b00000003401080066254103800c0c3d44000741c03900c0a615003c010140541614490300226880ba500048070802d00c00d4517007110018030b109040c2d504504d440c500500004e454542168100301c019040390350f01280815110b02d = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 791784118 1250 791782868 791782879
    0x40b0a1d0a090206120f0106030911092e0e0a092a1206050a0c0c02060a2a050102031e10050f042310051005030a020c0a0b090f0106080705030c 63
    0x7914424a00e000d4025003100030340080b8085900c18905503a0310740310703001d881150f005140702d0383c8500d021411280c800c40c01502604502c0107071181402c001e96407a4001c03904091040816002c511302e000c520b42d01100082c0302c0401c03600100020000e41240302e030007032203c4006022603191619500002c0c10070160b100100c00c2d10300c3c111202d2034440300d00100140407034401c242c50081c071400d0807402000c04035040b2401c5411314100d920310f1441001c0b0150700b01d500a004a01b04507146400300c40740000c0c06c4270700203411020f9041e5015410101e006060561150380050303a00d242007100041d0605803017050714083c0c00b02e28140030801103585250016550280c0b60a840d046122000601400c00703d1035806140030340c4640c01515400c6052031900c2001d0140346c1d480b1a554a000f44401c0c0107880c2401c10000b6020310110b030786086c1c44e170000c0503a4410482100c0125620b0340f40d05d00740d0030083d50840c030240d01400e18010012001e01a50000b09404405000e0482c42c1c280441c4d00c80081079580c82c807e4 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 791785368 1250 791784118 791784121
    0x7050712020c03010e010c09050f0306041704120804060f03050f13021c060917030f0f0a0e060c0d06050a0506180102070e0c03041a06130e010f090809040b0a1d 70
    0x20310800c0103402c0044010000d0250380c05400c0301038001c0039089034420025091500124032424401c4915000d18409002001c40d40d0303a940301c1c08170300041014805221030081000040103245010368825203405440e580780d440786411000351880f400c81201030149420b040130803650344003003103201d0383c407100d4000d81000307200c02440018508030303900d07881450400c0da640e4500e06104999020802285c42240d90a11988440c5d8401c02180000c440c030030050812400003454540b1188581d941120706000301042c4540c0602c034003070074035504440c51810598042407601c00c0781018000c0400074281510350684003030500010400c148610106007803060700d90204001264401c000145c000c11034480c0d420031b5414616240001079009840644181c06041c45c490403110500f01168020100206229001c07000044514050180440c4082d8030303559900040c0c4c402078580c041c01820f0344c82071100c150342e084800d0400c011150300c18011070041c0182a4148800f42440c0f01e141e040b2a010508000903 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 791786618 1250 791785368 791785403
    0x1205070302040b181c051b0a0b0316020106090204120609020a12030806030c0103141603020f04081f0603030215041511031009151205030408071d01060503070507 71
    0x40d01c103a9000f41520200040c0194250344d80e80c3c902054014212607035030b90500700b910080c0c0c5800d80301c42c0c003030300d180c12a411400c4043e2900d041a00d02030800761040c6055640d444c0c0d0502e0310b8200304d6a00a400180007a007400265080c81544080c5c0703d080d00442c1010b091400040c44c4c12850320006224a03a60380490095596851109004103445003490209040c540b0703000f4070040c0103880580c000d10a88418001702c0d8003074003484032140c0c0042c1c249025940c41000e4440d450392050f1010050507802c000303005241503001c008102409003880209a44460b2a0501412b4a40c401c140343e025441c05074140300082e40403484503c5441c5180c554a9142c85074149240d20460810b00960300c1d43c9080000d44909610304040d40c1708038a00900c0320000d5541307546c1902607da49903400d411015209900b4400300310084001d4050500410440b030429454004051510340c1c950020000c00d01c84038500c150b000001c0302d03414050607461034110308608000e10080d00307601a09038010403900251460f00e09 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 791787868 1250 791786618 791786621
    0x1003030e131d010b0607020603071b08160b090714100e03060a0501091401060806010c151410090b031011221403010506090a0c020a050a080d05010e0712050703 70
    0x2850326403031040002030308010b00035000c4004605031110b95428260440300a24061081d912070a401030702d031501e5982c4080c01140c42c401c4443c0880c60040352881208040342c400c3c009054038132280e1501d00c1e4100ca450038a005107a03170003018140f50b50f200107000e0100c2c803440483c4007c0e5902c1902c00c20034100d8030500036285c45103141441134140c42030078108039140d003c0781c20241c12240c000390f0801508a03940503201c1c40d01c00902816000c503002c1c1c40818a6544101c019803081ca00a03038148041524135090013007a1465070100100c14006002404501400c581030000244803800b0200403250590300425103403410780c141d17140c144e40d90341c409000f5140890300300d60300c0c000c0b000f411441220240349248480700f004d004610880c031040d110a5018101441001e00035200100f02c4a6181c1e1b41c180000e0160010702404030450241c10b4100d000600d0030020030069512440c3c40c03030745a030381d00030a103000c0f81c6050f0700542d012141c2e10148000590449404400295681000b0501c0d9480c400180d0 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 791789118 1250 791787868 791787889
    0xe120c010c230102040f05030d0c170c060c0301151e050a0c120c120e030a200604060e010f0c15050c13090e1002042105010b060c06041a1003030e 64
    0x100098482d070541400310606500610075150442c80030048a030b158801d050359030302421701080214040c240d01c1c0c00403c000d003040c03008080041101900d800100c0c0c0702103040200503520391070701c05c0e030201c0180000c5007540c000c8807126000e444e000c51400044d281880e00e01d6002c4403406d043c84800a034400180d4402c00b0700646041d005961072030344158003100207214600402c001d0707440b10648890a006a44a03102d140b84503a00203005004d00741c2c1da07444884ca144441925080701e00c40b802d400c80b10310b80b10000608010f05283e19160580300401002400d079030440340302401000040b01d8508005030300450000100015040001001d64420354400301510811382d00d81d003026420781d00001e00c005560000f04c8403401c0001501d0888243c4000e40c0c00703078003481c002d0125541d04d481c6080700b100b00b4840c4420519008070004100002c0c00b20101d41c1c254810b40704042150412410030081c000c400b40c00f40201881e6071040da016141012044000c0fa0040c000101007224000c103100541d581c100400 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 791790368 1250 791789118 791789153
    0x3040b03130c271505040b0a0509090d082a03130c080d02010e010501081207060f09080d1805100f060e010e0403020601080a170703030216050606010e120c010c 70
    0xa032030703039925000707560544201c146101c0e881c0b0b03180701d00c24030005029008078480d402000364084e03221801c0070104005000100c1780300740c00c110002c83c0003419680f210314081c020b107115000f60000002141000b010801300500310100240d5154400c00c0340c5d0701f0490501000f14407603a150780c0766200d509000310364000c59600079088903414500807404207804a00140b11500a070000c0000f0503c41d1015400d86209104101e0306802c00700c1c0311803001c0900402803150f03d02c280000aa00308410490710125011400f0070f035032003030700418254003003d91442214902c08004400c801852025943e03203945070613040800d10740c2d503140e0b0f0340c0945610040d008000900b49008000640c0d60f101e00c0c011090790400c40c0c042e0b00520404000040350f61001c80c0400e811504401c007040d10030298510342d006944040000c40405608008490f88441c0408030350384458820f0300070300014102200010f1104004100e81803040c000044500c40101000a040100e61800c0c24940909812424034448688500c0500d = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 791791618 1250 791790368 791790383
    0x5060d1803051b0a020d080307050d0c033201060e040f0e150709030309090c1215080609030405061605032205010306060908100e030c030706141803040b0313 69
    0x4100400d81c0200c081c02c183c5044604040030008015002503031380000b100040d40281401901e01c0c0411000c00040d07500180500f85145040715441c00c070400c9880c0840c00d240040c0c0d50301c00a903407000000c0342c44203500c100e40d10300040c10030030034070f0700803140006100c2d80c0c0c288420481300c0e008503126900325014188404204018800c105419551104170900140101540d020b00240c00c0c81c0c015035602050f03d40698035188243c0c2401c6200008184603079200d1f0034003c406110003502c050790b000d26038001c01c2c2031103944500c500e050041031030260043c02401c11900240070038025a1a010181ca11401d0101e1201010070700e030341441d030300b180720342101d001d1240c884495000640f000100c5040071a4420b0340e080142a5503a0012503c3c8540d60240900070782040e10800032100c4030b40c0004224405d484c058074504038041a0711031640e030003c1000c60341c454507010708000b520599814558000006c0d000c01c5910031022403240c2d00c912641c010a0030a140100c082103d20152004582150340d01c1000c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 791792868 1250 791791618 791791661
    0x10e130e0705181b071a091608030405100309062c060604110904020702180a0f110c030f03040302032101090b010f0f0e0303090405150306090a0c05060d 67
    0x14a0300c55800c2d0080c42c0c001c4450071200094841c005080a20a070030b80c401690301d000c40040412026031002030300350703030360101610b130401c4802c07408800c1e40c0105111401041c0c071040c2040406405030217a07004010942045c00100203a0702d030200c40301140e192516000900c0001490004020310381b6581c14500600e03900004641c10740888001d14101136072100b03e5800380c1d642030800054500b14024640e2505060000f01d000d8281038010b8040c80380300424a1880107500c4908600c038a100300d41c803911850300c2d0120313545841d005d44181480c41c94070070001460455081806c581da807007010165005201d0020001e801e00d071080c0203071200c044219408010302d0050704000168400c0030300a50651501e4252440c0c5258014407118200107069110341c000d0441d400800d4035030f804070940322900750100f00404000ca5540e44a8140301d1404428001d0302d000741c00e003d044c03802c1d1307004140080307661005c407c3d0b00128401c5c0f00c87c40c0131074a045400594426020b001e44c405000300c0000304010ba02042c0 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 791794118 1250 791792868 791792891
    0x30408010623060706110705010908090a090905030301050108040c0807031101030c020c0f06090a030609080c24040602031b19270e090c120705010207050103050f06010e13 75
    0x1009070702190318100303060048880e020400300140e402e4441c01944481d0070070444000503480e40114142102c10030340f040c1071a413140c80711429515041c00880c0c009030300050110041c40c001111a01400f03104d40e0400c982006552102e5480c40107006440c18001003100250800594076810b2000c0d02030002902c080e250340380362003590748400121042c0441d04100001c40b00e140300040b004d05449006007450300044800c4c00b03003c0c20754440000260009101e13000400030881500801046500c1a0411079503104040c0d4064280441c400c80c0b00b207200743c250000504141d007000c00d20341154000c01c00581d2a2130365102c2e9a201e0703105810403e859640458410380c03100c08011405918502d9848070244a0722028119040c110b003101b5115160140303038020300100c036411084507880302c5044101c55440c039922001505113084034180c9450381d40044410f0045503418072408000f4034080c00e041c00310f4240100c03600340a0900901d41d078100038501c0c00e021070301d6035520000045441c8400c020481501c41c103 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 791795368 1250 791794118 791794121
    0x30a08030109200910020709020a05120f160f03090c06050a09050303030105151309090b090d0c0c06080916090c111203040b10050a091e090b0c0c01020c03040801 71
    0x244651000e8510308200000005030502c00c006000c40300000d0f403841c0418280c100100840d480c40842c00718170a4078000709031800a88000c003218002615030617190a05c100d40100107400c02030520f0a014004001c0c006c200b803101d03100c8820440507090117440001a104110001c0c2141c1d034019200400c4200d00081043d044001083d110307016584282c0d0058030b0f001031680c0c0b403000307115141e00100740e0440c428000d04100c01030032610201c902d503582d0f559600c40780742054460985080e28450752110a10240c0001001520080180c60800c9101c150380b03525142108042481818180300c0a00e0010348141030520880301c141c1c205100c10740e000c54903220b014bc001e041c003004a401040e00000001c085220000b03401c01c0d100e6410f0021461603503540d40c0c5546486020703088240a00368060007017840e81d0342c1c05100700601284140060491207070b01c126030034640d00016450b080d0349001a28004506030a001aa001922010042e5514100041e207402840382c00c1900303046001c00308001c00d00382c1c4107 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 791796618 1250 791795368 791795371
    0xc080f0405240a0f09110d03050f0408030a080a0b010c02330a030c020a0b04140a15051006110d0f0e19030506090d02061506040b03040c030605130c09090501060302030a0803 76
    0x82c030004001c900c0365400d28108407a400304018000e1b120707140b021029440c0854600c48128400d140c01d070b0038011607105204064009801000c644d41000c2200200035600003030f182d50045c54084144007180303400c40064507106000340064042c0480d105041c00300b4680031030010b903400240000302e0000c1c5426080c408503801100130400000c0c108070101c2030340b520010340150026000209104640c840e83e9a0203201d00f00c020044d0b000780582d0780e200011418464803210382c9e0420725030100301440c0409440c070851803e500003100b8048070072988409000005002542040c05041c4810080390280b41601d14401900904d9440348110f01001d0000d0000c03501c480c1142d00c100100c507402c0c0c403400c680b02c1c1c40c1c04180d120000164050000512003c001649141c0000000b404091030542c031051142e00541c400c0703070141da01c1000720b80b0401c00c004c4103100d4694800d40c900f18503070030000300c0d682d51154102c0500c91704d4045a10703116030009021003980800c000b503500038100d0f1210003045c03900000704d400 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 791797868 1250 791796618 791796631
    0x18010e150310090c0518060a0c051e06010f0303050a080603010209040e0109060b150a0c030509041a10020d050702210604143304030c0b07020313090c080f040524 71
    0x5102c184d880c00c501501c02d480c501c1c100d500400621140c0d850034021240c0180b01007030200300c040b01c0340c0030200e0380a104d401c0ea40071100d10311461003c0080c47d01d526080040e4003506540e06030000802c00300e9807140680d104845c01b45881d407c503494100c0028064010b400c01305a100d4075003e481800c80e101548001986d034854070703040c442808911700b08411300180c0070a80c0701d69601082880062481004046109071180c1003c42c1890002c030007040440d0070b078100303511401a030384d840c1c1005450044a054010782c445c3c401007074804882e42004010b40600032009005a81c2483d015203640c01c4407500001c801c8600382111418541030070003200d0346000c00300d80201405680407007140c071039001c1c000c15143c01040c2c04091041241900b60318101314000c1054040140c11403141000600508809028202c0c0d58011511590301c0325502001c0c1e101d0368491032030343d440c1c14a6022141d81003811030385c0c81070484100401c0f46c0d41d0360400c0b03810030840c64240d610400e40d0f0f0b03c80710b4142c2d1980010b20302500 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 791799118 1250 791797868 791797871
    0x106210e0f0f1018020909100c0c051507023019080c07020a0b0901121a01121e02030c0c01020d060303170f15060904050f04061118010e15031009 64
    0xe80c44041104540c1c4010000c000d1406044010005d82064001945c00640b4002200c03106090380f4403000440b010440c041c0300160154490800380101005038081c1901c41411a400314208544060b550b0803000b0349100d080c0400910510080050300007458514425050704c40c2d0714002206034009040446002c2c40100300d0a00105803c2640365003910011076000e400ca082a070300382210304c01c4580160140d03078100054070b156909a80f1990085071141440078020307060141102d8005041c1d140c1c0c600c1c18082c80f519041c2081600301201030109107011400c00010ba40384ca5a0410224921074240200300b55800004e02c0d100c210b1155102c0000c0302d009a0b6203400315086102110000714080d520001002290b10100324140e0404440b0b4402ca10020501c0340f130000302d600450241c640448031400c00702420420403090000c070b806030046018101c5810392a140500302a00c400f0803201001a04004403e50f1034031540d112600ca40701c180c641442d00039101d141c280001004480c060243c201d105 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 791800368 1250 791799118 791799133
    0xd0203040302010e0633180108120c190c0b0c0610050f1018080d020703060e0a0c17032517040b04060c0609020a1205150106210e0f0f 59
    0x340c4000c03072614012950346c0e0036007210800241d503421075071150180f580703c0c4000140401c0c5055941e1000700c140000510b082210703562501100342d08003407491000010b024420070000000d4200410281c0c4140700c0002440301041c0b45041030165400660850209010300162140c038402e0300040b03040c07040da260a20380100541b00e00900c810114034060381c40d00420318250041c40e180c080c5060103210000d80024446007a51814014540140742511a02603000428240140706030380c01160049402d00b00180684801551881c1503040300c0e03c15400c01d1a80c040c20160410000d00c1100d840f24070f40c109000c0111941c01c1061f145100c1820211449520a06188800b81a09068404954942c6129403c0c42d141507800c1c2c49181407800204c070461340d25802c250045e91070804003000340a01a00042ea5901c2d00d00c1e0562404e910f2150040c0d50310002c0c00100112503010b6104560f00312841c0305010248030071544100a0554200412b4041c010004500010a800544120048105011524078 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 791801618 1250 791800368 791800391
    0x9060103110f0a0e130c0617010518040b070309150c020c09010e0c0906040302060c01021e0306101b0203070605090a06080c0301210c03030302180117040204051003080d020304030201 80
    0x1241181c0b081c0e030304541e14401c100044015580601e80c03020b0900c089481c10740107595001d030198101e030010008648482c0b95000040030042040b03001d450180c441100403072100308a80c031000401080200940c00e06000503010310302ca0340101190b10f034041021114051068185805031008441c2040103205800652000d0703e8500c40c064100c50400d03411020755222206481c54aa115140702a0456401c100000050f26058000d003925400f0000050b103034000d940d018002d5004201c880c0c449007800b8420300c5490b40eaa01c0340502a03140030700300604030070038151400c00403085214010354540140c080000d01a90064014001404221482501a42c560b0003c1d140000182c50f505030001d014001480b4110420304444200701c1040e8060042140301c0d50385000442d441d4204600103074010400f852071040c803070072001c80c060090804c0c0c0b12800300c2c4280e048001d00d0017000030f48159121408241744c001c15029100144d45c0100c0720320356a98201908030040d61080d40c1c00c400543ca05844a4070 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 791802868 1250 791801618 791801629
    0x160807051216091104032f0118060503040c0902030f0601031817130b16110a030203060712021303060e07120c0e0a0b04060810050a0c2705090906010311 67
    0x41c521002c9049102401c0c42007150013000102c1c40c3c1400000b0401010001c20342144500c410300905a031072410144010074425600c95035058003505000e03000b0303047e03c100c40001e01e800040d10851316280fa102e41c1ea80c1000c01414159912a0f0519440001840711010040762020720484007030700d061000481011020408407600707900030f4420036155038001c41c000e40c040c0c010609003610025160710180c85603403c00c0194490303100c050004001040010400c4996060084800c0341121415056451600401d80720304008061408118911f07140d062040c00300d40c10f440d011401404161360441e00d0b840d14600800341070804024510440000041c100c484007101d0300700603403002c0f100c590719240415a800048010340b5003105552101503186450721280700d4440145807800051101d81034010800c81220700240188071070303506045600640f01e0304003603d13800f809504014207400031054904480280380582040c0ea004040d5418480e145400092041c141c138054850b020700303050348004110 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 791804118 1250 791802868 791802883
    0x703020c040b19050f0414072a241401062105010501170c1e030414070605040b0d091506030c080d08060904110d0c080106170c0f031608070512 63
    0x4582c40f07880106208600300f003200d0101540f130140c0046541c110002035501c1b45e120880d03403d80000c1c1070503014104960f5001f11400c8071402e006402d40c1240c85512442000756030760a59281c0104050700c01c18600d98036070311500d598030707040300c0031202e40d61104402856070348840380742c051214407c00c241051000c18401d050407103105031150752250b0800044024000002040450011824000892240000590200c078842c65040c0982d4030b280a00d02005445072506e20301c460fa0384110014001e03141c01034122004e580c000c5441603114000351640901800c101d1728000d082075a8501540030311101a0048815240300d1080404100d131034070741d1070340e0302d0240000d1900055005404150745090052030250041d00034a4520440080c440c0440c02a840381070341121107a00b603603802c0044c94000e204050280c49100c10159022600700000b6986114403030b04c07a403185c80032404500440d5401c008120a8000c0701d1103407448030303595400031500c5a2407882003501585403409a118040004101c50 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 791805368 1250 791804118 791804149
    0x51801060f050103090f0b100e07030905060106080604021c0b0301061a2d160b1501080109020307050903060705120c0f030414120d0501051c080304150902060703020c040b 75
    0x300c01c07600c0c2c100110b0140c07045010640301c036034141c4400c17408280094170040c0b00380c10b464200000146010f55032030b00e01c2c000038609800c00d464070333950724006030000c100607044451500d41880c80b40c4a4100003070091150008000d6402802c070010061100c1070f0700142c401d010120000c100040c2c0e98100205201000107000966101c20080784841040d0700b4201c003030201d1640b50581030700e030021160a00c1540719441c245000c140d0004178504002c401c46103681d0220050020350585602d203800640308284c1800780440c90340d0003000050383d60380300d80c0c1a1903c000c0028101c4049081044016003954860140d01c3e4003400c0050009100c0c5910000b140c100490307641c4002e15641d00e60302d03200c2c45002d990560140304e019004c00da0302540c0d0040c010f0701d100c5410002c00521540360108012803444410203810042411803203400c0840c15a0341070303a51040d04810150324500c085810316004000080700250300c80404500c82c002d141d03002910121040d41035404101d600202420030038400c6510120 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 791806618 1250 791805368 791805389
    0x911030c04061a0c010f0504260a0507030503090c0a06260c04060c05010f020406030b0a1401022a060703080106081f050f130203090c03120712030b12010e0105180106 73
    0x41160f05000a0000d0440041c01000021850f00d1070324881c00307441066809503201e0f854004003808036001908405c0f81e00c1d00800d002031510a041c0c00c0508bca01450300080c050210220024203002002d0040b59400d041c000c4c05c80000544500000c0d140d4000320b0701415084030082c41c240342e40d00d40203441a01800034102401e042601c0c244048945807a0f811048500355200d4140400c80d00c0d050020700060714071038502044100324179043c060b0542c40f680c00703031108500804194100c0d0b43c01148102c1041c00d028008904000703000102016031283c11401500300304009007000c1410f0b88070400f0350595038696070304c01142d25600d80c82020005041c851034200107040008000740c1c035000c0e0625202000140540ca00749811000f10001c80c0c10468482c00d080c2c002c8031004081e464248182c0130040d003074104440c100151070301c58140c0c0442c426180010f065603001255095a00d0030785140c40b04081d20b000b8090899980f41c8a03003c0d010654540c10581d045050111154406014601c00d80e0030790b40f071 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 791807868 1250 791806618 791806649
    0x120a1b020c01020a151b0e0411160803060d08030f0a06050f10080709170d02071a070b070306090515041104182004060f08060904050613060b03010911030c0406 70
    0x581803490040d6100e4205c44540c0c0344080c07200100c8070300a00d8040500c50b11b40b00f21190264040c0015500c215650a0510408000301e001c100209a01e100030796030055641070700c90b581c03507000c107a0030f0b800e90707201600700103011081014006107030207824854040c082c001d2241302e6641050020300c3d0b041c41c201d0383e071001c06113803500c000741d209038466940b00a041c5040b040c80d551728000350941245940703220101d80c20139a0f07000807558041003000010700b42c11192002c01e003441d0ba0003802a010300b1500425100c4800301240300c503403198019101803c0c000404020314204180700c4800c0c010b580c54410302030350401d12041c0080c810b0200f51012260401000d00501c805060715070001e2075100504000d80d0070f90b10f040c6601000d4640508041d00440d00e1340e1007082004ca81c00350014500400082c840c40c09001000700203000420701542200c0303141c403004202d0341c440c0361810190400c1402a501907290110a1050200308101000750b10015010345d0309080c505401d100035681c15008640c940c402150 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 791809118 1250 791807868 791807873
    0x10f0509010b07060f060918060606020d0203030a0c0215010905040b0a18060203040c030b0c0705251517090a0b06040504020102060f090a020d0c15181208120a1b020c01020a 76
    0x108003120904070b0120006c1c525071207000c0d400450703841107841440d543e04506d4103010400d0512584000e05501d00003441640d1001e28000d580b44001440d100c070071500c0d0030800714201d000300a0511014a0001d0a00b03403507840d11807103001030200325010345440310030b031020441d8540103214011852103260000c01c01540303207807909000b0b980040c2c81259042400032000001c074412040751805141c007071140568030101810031070b151074014101c1140c0e2620300c00e0140003a10b00341540390300725524044013901c0d1841840041e681518840d1507050b80c0c51240c41040b10301c18020441240c01441003141c14600e485003000e2000701d40084400a0142c3d0100d0b0208402c510301051643c0d0020980d0121410602580d0100b03400c28440802118022801401403014280400c1d494041ea0700301d282511401000151440c543c01d02c61040c8805407003040079040500080d00304940380d2020101036012581050f10041e4000c05602510041000340350005000b2240701040300c1d0300708401640101038600054 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 791810368 1250 791809118 791809121
    0x90115030b03150f0f09070b0910020c040e0c040608061909080424140702011d0a050d0b06010305071d040506040b1e010e0d03121a18010f0509010b0706 67
    0x7440400d605100d0b400c84020b03e00200103003188a91540007800c660f03428220305609000b503019004006981281d4014030141ca01501901d500c46030032540390b0f492240010713060341040c5501c079140742c02c50b080550241c5401d800141503400040f00343d600b040081d544041ea941ca440c020f9403401030703c1c4d252100c40300e5010920b40000d4022402030039424503195840720305010700036020301403001544440980d80442e6821110306a030b9018800c0107075140401c2039000900b040100d102502c01940841d4a40320551100402040a880040c0c656040c0c40a13074245400c0340c607000c4544600282c02c00000450b841d2103007903e02c1c030404480031001213800c92502040301902c0014151604a603581d40b0304100d581d0740d00d065041130450111003850b80c50728680010600e659480b00c8074001d180005414001070b50000b0041e01600011400041c3c6003071a1585034800e10031901308551204000903104141c461010300503040340c1302c0c0081c1030340c0e80d40d98405201e0b0036082413080342d400c0b0b0340c24031160010500b036 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 791811618 1250 791810368 791810381
    0x10020c190608131703190c08040f0209041e0302030c0f0102250201230c01110a1209080d0204030506010e0105031207060203180f1e03040e070f14030a0c0e09011503 72
    0x213402c110400b0018005075083e2500210b894018140c261011540d08144031b21495000b0720283c98000038034034083c0c4550581a0b0a2074000f4040c09807080082e00740302c20510070452524143c0559401caa00300d0038003e550707801407030700c00c03000780650500c41403024030500c00c42e2544402c081180001041815440c600c1041c0c0d100180d05001007021651210001d1181100070070985410031521403010840c560300b15a40665100c01c480320402030905010b800c482c0c00c401e0700c0300b002408920354401d031410700c0044c01455030411050340042000300410201040503810f0702c1d107076020820729a82c0c42040555030720502a1004101c0b50412010300850550707001158412046019400425074151207249402a1203d21a8132a04041584900300d240e4024450b8238000100c025801c140c103020a00c51400c00180c544005c0c02142403100d4400e900940c000b4580e081c1c0302c901d09441c2d1804c400344e00040c00301c5858010020308407010110a511348140258140c1d0781082040120307921128054008011 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 791812868 1250 791811618 791811623
    0x2a01140906040f1d06010509060a05070215041a1606020a110f071e030506060607230a030807230c01180f0c0f080a02091510020c19060813 61
    0x20012603032652145002800180164480601003601d45140340165040d03280c0300d242072038424400c2c0000ca03a400701c2541d00854044030469a144154401035400f4413503080d00a4122541601504001408402800403254102d01100241c1403603a11540c1d14801c1c408030a02c2c4414a901400c045a0150b01074591001d40341881d4041404031000b90789882030761812103605d135100c050148000361144c00c3d40402010b140070200c03151411550380640300c0b0f100900c054021100030071110140501c0c9480e4200c030b1400c115490015917503000044d902d4810004054020030900400b0230504e51190014403079201249440c0f104c0001c4501248085502c0030300c13011050340d21107003042055540010601c070703118828014484180d68514100142855580c000307246d04803030250400c504140071a00030011740c0c3c101c481c10800da40e032070310301c0140c4010681c0075600001100242c8540d503400040038401c95208aa60320518241c1c03001da031a51080314028074001594800201b4401070240c80100354035407 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 791814118 1250 791812868 791812907
    0x10b1c0b0306090109230a11010e090a02030405070e04050a0b0c0c01060b0903010b010e10030203070c0b0a0903030b030c0a0b0d09080f07030e01030b010e010804061407020c01022a01 80
    0x11031900020346002070a0b2080c50490b55204001020071004449911007520500c03d82c81c040e42890f03905944400a03603102401c010000c1c40d0b19000341c0c0c850b0561810a10b0001c007200e6423414181103100c001c1d00100c03000c49640c4518003012800318034021445215070782c0310000300f004501a60b42e503180d10502a0802c5c5540e002403001c010b1403c001c2c01920041c00d82050040c0d01d50780d42904150135580c038440120b040c40342c1c40700321000e10340701c1c0300d50292840250b040c0540c1e42d0701e88100031030b100018403801804140c101400c1c801041070b03a810040f401406664140001040e4000b0981c503110094082c542c414103050080180703000c00c50140000c074654108c0054680700507160114103901c031882c2a00e801100040c403404054005508020b481c20a10b0704101c10480800040c0204524000301c0d0b05102050000500f08803950b00404103e1456614048003400c3c00c54019507140c044124a901502408406c55994034404410320221380c000390306241000a00801036407230075003501050343c1c1e01c1c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 791815368 1250 791814118 791814131
    0x702011103030703021e09300d0f121415040f050112050f06090c06090d020a03060507030f05040218090307050a0b06090f09101d0709061409010b1c 65
    0x40e00900185208052544000d0795603052040d6000001181c01002c190586e030500641800352030b0200b40304d45030000f0000c100e2204085a1030800c08240c0c5c2d102400d010701c1215640c1c02401d6000d29403894114082d1200044800907109c4803003030721101420110001c103408000766032082c50340c10400d032800c005040002c520486020b0001607400c02d803c00110b08c01d001c5d2440040210400c2440c4008502001a00d50360914000c0c203600c403117806020b10301c54100810981c11558440c0d80001005500511a0141d991f0328034248000d000c08984040120380740141404080d00c240c010700748261790051552150009107441030510200140501e0148e11060000400103481000151a098018060081c0707a1401c1c00400c654a207005041406650300001400009000082c00c40c802811000300030510070101c002a00280d5140c0c40c0002040c0304180e07000030a24010751000d003c0c3e07103403031850111085003c9c0a00070200d80a1288404d0200100f020600f00d008403166103100901003040450702 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 791816618 1250 791815368 791815397
    0xe060315060c03040302120a15110c03030702010f05091207080f130f140402070b06090403050c010c03020306100305060a0b0d0f060e070e0f0109170f0105040f1a01030f0602070201 79
    0x2c1e0841010001103500000d024010b5140000c0032090590b07c0740000d00c0104842d036203030b02640f43c1d40088103039002e888600130880070351003906650f46040c45d40100e81d264500b00740c009001c1c0c2001d005282d003240ca404003003004850045404030020380041242c13803901c403da60398409243d100e510140840402400100c10907059240e801c40184212255001c10724186030800b424800d01182040c0306070b2040100e9400144018002580000100c5c0c0c3d00d403050ba0356007010f90b614461100d001e0800d52134644000009a0183c1c003a60044a060311520008844644103034101c850540700036a0044245504121000d12040140b41c0102d258030301180f140f0503418140c0540700680c2159056010941c2003202f030f194080f100e9030742e4903011101d00d40050310100020b0903082041c00317003100300c80013940c0c1601401030401440d0700d0311881c40000c10062500d410b124880c0d01103600101d40a041c25982c3d0700b108403038502100e041e43d40080b07001c8a01d03880355580700025404518101c0c14031000c281c0c104807 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 791817868 1250 791816618 791816629
    0x50c0c031c0b0d050a0b1e040204020913051008070506041d04030203121509100e16030b0904050304051314071b0b04030e0f03010203090a2a090c0906030c0e060315 72
    0xe00e510a100a19554031107181204091000401f1241c0c132803800130740074403080000d075404d40d0440d405890040c3d5803007103040401c00764410840c0c10700896040405100c51030556034404c404a990601c2a14500c030f0f01c4101f0404148030b00d2103000d0400d5142d00344280c3d40c01d80b20139000c0e08140302e40101ca14212181d1030310040300c8001c03104150070850740212913034182003940089602000440d011072009080a00c404205000a403031601210207240d507840d86980603601080300d071040144414004d10f011716103a90b99500c14042e46d4080c1d00111001291340d8400d00855150040e288204207103503480020031510503089540000c504969010040080782c00c0c4001507014902903036600040f9015034041c010601c200005d060f009a01c104104042140c0c04103960340e900d42d0059040144215548028483c24407810540726144510a0000740e40251a808040400803d807100510681e9071a03082d000c981d409840715011680100e084285450900c0c015030b44a840c494200640c0b64000303001c02d1 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 791819118 1250 791817868 791817889
    0x5100e0405011505010c020a030320070321091202061303061505100f02150912040b0c06070309050307170d060306090512070201050418230703050c0c031c0b 69
    0x1d81d180d6603191507440e91001401c8020203843e003070030980c030115466804aa6000110f100103401c200b00c049401c480c080301c0454080c0c00c80c0b240f0045544458881c104001c002c0000440341068814081360481090300501c0761300304907001c0001c55681c00340c03a6002d000e032541c407008619661080801c008000a0120b11505404208803402012054188024801c5003881984c9080621001304100954541c1c001241c0d40303106180c0002001b19100c040385245002d00c040d5074443d01d00c501003404149448001c019040002c902d5007124080d448245013601110181e18026255401c01c200c508082104220304407200843d9080062030543c490f01050100c46054104a903016216030303c69080c00300c00c101c02d01c81d1880b101180d6140805c1c60307002078120f1069210380590103000740c2d40703451460842ea0203814421705801d00c00c0c00e500903030400c000c3c2007031003280c0f09004686001c0215845952001c00c3c0e8412402400c011807805160b060035003101032064a490f1106900e442410195413185250380 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 791820368 1250 791819118 791819123
    0x621030d0612030f140a12060905040b04111e06071103060907050a0801060609030311010902032e090302060c070c050307060801062a151d030405010e1f0305100e04 72
    0x11410b03400d8600d030050503100f090074082c04214000386a484410340031000c4450b0120b46003410044d03440e000c01404068610b0b58095a00507181501308070078030441d036581c644035601c20b0000c03560118021080011540c002c0a0400951500c08028101414031a00500b11140600c81034000c110380000000e01d440e40403100350450b0341085074100254201034800001410715a4001c0c020725041c03407402002c4030740f2444082d04003e0004000000c07840294446060780b0f401500b580d403c2c90b1091441121b01150702115404419880c1d040c6c4034100c401c0c891401c03040d03807580c043c08480e142e521030901e05030040c540c00ea8280c0006000001c056804200902c01010207403030311400341d0314101002d030403000340f008403969140d02d4105034645c41c80354403070015201e41d1050880050f2141c2c2e100560052080800c407a0b90351002075820074002e80004060800c0382e00981c0c6000c0c103504240c003400b0902c0c6104240181900c2d45000d030b01e0502c1e0207070f009550300040308164a000582e440c1401c28a405094405 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 791821618 1250 791820368 791820389
    0x1f060806130f02190504180525030c141e0a171e0a05070503060f040312020c01020706060305010b030307020f0d060902150a0801060816030e120a0e0f01080621030d06 73
    0x401a90401c0d0180550b47c1e01c004100c010500702d50740b1902d494134918001307003400880c045402080b000d42000c0c110f0245030065000302489807148540401c640070901d500b4420818038cc0844100d00c01402040381445000d0036009046140480341e01c20303c0008088a2014018210010005000c103849012a0321b031039002007030080f165050490500055420040c021742148003000a13411408407001d4001e58545000c0480b1400400c500700240142c0500008235400010a0300900c641500310409490049000700401d0182d981010390f02d109483c03009400c0b40b443c41130200d00b4900314500c540d186025a1020a0000155000a410031008101c401d2171040c0401c055030fa050340300308080c0c0900228103000c0410305004400340820364180c0800410980c440300040c0801e01d0030b120000039003013424401d580300d009000000e0180b80070070480a02484022068811940c030036070103240141c0002e4a012800202d40c0c10f5a200e0311f070500099500d1b80b00070450f290090700e440c0710f180c00801c4440d40 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 791822868 1250 791821618 791821669
    0x1b030d0213050a05030d052b0903201b040f060306141e0105010519200708061324060e0c0307020f060903090d1e03021f060806130f02 59
    0x400c4009889030b04250b000303522001101074000c5d0004200c5420b61b08d03040908c8280702120152001540e803408400e107100781000e03140010150848002c080441c00044c1804104002c0c502c169611456104030b00000ca0315500c0c90b0b8107a0419620000b103c0c0100c20010600170b44030b44484007a07400d00011040b01c40f0700c0c0310401035804103000300000d04664142880809500d4030340020260b000c0e0007004035a00c0386c3d050800c21917038024000d21940103101d0180103100d400249082d80c85000710701c91411680503580000320310781881c00016060580c01000540444515010180180c00e20304129240c00d90f5014085851081e08450512581004818a0f136070301d44044000d0401c0c0c2e808005103400d61202c0103001940318040141e442c2d906c2c00b07440c00c415035080d42c1001c01d05c01d45540220b00c0c8407058078034414107142c0d01007860902034910806071a80140d0805110084440030f100710141c40e00f1500201d00c100b14401103180406010740080e101020300d62b00044c0c12008104941c110800c42d102 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 791824118 1250 791822868 791822879
    0x50703082802150118020d09031101140c0f0a09090e0a17030f060f04020702060f0403030e1c0305030c090418110114040905071e0f1209081b030d0213 66
    0x39030001418031500c05404141d549007900e0301c4003d41070095440d03088070208400004503e903810b99869001e07820044c0401d090038140540101c1c122051601c544d400d10344d103498100b40a01005009240d141106841d0860050520005421201e0f40004200400c400001d0740c803818041c000d050074281e805800e0683d150b2412a561100120825521420500400c501c0003102d0220a5004106540c40030544500c100020300912030027400a600003004034101800f001c0d0300d405041078038400d07150900320700c6e200000c1001c9003880d2541d50304601201892200001d210344003558006030032000046c10030380104001000e0755a007071203800d8581140b01060003442034608461140030801c0c200409071444040f070003400351040740035010701292a000802c500a00c00c10b410164800e014211448407001d001006184c01d1300ca5034a2000140c420078004010f480500c100303217045510a40c1145003060404803600741c414101125030307441c0418080e40f00800b1710f074002490520255110f000c2ea150620 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 791825368 1250 791824118 791824177
    0x7030302030d1a011e121d060906190b041503060218100f0e0f150301030605070806010503060120030a03021309020708030f04060e19020102100e0607050705070308 72
    0x41c40400d0408011600f8002e040c2d8020206a0741c101031100340d03005000c03001e0030569200001c2407241060620340502c1031048240340300b40f2044c1c0c1440742c3c140c2d5101d0312915030407507464106541c65140061400320f48001d80f10140d1001c02d610401600c0460394540711003410041004076841a02d182d0b80005051006402e0350081080c80032040b2440150b039214140001d01e03800d01d00c08414107000c0c513405808042e6481c00040d0340a00700c010004010b50200c4e8150300700301c0e0400c0c44102c42c1641000049940b290180311090700c07801c8181d48080c110707520080111003030040c80703c54009290420a0403610b102c1c1c10300061042580c640c8000da41c0c1c480c0a031080341081116401203120500c184101d0300020711840c2200d0b04000c46014403440c80d252404c0050041c08244154421031203140100703451131600034801c205c440d000341c0903100520110007210058039502c00c1e02ca01d1541210740004d102c030340500f01510900e8002c1044a28458a981c0c0d0411903900c0000c503c4241d0268810501a5106c007 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 791826618 1250 791825368 791825381
    0x103603110405130b1315111b150a0b1c051e060421050f0c01060f09050609060907120203010e1b070809060a0c0204090f03110f1506011107030302030d 66
    0xf0301d40080200062074461462460028044508403031010305440140403000c800c112014401001c10440d5680e518100c0055910604485168007015044000e4003100480c00e810b6072440c0690150003660340149a800810380311200c03a0744a8005c104540d0b01001100d11461a40d00ca20020240d5900c400300018200600340082c44075980008100400610300c00c1c0341e5a405a9800d0556165100029040d5518001c1d90011440c504000c10f040710404d0054005a0444c0d1021000c42140f5844014040c240c40c0121035103a003085160002c6541c5007481100310740d00503045c1c503140d016203a0700c518480a0360b000f0b0340b007508144921802d11007020b80342d0824205400b54512054506000341e903c40d2498016035080e18070420000c0790405001c0d01491568141075801841001500e403945044c2940e01c04401d0294001100a201c09903442e034009503060313242014800410400d0540c400d00c070a0a10001e11060400000c5150150301d01c0c0c003080100c01861190300a1178540950304a294116000d = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 791827868 1250 791826618 791826631
    0x3121809021c0b0a1707030314031509090c0d150e030a0c11180103030203030a0c02030a12090f0503030f07020105060613060c030309051204080c103603110405 70
    0x304000c0c030604030140b40404100e480700c041d80491059640000694000703030702c0d803200e4003042d650002d520485401082c1c0e00281c9100303884007148100c02c0160001d107400215070351038202c184920f0b01c80c001d1400000640e802844002125120b0941034003240300c1159000b030440e08400300c4009000301010134001c814001212600440c00c00161881c001c142c1420300c480500348488286c10b84001e038641e0031407000304948410f6043c040b96580c0c60001d40e84d034021146d4080700b03071811982d003070701a1000c0704580468549660b2150300c0f40003042d20302d0007400740130380c01c40d5400940354075040044e80501c0030318410090f0780503130002440c4c100c0e03001e400d58200030040381c801c5031700b04070711503007180c2c41809081130311554500408250000c1c9002c0d4002d2442d0800905148150884000c0030001c40b4014000c4d03452183c04c2c0ca092501e00014003100640480e00039010135646000540d142940c0d081101074062203100c445030310f4850f41825103010446400c2504c42c024a61404591030505005050b046038 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 791829118 1250 791827868 791827871
    0x1b0f08010b0304083c0c010c020705060415050c2b0305161b0b040b10080102032403120a080709080f0a02010f0504050405090c010311040b0702011803121809 69
    0x2e00b42d9581c030301610400d88040d444e6280604590289410120100d40d6440d28011592244182d005d0038580c54000c3c4030010343e250f003000030355040303240701045403400c4030400b502060425003000400040d201250b4005410403105005a403105001001501926116170040c80010540d40e61905003418103019014113040c10503007448801c122021440162524620700b125070003451850741100ba10746e441000d0f006101840c14003007442005541d2501907a500207400c800242e486911701d00b0703408204d03aa6606601c1e001520030011100f01c41c003001c0d000c0300a0550f0300340310917190703100c0c415001510f045000441b1181080310b2250408145005440380000410600086010084d91130030404c000a04002c2400700a0140030b01401c181ea028040081c414800f5240c6146084e44d904c42240c0700078006030500748014890321000040301d0a171600c1c00ca10038500f00054005503240c139003801690200c0d17225070000102281084803007000040c5245c0e241c40c1904120640140303000e0442e0807042219 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 791830368 1250 791829118 791829121
    0x10804030504090b0a051206091b0102030403020f0303090a08030c0613050d0e041506050c16052116090b1302250203100c052203020d030c061b0f08010b03 68
    0x103604042568111030b41a0f8000c2041100100494019441544003641009160280d140613400115201d4072a041550445058100f840800c4d1080c03c00700d01000d000d600104003d0000d030030074101d140c0760148040c040340c3c54010b5002c042022400755070b112001503000452054611035003481125001004140e50800c21045600c1c1d49440315444d06d249014003161404a200c1c5403915003000c4202c948442000030550342c0e61201502b540d0104500350117a0094459000c41d209481c981001a1035001c0c00c4990902c041402e1404008003205404055100f180c4883c44407810004000c00903000080707000c918504e10005021310703885564104122240103000d43e00c042551154140b24488466550f000c12203124004070707003843c070034080c0c014405080c10000c4010640060040c10f20034a42400c0c40741405c00403444800640840c00029840f004030130701e50303000c40e114180c150304203800352500207031410f00f48202800b0a01030501d03440c0403c95468501c4a903580008010780101800d0010300d186 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 791831618 1250 791830368 791830373
    0x30c0308100e150a09060b040602060c04210f0f03090617161b0506070804150b060f030a0f150f14090412260612010902010e060306030a05030403150605010804 70
    0x16500b008043d1100301d03905624a0200b0343d03500e0140c100134003500900f0490a526600703000345c00d6025001d480054490100414112280b2904840c225405180b504c038940c80c07503c0094500b100800d100f5101241105000c0022800400c50105641d10a4444440799427400c040985900e100440e0005006410800c01c0100b0749884080c4d02c03528480d2400c00d1301041e0901d840c000c2a03017900400351151050300200501141c000342c107180114010518072100c04016071141d001e89082d805103a8002c1f409000902c16041e80101541d00100d00c8007011582000050864049804406400c1c11180000300f040004040001c07105015200c0f99103400001600c02011803079052002d0300c0140a0f8204000d8800c04620641803840001c0c40075620010307a002c8000c802d041e20400303949052040044008031801c0c00d9052052400b40c40d4181c451580b0308040c102081015000200015058050030215100044040c0010000782d0710030355079001165825035042045611a400050501c860101030101 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 791832868 1250 791831618 791831639
    0x60c05161e0806270a080309060a060f08190f080a020106060f09050f0d0302030403120f0e0405222402120906010f03082101120b15010e04180f030c030810 68
    0x1080d120002d0080d0061244c54500e1901c0704582c00039010010110600030a04400700340c280c01254003420610000b500e510401c10148140c0c421011182c1c0880c4070111011078209410040700d0142030641007044443d100c2c11510761240c00c0c9000140d54807207080c488036800500900e081d90303062411400c0c403030505001c2007c0b0050b40324642d04c640300c840100300400d40700700201c80103541c0c058551050f40444440213081c5135502030800c004504c000814441da401c0c03501c91148200d800d44507040c1c08410108881d02213110446081d80c0a00248006201c005011100c07504138100300480103a0701c1b2158140001c41d280054254101500014010884d400345040900c01703498005011551b907207580c500c50744600d05201c0010210010340400003562400c44c6880280700e41c000c0b40352000c0da03a10181c0729542c03400b00d0020705010880c00350702208907041075840080f000d84051442c88495202e0703120b00d80c00b6000008103d0000c2d001d00100350406038001e0200f5000070204156036001c07414030141c2c05 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 791834118 1250 791832868 791832901
    0x50609010309020319120e03120d02130305011503020909010b0306061203070f0f02010f020d0519020718020304140c0105030a0e150a0204082104060c05161e0806 71
    0xd04142e11424128103565040c08481c407001e070391142c0030313407200450b10702040034881e000b00910205603c0601300c00c16040100344642c3c7c4c48042680c452825a1a40401001750800c0c040d40c807039035010300380c0440090000d20a146103059a0508040c845155104000c014540249004060303410181d003400680c40000e040d60300b0200444130521102041d0a8481c651b0182074009007000b048100160140122601c072846954000c0c0d0f22120b87e0100c0e100e007039035581c3e85040b035840041c6041000c0c0160b05440b001c0c80f21106d10f5481070720b042c00e07a109113072038000110540d464401a800400d0004002d5803100b0b080c0c3c4a41070704045d003900e83d94080040d0003030000404900890382c88101440804505201c100180d90b0b8000003100d0038100249000c0c0250000d004240c0380f88105c03c1007103010340000d80710010151482454500d05424001c1c11100c5280c0d40108981610900c0c0401600280340008000a0842c6a02000781403013117203550000050650f0003112647c0010003070110400c61075403181c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 791835368 1250 791834118 791834137
    0xc0c1504030303270803180c030607080a061e05180c0f030a1d0d020706030b0901030818030a1202061003020d17092706030616140913140c040506 64
    0x40c620f8003482a0303100d030740c06404050008101ca050701c2d13410401c0040145010745030303d260312403108131804003043c2c1c1c0711411041e20b94140d00c105c00150714a403044c01c525a00599010b000b143e6582c3d500241c0c2e03400e41c0190220003541d0000e00040c810b03402c05c9440c01908001c0200d032600a07042140d4003107510b1041d0b04102000d6480000080c450040070340040b882545202c01c0c070101305140b51b0800fa00e845d2284406001401303450707400517420748a4020032586190040ca50000b50f481c540da08406540594241c083d10160483c83e40c10a5509203c400d0b40c0700c1c01100020340e0040c0f0048021300b850402004600310450302881440540c9407400002005640300318203641d040341d0060b00755918003403003c1170340c1e001541c81d2200340320441c1305100c02d11102c081101c1c1140d54550404043e101c0c84111252100091410700303a01040340304041c07100e04e01502c4070019107020080d0303002c0380000f5154070482041688450350b00c50743e0441c5e54a003035400b015003201c2900341420300c0b00141c40c42c80dc6420a = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 791836618 1250 791835368 791835371
    0x1a0f0c16050307020d0515101d0a0f060825060806100c02040204060c0507080304030b0610091508010312090b0a0e0f040203100302090702010b0d0201110a1401020c0c1504030303 78
    0x400041007010412a0300442e0020131070300703514419203003490380c0c0d841c00c04003c1c0d00f089071980850402503030f2000480550306a41e106115103a14240322104c0e800d8020071129041d07486000d0094880654402c0e1005800ca51000d004a400c9400e00105070300d40c84901724201e0080c1ea402000310503809102d103500000c040b2910428808840302c00c680d028203881d4003a6002d8800500000c029811005a82e0740768401c02c26501c1032980e803c54180c4a0295110150854001200090107403521880300c070a49900c40c00c000061984484512146522640d80003001c14003240c0180148001c20102c054844003e2501c010020304001c80c40c50703180540e800368810b0103003a003c80000c540e50418200c8407003401800454403441e20301e04500f1001c5039444140d00410441012440a038810301940100031400b42130001403803896030045131181c403200c62600190140d104020300103510120b0380c443c0300c0c0c04900056115403100a0450801c1c0c500300031a481882d031812500c0801c6403207816141100d070103003030 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 791837868 1250 791836618 791836657
    0xc07080c1005091002070206070b061302040305060403200d1d031209010e060307170402040b0402130602250b09030a1506080601121a061306031a0f0c 66
    0x1400092402804050401401a08112003612100d68821445061500103e8460741e806015480403440f82c400041e41014040040601042e40f400c0c09942010018001602d0440b5030003041c0101e0b04141c004a866402c894140f00174507601201c00d400680d820f4040326907411705214007a541d8400f50600c2c80034019451840c80a0340307a41c00c00f2014809001c2c059940e80413003803095034001c0c0e0145601c940070a6030850429110f00345901903034406c403201e13154540504920281e00e18640701c024400c036802600c0703840001040c1c4607800646180d04208200c140d2031401c10317501a08101002d459800c3d40d0110380c1c200c880c1c200541041c1800c807210170f40102d81d00c850b1000428184036481c0f402400106004680c84020b0b140c07a072068003122000c00c2654202c0e6210882907140e01d103018009031541400810305158001c01a81c3c103504900020038030703500d05a0581e80d42081e5030007540306503007800d4401c20f012268030502410680c04401341c400034026103400099403649002d03040004082001a49 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 791839118 1250 791837868 791837873
    0x3030b060a0e011d1503041a010602030403151b0e040608120d02030901060b0f0c0601050604061233060306051f0c030c2f0d02150715050112031e02060c07 68
    0x29000c0c07404c0c20000e0300429101e14969000710269100f40c50440d4500e0541030400040f02c156501141600c0e6030340d024510345032458941c03844040005071400740d0f484d03940f0241d000e46010901c80c1c8104103515124100515440001c02003159050303480083d4503004004051855071282040b60543d091f00600180c0344d03200c02803158018005600118500e840026080808049000150066202510881c0e256a803030340e040c0306c0c46010320301c68000403501280c1c0c0d16909601c0c1c2e03040300107080342c8031146400c40b13445100c0c05c802400903041c246400030f0706074109020082d032600070703d0040c04041c1c0300704508ec0c2030400504030b000055400c0710b00708107118812004243c0f041c070401c0c480c284c0101030400f0341500d07400915192000701040c10070008503e202100c3d5130402c20300781034409800500018410401078800140c40e40017110403a1300c1c3d10340030511425003030503200c0c060103458141e07200c400794041d616010340070300381850880280185101650104035800204545d22a4209011646031409031 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 791840368 1250 791839118 791839157
    0x5060f0c150a0203190603240b100e03010c090317130801020c0313080a0302100b01111507033e07050d0807080106110303061e030303010306050403030b060a0e01 71
    0x9030440031101160740d050003140c140b942c0140d40200c24400d0080d5183c42ca90001008031280743c0700003002c0100e0030300c1c680b40c0000038020102800c0c0450801160f29840200042c0721000400044008243d00c00100449030801b40300d0100c1100c56410024001da00350340701d52000711011600c02c10751000c0010f0064001406141c56001441d0b500d00035074884015201642e206c0c1c20240c240f820484604800050b0600001120518079401d600500708070542210b83c08054080031120302d050040c2c2042441c070301d140801140c56800700881124100c1c0c01c20010081c1034841490028003a0351280b01140303007002001c00c049440c0c08a600c0c188001042c407490744e0700342d0f000d6280060803d00800342640661904100d2140c4211044e54610360541c0c1c81c2d00040c3d402c503081c4a4160b0407076000b440081e51500b0100052a04040003030721280981c003003400042c0c650f6009030000c4172443c0d01c501c00e0004140d010b02540c00c0041080380c40034100100201d0042407680850346041c1040040504111880e0b00d0 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 791841618 1250 791840368 791840383
    0xf2a051c08090a170d0c0218250201091506060f0302070201020709020408060609010b181e030604050f0c0301020a050306090406090c06031e02090306062416030f02060105060f0c 78
    0x1400c0e50003e03560320300580c003404204038034000d038500a8180c1e03201c040b803060b00e80741440744d80103010220741030700040c5095450b2001010b800c4640244a8000715040711170032001610f480580c00821620110314080450102c03104e000d401e011b003000024050540c1054250703141030014540145c4440d21400102c4ca0302001d80e000300a114070018020502d24804180980310340030965162501c0e9036605440c42043c0320b101c040e5201045c2c03901140c016450004483c0c4606034a07040903a0003100301000080c01c0c641e09540c1100c29600440070010005014006d04540510072002182440c3e110940a80644001480705115030107042c00182000040d5020803205a0801d00c00036201d0340b034140160007410050010b03030540681115070215032056000b114407620015015007025150b401c2031040844900c02129207a0380b1801c003040c0c0040b03000001c5c000380620748881840741109810050400700f402c8492600f1500050018011a00c400d4126510750705440c00940e03440312000a0381c0d080c0b100 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 791842868 1250 791841618 791841637
    0x1803012901110127120c0305031b07140303010f0b04061e02100f060504060f3503031314011b0f0e1f140a080403080406090f2a051c08 59
    0x3d0300c1350982030006036588860020384a1a00b403000c1030003002c81a00c45803000e50340200016401c00004140c01100010308200c5102d030a03030282407161964034010021096480c1d40e0f4180e00100c01000580360300e0110800404102d00c10360300c0c10f41840c0d00108800c4441c0d002c2c003011071383c440101135418800c0290440a5054500800550fa09154075002519491003003521540c10040007040d41040314240004031484102030001040c0041d0040c0300600000c201074403242c01880e04041d04034428002075203e2180114480c040580d14079015016403901d070180002685048108500c60769681c0034410b016905040c0401c45030110a42141c2000e1051400d40d0000845010310034a00c1002e10720555103945900c800111520813403103031401c2e0141001709400100704001007008240204072880d000790060300c3c003280c503080036101c00451141e140e5048030400c403a04c0041c1080324440491007c0d06586c1070080040c1d0703181030002841503407000c09811b01c91441d040750108000014040f5580c2d01c8 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 791844118 1250 791842868 791842901
    0x50112061b080f061c052b02071202040b0a090e01050a090201020d081902040806091c020a0b0604090b07080a0515031f140f10060201110d09140318030129011101 71
    0x30b42c510341b8a4a455001210310110840000d03c090310140d001d80d403004640459004088080c03610030301a07005180000c06907000340d503034001194282c48101d101400b031703d14502e000c90516540e0044a0031200d005080c004034a16110388080180e0380410105100d80e80c41c54002d032130362910001c240807800d10211f000c1c440d500c0050006000d01c804105640f0610032101500c825035204e1030300c200c0c043c041c1101e941c01a08080d031180c0000303200c10705040e040240038100040d04038042e0380f9075042c0c08003900c802c2d020800240030020325280b02d020315a0300443c0e10400d450264085d00c04a59140200401079201d04140303203800724000c0295000d219148001103555106040c0800400e0071484143c13032220030840711410105a2500501806503240d105005561500e4a207201100003010072800454501c2c102c0038481c0ca0a01080010300785a07440f0448100d200003030007042500b1510340350001d0102d440340082905440c190045080491042030906ca0701e0800301400003801007502849a03007408 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 791845368 1250 791844118 791844169
    0x6090103290f0a0302010c030f0e0a03030c0b13150209030c0904030324270b0d0303020a17040c0e040305041a1b060f06041806050112061b080f06 64
    0x20107200d08220522501510b030902000c24040a20099280354000a800710b0070840700503001074460750aa205c0121545014000111450001035170f205c4240e2080d4002044140d095043c00071444100c0e802ca419242449416502c0fa50717078030200882c0d8002a00c95a0b4080345110342900d00f80150700f2078003401440d101c3c80346403924001d801440041c148408503052080c140210140940d40c54081d42e02e9a5140a036180c40041038907001c003505c142900d200c80e01c17504001042c1e16001c0e07120802d20301c030761030168441048c4134004115040740c190600040340e00b8024000490000d40c004410307160301852488555590381020f544d503100e2a880b003800198440c90740c240074041c0c407000c3d10700c0160807010b038030400c0c9091031016590b0308103542510140b1194808a449803a241c0e1106d0f401300040c1d06820008030803615144100c0d4003d80c0020f81c80100c102940c03041096074490b0321200c1a05608820301003c2c1910003e1070030030000d00a504814494010076440d55480241020582ca401c0d20007070700 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 791846618 1250 791845368 791845421
    0x906031c021e1b03030c1018060f0b09070219060b0a080d08041118061207230406060206040803040f0c0b0f09030f060912070606120f0b0a0209010e06090103 69
    0x1105603100c01c641d1019503032001143c5502e008012a0b861481c503400900c144013103118120020035400f06440015031200400c0c200051090041e0200c10102c0000065811010340a10000c0c01004180340110340000850038282640c1d804481a6282c000e040000d001034541e0100d078080c101e5811901951041100848076194440040c41c4540e01c01c0c00d180440030440b500f031080d05030403498230341d542c8110003000036403506280d01c521104840060454050a0392503a004403091079020401e02003c0c0d205d01e040c001414240104001070800b440200201d18003a201d420981c000600001c110355203080100091111018090014200c0440b40c0d941c6c0f054584021805d42c5d00c007001a40c0240949481c5002703503800416038034404c070030540142002e601d40d4020300b409607115502c00c80360703d43d0780d510100c0c000041c14106c420891103840742c8035440886003404042c1200c02030941d440c15004008264060744e20951204110300b09580b103035295a526401600a050966840e041085002c81c000c0312 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 791847868 1250 791846618 791846623
    0x90804180f0204030c0302040e15130318150516080d020409151a13030606031b090605060f0705150705030a2012070c0b090604060b0906031c021e 64
    0x1109640440200100210210030740141d00840c031000d006034000d004200090b0400b80c003c0c14008a400341618020b60003140c841c00014019110b9240e008454000c074000c242e0460074040c41d52a00c412480002d0b884c1503140c480703050901510000b000004900340043c0d400d14181c00c0f14450f03203c0c4520303884504000c5800025049403290801071820f200ca00c845a42c80c00400700140c9030405c160008032a2400300207a81c0f035110300c040c1e00d420031020f0301c00030100b8410310902c00518421180d4041401854021040c0445240c001c0d075443c600c0e0200401484d921700d01110b1101c84003103d1113445001c00c1c181942450801101da214458500d401c00002c2a0310000551042a91080c00c00c00040040407284c0c042c524140d6000b04407030208841e1440b505c00d400143da11004e60320f0305414110080e503031480b040380199044c2c0055403043c410722080140c907000320041c818050b50030707080d14506040000d81c2c03910720817031458400503051112600c0500c00d000c507030503403054404000d040e0010720790700c2d99 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 791849118 1250 791847868 791847899
    0x1e230a050f0c0717030c0d1a040b091302220e0706030e0f070308030406150e0a0b090c0910111b041b0818030d0f09030305090d0512060301090804 64
    0x103120403100005007030942e01c0e000341d5012a8100300c10500100880c19601200da02c090010035010300d040c051480d0541007401741c9815007200e9000525810040002d01c41541e0b02404614415130501b410454410b540e003c1c000e00b070a0301241c1e090f9458102100440b240044040f03aa100642020f248a03110040082c1b0b5404903000341c7d408101d0000560419a1502c144d91520707603564200780c00820100f00f0440246800c00d014130000141d42c001c014403079188480c00e42c40000344144420411900701d070075100c0c105000c4803e8035030500f81c4c5842d00084c0032510510366181d01c41c00300d8140014003288501d00b010081082c0300c00716030300050304070b440f22a03001207800c0d4144140e05003070302d03000c401c0006180da0a030011700782c580d54499100c0c400240c2e038001640c400c1d0301541c407081c003040800306824000d04c0d0300005d000320000703000d41c21414020252000185113800513801840005100341d400307030441e5143e003502c2503203c5441e01c690b0002405009982005441c019003c10041140e040e8009440c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 791850368 1250 791849118 791849131
    0x13170604080f090616020117100b0f0409020c0a03030b09010510030e33090c03030a1d09010609091802060306010e0406080a080415020f07050108070201021606021b011e230a05 77
    0x30103042341c460030040761004135090000c2c80526201002580d2400020b4040d10000b02c80160509407038122001c03c0380c0000500c180d40d9444600584207041e01849440c0c0202001ea60780d000319030405001c503160498010640e4205070341d400d1948100d61080c070000700300700311944c01507015800401d4000e14019282c29148005912031010443e46000047c04c440e10f0301c0e000e00071b0b608220802c0c00545807039482c0c40440e5442c0c4801c04c1e15400c40d035556440350780a001d0381c0d1221b18280b810322040204070bc2c11402c0c40f40403074007504002c0b0007590f541003c0e694449001d281545554a0f004080340c040d040b0340d840908144076440d1018104480da10142c000d0701c10700b90342c0350f4403541e00880481ea01c1c6a41482c508194201040c20700103944a4440a94040e0387d90001514150506408140840c050708007590000e9000c00c0042188041c0e2407070b100c92200400080c080c41030b04240c60f90040c003203d600c840340310f581c5803101040c6410220f1204110000301c18a484a8544101c04802030721040360070 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 791851618 1250 791850368 791850377
    0x30506120f3a1d0303310f290c0c13020c030d0b1f05030406022503022b05030a020706090f080307080708371113170604080f0906160201 60
    0x10700340f4600b0700100740c500c101d03650f080d903420840201c3c0b00303925420b5005024024501d01c01c0d0740440d110000101c00001454100060801c4d006000c81c1c00b40007046440c08210901010071020300340c080005100041104100e440e07050008245250f14028824900340c0c16060001241c0501403038030359403103403075440029a000649080c522650f007910b81419000e107008540c05002040128480344c1c0641684980098001c40764030f0400302445082c402d0400443c01a030041010b50000240c941c16020007141c51754080180e59840c0102401d140030081003500c94543c08a564024041d058200c0b2140c5500403080040c0070805080140c600d9204803101c001058495000c80c1070b692242c2d103420322070091031804403c8c5094003404082c1010321200c260911910f09418411551100d04c280312080101b81c061580d101034050162031421020750044103d2483e501c1c0403419414013141c0250300c958001e0b0010354940c000b0090110501450090940054003c01c00c031031a040114480d01c1a64001d884 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 791852868 1250 791851618 791851667
    0x6030f05100f03150209120c10181e030c06440403031104090e070f120807050a080706090302010e060c1e0910030506120f3a 55
    0x10300d0304041c0e034940319000111900150800214010401e5041c03121440d000151800c0c03003a1001401d00140390414a0164104c210200348a1606055079042e40246081c01715007005050503603203010540c0e102d00c1510f841880710b000c611040703074015240034551021041d500540c5814000704900304940c00711010701c0b000c210306025400712640b010151840843c24010850750700f007015034948000f410840a05480c0e0b0101041044110301420140018250010703d519810a09518007003182d0b101100c0f0360015034040c012031480c1101a40907542003004660303038181c5483e08910749001c20b54003621120022a5807400c00046030070117038110703020b58001e1144003a003075074480c3c03205000d41d02d0b40f4481c0c0f0100309100c00c02d21400401117a8084aa40032420200712070301141400b5035200381c1e580002d94810400c41586021138610040880b40b000400380407100001190b907400c1c0000c05091407400302c4405071860030101c82d11031103422070382c06d40e224843ca000700060802c80b03804207036240104001c103 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 791854118 1250 791852868 791852881
    0x213090b060306150d050106050c0705011409061b07060507060609140a0f140a02072121021902010e06060f060301090e01090807110f04050103152406030f05 69
    0xd124808040144880d2441d1111010494411803007420303a01109420301c00394054003a1481410700030041070711407965480002c06402c0c20701c10345420260500c803c2001d4016200184d0301a6000203009840240e5980444109039400d107500c0105051340380714144001c40da056204000d010b9840c81240d041c8802900c0380c51501c01d40741e148a400041841b00702c0001c0b9548110b0300001c1c4000c02110780011075501c8000d800d0100b440c00c072091042d090300000c00c1c10030070042d0300065a085030b260710f075242e6070013540000130a94412610381028149d01c060301c04055110a90480b40c3d90020141d0100070000300c81400780c003074000c81c19644110b002d110001100740c106842c43e4003d05000034011407460b030070f00703d070030b0028226000000150741d60b42515000044c07400c0000c06089016488070b26000912100f00305001c0c4008032854041c50514004000080d500b405075074101c0014603000c1400150040803d4105e503a052198852500e4402c0014005400d030303010072030410041106001a80c0d038507 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 791855368 1250 791854118 791854121
    0x6080115050703350105030d030b010f0e03120a0809010c051905130b040806011809020105070b040f24110c150703061208090306070c050d18090204060201021309 71
    0x540d040000704800708074400009104010700b0030b0300342542c040104810b00803200040c2c401c00810112102003414001841145410026088080c509141c00c1c0000381d99180000c1c00b14040e0002041031111080e0560082e607424040000340c2c00d68004060744071182890002c2c40c001080e83c0208165280c400c0800c080c611400807201c10b500c546466010307442c5003841c110b54030750150401400d802a1160702066650045c80104001c00b1a04010070155040030101c80c03001900000030541c1178640541400142d030000b0603240040e030440c02001d861342d00c0f401c03c11010341e04c0d84401040c0212401c01c246294030f00110081c01e60303103410380400c641a44911003c0182c40380d10600c09055000ea2090b00c40c4000b442503103940b00c3c20038a03000c2070442d6100441006881000d80840e00e048011a020010742400c202c1e86a10208500e000002144107031101c43c0c0300c4409460300420440c045020007070419040e0b401e4401401142e004540d2079a607400001c0c000d4010503851003250312903600008420005 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 791856618 1250 791855368 791855399
    0x120411150301061416030302091e091302042406030c0809100b0310020406080f070318020111010b060d050103020a0b0a140d0b030a05010501051f0c12090f0f060801 72
    0x50040141ca1a400d01c01c0660703040c000640c54194081c030420040d05501c0c404900c90700c05a20070344001d03860300340e5030781001071410000c40241e41d004500b01a9064907911240090740040300c5410720701d40080d843c0003040103080c0d1034080307510b440c020560050f104000505820221104c0d581e04020f1802119800c0b9586034065030f0508855002010f0490481840d91005c2103481c3c000302142d0703900000c0c8500f0700c01d907006540403501040200c4200180c0f14042c0d910140d002c0c4030b0380703810441080061440003117085078260180c1001542082e43c4c02c2c0f86400d62080c0341d441c500030401919045c810304408050305003408124010200c0c000c0000e08400e809060369420503482e125800c106040d030b440b851a540000e1440c40340b450b11200a0390b1151000c3c015007400d2405100003080540c10305041c46000c00c81e2001801008007400040c1500e250321503c10340b035069000b041c2400204507207004503032408203074002c0c001c87c000c103950006130003074443c03042c0040b2500c80d210040d10b6a603d0314142030b44000c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 791857868 1250 791856618 791856649
    0xf090609010902060304110d141f0606020a260f04180e1005130f0308060906100e0d02060f041217030114121204060f0215060109120602070602120411 66
    0x2045c0081000144000100c0400d400042c01810030040c054503040303500103041540c002c25070041040709a0b0030300d0040c1510f081ca40800420f005191034060000e6445094107000703040011070320550b24506241400306801e034522400741903203424503a0203000740c9a010344558801c00d405154a1786043c08240110042c2c070740303440050080007494a404d80094400100340c0e003141003100d034180700003c60f8000d192304d9a030702a0361605010f10303040c0c003071042c5d2520203004144140e440020f5840c103140d0003941114606401d81e005240c50104d8404a01540682c1095030b40005c1c010030042210141d04074604019801568160461038134008801f24911083c0686100042c100d404c80d070b480c4c00c0c20030580e900450342004036003c2c0c41501000c802c86803c16004080080d000e14040c01d42c0070b40c100f025400d1610501c0d11403d4500b00800060000079442c42410b020000e03441074042842800d0781036030106074110f101559914481c03129120100e00858040342c45401c441ea400150b4140411554500d45 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 791859118 1250 791857868 791857879
    0x90504050705070209040c0b0a0c02010206180303012d060c0215180402030405190302070501091e090b0102030f1602010801080c1003020f250524010b0714060f090609010902 76
    0x2800b58003400244900200701f900c000303406590010703002c6480f10042200341e1455440c0c080900c8107200083c03c08001514a1600f03000384241805a40d00102c1224110341003003162001c0c1a55001c0740564500b141c10094082129003000000c209400180030030405200f00e03440001c503030061202c07800500a1454400031800001004909030402da801107801a011b40300f101e41c10414106100c0c240444040c080f001a00036030800c11080d41c1002410000c0d1482019440f038080f000c4c10010043c8001c0c1c4540c0c111580c981003c805185d00074400c40300100302a400300c030703510031350001040083c4148000c200d0002d8001300c0001201d040c041402c1c0d038030110003459400000076802c81200650003049100800ba001000b0045640c6044a00f86414500c61076000801340c20a0500c00d05120381c004210a205185112242070300d04d14156480c15650020725440d00c0d4101400c00002c80b03000b59401617000d200c0c0d001407124024003800001d02c00d0f0b80001c1110003036501c00d80c030203080c0c52500200a4110 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 791860368 1250 791859118 791859127
    0xc010621080d1a09100f090911040506060f0406030204140604080616050c0f060906250f180905091b01050f030411030706080a0c0c020904030c0302120c030a090504050705 75
    0x1041d504101c00000f0340d20061005800c1c2003001030842034041e034620307105401080c8204612402c0b07000080050030070100c00c115900c929242d1000101040c21464400e9580d0400241190f45900c145c540e03550b22503400030340703490b12600007400a6001e4000c54200300740e102c0c1c031141c43d850304204980658402c4d2005c1c0a25495400407007040036080d5001a09010f4244440c1155040c1003002d10720702110b000051980d8200811078504202010f4008031358034860000b00c000205024000850307042c0c0c3e0740b0b884802c001280c3c00031544202c2007026001d81c0c501403500040c00e10043d400080c090095841a03504195480008045d801103185d4500d010503014400b6010b28503c990255900c64004c08002540d417920000190900490703030081d10100e201442030121000e03641c41402c0c1e0024a41c180b001d00010b85400154004200402c001e04104a0410540405200f484198480800045025214031340000300c161250442c085500026407114800605403806015090040050391981440d0 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 791861618 1250 791860368 791860387
    0x504090506040e0f07180b0a0e1305010527011a040914030c010504140604030203030c030406020c0a080a030c0203031302010c0f0c09091106070b0a0f0e030c01062108 73
    0x508402850154001c0e0f4403200900d08501c04e100c0000441c207404c025041c4e580c02c080c00d80c03014030743c240d40301d440461400044850760344904140b18103030f40383c503410034145564501d180511242d01c02801800ea5081130140600c1c10810048811129200302d0036103601105c4100030380c202c80841c001c1c196800507240b840e500c0340c14076901c000c001e58010f00e01c2c3d0002e95a1107110714a1640704602103440c0f03a55860400c410701c03190010001c0f003011003002501550a058074020f64900002e04103804840d4008007180402a0725811114231203003074070075074a40301c4150910761035503041708100c000401d00b40703a1805d8016101104481c071460f07182d25800c9154299800440d100e46a510080701c0500036032741480081902e04800000501040f1404250b59400d4603204c074454000310383c801e01540050180c0c000041034140082d40c0405109000900c55100180c05030140c20310514401c2e0f14000058103544004040d0040c030255101001e210100480f02c10600c29400d800190107003208030140703c920364 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 791862868 1250 791861618 791861621
    0xd0522031707050c0105040b0106030b03030703080a0b0f0301090b0106030f1814030c060c07020418050a0314090a170115030807060e12031302010807021f050615220e0403050409 78
    0x2c0110385031030a50304000d00b0740c00342821a00e054409a1300f00607441c004101280c0d16010341d043d0b07048158017560400c6882c3d035020348000005480400d40d1500d5280401554981c3d18440454400060080c82551114107120900c44c50a0180800080c1040d02907850740c1001e0180c0c1c00b0320b0168900c40301c000c46c41c584668821485480304034840340000c100c01c00020404000e607030b000d0003050095554400c15841008111143e6401114414441c41c000c000451404940f0020f6103400d42032007860741841c012905554410303e0445503002502c05004501b043c1080104410b0751100c200801c490100f82c0b80340c8a108546100081c0502810070480000031415008208882c0c00b4108503080b9081c002c44034030700c90b003007114a80704400c1c024803114155a441200140c00c00c1c0c0500180131086000c02000d2074803954070400280c696154408500542c580f0f41c480041c4524417056642c0380c00d03420711040c0c3e19840096545515455101021484508207902d49010b5580750f11968030b000d01d094851030 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 791864118 1250 791862868 791862871
    0x10b0a050c0312100602070801050106080612070b0309010902041a0a06050c0f0601060e100801180207020109050307060309051507020319020a0b0415060812040e1009020d05220317 79
    0x24860000740025242a0609101e0a01600441c60300454003403e080d0003e2402107c5c0c0d05c4016644e0400c0c004201054120040c03980080040c1d0f404400b26010819031458001070b0b9000849130f42c000000c10500c540194081100c4134800c80d13041c0043c0100c200b0b0305c04804000c45620b80e02c40d415502c01c0250f54015001007403604481000d0740c10b2403080380c01c06c0d0309000b0264031000200700c18914902c55498200c103e50381d40f80c1d4070300300304a0395414880c080a076125240482d5540d50303800240407040d03a020b0740d580c2e4010720005080f550060349818005014081c652400c503194400c100c15a0760900c040b116088c8250021b60045081c03107030b004d82c80c03404507202c90140b0066010303030041540070900e04501d291040b4069000003111100e00400c1404407001688101d03582e4004130b1901886c0b02402045504460110700030b9010341e1295101441c42d03044a41c08070604074070008221101001f00e402c031074818001000e250b0003050811102440410340c0d50401800510703e00441c1074006514103109 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 791865368 1250 791864118 791864137
    0xc0905030a05121c0c020a0233090d060f0b030d050a02030a08132a08010608031903140a0b0f1e0405090f0f0606150f0d0e1f0c03060e010b0a05 63
    0x28101e104402a00c8110b4111041179401a00a42041c0b01907050131525108020401122683c000000800c145140400c80505000c5e0303040001e5103c002d59180d007101041c4035044ac0341003240705148613002c00248042c0c05414001e004618094030310f03501900940d401024250069407400e403882e80c044820b05c000911201c203480070710002c00c0c007068507200c0fa00d03c02a15044903c01000051940342c1018040b94003c07590360703040041c1030128681c084151030001250b6115555082118002900135040c5001c80318004a084420891401c00c0c54002c404101d005460b44001907280f0303000d00c82074140f81d507540300c0f15000101c11810241410792200d94000c0850090314504868011000d040c210fa81000307100d00e5028074103029080c90f02d80c520110305021001c90f5890141034150454041c042c6900420300ca0b81d5131680a500f0701c105100303820401e40701118a5901c904030841c007000814070400448002450240081040a05d42540e0b80c16a409000d03180c0c2095a80202200c0303540c4a150030 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 791866618 1250 791865368 791865397
    0x40e0406021e090405010b0c0709090609020301050c03011a0405100e1210090203010e0109050a1202070f0b0414010c0302030f07020a0306021605060a020703080103171c0c0905030a0512 81
    0x1060b68081d1003003082e8001e03210b400700340d40c81100c401000b0540340c040c0c0001404000801841200c050000b030700340111003140c400450800003030300344000200035840b0080d405500b4802082143c958034001141603802c4070115070041d50520110341160b000e50301400e60002030307164007098024003039070711111031400041c500400310040f81900c43c02c0c510441404810300e43c90f8a103010461030b081c003078401d0741120403000304a2041e0070707260320b540c82004e154007405ca01444101030285d03a20034004500641400096501c00c2642e039039590300694014031404c1c0d040103008a1080d02513110307078400901241c0580c0114205000365052540a0b0300900040380d0140721380500000041580c009020901e0401d90000c40c0c0c501141011030030900c0042020510900c104040300000303411250081c15070741c200c400030000c3e01e400350318803070140b24a030f035010388024000707910303070940000d940007000c02c3c8403999503200c9030540d00c1c000d050b0354550042c4010240c0c2c000ca000d1010307054503d0007810400031064074 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 791867868 1250 791866618 791866627
    0x10503091f0213081204092309060f0703140708070e0927060417090f090a0903020714090c0a020106050d1b1d0604051801022a0a08040e040602 63
    0x35200d04414004215001a42c010400070310040240055030001d08204001c1d082100f44841c80b10010303c9a40194030b002a59091003141043c500740d420080d1542e0442c0000f56802e01c440c640d5a143c0d0101c0c1c0340c040f9502040c0001e5881c0e8445e001e07035203450004c002504511340f200c64081c0d0382144001d009104004038541d10400c20364032944107901900300f032564141101c2110407049141d102100000c1280c1e800f20040c00000b079020ad0300060805010005a500e62000e04005551035001081043e4802c06101c244031b0003240c80c0d40a290103d11903001c4404195443c58540100720040b080705501009140004402d8400d9070300a1004026510002982e1900c0d800002c100000b550419228030010a4a10601c6600020214080d107800440c0e00342c01501c6100f2584e41c004000c001500a0f40c031800890034400340c004801030150100300081d0340b140c0310141c1d20001094160800e846031590446040c281c2c01000c1840c0003860341150300149802d003000c82050300841c020300100c5100d0750030003 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 791869118 1250 791867868 791867893
    0x20f1819021905120f0c040b07150f0b1807050d1805060903030106030f06120f0c03020a080c0414101a0f04061e0f1220040303050c060f1501050309 65
    0x500000c0c1050742c2c0d40300e040c1c8031807040c403141e21201c1d0002c01000740196600240483d0074a40001e840869200d68403240d51100b0700d00d07004101d0f0f00000d002d00300e000c3c20010a83c400810f180c0010011140c1511065410500695004004078040e41e00d480854020070031900c01c01c0e03254011417000c0360b003503643c074129050540c0d4942c60301500329a40b0f10b440e000840103000c101d505015121100707007020000c0c0405814084026040260307e000246000b220150742d00401001226050080d9001083c8a02042c0e5034801c481d11016082c0c0d10390305ca90b1038404a003640c00510104140144a18940030601030308000454101c0d01c00c2007441071010109014900031048464020b0000c2c0030710b660752058203c404020401030904145c1c0305428440882c6800b2100c070b41c0040c0d445003405107044040741041d40b0f0a800403203218400590061186c5c0081c3c08428143c02c08020020007080300100c2e0045e0303a0b0b0407240742d021300e02641c04507611240010100401c2d0300c01d001940c0c0040786e240c00c0d41c81e003030301d1071 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 791870368 1250 791869118 791869147
    0x2a15040509130b1b040b0a1107150e09040f06021b030c0a03080f0f040803060406080a050705090708041a0c0d0e06011e060203040b0d0612030c020f181902 68
    0x2203600785591402e2510340020880d00c1500d0503040440c01c44800c0f404c401600381d0b400240228001c50500c100c0202c0c013030386468410f200ba0300d00700500c50300351130340ca40e291101a4a02070a60500c20041071038002500ba0b907040604426100320b4006246504600c070350795400300603600c500c3c0c201400c070b1302411b0442511001031004040c0c40e003040c002080c0d407d40034540900400b00c01400540100e0a075410000c00305041d45065512950041805680341e4a0398001f40003000c154010a800d40b04106101c0100400024034806440c005c41d0650305c1070f52440c60842e02d8450840e4010100c0b100a00b600e810010380b80300c03140d00a901131003023504068420144800b2184510950031007036110000411030680345103803100700200041c860405490401902035940d210301d03c198894040000740000020f4400e901c4040540400c40618584101d00d0034001c004801101e800d074845e00f6000d1002210f40340c02c040c100383c821a1180c4202c19a561505000301c4204001d456044d4030b0307000c00115504920b035 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 791871618 1250 791870368 791870371
    0xe030901121805070e011d01060804121b06021806190e0d060e0a120305091504020f040507052203121808030c030d05061c1203060803041401022a15040509 68
    0x2010714681c4a0740c0342c182c401d47d0705030300150085404180840144042c590004485034840e80008130a81c945202c0c0c04201e41c000d0b0454a00c0031400e001c05d0303a50303081210580003000960340304000c07090607001c01e104001c030512034040121b64071440f400703044040034060548482203940080111044041d00c1e01c401007034444800e441419600082c2c031401c01c01c0b410305512550b88500d880d0400840c44c106403013036a500717818004c0c903045000240006d011543c5000c0c0c50640094094401d0105040c2480080c04581040e900c071004100c0c02d4000d10b8603070480c4a40b840460750841500c580d0681c6940044da15024000c0d11051001c0701c15002003400d880400080510803900da0040d5640c1219250703a008950010f002c0a214031030424030308088004c480e040700c481a8220326040e010f180c450030150300400b029072000111340008107000a03a500c0b007070401d48140400780c00360358958a021250403601d041c030010b45204e403040444414100d0502001d0222010110301a682c82c01c1d8881c3c0009068200 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 791872868 1250 791871618 791871629
    0x904062405012c1201090503070b04020a080d020a03110109020a0605031b090303030c1b071d0109091208071209060b04061505040e0a02040905090f010e03090112180507 74
    0x3040400072035a1000e10b1481210518602c1c0400298419040800c2c001d4200b40622843e01040c010350440400e5220180107980074044a030345803103a18042806900443e0140c3c40740910721000210001c0c0442c8100d500c00869001d070020903019502500c00380c200c00f0254400b90360350403610005881d005518400f400c06030b2602074881c60400c0503650b032000c00e100e1201745448140800003503074038000207030b07900010780f025007503118100d1800110040d10240c07140c07000362007810000511110043c404c0094442002d841e032019a8803243c945055484c18840289114814086c2c400541c2c0701d00b505681000301c0340741035402846424500c401303861040c242a10420ba40381200b95841c5031038400c030401408040c03240350036a1600f00c03000e8000e002c0d511809080891880c0000c0c0326400c0c960407034000d4030940004000c9803c3c2140351a0703903400b0020201032250300c3c04c007100340002400019a1154107052b50f5010302c4c6254a04010f0280c01420240150400740d00340100000d07000388804e002501 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 791874118 1250 791872868 791872931
    0xa05031005061209010506030a050a020f1c0809030615030c091f09022205010909020304020609120a02040e011a010c1b08030c0c04140619080d05070209090d0509090406 74
    0x410480b8130b421242c2c041c180d10311030343c04a54400000350012908441a03501140d030741d98901c0501010a181400c0060310201145802c1daa14082000711000b80031181c0c8140c088458940d1440022044802e000b500b66515612600c0030280b9446e094019a52002c80f4141266040e40d02d000d141080c00c0082d0404010f0540100d01e82c14100b200e404c007038042c00450b0203540000d80c030300360001c1c0000b140d502801c512150000300003801e64031800b04440c103458001e055a40e54500300c88181d81c590f80c40032030407803003941001b0311490344550501034142c081c2c1504041a015161580055802e905110821250a000f80101c100e59444504940d070042107800302171a45d84210040040c100781c00700800d01c1c4207070719203482890480000c958603071380108140c0301809800f071110324521034141c00358041c266a00c40c6041c2580541c0d40720340500865442030300e4180198943e03282c00c81c0c940d10407144400c0007503418865040249408900b0540050013000700040d020290400720345000c0203400c6046160 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 791875368 1250 791874118 791874121
    0x30b0f061815071a0c0a0818120405031509030d0b0301090206071110110304120305120916050904110f01090312050a080703150501140405030105010f08120406050a050310050612 78
    0x10000e098851000e540b0361340a0105450480da030461240180c4c1d00620820005200090418868208040c4071255030300032200030a524544403521035210f070041030300a0040c0110040d80210340040b441c010081400594104040410740030b008010081070980e040d0f480d002ca000150319400014007503140108600c0160911450038010f8600d02080750038100540b0300c1504600e8040030060f9016507017140e90014150303409080032200350143d00d5000511035040300c2401940d500c00030301103e08a82c1016240403d503660402c100c0f0300305040350003429603111460710464500d045001162550030504005526640b286c4407244410290324407100800c1c030000d280c0c00303016004043c241d482109031400340b2000f40841d9038000b2208647c03080c181130226190611446650120654001d0701d006402001150b030750f52001d1800303c00b61300c5100302e82d0146d403490b0602c184508044400786da909440f80307803619010b20bd0446195200400d1a00d0b0a82c1c80000801c0541c2e64100030440417055241000d0315 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 791876618 1250 791875368 791875373
    0x30d0b060a05070f082208010e0c03060a0507110601060c031b050c0d050129040605090106090303080406021303080306030f010c021f14011212030b0f06181507 70
    0x488006105462198005201da10490340e80007080701d0600c0d034090228211030b0502c0c5080c1d0180d000e000c2141142e90001043c02e420065994a9442203410440081c062104204556070302c1e100c516080e290180c120000052007500c1507002242c201119103800c000880100070f59905003030003a04500c0006001418250515500000d000800181c42c2c44480c03404400d6076419170744070200e400071f50103644805c1484051000030740c0401c1458004d0b8090b440395404001c0d084080030340b19a80c0d14440c43c5407031400305803810294a01c0d0b06855190f1540b49549007141c909913081c02c0700400466071a5000c020250f10b14031600c074103100441c4a04d518a8903414803a080505000d1080b040210b2a07150407101c40c18682e0014111111041c00740f0200d01e100042c030f0021002d440c1d8109241c1c0c0c41269500005441c0303403060300300003909000b880407060301804601d01b18141e0308607620055000d41d1341da42c802c1c46494450014001c54007400c00700c80103c2c0040c0c000c13501c0c555940207110303d080c0300415400c01307 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 791877868 1250 791876618 791876621
    0x406080c16030309020d0206030a0606090e070503180f010f050403030b15180102010b030f0f0d02030909012304051f05041103040618050a12030b0409230307060e030d 73
    0x8010304044603050910790445040c81420560100c05000c05465049081c01e5484d218418404650060002c0c3c0e500c0c41d00c001c190015085034419000098a1a10006200d210440700343d03016456aa49880c50f40d240d8808001d01095000300002c40c60040101d115002d0741c091290040c07112480c0700c003041a281c00d080c05021210307035540c1c0d2400354101d40e655074500300c050011600d0704034040c41700311245846400100c2c0104500000b40350588100081941e140100203041401804118115824071640250490301c03402100c90a43d00000a00010301040d40b18104464000307850ba024101010340801c00101030302c0c0240e64640c1c406240c0f400c800140d1405150b00700150606403001e0000002c1010025070b18840140054810744d62001c06071400f551408071710403c0c82e048400c850400501d8184464030581034504036020929055a4000c1820180248503a05401415a1805412041c100e00d401e94200200340c2c10790008218a01c0064024454201a16103220043d42c56500d4500c0c40300 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 791879118 1250 791877868 791877871
    0x70b27040e0a061505090c0301151713030c0b071101060609030b0a05180f030a0915022e0f06030c0e0420011e030903020c090610030b061e040608 64
    0x50095007458200d00e10724100040c2d85a0507540f0600c00958050400a00410326131550481c03540718103c60148071410200c00c0c05903050347d0741e05840c001c95603a14441a940410b43c69040441449040000303101800220701e10384556009051040c0b11481994507186154011680c1c2004550785001000032114244510b502910079800c0c103902e03a5085803a05190980014590440e803600c82002400d0020541a21140801400100c50a54402000040d2241c000c40180d9001444c580c03c0060700041c1c071051010b44800c5500905840c4d072440c04107207001c1c5010820292521400030f0013030001c001d0741c0b1851138095454030340021003e00b549003440c110005a80004a000040414040422041007451440c4030381c07070300700c4412885101c00503103c008020f08980d0980000740400360005806800c150406846503082d1043d8151714000c000d0102030a44900d07410030401034103216414007036801001c0101c00203003a00d082210001c2c401c44d40e241c081204207901c2d0360105003002032540103031820303 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 791880368 1250 791879118 791879197
    0x15020c09090c0913120c0b09121606060f080304091b0e190e07090e13150e070e011d070f020307030815130221100608060102070b 57
    0x8081e052a19040c0e40c0c0b00d00c0b108400d8407815242d40428446151401c504c0805035002c20b003105088485134000d090801a500b05a803180e14070b034002903610b9000b2644851101808250f2030510300c13981880ca85e030a10b05402124080c0d61081c0c041414448102c0304c178000d20440004560f5181040d54107001d48400c0208a001c1c1080c1c00d40410398144c00124801b0740710740c2a40c40740c554000e052020001d14036a540860440f62100b005c1c0310b201544040001d05807600159020707c6070f11203d00c003661640d0400b50180007001446100c84241a5a412030b080002070401200c0301c5540320303400e08024044c280d02c41050140480e040765564101421525030050250030808095510040301946130b22807038800030100310001001030042e001c00a09403c414034040c0c00c9414880042d43c600000398400000200c01444024032a5200c018100d40607115140f80368640c41070074500782056500120290a00f8194013030284046503500c0c1d0707400a480d000c48110119005c03241d8000b41c01c0c60703219929945 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 791881618 1250 791880368 791880379
    0xf20060a0c170615040f0b1305030d090b03100e0a090b06101b06020f070c0501080c090a032003030307020d0905012d032310120b07030509011515020c 66
    0x10b0b480302618803404594050b000303440b40c01413a0b000701303003400003449541c002d42e032289281c0902040724020b0401410500400e0f200080c0140c3d101d1007010340e1102070028440c0000e00100051201d21480e801550708810341d0102000c0c1c5a03203450040511500071520b180c0c940707544482d00e0b002c0c0f040c0000d1054004205607141d00e04400d40030401010075540d884020071402c44c2c0154002040902d5044a00c802c41c4a05c24a40310340592502d00a60034441c40703500e000a2014002c80c020206c03800c1201e030380701c2004100724240c074078559403100b083c400b45561884a0071051622503039510240f006520854003036002d050090420140640f040d04507400c0113040082100c1084060340c40041300c16030441041520a801c0702030b418044004d01846d1040c82e0100903018801c1c01802000302e50320b0b0040d240e5100100009464001e000309a02540001174010b89115010071301c41c1d402a800542c001600c030001184030054583d1440f10b212507607101c0d0403541c0500351913113207295041c0300b0354505074001c031003 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 791882868 1250 791881618 791881637
    0x10f020f0d060e090316210807180605040315020408031c0c05040e0c031305070f03060b0402090303070f1703160314160e030f070e0106110316030f20060a0c 69
    0x488a6407406072258606c00841c4a21602c4107101d48080710300404901000180c54011010100818140c4161101c902146682c0b681c050845401c0c50440d09640d042d41da0541098596140d944010110400c0000459800c100120714040c0500040111040c1c0029040c100c1003103d480c0b2044411a4095004001040c0024041c0c3e81c045003025030001c030025407644d01e94444079409184111180c0c0001d00c00c1c4501d0380c2c0019070040d4030349001c0031a4007a9204000485103030741404160300c20082b640c0d41c503410400038200014039148248619a02401c4040d000304200500040705a000341c031101000c003500150140603079450f0107040300c1949c1094403c400fa08040844030096070f00c1a4084041c0220101000c2d6907403001c0022201d594408400c4403e2255140710071603900000f03010b2000042c092100440c00c111000085854201c20f0030341c48040c0742c03245c1d2070440718000041c010008215035000110784441c01801c082e00f450200380064030403800c0601910080303800c100704800620000e400c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 791884118 1250 791882868 791882881
    0x309090605060a1d0d0b1008010917070c0e09010b1f120e031216030c2313120c0e15030606060705010212040303242105010f020f0d060e 60
    0xd0b1144628203050255000d40211076040458a0041c0000c0d001402004c82c0780601c0791b0790404074041c03840151010742d000e444050603800c0e2400550098003200740054402c18400084000342074070360094040705241501d03841c040a40940c1a0b03078424a980d10303401c100005252803030026500210b0010303181c10b0b004c040903001e0990080c543c0d012103800d50350700070b40c5049030050003110441c144601e94031841c0d140c96201912028110461080040e1414080c4d0413007a00034441a008003205188000c0d07403000d481c250b008280d1018a0200090000143c0003c00b50701d40c3e5000c040c60740c4210240c3c015181022114982258011724200a68103d030650440c02c2d140802c2c040c0e080b11056582c01d56440c07860820764007a1244040341940c08000c18200414103500d544001342c00c5a00760a9448084000b02e40c0400c4403c59001d202a11721a81d410000c85124000c0c03040103180c0302e1000480e0400c84e00d020070040707070000406446000c0b00013601c17081000061268401601c444c50440c012030074400c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 791885368 1250 791884118 791884129
    0xc030209011b050c030d080a06050301060b030a0903020c060c0d0f0f0c032a1407120803070806130f1e0204240e1507050c090405120d021b06040309090605 68
    0x2082d65496501c00d41c1180c203111081c4108991a2000341c204c030581c034a0000010802d40c01242c0c000340c6c007464590003080f2890113008010407144528640d0741503403101300d10003005101c180d50071820351090036003034012602d13100041d000604154003d851050509680a01050f1f000b0110b1020010070255036040b20b60000d80d1400441d4051a007210100d4189107402e01203442407070680b07030020310210094204540e41400385000f225860695a00c5952001090106031003000c00502003682800001c003960700c0b44d0402a0300880090020b6042c1d9140c041c801e040303a0f201c04900d800b00391228503008941144002c1020301660b08441140740c00c0c034011014500c1c450400c0407610340d100301071710603040358814070000c21007030402006180812401d40311011980e12030001214a80a20440541c403450700da15402e20598121020303211041d40740e00b620400d5032041440017401582444540d0340c46030203031502d0140726207060041c0340c1c0703084c5802d0140410400343e214641040c1441c0b0103000a4071070303 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 791886618 1250 791885368 791885387
    0x40510060b0409020c0709020403080c0f01020301050a0b160b27060103021e0d060c09030c050613061103121e091b09070c020d110a0801020a090506070c0503060108030307030c03020901 81
    0x40403c0181c17140150408242050f1140d070246c1e000d5070010501200380052400108a84040e4000321107201e03a2803484079090340009d11a15622480e40502040050307800c46c001c042c04900000051400b415546e1902c501c0d050550b03651800040d105003510089280140c41c80e44104084000c00c0700d0b40c510360018201d1980c801c0f010720b0120410300a0303400c81d00d03190309051099500038400e000403004800020120700e9584000ea41002d03a4890000305401d1120481706409000780160804504001c4140c074000c038040b20303c1400f4071007000046a40304841e103900780101c03201c5204200901d1264158008048064031152060b008002c0c840459241d520141407002c00680b41200c643e50786401c10744600030300c140041d400c11f005050481c1003014880400008450882d4074001e0a611290010700300d00400c603107000400c1000c401402246000000703401114819480c1c00c00c116224400300342440400c3c0d00115141c1d002106001d00140c05000c0c0c80000380700c5150840c146502c0c0d60008004101c0c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 791887868 1250 791886618 791886629
    0x603020f030f0c1c14060405071a0901080c040b0c06010306050601022d0304030204090b090d020309030c01050f13080a05012304080d090b070c020f040b010806060d020d14040510060b04 81
    0x15a40003c0d40c4141d0f0480c41113280d40002c07406544001a01d41e4580b0303078104a1302283d140c020a040850310103105040c0e00c0d00204c8030340040b4145511540103592219020308484101c110a008c00103402c4003020046c0b80b020402c3c4017030b0070f0b40e52451030500140d440c054804e50564001d940c00a00301c102d440b00ca603c83c41c0408004107428260340180c2c81c158071480c1c03c040e4209040c2680e1805001c5100c01c441c0c0541241d00c2142c0d52017000160480c3c503809441c5c650396146d08820740c8403c403076224101410081603002e125626001240c2080001c990840d40400483e4010800703070307824454284944d1001c110b1043c80100d8810301180101000d8000810040154101040744078019005900012000307903c0003007401e4604001102802c010a1444200c1c41614840600c100900301405085050304041c0c407418031a403501010465a6041607101303035030480d400c0c0007080d10350410b40656002058014040c0f03c96060a04001d230800f41c080d101d81001904200301000305000c12400c880440701c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 791889118 1250 791887868 791887879
    0x1d0a121b051c0602070816120c0b0106031a04180c0902090a03030f020109061a0f0102120f1e040e0604140f0f0703020c011d1e0307110402040b0d0603020f030f0c 71
    0xb0354502040240144000070b049000041103102c0610034107040384580d14021115aa18040c65100458407680d6440c801440c0c981c1140041054a0282d040180b000c0c0100b042404442415008682144d04000c4207140340307521800500c09101c0411064406080c042c10300390314050203d0f000c66040b0003140310050410203440800050240300f0761140454682c0410203000d299441d42040940c1890521803a100e8280040c8038002503000048468440428840c51070400071a01c5203807009400c07146070340a000e00c2c040f035104c0c413070314101c2c000704090241003c24080500300a410b010445545509594200c2128000c0c808801090002d540c1d008070340303022481c00340d40c0d032810480c0039000303136503080110750302705082c0340c410760700070110b0000c4109400119580c00e400d01d0310341224610291f07224142d030b401c200035140108a0b46010b06401842c0540003520b056640c003680d40c02c1340c3c000110f02e41c203556508028130031840e19200c0001c90006c100c2c020549408000012174449901c2980c845c840c1 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 791890368 1250 791889118 791889169
    0x901051e060a2115150f0e0423010305100207031b030504050a0303050d150e190b0d060b0f040c14070c0e09010e010f0204181526060915071d0a121b05 66
    0x10343c0c4582100402c270040e40024000703000f4491074018240c3c804e000c100c0380c40c000da51710034a60000d03c0c8240c490254250703a07580ca40280341404244c408607108015420850100700220b140e440347d82c80302c0300840c841e0303644a17540c9000c03507020307421180c071500426031a09211008000c7c0b041d41940700c43d0400151061401850000105030004050181e00507800c08004054441808001d901a003030802040c1c81c42c01005d81c1c03860800044031039206841d40410300f0344807059072246446000d08201841542d00c4c1c0441500c070090b02800110455180c0722a079140c1c1c1e41012405800e00036211405a610310a44c00c1c8dd0601c2c0c40892401611760300c138481c096a811a501e40e504e050440400201140d444180717840c0e8030399182d100000300030320260001e44074050204643d400d0001e600d540c42c1c44012640c1c0f40b41d88030b60600701d9240b42034061801c00b04c00f01806040c2150382d80c0e005a0000c1902d0780041300500058980f8038401003000c2c80344041030300d16410400171611800c0040300e62440154410900 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 791891618 1250 791890368 791890397
    0x608060a060f020c10030f050f100b0f0d021b1c05030c1309111b1203010506030402030f06101a130501030b031c0c020901051e060a2115150f 62
    0x3130a40c070543d2503602040071080303501e500780c05600c44502044080c4007400180d96030740500700890030980e059803049030b0400007080740c240d0040142c21215290142c0070b151001580c82d480c1070b41c10001400304200148043c48085010801c2503221200d03c0340b200005180e59228060000c1c080280220442600003e17002c1250b000c10701d4010140980302420080118800d020900035007211414001001126040c401c414074001010b01c3d050701f00c09041407440c4c1c02c000038000c0b281c1016000326014404c41d43c605140031014841c0d90f01c14004682400c07111031411088003024007040c2500d00101204000000d951060041c040003038500038200424000790300b10119160402081c00c03102a003041802c04007040d648040c0c0200751500854074442280d0700e65080000012130358544000c3d070700300600b101d0341d80c2c11301c81c0181c9080b035000e040403001c050702600401240c03c180d00700d50140035600c141c0000c1c00c0081000440c041e00d0003155100c18803018134030141c010302803e00403005001c2e80070040b564 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 791892868 1250 791891618 791891623
    0x81503030d1506080714180409020303162a05091305060f060a051509040b130606020307150c08040b0c1c0e151b030a0e060f09070608060a060f02 64
    0x51420550500300058160545501840ca1090040f41c0c00140d4803070124240c80d1107642100b1002c0b4902448629112019040d007002244844610790401e48400b04140965000e001924001c4024080380c241c01d1407034600030003035002020032540d84c0e15025584803c401c02000d44030082e98401e4030079503801d0710340705540725610b0444030004003d0f200d250100a0030224040b0f0f0b9034052842503650001c034070780742e00030050302c561500240d8003844010b01c0304a05500e00307034102564880c800b0700510324603044031420b00c0a40c5d049130803840150b07100194a40c00c004809081c0014503080610401134220340e040c0040002e90041c20142441c444071012504900d504c40c01c541c0349104254501078a81c60041800c00a13022000340002e01d40103c0c00e0918044043c840c042c0d124150120701800320714605c1c0500040c6c4e800c041c210380551907581c044885140000c1000382e008401a06002d960743c0b0b030090002d803524100d90016020081f405042c802c5580b281d005140035a1154100001982d89480d0104e2 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 791894118 1250 791892868 791892877
    0xb04061b08072915040c03060807060207141206061e3d051b0c03030403080304120908100209011106010e070e010c2a0308030114010806030a0308150303 67
    0x24a0000c00040b107004000100c0640c0340010481001c00d0020084680301c0040180110f5000000e440900319090142c0352581c0002c0c049421420002421505c40c00101c0c540b0486e9000b000140c0c0c030040f424070102010f00088016444116054500e0380451600c0f25240c04001d0601c0d80035003000303e4a40d140c001c82c0c208112907000b0151408030b92503240e03803011501d45031301c003602002d4140795002d0b8110300d018a000441ea08101e91941850400c0d454030216a40c1071480102005000d90410050035a070140000d000850062128a0312802c050074141003001c0203a0200381803020007207041119035000b00305107208803403520340161216001c0c1c1c01a01c1c13600303000c2c6044800b401203100101380c3c2202503680314050491942d85481030100350b4010358000410103c040c2c80c100c1503c1c0070710142c50245200210b072a0003881c42c0d821451345c0365135400140d0001c0e0020b501c4c0034000d241c400082d50380800d00a6001d40210003c0c16001280d031000b5041c504054401c00c40203800e0503d2509584040040381d = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 791895368 1250 791894118 791894123
    0x280305071a0f13050a14070b040e01031a16030207110306070c030201051b03010302040c03020c0a030504030b220f02030f0a0605011401020d021005220b06031002040b04061b 76
    0x140c41c0809074003407151070700310200e5680b500c0c002180c1c0412900100d0790004844964840024a800101e5480342912010180b90b064100c4c8503039040070070b895061501030001010703070500e41034440d415454809081200903080b40c180002a808020140308501c00b45a65117865040050340d58950781400010f520f403d0f0b4030240c03d403050b603060100d825800000e101040340030340e00802050300d600c0d010f03800c2c203102900b041868460500c010f00c050b25003680001c070505c511b410010702c1c0c0540a00d005007401c10140040e0089200030034204144212060f810ba4001941d6200c0306400b80607010084806017600009030100a41080850071510304100038908107111100703c131032100880c075029005c0e100034050044251280181c0301c416500006640940c0d8a141c2c0240494400e4141c81c040103100081c005842000c02d102c1900204050001300c000c483e005011058072441c244c0141413a007440d5542900e04184100402c00414400d0300550b0300303030780840c03614040c2c0600d4031070b000202d041c819001 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 791896618 1250 791895368 791895383
    0x20109030906140915221203180806040c1508010e040f0c05061b070f060c121b080417062202030c090a1b0f050403060b010c1202071728030507 63
    0x26144100c058001d00781b031074103249102114158142d104440e51080f4030408100324030911044000901a1807442294601c2d05e0122441580d01d0440c0c17403800405480503520860803007010309c080900c08441c401000024200b107001035240980d000d0060358000d0000e03000c000e00c080b038881040100c07052507000b01402403440da02c1c0c1d080c0d403203e01203810303124038614114425108001460100301c4400d5045441a0310351240030001516000000c40b16000c6000c100940c41403200303e04206110b0001c41c05015450103903c035401c10881020300309200c00d0b8401c0c1640450200084000d08500c45006615070303509a0401191134400702e07181c0300c4080166541305a5450401c10018040d03805180e089049000d81040c28550342c80c2510720780200100c1d1000140200810f1022480c0c03070700805080c40d010b2400d0442a40c50b40ca800003049040c40022005800071002006102c44942500003c0e080b65005040f0010401c000e1000d2030340c0310061542c1020140100c041414060b00c165070440b600841f0 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 791897868 1250 791896618 791896639
    0x1003021e03011d060702010c210203180f030a110f07032003070308070512070b0114011e110607020c01080f0601090b070503070b0703020c0606130b040c030e0705010201090309061409 80
    0x3105842d04d0085440d100191b1130010381c480c1c0710707201c0c400411101c03e1481d1058007070141c800500e8040e40c00286110851508900341004401c005c0041510400030000910307200c010919009100c015603101028050b0300c4600f004c0c16101c0c0129681c02180e622609017161a030944102004400c82c2141e05541405411030000501400760024151944140281c4214146c040d650703011a000350741e4040c01c8421a940144140b0030350040b4544114014140460342c1000d40c00011003503141014a500003802d0800b2007810001d0030050b0507081102400503003000091800024090134009208032038040500f004500c40b40d000b0402030000e0b044008140f5a140303414100645ea9602c02c40003202c844051800140c28540700c2d20a950820717542401600301c0d42c0300e10007048158050260841c100e1983d03100c200740c40d50350314030502d90106e075940c402040000002042c5410300c496a030061303056904090340c00c80003030350145901c0240d80e61420060550f41d034031082110300d0b014400b401c40e0000c420744c1 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 791899118 1250 791897868 791897921
    0xa0f0207051810150f030f090b130c050405010810021b0708030c07060206040215222c0f0f0c040302061c0b0103110406141201030b07081003021e0301 66
    0x450300c03441100042c00448025a9546000921044e540c07035030400900180030038079007903200341c120440f121350300710000c2082d02070b6480d4801c41030700a8482050f2000303800b0f03180042054400b104801040204c030700300a5589040103841e1102d03021010303035501d154009000c1d020700c04e601407a50700f41c4040e14200c509058481d0710595a85d4025049040c0a00c982e01c0c0001c2c58a10000360680300d160b000c1d00d030190600030644008103a070000c140449002da56101c01c00c5400c54000703560b800400d0040240d128001d030541ea40c3c0010480380e00c6100f0b9403196081000820410300450982004007034640b509a0303070f41d1a50790a140c0c003450300000e610180c0011601c03ca0001403075241d401210071202000b16500b03050040d01140d61164607910764140c107010070440140605079010810b242d8500071883d012204040e1701c0b0001c0260030443d00c0f0a01482408200c5520030360031940070302003141001304507045400041221b00e801032401c8101c04504883c82407904e080d081590b080704540400b208030308008 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 791900368 1250 791899118 791899159
    0x70602130305030a091406161505090c010e0a0302060702060703021e01050a0c0206040b0412030608030409020d0c140403150b030114010602061e0a0b040e060108030706051b0a0f020705 81
    0x1004d03000c00180d203000e400300b150170710400303950a0807100611700703485c000c5d1a007010407903d00008070603101b0707118050385802072411354058244126402e0015012402440c0000340c0501c242e07440490155030341d454288010307124030049500c01034046a40c591071b0304084c84e0403842c2c16143c20502c508003000109090500a05400280c010107040c9400d001301e030800d64040b691110201c401602d0804000c02103030100f4030141c02d032984445c003440c2c04201a511407940e1403035540164064541d0300c0d40004c04c5408000d09200d28010580c030392504202e1002000d4850b07020340500d00001d002e55000c00d04001c0c05194640c400400c01001800034840c112000a15030640d03402442510b0250040c4400600c01160310141c885070820f4144e80748000d5190000340c1001001001c00182e0040c2d5200f80d001042141084401d000f020460000c590711107162401c02c0c00d83d4005040c00e1881c0111644034010030b0002002d0f1a26103001e4030300550a4003102500302c5c81c150b400c1c0e00203500001002000d408a9071603 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 791901618 1250 791900368 791900377
    0x70f0303090b15010c020f031908070b070302070210030e030d060b03100927020a0302030609061005041103010e060a05060c010b0111060709290d1a0a180207060213030503 75
    0xe5080480b003039480354000d0310000103550050380060207245000005142c40400785100c000003408070341c0c041c000c1013002504140b8111054801c00703000b0890108000310391644030740c004d5891405604040c0540c5c04510120b005550100c00e160f00e40d074221040340c400308140e503a100703143d003414000c480e0384898002140d81705803546800300042c440e020400c0e18042c01040c024405640d103000314580c01111981c00c0c43c0703440100703d0740b11800180000240c1d40401c100c1d4000c4103841d025205500300707420275203000a07940e403060340203504052109044214540683e0704517284503150541c16614580040c2d122421508515840280812072860080c0154808140381c0001e803147c00d2100503602c0110742c1c6580840d022000211419002c1c8501d81681a210509403c0e119562081e914048084400d980018111141c9141e548100c030038003540b04400191700702c0e07050390030449080c20542000302d207000071b103000e0b8001c603000615141004001d50464111240c0503102c00c01d4903407245456501c9902 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 791902868 1250 791901618 791901623
    0x10c0c020f010f091205030c0615120c0d08030c07050d1d060c0d050a170f07090518180a050a0c1a04060e10030f1a2106060f06070f030309 61
    0x300c00320344940703540951003503d4241c0d03660300c034040c10910b0300f840c03031842d886091400c80300e6020610220150010400c9114060304d650101122185009000d000516010301c00030402d60b03229840e01550741c1c40e009002c000c4107800007000b81e071365078038a00105820300c40d50a0042407441040002c0e0740301d41e800440f00c400d20800200ba8038107407044404010341e9019103486500c07540c000c107102511f554082d00061204e14441d0130301820980034002100c0d00200c08460a002d585140340030081d000c0d900801c182d01038070b01114102c0c81100d03080501c2c5003590b0010090300c0030090109011700012020000d4014441d8004202c644010007480c01c5102c441507449001c401207801c44106514907580000c1d0350687c4c0080c0e1b0303050307038144081c400c1202041ea0152540b0034140d6854074090701175000c6c01001b8603908907407641d032400d40380a01800154a401007407100c2000450881c0c1c0484580462415049a021501404aa00607a000030020320813084010b05a5410b0320f0003130205134151f08050f00060 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 791904118 1250 791902868 791902879
    0xf0702130b03030c0105040b01060201061410180e0108071205061f090e070e0a0605010f0e01031104080a02090702061b07230601030c1421010b09190b12060106120e010c0c02 76
    0x3d070794070ac0076420303030f4041c0c02420035521200320314943c00d00b03200d001c4403100e4480e07240200300a0113402c08084214140e03080000c102030081c00600c00c0c030340c08016440003400d03503c08000114945449081d03c520001d8003035921b103d81e502c0005056001442180301500001004100038892442d0380c40d0344640c01d2140718203981c11500003800c01e00040c4a0300d02140d1042e102c1035400300e584403007103403d0224010801c2c18155101629501103010707502500113010101c0003803400305c225004111103d04020400c030308550100040014071040780058806d4841210356242d1240b4070b512380080400c280c0358181d00c807403411044241404000060a0781201d014108800e01581c1700c80d200c240000c010b000703098000741c900c40c030006403100084101c4d503943c402c0b074000110b40d20390700d00103152928140c482184c9c040310100c2060f200d507140d100306c050166003100c032064109000104d50380c540030144508070921002103114054452141c00c44280d080c110ba000304100c0c0c0f2042400f0f0103c842411080e401f44 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 791905368 1250 791904118 791904121
    0x80c030f0303011a0412030e18040c05040b031219140703020303070e1807210504110906011b0515180a060c02030903061510050f0702130b03030c0105040b 68
    0xa04010441003492210240603500e1030382414000f0144032030a151404007040208000642c02900030801c10045102c5e50f54500324502010405c044806182c807105290084441400000342c130710b4030080c0c03c960056602013040d5044000003810700c1040364004900100004001c00424081c0c1c80c0580703103000c0f5498003618010842c9140c01a800740e000000e0160b8410404250b101d07015801c1c441d800e106c0101800c0b44000340902c0900348840c2954804007040c40d410b4450410800c183c80c1c030100300302e081801c015502e095112200c005001c004243d00905040c1d000c2150360b48115078107411030248241c221801c445c580b03080c81d69a90a106200702c3d80001c400858527400d9400140003004c50a000200b0361200b0b10344038400249003482c068019071108000c5070106803070500803248a0210200c00703d02003807800c000d1000c04004603042404100d803c111a915000c103400a03580300755010380798080481d0240309030308010600d690071258548800300720b040b400c800c1504668800c82c4102c00041c2d56 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 791906474 1106 791905368 791905393
    0xc0c0a1b0b1c0b01030c02070b090406080303010f080d0507031706060415050c0709050601050a0e03010b2206050108130b0a15030c03030816050324030f01020408 71
    0x1600a007a800102030a1944030f0200c40031028281484040c0e20314500a4480080d03020345891410041000360315603e03241e0080b00a800107404032980c2e56181c4940c4c1000d41c01c94403c003001d600c0b8603603003000c23003611034005d0740c3d2800c0e4951102d6100c0041425101b0000303000400d450b8118405100000d00e1080c0e00c020410959915190f0799a44c01070104c1041c05c05015030032103403c030341c2481c0901c881da0b640001180c9014000707140880403c011f00740040d015200564682d60f120b0b91241c40d5000d545480c02a0100e0402c8070f013000c110030340e502ca0065070210800c0714091a01240c542001000c907901d0705089034007149113403000440d00c24400e500c25044a42d900159500c0d07003c130005004041d00550120342259408800400002108100401c0d61000030312004400514031441e80f21040c94000440c486403005055803000c1e203541800c0c038002c1d08240708903403841c807402050105 = true := by decide +kernel

theorem cover : BRFrame.Cov 791726618 791906474 := by
  have h0 := BRFrame.cov_init 791726618
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791726618 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791726618 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791726618 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791726618 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791726618 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791726618 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791726618 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791726618 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791726618 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791726618 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791726618 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791726618 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791726618 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791726618 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791726618 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791726618 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791726618 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791726618 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791726618 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791726618 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791726618 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791726618 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791726618 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791726618 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791726618 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791726618 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791726618 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791726618 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791726618 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791726618 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791726618 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791726618 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791726618 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791726618 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791726618 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791726618 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791726618 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791726618 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791726618 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791726618 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791726618 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791726618 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791726618 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791726618 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791726618 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791726618 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791726618 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791726618 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791726618 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791726618 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791726618 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791726618 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791726618 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791726618 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791726618 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791726618 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791726618 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791726618 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791726618 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791726618 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791726618 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791726618 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791726618 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791726618 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791726618 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791726618 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791726618 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791726618 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791726618 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791726618 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791726618 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791726618 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791726618 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791726618 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791726618 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791726618 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791726618 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791726618 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791726618 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791726618 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791726618 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791726618 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791726618 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791726618 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791726618 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791726618 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791726618 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791726618 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791726618 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791726618 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791726618 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791726618 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791726618 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791726618 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791726618 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791726618 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791726618 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791726618 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791726618 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791726618 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791726618 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791726618 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791726618 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791726618 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791726618 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791726618 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791726618 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791726618 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791726618 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791726618 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791726618 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791726618 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791726618 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791726618 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791726618 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791726618 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791726618 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791726618 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791726618 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791726618 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791726618 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791726618 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791726618 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791726618 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791726618 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791726618 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791726618 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791726618 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791726618 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791726618 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791726618 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791726618 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791726618 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791726618 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791726618 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791726618 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791726618 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791726618 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791726618 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791726618 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791726618 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791726618 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791726618 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791726618 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 791726618 ≤ n) (h2 : n < 791906474) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
