-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1189
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T01:40:23.858343+00:00
-- url     : https://prove2.me/submissions/a015c25d-8926-4c54-b048-29e46f22adf6

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 213669064 ≤ n < 213848920 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 213670314 1250 213669064 213669083
    0x302160b040303020c011407020c01030e030706150806040813060e0109170309130b0a08030f19050405060a030501060806012f0f070602030a170103020f040b0103150905060f0d 77
    0x65900e42100810281040b400d0507000d00c00b010301039509114056908070140918440303070800c040060304001c4412010360405061913842541070000004440e0115402a0b0009881d01c03c50350860b10b900890300100a6402110f050105104092000c1c10b5502c0c90512803078447d0350307140400e58414a2041d9254042a0800c00410210f80f041c5003220300c002c0c000d01900d103040b0b07008000510b0a407442e0002c1403026560450000103042c46a03000c00038000718001149402c802d56584034142c09054507200e03501a0320300c040c50842e03100d0360686004040140403681c5516202e44090081d2509014020000344440c000071050b6100c1c1d01d04011030310307591441c0d100c0300207a070240e18490450100b0134001380c0b180081d8400f0000c0204100030040035560302440e1280940080144003011203000a02001090310051000d41e81d001c4000360440c00c2100c0003c0c078a000c10b001600604590f00b60a00d00707070403901000410144941040340300b207004540304c60981c803150080100b085020700d4080c01e403044 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 213671564 1250 213670314 213670357
    0x52b0f0512090f0a030336180509060702060408090d0605130203010b0301110d0207021f090609080102031006121104081608030a0c021504030c151107050603070f050910030212070302 80
    0x5060f114003c1200c10b0076140001f5201c40004080c03c01e4250300c42c8480081400030420060002c1c400ca5411580e40d00282c01181044c04000b941d446020700090002540000c3c0900e10755142506030305034561041041c0524600000368417409607403004140c3c025403c01411a0355454103108588000416290321824031305000b40340c400940104004980001d0301304602d02000d8161010f2554414480e924a07992320b090040003445070010347d00c03a112030780c010720900440306507082d00c541c181e5000303150442c248070240c001007010300022080e0201d0558005400300300d884000c5441ba030f00c03c000d0020100019a80d550181cbc0d0792041860000002d1251806c400c01890500060300d80208014100b9042a0f2251a0528542c0403540882415030720801d0b1603605a80001340480c59941c2e0001408000f46094081a03403440014256010801542848514607001d1070907108132241c003030180c0c1a0b800100710082c000754480303141884403615500001c0c4130f90303110340225800346a001201070203454 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 213672814 1250 213671564 213671597
    0x3011401052b08030a0507020f06070903020d0809121c080c03010302040504020a03152009010801090e0a061a0a12050a02150d14070801052b0f0512090f0a0303 70
    0xc4456401c1104a0454980c00040f0f81090055401003000c42c00008950801000c06460300c103125418803c1174000b1000c20500756080207590f011070786c059030102020102b51910328001d114407521154420806103001c03046080015154101d01543c4034000000300203000107485900381207d4059206d00204010b00c0103050541040f508184003412485a05460382d4541e01415641004075501c20703514030300d820040d2624000c100109107070800d81868004540c0c00240018014002c0c4a412903c6200f5048050401c000222500e81c002c0c0c8204068904002c0500c03550494800040c0b0680c04c0b035102140d10540040e01d0740690354000c0041035046590b60922a103a0513414070381100303000500100342407403442d0040030b19180100021101525000d14058180e600607080140503216410500c3c02031001c22a807049030182996070a28400030720724020001d2003801d20002c20600505001c00761403213a007006400000c504a90001c200501c1c8003e000b03002038948400780024800300402100352 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 213674064 1250 213672814 213672859
    0x20411040e0a090b07031a01110c060c03030f100f0e0c07080705030a08010b0f1e070203070e07090602120d0903090308030c0c01110301061e03020c06070309020301140105 75
    0x1002a28165400d007a41c80808480300034085945071452625803420030204102c0d440d0290303010180b8281081071454031039882030030650b000003ca0520070010401001030b5010082c54203410390003444c01c1ea540e08603000c201e403240c00c01d6403004007030a103034401308a8004c8514403d9050301c44800a40010390714240c001d92020720003410180101100304114000302d15441e0041c01424041c00046a07540180030703000300003080c164403144c80c629003800172100d004e241305d04864489800c07000c0048840c6016181c80064440c87c070009505101d0500d000450305601074060344944082c0d16016040f507038a200036a12040914a4004404010031400c0b0030092145c0c00b44800b030303020b444c00c903040c0c80d103d9440e5a802d902c10b4403940207018001c64404804178090050001c107505589259045515060010701841c44080495201c0000090300019542c0710340d060318220f000090881d5174509114402400501c0d1461003a4025401c104805003d0302000d05001c0c122640075001c00c081031004220082c50 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 213675314 1250 213674064 213674081
    0xb060304200d03050405091e240414010e160c080a121d070b04050a09021e0d09030e011d01110f0109110109051005160602090d0b060109080f0601030204 67
    0x40d5807645103407290711003035040c1c00b010f48a5203032140e80314101030405c402908020000034944102c02000e00c134030845081010f820604040b010b40d11658088a441011300c9000c080c90b8100c0e1510351403038480f000c0743d1010307030482c0d11981a0103550741701d03d0b00801e408200b50801da00445c06144c850320001d2445801461201981d103010b4440009188481c6c01361034a11b0f00b6200035911004040060b40b00a10014000300b64903801189000d180001040e0711142520961140a03400f141105045800c50403031420b0341201d00e003072a558450008484000c12601c138099000400142d902200c45d4001e158140a650000c0204402002c804004481c460a445280710361806198681406450709000d01840c0d244900007020020a5100006004d58819030140c0c1c070448112069904117138000d001c43c0c1058041c107400848805c10342c108400a84914035010750400310f00702c44002403081003042140144070999491106a2342e5041c81d80c0d40f141e914221105542002c0010001840c103640152078 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 213676564 1250 213675314 213675353
    0x40e060403020a02060a20010e0105091605040504050a020a080106090b060f030402040e07050402120a0b0619180f0b1803060108071701060b0f0415020102070b0103141609090b06040b060304 83
    0x21500911030f00007100f6007e141c5c0f4955691203402c1d407854100b00703000f81e5510000d4003000341403901c40808101651403443c8141c6006a90380c1021605126041c40002002e54010300180501541d070004030b40208290b00c0368028043c909041e20350f03280761a40484944143c440d245078296141c0783c08210040c403034103800d42c01d5445100380008060300c075400039019074441506808000c0c6003c40c6024251901b2000d654800d1104200d0512046e015500c0424401c00520b00021120714814030160018203e402c0031030702c1c810501c1c0014981d1070050041185da0b5060214200000c440d01c02d060341c400303083c01410b01c40d8100610600c01034030750b154010343c82607003440041659507660b948a9090f5000c1c612040104000003004d0280141c08010203002102d84e100031440c0c94800e450f03000084030180030040000c4140d0000c00b080f404208060002da010095006016036900c51019004200540003250140d40d60300002c0c410349070611411000780000f401c0361b4915940c0d65038541c0c8058841c4040700703 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 213677814 1250 213676564 213676577
    0x3110405181b0906150a050f07020303040906150c080316050f0a091502070812070614190f050f070e0111070e1008061003060c02010902130b040e060403020a02060a 72
    0x44601d0411821880c04104a0010b036500300c50350501c40d43c08802840750f4082c4404038581600c24041c441100c2545e011807920903201c10610001107202e00c60420f020b9454070000c1804191009140e201c201145c018412108004400d07040039980b0380c6880401618800b000d00c006140d001c0200d40701c5520449078917000d480c1c152088640a4103400180c500c10014003211024040c3c0840d040440000c100310340000e110aa00d0b103008030341e0780c00240e01c0946401101040500030030865801845603010300f008411081e19040508903003000001a4902045040103100c01c440e0703070345200b6680a030009889103d851b6440030800c1d500c20161103100b42c1002590306100041020600160014150f0b00007400c0701402e0044151f580d9100d607800c0484603400c05801d00902c82d179049803030b1044a6004102185070340104000341d0040050b10303000380d001405034401034480310712503009148901c41250200240f8400d04141030780c0d818120f0b80100540e003c00c841101600d0424050701c40d90bc5289080b4 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 213679064 1250 213677814 213677851
    0x90402040b030c03060f0904080a0e010e030102030411130e0601031209050607150f06140d14010c0302090a0f03081e16030509130b280b0c030703031503110405 70
    0x1c80e440d07000702c48158030300c040401485001c1c036244000d404440b80440c0c0e001205d01303082e12107203d148600c1240301c0a0203101054900c059000380c020764011100240210346a240909003003842080305045503200b002d0780610a05411658411030304526008170041001c0d0382141d80710500400b00809a40a100141030005010303902c02d801002001d03c602e06208802c0401c3e094082030f1004411030020090402c0b40074080c09070b000c0d0624a030303071801b1607000e02c803070b0414181070b5480c0d04084c402c00e0b944e5007080c1501a4054042d0020480304601f44c1d142100c1d6036460400c01400c0c40c4600009110100400c0008010720180984102c2c00701c1c9c500c00c8910b8428228618007007428140d8041380800c00214603420076240003940d050320185c4054060000312400400203003640c414a040120b280b000c008024240301c508038100e0064071462460503607400c4804a00c0c0c3e903e030400d80040700001d0030910088105010401a01700f200e80c80b40300601301581c0d017010032010b080001e00841c1c20700c05a0510 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 213680314 1250 213679064 213679079
    0x6091c270f06030c0318120e060a0201090209100e06061c020304030e1e0f15130f17030c06072001060e0105040c050f22030c03060c030506030c0a060509040204 70
    0x32400410920049982003841d22a01800381da01c034002c070300141443e00402c0c40118001c00b404102d40b69100140c49240c010250307054601880009009401c0354010030000c143c90703015030207503d11500071540084141d490303a044081c0b42c1c045000340c0c0d0801910724081004c904100740940107503248414941031025a44e441c0300200d03003040701c050380062440c0c01c0c0c0503468101001e9480110fa11048403804010f59840801c0200d1a160480c0780195070b84104100703030f4401e500c141c90300010301c84418900c165a5002c000040c0030180074030f0b2400500c489204c119203400000310780801ca500c5003d4400f45e52056001c0d00da100300c0180980c0e9156100e20700000181d000e00c6800040e215140301d044003941004207010403100c0014800090101c00c100c5c80a849006506035500052004082c2401c010300c011010400c000c2540001c2c01c84c0d100400220070000d17584c00c41500000c076960100016503900f0300b09581c615441071200c1c0c100d403528400b4050948030300c0003001c418801401c0035103400c0e584c000 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 213681564 1250 213680314 213680387
    0x16061b0f03050a0305130f29131202070e1504020d05130c081612020406120605060f0d0213050901061806030219050a09090215030a090506091c 63
    0x100324000b401c00605100c1c031a40600c80e0f00c2d0410743d005586080050305c1c1e0b9502003031300345103400a01600e001d02031090b042c040c2c03203000380700d44082d00043d02c549080140d41c135107164211450071100b595200440d0820300380700041030300c00c0301c0500c41641004c0d11410340f007054100d18880c3c8243c02980030001e0b10b4258016010b103d0003494500703842507140310755040544040a031500000c02a40104d508100c80c103034203410340c8040d50f40e00110604554591310000b40240100d611011000ea0b8a80404003801000d5110310b102e007030305585101e80c0b5007075502041084900c8503002903100d0700c3c280c504100c09907103610940c0d100300c90000001c0c1c11078540104401c0c0303e8081c00c402c00c1c000d888180a0045003440000041030f51000d95081402c54204070014002801da8091818160b17981c000000555588251140c60004122812039072418205610340142410132000e403418800c1038042088100f00041d00ca0102586010030785849140c180c080341e44032504004502c1c02c0f04030307181001d44580c0305030 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 213682814 1250 213681564 213681593
    0x9060f090f03090902040b0d0e070e090d09090c090605070f05120715020301050108071b0f080306030d0e06030c1308030c01090b0a05090a0f063b16061b 67
    0x1150280000103480d00820020090300304d50312990061004004003070800c81a0303124000248408604952040403580c81e1103815031042400048910502c0380401c000f191500c841d213240d0f510645859164404001911521460350000480310038040240ea440345000d441c410f480b9050000d402d080c29104d01345041c0100a071050521f2002401c8000c2001807900303920074490b40782c0198255813500300064400480240b04005100c210a4120014903031803045000700395002403540c80346401414540740e15007040703805074000d100d540c460004041c0034440408140b800201600d140d0340d01d03860054020340160181d000c4030300b101d500c042014a01407000d844408050000080c0758400c0381000c1c4203889001c0e1110361150301d010140104001c012691003155604031440960484543c030b4500024003000740ca2856400c0d540c8244210b828040c6e24155203043e000d070b1510500d204c41903003643c131400b10f2034014509058118041080c0da0041000c0b006a081916032007090302c0e540c0c0c543d6405910f114 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 213684064 1250 213682814 213682823
    0x3070303260708060103180f020904021215060a0605090310020904060807080d0207051008040b0c0f0d090203010b0406061b020f0607030c020102070e010b0307030e070503010c020303040b07050708030a09060f09 92
    0xa404c120040d60305100d50030001c28112902144142d90780c607150b45031070b00b211020303004007803800000b800c0d510350794590030304142032004562103002c84828480700c441c02170301e200f0710a102114001a5140c81201503e14400005019146090740b80d40740c400254400151940c0250b115400050043d005000a000500503040600015051014005e0030309110307802051183d491400310521081d8814041a48940c0c449080441912803031924034082c05000381c4030040600008500240311016048604154400d400900000703124000300800c1d1070581c0254000a24079420641c01c0c03400403200801028005801e04c81d031f600030903000c91000e5000040540108040d89403c0d011540c2c10010f0310010065030628210650410001d644e0702d04c00036205804060300c450f07091540c4001402810020700c0002c0080000c0d0101030b602a4481d0000c4405540b84515000014102d5002d882281d0300b240e4072081e485d01c0d541ea0b10203120b00034081c1500580d18180c1c0e415039036030481624401d000c04540103 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 213685314 1250 213684064 213684077
    0x91d0423011509140a021c0509150a0e121c150e01050409030c14010608070602070618050a030f0602041a07050606031c0f020a0c0f0501120209030703032607 69
    0x4a40b020640301589501c91400c09151640305010408203d10294000741031a00141c0c7d15000112070384004505035004844503840d16051021100340041d010540d0b0150075004c42c220750300c80013803408544071850180480d80196420210340c5944400402924482420740b4800b008250f51032000c85c0c04484250503012100c11080c040d1003c1c222402740140b00031102400500029a8000c0020003100c6009140f001788554440d0f1000003904402c02400c2c0c0d001c01c45500c00c3e5907440c0207540d00c0103481184040303027494207078441281c8400c03200701c262074000d4401c422244c5103568009100130042d130151503c0782d080c040407644401d400030040b4108080c0030469114212810040e08212000c1c0c2001d2007980301c0c10300c6607a0340c9041403013082c000d070007401c1210740440e050201343d0030211540e00003041e14085000100b21032905071301000546500381e8506907401d003c801d5103400c0b4400e1018469259201d00002c1000070f01c60411120b18003401e40ea202c52501d14144800c1b41c0203800d44043c40450319 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 213686564 1250 213685314 213685331
    0xa050601150210051005190b16020303070b0f0a0605010903080901080712050403020703020f0306040b0c090f1302071106120f0a11070501060e0a1401050616080304061506091d042301 80
    0x7d008003d5044641003400c600b644526008459515109142c40305180801040c906e5040d540c0901c1070b40c2c20250044a0303148949071010526141e804e044500c401d1092070600040f495501c00d020010940b50710103141d030304c2d00c070900c401541c2c4000c0003840c0100300040001c0c4000d04a00c50701410b80518401d40003031040354110310400003800385c20a80308cc06540648c0030400400e003403500c180e402c001400f5400d95030b2421400802e0202c5144642d450300940c02100c3d03e01e401021707900504040740030317607074803243d42a505041050302c2c400d4030307040404140428080751826403800b80071a0070541848002403000d10f41b981c400d88580000c4002d650381c0c0d54540741005031003038001840f907100350328400402c2450030030305080c0350000060080900a070b10109000000807500c200c0004402d40211402d81c4034031f003528004001e0030080c1c420b00c000c00b00040c00001c1050140c0010400d66001c400c0920f0304001400c041c00160f400100300b615201804540c91541e09030318182d081d0194000c400210f100030 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 213687814 1250 213686564 213686569
    0x8030a020d080708132118080307021513030f030810050a05030a030e060d05180f060402010912050c04020a05250206030c0a031118030f0a050601150210051005 70
    0x100204070350400d00c088041000ba00c03552000d0600d50200501000c4140e040c0315040c281d50114641440112400380654041d132069041001e01000001c070b0041c50711a183c4500c0044c0d141d0040c000000d401480c070010b03c600311600c0303502074141c4c9040410b46410a99594407007100c01141c1110a80c0420081001e010b0030b103041116000103080141e800c0b04c80310b80307450b02280e9a08201c0c00041c0400420814952180d0b503290308642580c14441d0090010b8203100c620005c01c000c1c00d19288189211b8113102041202011506074070541d0140c40d0700c14110f2a0a08950341000544c2c000c6900c0c0c01060400c4c6200d0365184068400403078130360f458580b1134401d650080003c85022a1012004000750020401a0b84900032258020640390300c003a01d4801880054001e4044006408a800c1021039003a1340030014070710f600e584d100110700302d502140858401b84c1c3c541c6002e400152440e04820010b014603500c804c01d04099440c1803040340c406808004240040ba84140c5d00202d450328170721002c0010340b = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 213689064 1250 213687814 213687823
    0x4090905060f0c0306130b0303040b09190501090b0a0201021204050c030c09040b0a020a120e0102030f012310020f030313050f03130603150b030f1009060e01030b0c07050708030a02 79
    0x8564021465a030034600c0070741c055800002c00fa2441640f18098030606ca9986811408071011f0282c202c3e0748880d1284060700e21604440c501e980544298044000d44006960040007100c406840d5080c280c0e08007040a1110ba200c00800410366408004071000d40b80c80f004540c0c400c1d400380340038144240704c2d5800c05040031480244135100781c088600f400b010650740005c55411071562500143d480c01940410356407842c1d00030003109100e01c1c000540c0002401034002b035110303120b4684440007980c0c9500700c1041580031105042d80746600410281041e0401c01d02410132640240101c0d4100c0b02815012807030365004a5840203501c003081e02040c03c01030204010711403041c40c1c202039803c040c803a21340c0d48195005446407800309604c0c0c4030103001c00500c2c2041c40e009030140d0784400f0390701d2074496000154a002568035202480342d4001c00214200c0b144039810a0700e074542c407a6000e591940d00c84100ac5140601840d9a0b01d10070010140000c01c01c02c401401070240b680030f180c49280342d20019081 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 213690314 1250 213689064 213689071
    0x305070f03110609030715090f0f03020703110604181104120804140d020321070f050102030f220201080a0b060c07030b07030501030f02130905100b0a09090308071d04020409090506 79
    0xd071760062041d600020280d1010448447c41d031540007508502506020106c0100c2d580d0141145c00629210824035502080220a6900414420403540f8400040c0b00d010b11481c450704810480c50300c4462880b140301c1c2c0140c42c011070310107003003414075440745c911500c84061789504458142e000101002540b81d442103400700381f50101e4044680c0061500130a403034101a920440203c50745481441042e1420005c1d02d0b445070308078400003061845454424000e60040d0307100b041d803107000340010f545840078020403c1e40310150440c1c0880c126842c2e0041d2002417000d4800e4803125100c89503655592161805059006a248002c000091446c01d10060641d4041e01c5202011308010041c070200f80c5000680e004251706592080c40b0303089020322903004004600d40141980a8901e000404140c4c1d504203c4002804592101c01143d981c401c2c0401c0b11031420004010a182c200001c202502407041d00903a41074401420340858261000901242d02070340042016503507a00c2c61506224003040150707803 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 213691564 1250 213690314 213690331
    0xc0f0909050f010b030403051207050901021615050c0a150902090f040f02060a11070609060e0405150d0c080708030d05090d0212030915040c030212070e010b070305070f031106 77
    0x820b05002040e0b040404050148400b0324a000003c2000c0611500844a40d82e07402da040d8022800c0048000305140d20003001d444c0148218200000c01420300038440c02100c0440c60b10800c0050340583c2924a5009850300c401380d80604034103480450241010200c0e00105400000392000c621310401c00e810201034100004136055200b084005080024120107554045808540301c00200101b2175502c3c1c10340c000c140050194040008540d500000400e0a840007500d504410948840920045820840d01c00c400d806c2c548450b000e00f801c080c812402001d02580310301450b0364440c0042c52903c1c1b940d03030121801e6407002640401e20b207400d214203604144214043c0047c0401010000c0d40c41080000d6100c0f41034000000c101e88a0b02007001c40074a03000301d074a1811929084c18000400c0b01c82d0f21090380a480070806c0d5081090000c65128140c0f041424828a40d9007000c1a0780900c0c0c011b61011400c1c000d0030404200405d0051100c03110a038400c0c0e5072120b0070410035881c40e082003006440c404 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 213692814 1250 213691564 213691571
    0x1106180712030c031d0d051b0402070503071101180609060e01050c030a0822050309150a021c03060e09210c030d090c09020a0206070807020601030c090911040c0f0909 73
    0x200003d5000c2240001c41c0e40500d080003c04064100807083c041e120403101364020741110740301c41040f002040120810344070303181d02603444c2c80c02810b00080e407061b064000c1554104100c0c0200003095103034000c500f6039045c94144d80b007114000d01141c01d602140c004101144001c8000c100e42ca50008460010a03000c1c40d1031400c1804010b2402c0c0e0302d01131000d9900611031080002a002541018000720800c1c21001b6800380524500f490358032680300944481c014140948400c01c62314000c82111400c1c0c1e929402440ca001148484400b8150034410390700826440d140005446203001d821940603202000c040e0000c3c02d5560b600704c100c400c0040c14038401c00c2c000c0c020386200c0040441a103d8000440c600403e643c0114a011b0100205c9900300896103071001c14002291980003440c40d202c0d540d540c50741480754454240c240e2b52004248001040284400410b0203840000e40000503894401c03a140056104408006026074414902140001d5400d00c002d0001c658011070740c01c003c050044040 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 213694064 1250 213692814 213692849
    0x705030712080c01110f070b0f101205030d0510060f030c051606020412060c08010906050604030201030f0e0f0c130605030d0e13020708040e0a140609060111061807 72
    0x5400c00307800303801d020304a05800302d15059040004c1d006500c0e120748050050341d1303864111104600d503400a250a50b0001d03560000a0b1401454402d52030090b1554840e03028024607141d1000300414840404444600040c00806500182805460700403d02c81382c9505400d400c100004215280701c3d4003440030142002c1001c42c3c0c4640100071207841131404d03200051058424180f1102038071499100704e04042c01d480c4941c0510400d503105402c8401ea994800170b203070344c0c1c034101c0e042525420b0082e5a40980108001c00066009620a003a040040900400d034200102c000c903090046002e0401619004903030307051034500e0309004e4405110301d902d001308042c40c1810042592203072585035000c28070003d5246a286555030301310380c8a00589407041503640f4a03003490003000b207801c81d104a50030810200c01041c0460341c1806800b40c1d95030050700030f032040d5490070104040520080d281c00d042c01289040882c58000c203000035840f500d40955a00e1100c461588240d250441f507501440c051301100189 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 213695314 1250 213694064 213694079
    0x31c05010914040201120b011704060605031204180f060905040c0603050a1503081b06100914130204110c030f0304050607030b03072d080a060c02031e0c0c090702030c07050307 77
    0x4510041404850026021641d1f50044c1e0354259640013030707101caaa860007003108000a540201050b0380f000d03410784201d4621030600c0410360003280078450040038040307140c50805040d58484001c0c2c15a1800c0031800a9551010000b00d5809440c2554104021801400b44039014007a107500030301c40c40420040700c0c0450491424040d064040180001c038001507028152071002a13a021202c1103800762901030400c07a9503980c0040c1184074406460f8200a4071b03010540c560b244651042d9400716424854034100d5003004010402180b6400090006104410030114208003900d0100c19550403180d0f41d00b01030502c0d5140500082100041608004001580361804216201202c20003a16001032494a5803c0c0c80d66141c8400918900d8501d040c0004060384009103100c1c001c3d0080790304206505800404a84912641e020343c1c1d51151038140640444080c2e2000742030300c14002040d60104800d080008940c803100f5109800141e001043c2e040002100340074070ba004240407801010081c2c5803090 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 213696564 1250 213695314 213695327
    0x5090402162006030610120e030c070e010e07050f0901020a0606120213020310030b0a09060c0e01030c08220c03050304030308010f06020615100c14060a0605060309100e031c05010914040201 83
    0x246c804108903c82200140d0202d9040780b40b20000f1441980d44655402c0e600c10f9866030b003031141d40d2920303040303100010714a900003810500603a403035540c0a1410852240c0841c00368031903055241103104400c0c1d2500454018422400685078184280304514654010000b0f82e5603848104000c180c410414040400040140c000c11a41d02074100785c0e05580f9614694014007030002c010b0801401c0050034402c0903070000ba001501320090704d04008913403001c0811103010204403602c9802602c2e0002c1019100c16407002400c5103807003010040d007099101c2d5075032415608581e00850124812070014010a25521007203800307030103e03100a0806180c003010444441038001c0c0072a010b01400040409101d11a000034148640c00500c45c0b0181d00b1b9100c0c541c2e40e540382c1200d20800207450035402003041c1ca001700c22a8041d40f801402056910242d00000740104182d20f80362085100400c0000d4820010800c40d56128200280c00100d941c5130150400c01d540482c40e40703a0b1400341d440200070050380c2068 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 213697814 1250 213696564 213696589
    0x10902090406082a060c07090903140307080103080310031703040203120c030901050304080d0e0a05010c0c030c15020417070305060109060323070b07051b090103080a050904021620060306 82
    0x10a42449500c2d03a0b00410170520034526001410300401d41e01181d22410f0303400940400344a1703034610301c0c1d04160464818450005030386460000b0701c02c900400c00f040484014580086a6061a2441035682e690324203070451803203001c4404000c08000c01042d4070301417001408060200071a245030408825040f51203100c2e00344210306002c804404601400030050a88920480c0320004008440b11130310581e80d41d01c0440c0d011103840d0b00700786c00c400859105003005140b40b40d064848100c4060203035a11055080b6844407984440e6080c8070000701460700c0e032448410b800041024100c1c260075800e003541043e805130407680000c1c1c24180c0c1080020a10368508980711002c4210080c4003095007243c0782004500e912140700f208010510342c4c20b011010510a003160240e41c0ba42600f00600802d024815800744800780042c0010b1040c1900300c0e002c4c000070002010000c00040c54403085604000030400c0c600c0040d2004202d8003205803122100510150f1411f10444440742140381c02000100b0600500 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 213699064 1250 213697814 213697873
    0x20d03020f0906030702032805070201030b0402160c0603051f05010e0301090c09061e0b1c06030203070e0a0b0f1309030203121f1e030b1e01090209040608 68
    0x901c00c1d215100c95064511915000385015a00c1c00d10a070001d40d00e0b00440c01c00d0311031300320306440412a0808520140c5142405450352800d08102c0d400640007040c002c0c0078140c0198080040d402200708106001445520414880d150344e400c0002c01401c50f10020404405043d01c1c0011504190319050b420b13080f00ea00740ba104100003200d00200c0c2c051b1422000003041c400303403020007181c03191441d040b1038196841492004034070350f0b5600440e0114a1b0900c500040c03070400304000ac074030390600c10942d51200c0c145500030417203c0c2c0e6540800d1810314a41e1140705402c051505110903290f55000302c1c0c03807400342195880200044080002c980480b58030340007088540d00d0000b2010036000b071080d0307501c44e11904082c450515107d0581c0c48000e0311101c89000100c00e41c800411020034012034000d00d054103400130042c5504603a1014031420019154101448520480c1e500b100501c4410a01900ba2000c026849080c0882484184c603440c0e00a13403140c2d00403c90307081d0204a0740b0f00410881000 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 213700314 1250 213699064 213699067
    0x30506060d02010c0b180c0411120405120a02030d050f0402030c330903120a080109020a031d0c03010606090e0c03100b04060807120b060313022706130606020d0302 72
    0x2e10040c0d808440540d0014081c03090380c1c2c00c000d00a44c0d80c00c000711199603040241d07910305180340104021150070030103080c03140800344100d03c4c80a50700092107a11911950485420030b40c0b0b404011260340010400b400140d200007240841702c082400740b681c01460300200d10000e4102940000d80b10340a07040d146000300c0340110859040000400c03a10000360301e03005032100400400040075207513400588800e001e449034900e0390520307074485001c0300c1541507917a54040c07030359080541c854082c0d440a6218070400d43c44994a00122845881d00c0510540340c0004018400103141490b083d03449541c07041081c400f80340d41c2007017400c0c200e01c0c2640d40040c000d040c03240e603551440c03851043c80c411750700114143c03100410040746a541103000180900316648030b03130a80f001d14454040503148034520b880c1d000178040c000306020341c3c01c241c4c190160501c02000b442004d01c0120300c2c0d002c405000c410400c07880116005000701820100121552022601c1090140c0e50403c41c0107960361840101680c02c0650 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 213701564 1250 213700314 213700339
    0xf1401050a112103011d13030e04090206030703020306031b1005130b070b0901050108030a1b0c05041104050906030105090c011b06020403030906020105070e09190e030301030305030103030f0903050606 88
    0x6015607501036a410740781070f510a40c00054a0a00c0c0c000340924440001015440c05c419010308841d01d00c81c90400c0800c03100210143d41c1112030384990304506420980f681041001a0364602c00745200e4640784e0740050300d914140701010b02d401c3c10003504244800c061a441c400c2510b4036240000c03a011039040c2169100d1200c50001609030f06588254241360003c5403101c104401014070702d006440d510005d010320798840710299180c1c8074500b0340c500813a24400383e01c0544412400e5142d0003c6c00f4040124000380d55038080340c241c81004c451564050030002e000e100624040c0411500605d066008005a1816804640e070715002d8551150501020903c461001c1c580305c1420740ea21a44400250341b510307603038540a81001000c1c001c1201650134940081c02c01441181298100c1d0030040030389030543ca4462a595240c2d0b002c020326a44c2d02e03114003503010b1112040004500a41c0300c0c1d40c0e41c40e925851420700038030003080c0d03008402c100724148400b000420303400200e070f5400240840d141c400000 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 213702814 1250 213701564 213701597
    0x41b03111b061e010501051e2a01061e090b060706230906041a07030902040204031110050f0406052a1b03010c020304090e0a020901030602040f1401050a 67
    0x41d00d10342420340c0c040100c407034007400d90100c0e601e40a1001002601420021900c51001580090041c103000510074895004803100c00400300c148461102c061038a450000711061243c2c240c4a8040560b0b10714400030903030041002d200d20001443c0000c1816410f48440700c03450440450742c0708915003240c5030341d11180241c0d01c24084540342a031000b82000340418401d14002d403050001d85440c2d0324851040000c941c0b250102d0b146100b42d6226207183c1e0001d04285c9464250b00d00500440c040655a0312107100503107852000740007030360182da50035040d20712441c00c00c5030584600d0042010030106100600b9a5481c050a80c0d0076031b07086040080d2a085045a0407000344203000c410110425209002c2c1c28090b0080b505410001000d040d095649400c1c00505090b40c911810740401079004000c01c2107108504c1e80031180114140080e5920003280382c00040c5d0420088c2c106030b40f02503000800b00302c80410104c1c114000e01020140d440e08021400010f451801600c1c442414400000354414149 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 213704064 1250 213702814 213702817
    0xb0a0314010e030703081f05030a030809070f121119030609030203131701060b0a09120219171c050d0c09030b1005030c0307052107080312060f041b0311 67
    0x182c03810116500c8506904001700f10103802c0c1e80000502d0804924800c00da200c100d000402c1c0c660190041101c0083d0f59011184148000c0a070341243c0034811020031210200c0e490400206010030503803600010f54180080c0e5015450851441030701e010600c035200070a0f100b418412030381c22440c001585051400c05034107501c101e00c40c21000c03202132100403070702c0515004801c181d05403610007004101d44800c0203c0c40c900c100300044020031814032040106021210201c0071407880900f8034861030b1100e038044240100103403c0000344c08890240304010310000c100000c090303405480e40c00032600742100702421074403440f1086480c003900c80f01606142c1e802484204006c43c0d2152881d8250b00d404215010701c00170038010300d8030900440c4105003040c900014800143d03440200aa00c4884400409103482c00128000c1060360082ea8400108a10140080c100c5601e15603480499843e00e401048214040280c2162180c1e1030500d80e42c10100c00b4649851260116003030000d40d81e0081001c803040c5 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 213705314 1250 213704064 213704081
    0x5100b071a01090f050f040201140d061508040201020d020703030c1101030e0a030e13050402061813180b091c05030c0d110406170115050708040905070e03100b0a031401 74
    0x10950032200010f441d101c0c07a4441c0060783c0102504101548851520051800e03051b40c0180c0000c55142c600351804400718000c04500c80c810b41c00250440d039a010640710801d00400e08008140e203c4200019944c06003d0003907085d2892015003051800c40da80a0440100f011000e00544c034251040c4030603034000c3d4006200c1342d08210481721201c54900e0002c0110707460849090040c0f4446960042c4440540522801117074000c1809003003410f820313801c0c86070220041c1d4880e032090b02d980300c0244261440c458400d002151640c50005c205590401205804000d00006440d07440742816a00342c1e4002040040c42c0c0c46d591812654a4130b41c1c0765032140c00d005141c004c2802520304480138401c60440d100900481d456502c804c142000000e0a40d50200310910950809046141c807200c0c0b0301d0320800c01014041d208174601c07070801d41c030742500c0400c03290b04072050f03000300310100c0900481d4070301040303050000300ba0b140c01231004006000100d005d00741c840c0300003081c4402c5405808980300302074105081e0b = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 213706564 1250 213705314 213705353
    0x1b06120203100503031b011503110d080915071106071203090212030a0305011802160b1b0307050a03050603190b0603010e06070c0c050402040608070507390905100b07 73
    0x7140c0500c9100003414400c0101402800e42c40c004041d000c000310107808d4400c5a410511220811280c1000d10030003440f40f440480f40314108101d00610396035690750490345168081040d175210326551030558078019400000c0d511800080c45032a0004014040b0381c2d480c480145008600c200892020070708034406005c0912290101103848082030b03516074800b0341211000640d940601199080040481c4030b40c40c18015001000129500851044000c0b01d03040445503503554511840e8401064154000741c400350005a0000707080e440c00385d81402910f03001401103000e0302c0405c48a2054051032400610000d088082d40c07400210300341c7d001c0d4040041d11004109541081c50f100100030584681401c04a542d031800c01004905424180f0903a0b0694809469090003521341910956040d008040202c0701080c40d582e036000340380c0348615030410545d11034045c1020003001e54100c0000d803040e0340000700442c1c41d180400c03800a910010750070445000c0d02c0c140e44e980b0382904140300400502c40d0b41c0c60b03 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 213707814 1250 213706564 213706567
    0x51201060e09030d0501050d03081f081005070f030b030c0d0305130e0105100507030f08090f070e010617090c010e032a010f02030901020703021504120b041b0612020310050303 77
    0x40310040021302101441207000c0143d03a8071802041b4001000c84005800035600d0b030000349240c2c200c0000c0c0c030307800c810301c4680c46421a681c01c64207142001c048901c1c501c10751510240031440d0380014035040300c4555800c041c0b100d0418080880d40d2100d400701c18620541034400e8010034180904100e80ca900141118001c0207502d4069100d1a94400c1c8690390090f100f1400d1900d5051091041d0b50500768140e590303580351000f400342110220b03000340c00304203103001c1e4061601651000f001000c00516120401401561411002800704807404002900c401c0020042016805022808102c00c01003420852800310680307010901d86441020b600742c01000f50050007040d50310100e0600c0388400709988280300c0ca0061481261280508190640540d20010041c00149040f0000d0729850440c2e02c0050300305680c64810101e041035080054071103103041d8081c0024081001c100b400d2078002103000c1900b861a002c0000d01103450103182d48401603010005c19100b102e041480801064003c0449 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 213709064 1250 213707814 213707821
    0x20c01270509040c050a1505030f1005040c12111e030a060e040303050901050618060f01051e0339070c1a131703041e050316090b1504051201060e 64
    0x70000c41340d203402598841d010003000056450108002042d01e100d06a1303415007107445448001610101c050124030920002540104150f1207920400b50b1000503995002080380b0340c0c0c00c00300125180e83c009510881820018181c04040301ca0f404841041702c400107598a0381d07a90420002860b0640003030740010b04510500083c1a890b0300140e0050603030074020012511404100400e40c5880000105803000c01c0340020328034502002d1501c80c0b094181465464500144155070490f0110501c00c2c5c6428408014025540980c00081602002c580d40b060380b1420485071149600f066805e03090400180021080c080150280d0040c0051036030311148860a000c2a00302c202035000280781d00f00702041100b0011700031410700c100922031f66402010318605820003051020b408014114242c00b03510341c410020b10303034404200001c0d24080715001c28280c02c0c201545001a100d60f6000d051241c0a010b0001d410501000100d50031240b044408007120b070024030280b0701610b107640c0002280003058040 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 213710314 1250 213709064 213709073
    0x11e091a09030a14011a09010b0703020124180903080f100b030408092418061e030106090803090306060d030314040602090f04050412050307200109030906020c0127050904 75
    0x3500d044c6050080c84600e504000718482c2030201c0000b1a444003071240100095119100100f844501900c008240b41b29090340c540d5000e80680f15425206252130300c10440080301031114240ca4008080070700107180c0640f00109030140280070000c0b0096902d01040d08140701c00d1031400100041c1d6512502c034070385410068169080036070514082c074622005d051441400204000752003400062041c00c00040c2c0026410411504400300e0304a803007008080610141c100b10030700c2003010040d006d80e807981062402400520203600c128a640d10a0000360000c0e85d01168865220f0307000d48070b4500700c0074941005c4029089070b0945603894090b201c2403105100380da800500308280709441e0040380809104c20300085850454014241d0400c0b00c041d40c240130303c06c03402540c120b0020f1030407500c01040a20840c0c0c004107500e20040d01d5a648906c0b440416800140b44801841c060002e0020001d00000290114182c100710ba50300e000140d00e032100b040b040b1a860406030401800045c041d1405190 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 213711564 1250 213710314 213710333
    0x240f02090909010b030601090209190e010603150e04030f120c0206090c0d0b0430020c1804031b061b09080105010f1d0403030b0d0b0402011e091a09030a 67
    0x3140a1416100061110501401980c01251000c0c005112980c6414401b034025001001310a40c40348044d02d08000c22074104000d640600444e07040c7c11100c0d4500314018044650112200c29045503025007003080d035140f200e01f07660254050500c002c100034400310455040710000300c204010352400e0f918001180d80004e8080c400c5610fa0304070b23455640343d20100960201c90074401051072468900003000104c1c091500615081b460860a4001c84802c07030001d110700d00c00c0903100040c3c0c810385040d9000c1c50404890b21005003400c000d00011300342518004c0900c10700000e080400c1100494030030800c0f0b259441140a04500c102100103541c0d415001040158144100701c0ca80d8241350022681d21f040c01c031000e003101c10841400f022010050300788c0e895044010415000e0503614110b02005895400c0081e03a8584a4644410b1514261001410700030074a074503000307580041040c15091b25005000001a01c1c1074200ca00c01c50318a5549644403403280034451900350180b032074600c0c01c01403081d0 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 213712814 1250 213711564 213711577
    0x90d0e030c040606020f0f06091e160e04030314040309030305031806010609030506091603034b091a07020d050a080408151003030f0c140304090e19240f02 68
    0x10039a40e12004604007da80c521042e00c8604080d007000f44e08070b1f43c0c0c1c14160390700c41c21180d45100382c540150603030303c60480e40b0265502a59004000708100810158035105170407040e1040000c40d4403d0a183d20000c007082a03600005052240000100702c00380c48103100100144c035500304484081da10b6100c020102030a07844203c0303451007400b0116124150100f200003900000c0704c54211880e1450320111540100380d400c500303403a242d0003003400d1910031003000c2480455101c040740341c1c0300b020310201c83c0c10310500314514001c015103100107000180e50380042c580440305850791541ca0b14407500019410f54440030b0300030300911981d0080404c000001018004a0312901c040e110001203845010051741c00c2118007030b02c840345180090001900520b0309606c02505880c0c0308404142c03d5450508070420b1403100b81b0107900124041000e18202d0142c421b464150f08064286003100c542040c8920f00c0c414001803004d2411110303a041500302c80c01c40c140380746681c4010b101c0c10101c0c9810000950000 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 213714064 1250 213712814 213712843
    0xf0609020a1202070224040305010c0c0210020c0102150c28030510120b0c0903030310050a0501140702100c05100504060c080112060c12020703110d0305090d0e030c04060602 76
    0xa100b110301032040c1c800e4a0600c0d030042d0842141501c42e4000d007889a120301500710070800d0600000c03021503030900c44c0381c0000d003240d2640d514443c1e1030700400034090088005141154840c25240d00240da012030750003440540c81100362656101c44400000600a080310103440b0b010b85c9000d0300a00140700c0f80f84101801d141c81c00c0201d5110800c035449001c03118081c070044560b80740040e80000e090780f5001a80200400041c50034041c156000a0540d40b0940d10780d00500384901c024040c500d00307404003500030300e002d00300545803811000c3c071203402e8050310402920030100003071551496805103008044103580403040c0c5045641d04407002c0014002900e00ba01c0c0e00c4c0c03030656210315090040004505840000d15003070b40e00744641e030f64900648001486001004491590307498050141d00280c109a80310380c850500e50803006c9012440e0482e2516100c0c100b50a1900780910410040751600b17004031390f031030000f54001c800004070f4500140c103600320b900646029000100c141e404102780c946840388 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 213715314 1250 213714064 213714077
    0x60501050f04050705040b0a0e09041505090c01090302011809020a170703021c020306011106010602010606080f0402060403020111030702060403061b0e01020d0e4002040e060d02040f0609020a 84
    0x2101c0a200c21100c1c121a1540807030001c000034010000c6110203071035a030000d0b02d8035105285003500440c0e07090311700303640440f6800c0c0d688040c0c2c681c03d0102c1c0540c503800030079007004100385000b9000003400e5022500c8064180100456010021107403039242d8006810071174025587d40440301c0008100343c000c90142000000f54401107002c1c0da100b40221452160035111100070034550744958002580301602d40c4d8180031300d000c0c242000301018000e81d4000d0085800005032180751850140c031264006080b035500011710000c000050f51100c090b2020b44c0e0f0280703440800c0d0482c203a5000e1552056400180d401100400c002040080b150040c0d00c07020a4030104103030001c60b804013511582a160580c82c056001068203c80c858070980c10349448003030080860000111142c003505c3c051001400354858050100024080c5520f20441d907030090400c000e00318503051403c0c4240c0c5946d500585400d00c070b542030b180c1401c02c0d0340c0c494110382440d42e071504080154640d90b808105c000d520080050011894 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 213716564 1250 213715314 213715339
    0x23071e170703020603010b0d090b04060e010c1e0f050c0304120c060201022701020c04020f09040c0804080d0209271b09030604020405060d080c010e162301020705060706050105 77
    0x1001c00c0755030440e503000d05401d09603401c02003500c1e220b4201c6101d0b1300d41c0ba5901c5850002042c035a03d01180554003900c0300103001d05c640c2d00454291075180354a00e0078046511078246240c0c802c80a8440d07000013624004190811100c1c0484a070300c182c1d81c900c5454030001c1008a00e5a8030341c2a4140c1142c401c01544d0981c80d55803106030301780c0c028101c0824040100b1010581240940200c80c504150144107a0300f0002040c0b00080403038000342e200d08510f080c003140c200d5036030403c0d200d0028003052904001000c3e04d401e55426031a440351a05103c0010307000b003069811a03c0e12800d503554121034002002c0d04110101107071134400070840b60030001c5808020301c907100c0d10740701c0d00b16040c020000d8090700741a035540c0c003808041c00000e0012500b100202401c4008551000003402c020f8416000100e00702080e59407040c60301c080e14105866003880840204903042c01703103a00030340840c1e0045200c6047d0900c840103038205045940000d8018600241142c20071200d94800e0f41070f1101211048508030 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 213717814 1250 213716564 213716609
    0x7030b01150f03142809081317031c110a080a0f06150309080f030c0304120f050a080907030606080c040e0114060d11150408061323071e 60
    0x204e044c00300800301100b040104d0204d00c3d0850301d04403443d40401c10000b080d80c461200710308440a102d410341c0c5205d4041600600d8601c1d03001ca120090019000100c1c003c111052029180c0c4500c0003901111004552055008200c507009854030207000d03910251a030004260141815000f02c40c001c04140c41c010f201100d40b82280316910680e0b80e80e88500c1c614800c8a0030980041c059a20180d80d03a038014400c0700303410a003c1e00218414840302661903181d037031611f4108250700080c41d1f200c041c480200081171143e0b40c44011b0303aa0343e00d11498980c000c1d4850301d0245080c041c40c0e400c0600514107214010525000005da00c040c0c1720816101008440300c0ca46541d422071310118254003c500f00c1c003012034078034036044290070b562902030307440b012420810340700140c0303c1ca403103000b121049074012504000c1c0c10028051554003240c0290141c0d40a4032035692400100032170703064000704030386260702e48500300000c024050260031044c4044055540108a06103812450b1003180030720000d03111a000d042 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 213719064 1250 213717814 213717821
    0x18210705010b040507122c01090b090105041a04030c050f010509150105060714120c060a06170c0105030a0905060a090b060a031109070309021314010f0b030606030907030b01150f03 79
    0x200203690b5118100000c81c1c5486c005403400c118118903072200e00b85640111601d2601c2c4420642e03031a000082c014400780340c14801208002c102a00c0e59140404000200d040c0f82012441e03417841e049005011780c0c80d40380c20f5410300c0420f44060618802c0140540320f03003005502490181500c0c40c12141700c000c1407000307040480750900655800003402d210340d10004a1410703008100c402c09105442801181d00000300c000e8201d000740f080c0c9544488288440307044244035080240580c140e15418001440c5d0080c0c0e5241541c190040c1044000000039500d400350b9801035099079400b00558002d4103003114600050505404240e50850400740800c0d05450240c138480f086a500c130310602d0360300802c2c4041207082d850040008003855111144080143d6403420445920fa0311040c000420100158242000d0001604aa503400f41001010700107048040d050300d6002c08101d07070f079540e65035600444a05201e810b9000504c2207865100104080c41c401d252042d40840070764801d040da201d820422000e0707 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 213720314 1250 213719064 213719071
    0x10f120c0909150b0d09170f1e090607020f010320041401111e0319110c1c060902060712110c010302040f030201080414060114042318210705010b0405 66
    0x14050411010010b2170003074014002480c0540d8220368024040560fa01e003981c0040d00030f560b007417030000303c0031911041186d00e207441c41c40d906001c0b07081c0000740c0c000c181107210f54600a03120705107207429080300341c0c0b090b00b0001340b862023090b000030707484800040c411540d0000d0045203041c500c03030304900300034cd442010104c0003034014000900d42000788918041413100382001c0c000c00703400208034030aa2807852054084800806036150031401304a07248240c244040d045105119070817055101c5441150601c2031444c1540081c00011420410310000b081440782940080c12104800c829200040c0c100d0841c1800245907400d466440000d80d00440491103203018507500801c0d00071003480554810040507078401e100340c0d5109100c48134000c0c00c82c030b042c000b49d205460032205148011420f090901076100000c0c4260340844605441c4c1407030040c580d0004003200700050042c4006400780d101003100220344040040c20750035a00302c1d43d0100c1d0f40c030740c031240c0180c41660810303492208606083c03003500e11 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 213721564 1250 213720314 213720329
    0x415090b091b1b031206120604171614010209011706031504390603021201050d08040b03010b0d0e030a1d010302070204050907150f020705010f120c090915 68
    0x115081c81d005503402c0c503005034030f003019100505080d21000302e40c1000180f801d8100c0e4a03030199985043c00401c41c9122003c0110610380d000103083c08001aa2158525034803589183c001d5240d400d6140e10003182000e5110181110301000703154119900190b0080c0000e04003aa01c051880c0030284c9038101500c025102e503501980903d40c0c107a003c440b20341170346401510500800289192032141c040c0c51200000c1510b40c1081001014548003c04031030030002010340b4101941849e0155661181600051103002d0050300990304890400241400b203070050000240c5081d00ca503149c00110105400566408030b04130b16245100300306107400002d03684e032981503030740b030416000c8040200342100c124043c0c2541810f400b0f1120000583d9140a0301d4441c01400c4020110710385004891600c0d480c0854000042c81030710361340d80ca12290702003014000d0310803c1c2414008400c00e4107080303c080c62a2840a4200741c0360601080100d680281c9140c110b40b4004410b20109a04980791804000c062203540c4 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 213722814 1250 213721564 213721591
    0x304080c01051f0b070312020c0c13091a06061c020307080a11090f19030602030f0601030203040b04110d0c0608040c0b0c0a23060c070c06090501080f04110415090b09 73
    0x704c0f41c01a1001400c2c0548285000c0403200c280064010071790704a8406034100d60840710700040182010359904080400090b03044c04a44060b843c2c000180d9502580d030340424503903500042540d110041202c030700a03085821044401c0326140000c000f508240d6440300051040c40200b09581400d0041c6414082c40011036031421154004004000d00790200141e00f000d6180d0000c14a10a130000103002180216009641d91606a00d1119506402400385050620600c18000405c40c0b080b40c060340213a004034010f003182c1c451800070b051075030715003c01010303500300410100c0e0196102c00364500070ba00c40e000741500d5a84402c0c1d42c4886010343c981e034140a40c000341c1c5410101d80c141803c400c0b07503003040900d40ca4448051200d203003007540c00c5034400000340700091882d040045900d80e40c002400d4600c0d0a0000d141800e000810100000d803940b0141a60310740401d00348001d60321039207425140140200400711a6940300f03003070100c6500c15600c1c0103150120410301410031000c09407048d480c0d420401c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 213724064 1250 213722814 213722819
    0xc030c08060f370606030605040216260a0f020c090417070f08040618090606090e09032205010207090b030d031503050106090b12011a240304080c01051f 67
    0x2502c42c00c2225011030f11614000c5482a5108460a40c844801191440126000d4100740c0050107075001580041d0091f071040020307070071003c0d035802c1d004500c940c001d41c0c3c801270040f8038424240da40701039100141c0a01000404c0301a15400c200c0c255400c0e446a0269030740e0941d40000c11010b80070844000c0c0c008400706420503008201c0c003008100052050b44030840f421030703644489600350007503081480031409603c80281c140c2c104c0d040107001410440380501c0b40c142007a80c0102000018400d003a0648942c1001c120720a8091084e5003841c0550240200400c0e405268502e145c0440c0c815540035002e917290200f112030071406600105000580141030121000100310002c204000001e00326004400002c0b0002e1000e000d440010941c0100203e1302d00700380001c00106440c00c20001d00580c0c5081400402903d96035140d500700041152040c0c0310010064a0b40264001c0190032200c1200000401c01000010b43c0a08045299403001b0411991900c0e811200c4004100e419048100142000c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 213725314 1250 213724064 213724081
    0x20a020a060f050d0f02030a1b020c0906220605130221040201090f060c061401080c090604060b0c1b0a0308030c0a171603050601050a0c140a02030303040c030c08060f 73
    0x140c558102c5070300e0401e240451a0340000e0407540800d0079040003680010500400c060749020b4612094410b40c2c006038030024040004c0e41e90240c220030b641c092482200002d1039a40e80d004211400348550328103090400462040f000201958021a4859030341d1040902d541c1ca554400d4552840130107404035880c3c03850041c18a104500240700301d04210500d0f03400f142d110100d910a0000300a5926104915a0301d450000300380c0703012182c4080104100b000411142d030b000a861081c0071810742c0c0100c000d40700d00000c500a440309410540340240f00040c00030b603549001a40d01d400a441c230007204006181141040428003240c030000d00304040c01d0010800c0d4404c2d41004010000319070a000398140e00760060500700303140032641088400d900303403041300c400f680500070164014000d1030041d02c2c005001001800107141813802800c445000403140c0c2401d40704001d81d40c105c54000b01100d4482c9443d03c0c040849800c1800700311401c400c207040002e015400016a14010142211022204d0751019103 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 213726564 1250 213725314 213725327
    0x18040b15100e04020c070f210b0c031306050106020d1103070f020108070306091a030616050a03090f02090109020712020609030d0b041506031a01050f0910020a080309010603020a06020a020a06 84
    0x92032035003e5420022801c5c00c0fa82008000c00800d501c0d00348140745132900b80c6500f481d4280a0400308990000540c2400192600c0c0034950300c030780c041820540b207464048440f2002d07007600000500c02841c000003c03e280d0380004008054180d00e0351600f80c0554400000c0f034480c0138000006102800d203d504900540c0941c428580c000c40d1468009134590b035a0054501340c81d020042440d844503001d0b0b4508480c00c003800086d90080768103050700050792203088024128400c1c28605d01c101a501d0700004108212440c009450300c0e0010032400803542c441c1a0304000754032200d403c070342011200b98004003845c0049451480341e240303503000c0c41c20a10040d05420242190300b8007030390701603641c2c4019440c0511240381840604480e68000401200c180084204e244002c0c6131241840030034003010384440302600131169141400e43c0d0803a12a090901d05070b180c403480d084010700d126004401c210740c044055000c0000c690088032100010740c1e81c0e1005a80710048010007035002170540c2c3d000c0c04414040d18 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 213727814 1250 213726564 213726587
    0xf0a200109050f0d1a0f070f0315030210120f0f1803020703060f180b040c08010b09040f0c17150c04050108270a03020f010c050309060714040518040b1510 68
    0x30500c0344d01702101024401940d0702160451002d10340d00d401c0c02201c035401450000e4030102e0b0708080000301c0e07503c464208460280e1200900c6071910f0120038200c40d101d071079524101d8080080030b0010343c107240c43c0f0310b01402110540000051800741d074000f034240c00182c000443e607019006040c1603801c50b2520750140075202c8840d15116260405043c6082221142c0752442f030242c401c00c0c180382403030b00e040441c441042e071040c84240c1c10b2002d2503581e40c0e90721403080d400030b44c0032000528403441e6203030926031500581d100080b541800008211082008078010207004907080310805980c1d160604004a070207280140c50000e04141c0018503851100441c090040304d0b0b0301012890f0b040e00c00c0c181441c00014003000c50040e08422407610380102c0c01d00420f0940001e6040841c110b29104002030341d1100c00078422001c001500c80c46103003426404048034080c1030068001ca01c039171081c9100440340402682c042740c1c9400e04d01d0000314407207028603001c0700c1420001c048541240345040b003182c2000001d03 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 213729064 1250 213727814 213727823
    0x606051903110c011e1b2006040c15050307051c06030203071701051b1611030d03140f040203030d1121190b0604090903020f0a200109050f0d 62
    0x82c1c41200a1881800c00307040d030500400700214103440442c00e10000c03000b561031920f4201c0e00f45282030320b501320300000a4400801c1032170b1a078421f120f030000e04c80380d500040c042d03101070b8001d03c1e0600040c003d00e910383c0c400303441040c00340c3e9054201961045807140300c1240c071040054024080c012182082e404024450200c03401e001c1003481d1243c000a040c26030075445101d81119080012404100030701800b80d000c01c0d00c1c504038401082500401c00c99101d40e02c0001403c141d400e000b581044201030000d8102c01b0060f0440700e4051000b070026000f02981001c000a00501c100003905000c200340950b881340d035015005e5420320880c1c2c541c0030041c20705102610020344040c030403252964801c582240c0c140e01080401b507807900b482061054035800c0d8000341121541803842d1500103488441c1100c0484011071000030b94503a0504080707007844004c00240c240c0340107601095007440f4803203c900652400805010001d040007000640c1c0014403072080680000c4140d00c5808103181811203101c9280c040c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 213730314 1250 213729064 213729071
    0x90c035c1c06060e01021b0a05060304242306010c020103050c090d0f03110d0503040f02040f0c0201050106080601020706021005460203011206050408090613050f040606051903 77
    0x1484412002e64070541c0200f000500a1030114071150380c100034014040c41d0541203100102c80c403a000c50405a028014240603920000109042084254600384041c0e40290481c10401c0060340d160b000d03040d201081e42e50000b61100e11030040c40307107140c20390107400148c4485441510a0b4019070281c5801414200303807080c10710061102c3e481e04d000d0a00c1017440340c0503945a081c01894081c005050009034060700ba4480b1051a02c000d400c1001c40e60803d0704401080480c01141c40050082e040485618110318100940d0b400d00e81d0301504800d060b10001e8503103110740c0d91070340012a41d032a22485001e00503405043c844012500396480541c000c0403a5422820740030401c01da0b644c3c0c96a40300c2c8584000740c280c0010010003150700301407468074504103038113514652500d00001011460040050110b41d070722000300e81001030100c01c07109050400342c00e243d159400c0c4010f0082c603503ca0720805004040001805c049440c1502c200815145180c54032030502e140f1308142d0099800489111003031507035 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 213731564 1250 213730314 213730357
    0x114090112111b0f01050906070807110c1507020405010b160303020705070302100c050f010203061011011409030702010908030f03041707050307060204052701090c035c 74
    0x31a03c55018941e5040106074800c0c84a2040b400c441000b0038142e115007048007448502540000c1141e04010341340b070603020300d0500100c02410b021190505950049806204496221002003c1d080030303802101e00b00f01e036a0b80c0b40c8108640d8440c00036598090201c503c86600024003981c080d02c0c0d003500823001c45550ba03840350702250880c417100d50384a0124440322104010084200084403070103000d40020350440c24808049018580b00321140c40c2804141948981e415009500c69200c6100424030300705942081c0c00c80b41d4aa6100480a07070029100c40000300308400300008541900d03206032030351455a40c07a5160002e1404c40e8803a411103401040004c500425020809040c805c3e0003a50016580c43c500350401c1580d2018030030211142c2da0102d503030319906180c40c005504442d0800e00c081000c1e0080d0728110000c044010702e980540500c40c40c00100d43d0740c00c0d05c00c4181e0704800f407001c1c0c0844100c1050781d040841d444008001c100c00d403030026994606008080e1501c0303100c28081981e400d1 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 213732814 1250 213731564 213731587
    0x13002040f0e0412031505041e05070e10090302061207051209012306090403081b0705030d150e04020d020d0803090a03021006080c1903050703030e011409011211 71
    0x40c2e500040e0a03003100c105000a01444415006510800f401c003006008117600c812001c480d11846110711542d5942c140d10f0f940f40704407280b982103001d41e51080207181360456002d03041c03000e800b4045000e682e0304000ca0082900540f801e600f56030300281000c4c1453b000111188001c00000c090204104042c04282c540c0d00203182218001c081040000c03d14000020140d01c0d108031b44903041400c0102901800790585414003c65009600752400001c1984c3e0080c82041c180f000046100740c40b040055a03101b44400030000c0c00c85d1405034441444a51000c00400705810418000c255a044481010800501e040003c0c08040e610160840002410989506166820454620700e883c2c01c074110350400c056060000c03074802c0000e003000308880e03410a1806562180401c42c054012600e98403c1c00d180e10905980b4001940d100b030442e4005510f910700104401d03503540c80d4a002c00d00314074040341c8250042003981c03c2d030a07040e52040303446102141c01202500c1440380020408008100311b10a12 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 213734064 1250 213732814 213732839
    0x51c020c1212040203060f06100e0316060306090507020c0109090915020f0304060506030f0a02120f06040309090f021e2a03070b0f04120c03121409010b01300204 71
    0xa0068444280e0b5a1030f080c014103007844c100a01401055294904011040d951400304142540d480d261189400c001040481d2401a00c4c18203c500040134402c00281e00341d1680081090b5121000301344403c0d12410320030780e955210101c9160104155650511041c1183c3d48001030441c007411003010381000b141d000c18100e0303005090b04861482c00001b000140400e60040307640040c02075000b420071100d00c0300c850340ca80c8544070700244500321b8880a801094000c011525011031510180c40443c20b0500e00074024503820701c01d1300e00281c01e000c0304460740728880c805c2e10340364070702102410490440740306910040d501150002600e0030001242d540b4584029002005083c10b40004655590050400d820306030801403040c42c03901044030400c030005070303058113080050040d4108402c0103959850142c58a4440c08068000203240c11551030101c01440e0b616802486000c0c001c02050040d08011140e01d40b10768131038042564070f010f01421107228150411001200d03120014241078503a49011080c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 213735314 1250 213734064 213734077
    0x403030b130b01030b0109032310020f0705120418240806060f04020f0f090d081216030903230f0d0903201506060c0a031e051c020c12 59
    0x203030b0710401c0060550301482600314841d42401d08005440c0b641d40c43d0360303c1c1c0b03c1c2041d081d46c403c619000c08400c00f401c1002031152813404a5001e40d00c900d102d4442800303a40040f401901c2501c103904002140700503240444050ba038422140103003107590607203418041d1003a1403c40e4881403a10141d035405c00c0b00924504040c02d0000040c0c41d548c10b01104000f11030005681503403040d03104111125185400604480398080d00002072512540c43c400024a0f118449401401070400040c1d414501d0058030300580c4038403107003035aaa0380c10704110402c904907500040c000b0081040100d2085145844000a0021010000d150745ca0310451022000c0e042c0c00082615007000d80f00c0000404150b0004400c3c0035805100001030950300110306d61a0752180e100866100881030000840c02039241c8800322480d880442048402210709850300501101c8001a0744014a90481d200d40700c691150048407071000d241c030303851801d018662100f0002544559a10581d51003541c0941500e82c0103e40540701 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 213736564 1250 213735314 213735349
    0x150f170a0603060b010201020901090e0c09090a06030309140105030a0b061309020301051e0a21080a020c0f060307091412010608061807030f1e321b06030403030b 71
    0x20101e10310310f480c00907a9403e040d10790547e4014803c0307102c20b90b80003000d00c0c1280d40032040320900c7c2c0c540d02c01407100b82c0b00702c410550708050f1f060304021180140382c0000c1b04480c869564410f8490b1b4601c4180d03c01c0c140c40452500042d410008180400c03031a421119080342c005103e1403511544604802c1c01080c5503010f0382402d600840100018903019640c6500040c8a4101c901540c8030a000030701801081d000b200452040442e20603003410b03940d124500c955038020780c034594a0100d048041d64424210040d40e104040360074020026007004402c3d00c2c00f460f12b0340c94454a4a04102103288500c500c1a5815000703006144041c80602c1c0900079400101004000341c5041d0600c0c8039204041d201d02d81408090b5070160b98100005910104542c1e503c42d084181e090016411290020340e8101150b400340c01485800f0640c4814282542014550011941c0721880aa03001002075240c0c00b5000010504210007003103080d40781000001581c0c010310920f40040c5610742038000030552811079070f0800 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 213737814 1250 213736564 213736571
    0x10b0f0f04270201020616050712050f040905041e020f01031a03060711070f03121224090e07080a020423090303010303082202060c010207060204090b0a050604150f170a 74
    0x2e0565805211040d0480180ea02400a113895800080d040d4454607200400310740400f09124903c610400588010b0706c0d139611500c0c1d80d207599450a001038001a00c081d1307a03c250141c0c1c00d0051001d01d560b02c8000030341c040d00e01f03004020350300010343c0208040d2001c504070096005180d080390390240411445151315894406c03401200005103442d00d440c5070059103001100300c1302400400d060350400002030040e442c000401d422014242d101422900d0315294021505400981c0b00c000034414031015a444c0030740822400e00095210380d0780d034045104011203500489401400340c03c0c1078000480e440741100f05802031958040e2908464841202c11844075040440140700701603021440301e40101e8810550a440710142d010040e941400e4903000307104806c0010101890b020a405560203036400c000f00b1501c9982e90041600503140c80d94040c5d1049140150101d45850000190ba082d40c29945000d03840c500000c0055414500520300706080c003910340c0304042c00428240b440c0380b05510809010 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 213739064 1250 213737814 213737891
    0xa0f050312130c05040911030f010506040b01020d090b0d060b03010b040302090c03041a071202040e150102010606020619060e0108030a02100506060703030f061a07030e0102010b0f0f04 81
    0x70390a07840070b07050128040440e1208008501203030700c00c40a0b24011200004d0080440ca4030180400e0600c14464040c051400820151003041d80402e02c900c01c01c0c0d9090209911030001280c4502c4a100400046900d40105000203e03140020300101c0960303c1000540c5912803036105001d030401d81c411180f0260000b403d00840c2880310105400190812010381035040a50315521308107401030302e500500d01881d0000f410340d880384416205c0c0304420942159200d4891a500d00c99810885d50010300800c0022a044a548140300301c0c01143c0e240e130301501040c0c60740c40100c101010080c0088100f1a2901c4010422083c0020594000d10380b000040d40d4403084100040e0501070b103e0b00b052007451900d41040382c66143d5070b08903444681d2600d0000740b00081c41c450f141c000d00603a04100d20041510070720038080c862040042c40114040d40310001c0040706613004900b41c80165101d183c1001d07400d0003013126424400203e0400c410020008103906506014140c0d01410010302c1c0c0c1203020424040c1c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 213740314 1250 213739064 213739087
    0x230705031c0606052107020a1e0203121305010507260409182604030501060b0a090807081c0203220504150e07260f0703060803030405120a020a0f0503 66
    0x1000010585824000e041c000e0050317403402c0461102d4807412524000c1000150340d1803080c005103410951242c05204080d0f00e1894015561241c103100728000e2040110035080100d4090030b94510500d8405c0300c034542810f00004603110341044204842840949000610412100c60344945040860700744a460318607100006040c2c80c2d11100c40c2e031139000c0c08405000411b83e0300030001e000903d0109111b400c00e500300d100034114811175201810035481c0200204440c0340700ba0050500c0800c2d540d4a481c4143c407040100d4483e10f251250350800c0d40326440380980c00510020039800a00f071070060384e003400604030301d480d00e4408100d2a101e4403030308940144810f280500c22900919160501403181c00e091120820070010040c00d03102c2403004100c00200c203603940c18001d0601c0a00ca284000c1182041000c81800d600291014004030341403800200d217030800042540d1149401400504a10003030442034440c6c4e03070010b803201003107000300f58000e03010400320b02090750000e00c500000c50f901c42d03041d50f0 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 213741564 1250 213740314 213740321
    0x50309010311211506070c0e0c0c0a1122050103050d0c0206030a020708040f03030c02010305070c1e0302030c0106061812020a031202010f14090c060406230705031c 72
    0x3000c80c04101c080c41070381c4a001c94440103641c00c1c1c658900c0b607030710791301d50710080c080a410105110790b100d03000149180801c40ca13205c0840403600001005880c640300c030100111507014520807800b050340940c024001142a201c005a0402e01c00f9059010000950050890030b06011102a100076151401001001403c000b20413144e40945041c044981155002400c2c620014041300380e05074020542e0828440b014040301e004200340c20b90f0030600d50380c91501409414103050280d010038605000a0003e90040d10a1580b0341c0e4004050704a00801710140c005400e00d12200754214802400038641c80c0000741300b40d5016250b280c03110112040c500719210b140041d0381d040801c140e06040c84000040e01c071034007031406490f030124082540280e03483d400c9004265030290714018904020b03030007698040c19400b85015105d0001651034803c2c851003030068902c15442905c0c0050407401d2000c3c04e9186030001440034590030415a442d00d609034544a1641c2c07c0624402c41c400a1485c68510500c028072 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 213742814 1250 213741564 213741581
    0x703031e1b0e0406090203310213090f05190203010f1b050d0902040c0e03160605031303180305031201080a0507030303111308030c0d031b030b010507050105040503090103 75
    0x10310a000c210a41040d41404680040180d000d20649000581540d5582d0304407402034100018110344901d4900d000c43d00c200c0b2801240b202010444a008506543c5600f140342e110ba005000c07010f241900b990b0480043c40100001e654030111249880d0029400f0701c045124000c045d00152400c0c0d02c180101400c4414811007085a54a44000741550820010070a5500c00c45405c0254407600381881180c0a0458060020360040c50070700d2182e0843d4106016006841c0c064084130000080903050342c1c01c40500380600c00100d00240000b0f416442074080c0b103000d19209141034030141030348841c2124014040c0e042101d41c2c0d040456110ba0f5498540d4525004144410041944544079151103440d102180000340406864200c10704032144440e04840d08403244807080c4295650344c801042e20390300484140005400744010a29005101c1e01400160090050b0802c4c51a4000741042d0700a0030810703802410b100c41400b040e8007040080c4242c910450081c006140e40e1146c07500010110f0b420711 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 213744064 1250 213742814 213742871
    0x20904061514160b07020a05250e07081503100e0f1507050702040218060c0f0105010f030b06060903010e0d08070807081e1506040602030403020307050a05060f0a0e0402070303 77
    0x40c00b0900c40f5450140fa6086072603040030341e02200c1d80340d40404900344030600c8030243c4544074400130061403030b40240b100652030795212909042140c0b5074400b90201042522000001083da030041011400b41c0c0c90030142256006046880706a500340b4090107039204030094080076008115807c801a00a00000001c8212070b200081c0300d140c901d0010b03103a40110f000280c0941c3d400f00701081400d00c103442c07041c00040c005003001d4442411641082d40c4203100e80c4905c0342542410000100784020222800c2580c6d4480d00100c4903507120024400c8a411801e0219895901d070102d09072000410704c40058104100d42d00e84080d4501140050452500030340090204020503081090b409030807003007030071780c440600c2102c0752035107079400e0407003c060340c42e0701c502d03071144001a000403031a030000002c02c210b910940542d048030390303508104607031030810348240f0342c01000410014107011064001024002441d0034138000008460021070100d80042d135046000c65034890100d55070407a10001d516192032107 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 213745314 1250 213744064 213744067
    0x6090f0f05060d0c0e040e0d030606030b060706021c06060c0507210f0318080f1209210106090603240e10110c0102030901062102090402090604020904061514 69
    0xc10000c40c0080c80f80380c4a1040c40d41d0b45a00d10040680310344050301000f070004000f132280c030b840c141400b61075444800480002c00d140400001302c69000f0300408411110007082e56050800c030b5190103010750b011100020300c030a20081505811845446900060032071a81d4442c0241e01910b009450a5001e4100fa04400000e0300314400d000102095486500d5112400401a103001e1509070b5590300710300f4048800303441120012503654070019480000c1c6004d0002c44100c070103d24004030061069040007508211901c1030404c2c00c02d905c0001030b65a030300c0d48000140b0780d6a2000144200c0e08203400c00c0380e0b600c1001283c10984402801c640701400f0300d2490030400e600c0d000401c3c69031682c070940314100a0341c48625201140030158140e80c2402040b90080d0760302d1428030641c0d802440749001e1244280c0e5070605112603450482c4912200c0d40e805803960015803515001c0004a050081100d0303845a02080940c070607803181d0241c84010f0098035140340c20792030144400303890400f0b40c1c003146582c00c20 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 213746564 1250 213745314 213745319
    0xb0a1e08011e031e050a0f0803060109171e07210606081902041503020303030a0501080f07080706031512050a030206060f06030a0509120c1b09010305031b01060f06090f0f 75
    0x41c3d86222500d22444c0d4000c2c644c00301080d140203801d04c001c0b402d01910168004815900788004240158425038090b030742d402e07200f0f496034010004015100c403046441e4ac415450b008111b0301c1e4404007611000a142111040c80c0d89038031181c1d59010000c4041001d0030105080760800617103000d6040500313115005000f00b01da079041042d03100d000c0607e02074800e0761607401c05110920008040b0b00591340103070640f5540c2c507010f6800c001906084c405c4182c00c0c40341d00d46840501c9004111368007aa541c0001801207035240c000202c1c06000324100e02a8141e040b90800500014142092000c1d94480c2d00542842c495a04001c2e0074080006c041a0041c06003544020042c0e44440c00c4030f9001402d081c0c0001c85441d1607082e1460b24150160900d0a442c0000d495418a0710006503c0c01308150001045a00340c80d19080c0070b010b040038840140240d10a00c8007001c941c0440300c02c1507a0380510400000c440d0340e203108050702181613909c4000031900c4014203118039100d034400c0710085e00e80d5035501c800c0301e071 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 213747814 1250 213746564 213746573
    0x130510170f01180c052203050c030a0305030a0911060d050a0e2d0a02041508100b090f19061403010f0c0c0201140c03030a021206030a0c0b0a1e08011e03 67
    0x90082a0950b0669070700d43c1e40d44c0550096040e10798504155100b0300480c20071000c0440c1c0103c181c0010780321403180c00807270915481c2c00a10b0106155150b9580c038259264034a481e0003400c08050226006401d021003801e00c1e807a44805090720100e07201020500b401c0030702e10801101d0320321384401e1a5806c108020a03500181000e1455102c01d000d0618807035100040c011030520003d00002540300341030000341c80f00c42e1a0300200c8410380b50032600303550000c900c40ca02941250303a101c5282d500003000c2400106070441e0a50203e51004000d100340800801e9400d03000d00720741590300403034415400c80300d02c1e454030308092090140d04000d110082100120402c80501286400c041c028100003013265001c5100307070514155840300f5681c0048a48070700302036650101a41101c00c0020b02e154002d00000ca485c50f0028000b507a90360001c3d070b80180c0506003d03040c035040e400304101800380000c00941440d0a0300e200d020480c810400c2c1c1d00d2403203650400200c07070038211159030191620200c1c61410302c0800d = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 213749064 1250 213747814 213747839
    0x60306060c0102121e130b010e070e09090f011104081b0102031902070617060a1703090904050601080706050c0d18050315040312061a130510170f01 65
    0x401240c1003500c0e0351120a80328003911408021901c40c00b40c600a00203c2058404001c41c0c444405c040168240d072000c0700705501c00c0d4001c502510512119004001c4500e101c0040350308041030345001c0c61151111000310310742d010151505200d5038802c0d05803501c020400e101d5280691150482d0524091808600a41d44c100c0008058206550814142400da000300200c2d040100b00c1440b921203508a03a5005c0d4461100780300f4840481c105828083c5030b40208160a0300c40e14000b44042a81414249550701240c00401d002030144410816103076184e0391468441e101d18441e1008240355814400b080342000804c1c0e22110074090140801d190760880401c800c0c0142d8500e1821000d43c0f5080800e03661080d9203030b8005a014052070700c0700700b030952b00c01c1c2c1072620450007134884005088040741c0030021103105105002c40300702e880300e0002c0e80c00c480b500280011410500400c03001074a4400048000c0f19061881c070100340f124481108000700c0301e062590001201d910384801d51314140c84a280e8 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 213750314 1250 213749064 213749071
    0x1b060114060f09010309020d05030c010515010f0309030302090409061b0314070c0c05060c030909011401020307110621071821050a0c08070f090504050c06030a0b0301020315010f0e0603 81
    0x40c1d03280801e45030184e034801d070300c200c404070f80042002005024a0915540340d42c0401640c0b100c95090600007102e8144e1a10150700b0b600040e074034648071490002e800c50061408000480405408025011041ea524000d07170808600503140040d1000411000e45032515900750900141828080c40300c030f07001960725001d540100d0300e0510603e040064a001d00c041c5045070440c5502000c003003100410040000301803c0c80010075590000181d0700c07400203a40320200b00d134400340140c1c0204001000510b49400706843e110020740b03554180030b0099441e03090410f802d8003c04052101c00c040000c0c65521841400c2064901d0207074001044c00c00c4403200d4010103100c1036294201c96081c91300c04005e020410301c048103030030140e105907964680710103030340b40c050900c0340c240d81d01e45060011921408602c101d501480d030101c0203088282c0141c00b8003040707800c02055180e480f99034030f55849054400b0b00081d032189800d84042e2002240c0c410001d0129006002c0240401c10800b5201e101c80e15644101c940 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 213751564 1250 213750314 213750337
    0x20109051207090f06080c032a01020a05010906020a1b02060f070302030705010e0601050a050a142701120204050c09090408181513060f0c0204201b06011406 69
    0x40803988514094505041c2d980040344151404a020191074041e50080e000e0380d0000c4103403542d8141c00400c050b505d15000e400354010307000300c1185050304400c00c0d00604e2a0300303042c01690f404160030f44800d0300311207074403d098035010740004109151950005c00d0800d03400e0165400c4040301002d4003c10050b018400444140410008860091600801c262a10f01b58448000d02007507c81c9481962100401e1081a0080054250119680c50030302108400d443d4803220000c422007002c810041e084c1c0700c0d03021030ba1007618240829000c18600220142c045c0c007030b00030040d203065802c1c414041250f00081804a505205022502143d503130f014580e0741107074001d140592107050303001c0d251200380386651640f0340c40a2a8820b0440c0c00700c501002e00288490210507d2a41c0d5981d1019074a9150340c400840c0041c07046130b0040b005141c69400303005904440080c44030b400c40014052241a441003c0c002031402490089408281c3c08204035800352045050510030307144880c01151a41c00785100d60308 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 213752814 1250 213751564 213751579
    0x60501020703081c11390307062a03060806100308090f1f02010609050708060d0b0a0213121704120b180d0f081f0605030a14010b04090b0306010302010905 68
    0x2846841d64000041d4149281c0a02d6034500644654150130311209882d1603014000c0b80c81011680128800c540302010340c640035506d07007241130b40c4e184000c2c800040010070b40301c01c0010ac06000340602c2120342640e020380d14002485400c1251203480c2c0a801419009001c42038002480001d2030365007501d9102005a4094074001c00540026001105210915000801e40080c880800da8150041c5040f51102c04040002d9181d1100803201e0035000c580c80e98020081100c12000a040480d44690241d480c0c2c00060414048048200c0c5114096000461032582c101300b01003030244940a00c400c485002d0151032416103021607001301d441c0301d100301815021680700001d03980203034002005200d038034100c10303582004622780f0007620000043c0013201c00201d440002984008a07800781035010301c2c10410003030302545011000c560642c40200090715060300c03010001140348400820320302800c101740606803501c2c00c12003590100e4103901c0009210394802030041002d41d800144803400d4a8065501c01c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 213754064 1250 213752814 213752857
    0x60519020709020c0312180309010503090a0209040c140a060807030e011107051f09020a0b0705151503010c030b1c0c030c060e0f030a02090c030a110403050a050106050102070308 78
    0xa80c204803076070744011512800081d505441c80310110090100501240124005454441d040c01242840c0815501d2a40c4104001e03c0558002c0c03018642c40005a011190381d0041940403459003031040d1000c40b0b00014118090001900e002e100000001060b1644004c4600d0030100501c2c2d4103000e0200000c2c169190100d1015000039000301c02040c002d0009140c1d1440c15161155448040c0f01c80d41ca2100d2010b00400c00351051406007403004d03a0028080000c007810042101d140345e01c1300303104481d14803460300c00302220100810703031500c1039a0328526103c0c404110003e150075120740c0380562082501d050b446105d1644c58040701c0c41c100014109490004030249420021500c0c1c1c0d400c06080890342c8040080d00c0c0c0d0740803058075003000068034402003403d1800c082c10307a40c0c0c008000084d03200e281c4c1800034070403041300e00141d6070210b0601408140d076010400700105540c006e420954050b00060400d40501c40240101c000800d403e00c02008410b145464030a110b01882036030301c01c0c540960100 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 213755314 1250 213754064 213754067
    0xf0c030e120a0c05010207080a0c03061e0903090314030a1b030201020c06010e01080106090b090712021b10230a0203040515090309040c020d050418021605100b0307060519 75
    0x1106031079805000c9680c03030045410244140501403150310300600c01e0b4003021036240008901104000d80c8800c51240841c215a01c800c044d1a040402c00420061f1000090020720320740100c20055009842e04802c0c4d6086044c03d064411546500700da15030710801000c910b46510000254036149a04010b80d4810303240c0c43c0c12030280c40356191441c1070b4840c201c00411000c81101015040350f000500070420141c0c0c4225030b205440690308190380c0411445c00081c42203000340c10040f0b0501008400502e0015528520344c5103124032013080f8815880145000440b10007481035050b0a0f64000e940304668003c0842244650b00003040d0f075029540210100701008010000a80000d07046001c9145a01d00071b0349107990781e0010302c0c865105508204140e1a0b207400491505a001307801c1d90340510b0941000d1401d801b03440c0b00c1820182e1590300304081a88108046840d40103640300328003401ca8031106140c10703401d40d0681d0900034031a4000c14410010980c020b4204c48a24241440105c80310303560000 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 213756564 1250 213755314 213755329
    0x51605030c0c030403030906080702070e0f150325051206040f030315062115051009080111071712070e041b18140d080304240614010f0c030e 62
    0x10700040f4030001c5008400c2540140040003594040d5450301e1240d5141c4004a070b84900034403034025800d60039800b00751070f600c01c0580658000801040203028400c0701c03022074501900215940e0a0745031405044049410202d02c0350b0003003508803008181200e000b041e5a03110000580010f00d60314044201c001094080d0300000400341c000d4248a00040d5100806410704000c40071030f036401740702941104000d410a21918811660301c028031001c1d6401c110034003c0041d128240355040c44070803c40095401000d00807011600600c85a03a42ca40940f40380441c85440700e100d0801c03a455040c03003100ca2030b15601c0140350380400b440c609080240404000705008100e988030794400500740d0015040d416400603440d0100032409146850401c7e6600361100050084000c3c0c01e0744590308988150104a045000d15080703801000c481401c10501c0d200e0381c482012a90041403490388503141006150540840c20841d0038080c20101c0340100415001090710750040c0000302400700010b50b014035501d07201c1 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 213757814 1250 213756564 213756577
    0x206040905061c0809041112040311010207080d09020f180a0207080f0307030b13090807020d110a0602070806100e040b070e04090503120c040b0403081e0a030504060f051605030c 78
    0xd403541002150810013401e41c0001059070141e42001c0301c2940d20494581120a9607102d200d000c152070702c41d6502150300d41528600c80800751740034004030000c2100c0d80014107010b102408001007007802c0c0e2060180f00c403e980c2499206001420034500c50f03803031004000ea800951b40f00c005903a5100fa16000c17005000310703550711401003808401c0016450b050707404000e4000045541041c40740420074094140d40c0030b20001805243c06116850041c00c14041e145003581c07003681204040d485040114085070365950080340107900900c01001002e100b8403245801c6840c0220280a00c1c0c14003410070350044025000508403841140024421803203202c1c900c0c0321200007401404400001c3c280144d40ea0030260340d4000002051004c18480742541c802c490441d40c40b0041241001e02e141c40340045074000b100004031220000709800c00c0c19040000401d11161a40c0780080c031400c060034000c04407000303a403003c0c00301840c050502c0071f01680320018400c0c20a191030481c1d0b0342c0ea42d03c403144a20b400f40d85c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 213759064 1250 213757814 213757849
    0x30108060f07050412060504140c10030207050c040903121103061c0c0f12060509071212020127050c0307061215180902030d02061003030e01021606021f09020604090506 74
    0x10945c0d00204500c1d074021500660240251400020024641c2a290803144142c2e540c0407411410112007036002c0d4014003607a601410641d51380a54400c0480e00f902c0098000310002403e1503001070400c1424410b800206015400540c114641400464007018000340c6c150000c40451140408102554640c03002070604001c0c8400c03c5580d64030940114060404115111401c010002d0130091000460104803400505060304504181c5c50b40d0801d001d20820500855480304400102e44000c45082c2e0701d00d500a0072076002c1c000d00303420400c0c2000c0340000b2962081d0004842003140d140c1c0007003100641070741003000060300610542c500c09840011340c0141803ea41c130309203142e030400315035001501040c003c0d4107840c00c500602c0c100703c0e01e806088405191162001030180042482003841d010380c51810300407220030404c806450281c0004c43c0d4803100c0140d00405260445104001c4540c01c10413040d0824400c2c00c1d02d0742d000800340e0145003c0c46840e0b81e9244002441a6034210001320341c007060 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 213760314 1250 213759064 213759089
    0x130f0e0105090f0a0206040608040503040909050303070909140f07091208070303060501080106120f060803121602030918090106150215061206060909030c100e070b030108060f070504 80
    0x2000081806031504950420307890040d8000b140d1812008a1007540803640200401e207014100401075620031400b50081da420b200510010414600a1141d40c1d00c06004500941d107916041d034006040038444e810804103030341803c610a514402524001e50803170900b44d480401c55490510403148010540c4c094612549160507038020711440304001e02805020343da0900000c0d0703c0300015220054284941400200040c0e40002240300c81d900246a0480341000401d095a881900610b10b41101c00950b0544a0031010710040107009030819940d24441e001a5007040140750004105960004241c130140c0503840010352050000e600003400f0b40506203403030b010408801030080d900c6146071b01c800b840c2030304400450260701d008220320f48a400d289008158981c1c80c03000340041d642014190340450710041c000c150062000344540000c0d0081c0c1c0b0030002d03034544c8880305503140880590114610401c100010f100d1100d000c110b807507000190000d03c9000b03071210301d030403107040c4200d80c881800440c0 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 213761564 1250 213760314 213760331
    0x8070f0312060311090f0606250803040803062d040203060d140f061b070809030109140c04050604020c060f0c070615081b0105090f01110703030f020f0f0c130f 70
    0x1007144d08014503055400d003040303a642913880e9001800c103440f9183e0020301845414103d80795266401100c0c4042d07091844600050342d40c1020540054404070f0780300101100f04241c1d0306010b000e5106606d04890003d560b6154215003500203c01c0d07584c424000c40d0004005145522030700301c0c600c0c60342d0b881528442c8402c0c0460203240c4030f0040600c2400c0900903403011400c01310118100650340c0004035925450141705590300541540400300350798155403600c491101084807210841a65000d410151102c0444d12081000311480180000c2c4590300c14484480310700000214240e01c4084600f050803151110030b000a00e41c0507942d40107100c0f0f410001c00c0c54504446050940c2210000d408854508220740b48441241d0b44540c160703030009400740302c0743c2c006140447c0d0010042c001030505400002801500d1420f044240d0800c4e004200c020300d143c80c9060b41009481404590348010f013455084900c0083c0c5c44070a1448958415012000228640061036015200600c5450350810061301c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 213762814 1250 213761564 213761573
    0x1101030e072103021b0a06081509090d020d02011a09310201030c020f10051801090503070201090b03100303050702120a0501090506090102070809090c0c03071115040308070f03120603 80
    0x80040c0803c400600501045009020700400c9004400c0d0700201082a007900b0f113602143d03c0400240f5103007854065000c07000941d25000300883c000e482100c003a140c003110a1740007929000080e4006011a89014140d00c00340c9003100d64050b0b000c0080340c8480160315132000c0c0c000151440107000c1035991041c2d10740305608520701117220180d8401e0f00e040c4101c00c1140401e0703855200e5400501696004845031004100a80d80503503481003519080700b11101003585181d08481e50301e07504580301c1c1e00000f8108103641e0004540d0009000c1e02c90501d14503c0c1a1040c1010a14580b00080c2030003008981a404c650703844a074052250300c034808031100000d450901e1070107400c044c0e00507200390007084041100c04006000b19004070b42c000c40e5a61500002200b80704088100500030b14001c20180820b0103801824402400324038000c001d02c1c13101e03240160802144010301103c0c42d45107a0100030408c00215032605542605030420454038004000d4141038803060030400404e1a0140780000100412 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 213764064 1250 213762814 213762869
    0x803010608040c0509070206040b0601140706050411090c2d16020a060305071704110303130f090207030914010915090306150e010e04080f1204060b0d1101030e07 71
    0x35401514803c0586658000b0300c060840141c1e0803000680004002030042445c5441032500b2600c1854043c800c40301c050500c40d8607402c090800c6441c01d441d03005100900503d070003e211503c80440c0c1e034220302e040500b903070b00180c4690a07404c0d0021103406c11001c1101c001c0340302c110340182c070720000b070369034941c1c60124480c030007411981248248194a0007042081c801c1c40340503c10f440a45490000c0903c40c05405201400100b044404070f070703074085110f05074400b030000d031038454070703c114411040742804503404005051703400103c8114810320400e0040707507010182c0c2d030844a0f00c0d10000e0040000800403680001140c00038940218070107003010a5550144490044a0203803c00b048000742201032201d01c00080e11400d4480300c5044014042040c4440740300c1e401c40e20400442d403412500d415007284903003101d0311900341103407003d0030801480036038011308640140c101e40114918040d070795844459282448110304040c2e5030340026030005801c1000348060140c3d510107040300c54500c024038412 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 213765314 1250 213764064 213764071
    0x1e091903060507020703080d0b030703060c02010203060108132d23010c1403040308130b0f2509140a0e0f0a141303050a200f010e030f07110307030803010608 69
    0x46618090003c1e08151001c0b4408041da036004107071030b02d00401d0079100d4002d804001c00e2130742d05024006000000880500c20002c04155030b400141c0c81c1d141500014042e4003000746914a00c1000000120002e0702813007442000c2c484000010841c0c44001d840c070a41e0044180c0010003d00900040010140e25600030021650a1000901c0040c00c034030b80480d0428024011240400020310201300002c1c010a072080c1d001c0d1415041c405014987d032509010800c0507190a00c505008000740311088100520004201030404280c209180f40000000d1003070b41644180303007036001c0c0e42d0344851556540d0f031009801040c80c0c1c521141c0504184899070500e0f082501d007140341c00d1034038040107a01d0344051300040c440c08111041200d8000325450580f5180c1c0f0211034601008201c48541c1a550800d079030111031510940700030503c02d0103c1c902e00b400c49103040b032180801d40c010f0100c0b039800e104100440340459848045031249008440210340381032020f40005000d80b030040300108a9541c0301026034030 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 213766564 1250 213765314 213765323
    0x3070806100e0d1406010603022506021c06060201051501080f040804080f010509010f090209041101230a11010506030705060f04150c1101080103020a05090402130f0b01030605030c061e091903 84
    0xc00c0c6c1d076918801d0b0100e11030201d80d070342d45000700700b1060b012107940b0300f89821041c040c44000d440c00701100d030754a03074800340d841e080400709503202000d00903650b0900c200b580c045060b80ea4110328564140010700803032002000c030131401c138192000808000b03001e81660000c3c103048003220300c500305c101c1c501ca02804c0105c03024481986002d180b00112161030045120b01074000d0143d071319a8645445031741244605819281c140000880d11040d0030909091102c1201e103003940451b100c500002c1c0003041041e440010450cc1c2c0e0405040c0132950303401007103680446408a032100d640d01c1d02c0c8041542140190f0340000d000d0842500d50395101d42c2c2013000d89100c20300c02c071112030740c64030000b005481000080c08007a410100082c424006400c00ca0b5507103800c030340010010030785018044400b2064030840800c2d044110780750043d0144650b01405240003501040340170781360030380690340840c04a01074417a0000700d0ba20b840c404402d002c003d540c221810b445010b001e41c0100d0b0700c5052480c2010385244021103 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 213767814 1250 213766564 213766573
    0xe0907030b011806080403051e0a0c021c0b01150c02040606080711030307080f0901090506010311041d030a03050705130b1209030901141e130e0c03070806100e0d14 72
    0xc03c0410b44001c100741c0d40c454030f42618649494034102ca09410800c031800610a4075009641c049038400043d000000a581da4800c55054a20602620700400300c4603401084180c403182e8001401144803a0645540c884242545c514ac90707421207903011810000303034029140c0100813680c03070340c0169034900c00c4a41e0b854078091a542030300050f07504c0c8011940340c0002609800490790380180018925000305041002141c40c10b040e4807402e04101003a40708035558100d11080351031030b00f4640640040c0e0000710a8010f5074100b00d9101a0b12403140d0400102055650000154454000d006490148010950b203030340d0701d40c6030700511409510a02d00300204082d03020014010550000c01c807010807206a41d6043c43c100780d031501d00030f950004000c1344035089124044504008691026140b03000d40082c10070001494078681138003c0e00c000d084608403041c100100101d1541140381140c00c44400c0c0c404d4444004424011520004000300f126805000c3c008003409004820750010b080c0c00140081e40c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 213769064 1250 213767814 213767837
    0x3090607080f070516150e070611030f03010302060f070507030501090213021801111e010501180e0718060b0c0604210e01140d0207050f0106090513020906010e0907030b01 75
    0x1c0031100d001c980b43c00003e80c017040b04243c0c40b010f010220444601c980341102c00340410501510a40d2030041400110341e020034410400310303034440451003c0b0601d081c0914580300391085042413a102c1400060b0140348000782a60420340590200c0da6402d030810140c6001c0c83d103e1410394044c0440d0141a403140c54200c200c92a43e150701c0c07003125821816884e502c0090400040155071482c404094000c171341c01800820000c0c4400f03885c040e4a81c20115000040e29070400d410740f0180481400242549490211442003020000450f2025101c81c210021a0301c0b5841b60144003a080301e8000e1082e001000c42c1980800c880055064010f512507a0145140d41030400b0000c400d00c1c903001d5900c00224140500a055405000b049041f8401d070354400d840d1001110203003040ea800b004045a460780441482250f41c5420310414010300115007042c8251700f4605000c404180300d00030083d20038680c8002140c00d5a00134940030a0b08a03025000100d0f5280903034001d0000c00704041e032075000c6420700841 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 213770314 1250 213769064 213769081
    0x150f0614090604080d120204051305060f0907020109050f12091306030f03032307021002070c050d05070f090b0f010f020c03060a0213080105090a1b080307120917071a0f0309060708 79
    0x90b1420b52740b01606400302c0644180e901c402401c4003a041640000c4020701004060304e80c61000391140b500d640000c1140c0c010351070428500040e0b44031110240d0071400703001804070155070031100008402c50708403104c1d90f04100f81400405a0b030740010302d81461399006070304041e01743c1c00842c3d02110002d1001c6c6803d550a00700d4225000440381540142c00c03064604c0000142580035151141c054188030320600d8544000c21f003c5038003130400b52019071290108100324203c403e072180190078400818000540c000000c10107045401c000345042c40072401c440007a0070320070404101c0c003100050840c1c4860070401902c10007035004200495a2540b09400030815503814012903010303508000052200d4180c40c0c903810a501a01c41c1c0c0071031604800400010100e000300040d00b1080d002c0c4030340440c0000e03e0400640f50003620743c000403000b100701694102c185800304031001221003098172400d200c68101d2110000d131003611041d40d4070301c00100600c820403000007152445030080342c42f8454541c603488031 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 213771564 1250 213770314 213770317
    0x120405100b0f030c10030f020d0203060405070512010e0613051501020106060c020a031e02060c010f0b0406030816050708070b0429030a0b0a1d0a150f0614090604080d1202 75
    0x65150709a8015a598031450824845c0e4203481421803500146422401502c03806991100483c10708142e000b00c10310000703250910070305800003840c0c00c00c01d05c0c0c4403800e030b24903413100350500c81c90006d101d81d140040c2d0542c03a1190301f18403803043e034502088207241100e03a0000800e001c2d180c0600541c64040003060483c050901c01d0020b64004050540306461556009100c3d00440c6004515020110f881001629180068080c2880c2e840012075091b0140d16802c2c00c075020310452910039420081c0c00c00105010000f194001c0c4140c15080728044507a05050b46055616401100b45128408001480100720b101a00a5402001495290034294031401d4901c040c480030054444030200003048881c0c605901041e101207024107002e120a6031101c0722405d180652a041c48450000d070f041203401c000d41d10410143c20070317400905480904225100b111544d07103004001c10b00803d4404500c04100c02400d5070380020000385459543c98441c6c00d00750b2201e00b00401d03c800714091517640c120a140600 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 213772814 1250 213771564 213771589
    0x1060c120810140d0506040f1103010204120206030601030e1e2119020a0b04061d060f060d02031c11070b09030d030209010c060504140c010c0506060d08120405100b 72
    0x701e20820103091883e407800c9002000c4009031304c640c20360740050000340f05200440c810303802442c3c180307885000350405001c0c410b030700ea4840344a0f0748100010700c400d1210301e003901402501550074039207943d60840140d000b410180380520b110700c035024a0000280c402c404a101e80c810840a0345e002101c0e007001032104003821441901055818841c1e09140b02101c1220503800c4014411039120120607141c82c0340300c0c0000c0d81c05444c440d8aaa0944083c1220369000107498900d01c00245580d10f00104020110800a04000d00c02e10444402006554003007000007036001c61104c0340540d4440f125000380560740c980c4000e442c00d00814030002500c2030b00760140c2c0c120405c040d014040c10380c0802c004500035070010032454144031400601401145041c4140e92103a07204400c2c48107640340c0f10048a1518114400007810006000100c000140001c901503810401c144c2c1c00d000c046030b8616001e61b060180324114180000c51401b004144030001804140c44c1080040c00c1109106502c14460100d62a9 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 213774064 1250 213772814 213772831
    0x715020a0f02060417070c0b0406050a0e0909070603110903010219081305030d0504140a0c050f0a120f0c030807060f0b09090a03081503030409060815090d0e061201060c1208 76
    0x39281721028040190090031042c1c403451100d2542da88a24400010f500302c0e800203000628045201c1a106030450411a103a803400c031482e80c0c8900e000d003c0580e50300741754040c81041541b10102e04220300c4072002a0340407000018000e640325801c040c6508000c0003038140101c0001c0040b000b04003100307011aa01c01402d5080405189420580b10b02d050240c040608122110100c844002040007004d001201840b0b204069204a2519080402044403040b8401d207215040c208010010a0011036010811962040030b000b40e021040c1850300340740700103600c0640030070320009001d005c00000740d102d0114103003400c404020310320681003032100ca074404603118203142c0d20070b06080c03004c64010906554040c80c0c0c0300d5a01c0e80850b20394082800d40d0401da01c60088a030f1103490900c00c04405101d815601030405495180c0b501c0c00074011035540482c4003200086c07202c3c4182140c815210542128101c58190301114282d580d1008014101c01c0042c070281e03142c0c01c041f0100341da00d9115040315800f50040c0c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 213775314 1250 213774064 213774083
    0x30c01091b0e070909020306030304030c0e0a06091107031b29130b150f06040605070302010515030c0d110405132f010f05120405070e090a0222020715020a0f020604 72
    0x40c0b0f0031700d800079400504242da051005210001c0010252030340000500366208903030001e4100003480805031542504445a514100246010a90a01300a95005941615008444025003946008920807562010b40155180d9096039034084403060162050365030303a0031030611030341d80111600044260ba0030090031191101c0c0400c1c607440c800004401c1e40030f0014581490ba000480002e52180d00c1540440081180422000207141d0280300c0c16a1000c580c102c1010740502c89c0001a4990044010591241e040f9000e901c09001c2603944013218150080c3c0b0070001410305e82003c40d01d142035883c0031075a0350000811810303a0280c00400c201c101101211800c1c1130719485005588401190140714104034050000499035040e4040d464011401080079241440c104028510700740402406441d844c0e018050090040e282c041010301b40358030b45454a4040380340002d880000e8030507002d0141501f06c0c0a9280c84181e042540141050354103512045208040790b502662125021034000c1c01c0c030b084 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 213776564 1250 213775314 213775319
    0x130e030706021b0703060e010e0c0307060c03051909090b0315010317160b070311040b030a05060d12020105010504151a090612040c0e01050103020c0c040e030c01091b0e0709 76
    0xc00390040e00c0601c0d520a1000d0203c0ca6422002d0301c1e2854035401529042d84520062000e05400e1041d001c10010b0305000d0801c2600a8000c83d99440c0c0341d214420401001c0610f1005040c400c909441c50040041240d04211011000c01822802e103805440710492601031a03280314940000c084100703800502c1a045503a1850b10f130501c424124005120241c4070421207950300e510310810541000e07100c3c40100c090740c10100401000c5030b40351100741d40c551401700302c1442402e4007401501d505c501d2004011070290b4603840850040ca88031100103080a0f0f408107d480320079019080325041e900300703560070070102c004800403100d80840780c07088e03072550390362030000755662400b42004010420010b81914070307001e250114020444011501555846607400c4103011900d007101640d0f004240901c3d095041140510005803202140402280318546e200d50300c01a0148c00c1c0252964410365000801441000d8101b07003e5000601c0311840024001e042e0101d11512100301060140c084c80e520401d9250 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 213777814 1250 213776564 213776573
    0x51003020a0219080f130f30030c02120d110606010e090406060302060c1606050906160213020a050a02060105030d2703201c030815060403061802130e0307 68
    0xc40f000d01911400e00030002c000d151a07040004046100944407112045803800340314080c006443e8101864580c01d000f0508001100f09131070000c60f6502c080c0491448100e460305407252299890000c2d041030411450103122240030810382c0416080791103801d881100c11029907211501190900c0c04610951400c8059003030020f45180e105124190000340703030352a030300011801d40107018101c2240d44240303d01c4680345c01d9145181d000b0440780c1441d60420b50314100282c007a018503a10442c107a6030307680c500001c0d5074132212450294140d0810843d41c0c0d170400e4000030b0040e4046110140503214240000985003030004024108014543e07880c10a02031081c002c403150401140c0504442802c0d100210210303009180c1300014014100c2c1c48050110800c3c2400120720824110910040052410b01c022035008892107070b000b080c0141808500c2201c000188060085410207884075140228a00c28420003003101c0c41701c0c2d8002c5401c0b600303200c99112010245c4004121400361500203100840c00103 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 213779064 1250 213777814 213777853
    0x60b04170f0703080c150408031501030f1d250e060a0b0a03020a03180f1101120501080c1906350702010c030e0a08030c1b070f051003020a02 62
    0xc0a8180690302020424610326207404155041501e02c100005191640304104020f03c0b150f407440f803c3d8980380d038a041e0701c0342d0304d46000080aa2480d13050352081c0e154103178407075440345004281c00a010842c44d1448440180c803c050549451254400d402a600d03c0c1002c0a0000c3c0c051862004051569800c0441200042c440130340b0b481d8000080510204141041402812181490b90f0300180ca94014200041c00c1e514244014a120342d034481404000c540b403d40b00e0b41e42e55810072003012940d00c10f400100c582118400f9141c034841e19020012903500000700d61a1a9182c00300c5070529905001000d0100f12005442044045100c0000305822039000c42043c0e04216043c01c0071001e81d12100f0051132403607200322800c0c40181d5507804d840183e03541503c50b03810454014070048c8924452542d818600f0712019140082800000c41c0038bc50550764400c0e4564070092001c155140555100c440340d1126550b03003e020300c201d000010405c1d0b007620071310968040295690040c003140015866090703c2 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 213780314 1250 213779064 213779099
    0xf0616020f0f06031303020105150102031e0d0609021b06070206130321020c16050a050402030a06080f0a110105070c151107060504090e01090506010612060e011409060103060b04 78
    0x100b10525081035510071018510905002d030039114015000d00e4000e003100c800a01328180e0f004600460307070499a000003990701c0054800e0b0301200e00d0b01c115007184428001c0300c825001141c100344002c503010303a180d000340640c41000c0c2200401494401c20382501e84108480c044016031008002444040c1c0581041c0341a5009050101d004840c0741c6841c202d02070102c00340c8540e150001001c1d4080d80e420404650340d11807061441a01504000000784400c0051007140e04c11600440807816402045d44558000d002c010221380146820a8445803a00040541643c100302000b10b0700740d00754040d40c1201c00075a400001040031034140701c1801030402e00c5014800c10849d24680e13107480e140c000c004d40409020540c840755200d40c07408404505a4980d40140c0500d03905140078180021310001d03686040d00e00c90300b000144c401080115500800d040e0b03001400d036640110001034194072513100a4400032080c0d40d000600c0d0748000041d416a1018412018001d40400042000088802e002000c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 213781564 1250 213780314 213780319
    0x605070203192402070605071e0801050907270f031b0308030109091a07110c01020f0c090712050712050603061611010207060e030c07080706020304260a060b0f0616020f 74
    0x6000f060b41b5403004480c002ca80355008a0316000f0303807545034002504190201e148500d0110171540c10103020030100b5901820078004d21140100c030381c000354030301d445981c0300c250280c5400c0319003a658034404550803040d100c180c2c1d52039854607082405512000e0b45400743d076040381d032240c5141d1806403600014040c20005503003001080d034040c03d19449180c09907000f02d000d581c5001c2ca0b80d010146090a00d01e030b24081074155840000c011224410110b06401d043c10219900d0005076100101915110a424001040680750004200005030450000e01c0402c00c00340d8200a41d54a00d801d0540c0c56509494420400880c002c2c0080300501c180022036078a40450000f50a101042c0c3d2400e0507219444a05d2040f43c001240b0444039040402c4214001c00c01e00004001c03051070300d05c020391244514000c0b00e00d1840013003201d0140ca03d104a005113020528422074039038414908055005007e901e100b24800c1e040c4c0300313010382e651401005945e000c82d20803603140580601c59007000700e8018041c11994 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 213782814 1250 213781564 213781567
    0xa15290d020411030a090209060f0a0509270105090610031a0402060f07060f0b010306050108010e06031c0206071e0e0f0d020301060303020f1c1205040c0b040605070203192402 77
    0x10f86010320382e0051030044848480c08510300300d0510401811903001800715000c3c2d14024401d0305541d499182035411502c1c00e0f03c450f4180d85440c0c210200600602d00610010404004100c03090b04055001030710800041090303030200d41306c040885c1c02500d4a0700c80540a040d84140c120010000d03a00391940292001380800d24140301100d0442264101001c00d8911640e100e41101c4650705038050301008090034a81002400d01b0300c0c0028050b15818003818404141c08400241c5c03c0c1c504000c2c55980714202d002480064800550095592004036400c00026800c2d00d801c45000c1e40140d2101d9668949454120b041c0640c0710600c0204c0a01c0004c130b581c8000024210800b40c1c600384070301c4012754025405013403186d0341d910146107882d040c100319032400180c4011404540740c0c000e81040c8003c1b25040302080070303140c2c2c1c20b00e0001c3d0181c982004410204c000342c001450f81e0010010040c4601c02e605507100085204107031030500714000c070007401000c1010000c04801060317036010352011b1102800103 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 213784064 1250 213782814 213782831
    0xe030906191e260907030b090a06140415051501050d18030903031e090e0402040905070602060a1512060b01021906050402120607020a060c09080a15290d0204 69
    0x2010700c441080c4080003c5001c1c1e00c0e08600b001140740301009102ea04401071551803c0c039104d083d0b50b07a1210303c0702070300c814151804076095180c140702c14100207030010b90903c10910b88403581c088171101a501100c0d0340740341c848064240303003541c010395104128203125014103c0c19403005503907135441407090464895407200f214050804070a00341c0c01b05402a95103540c2e03a800c5140150101c47c0f68402c010340e8441005c44074034659030096440c400d41c1c011401400a83e104c61002c680075002c4001e0041030b80c003402101003116a8000b500c80d100700030071a0180940503079100b0040c81e10300c10340070340641c01c8086c1410030082410380d0409200180c061040710380080d648081410008140d0034200c52180e110003d2005500d080c002002c140c0a0007401351a081c1080c02d8065a607828040e4000c0045450f407114044403400740d43c00c6001044103000784c03a040030f81850128101035044815001c050b1505d40100d8611a40114400c00526090100080e10304e00404004c520324440300102c1e0301039142d0040 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 213785314 1250 213784064 213784097
    0xb0301090606020c030304030b0604020f091017160c0803040201021f1505010f08071d100206090f06010810051005060c0c040b04051306020702040603020316090e03090619 75
    0x45009041803800003030424280300009080031080c4500703a220741e200b0305c0103201148140641541040c0b040341d0059036003024801444040c060160b540c0d90140303180301c1c0d2000340c2d40c0201e000c654164106000c7c1b603881e07640d6041c42640c007000785844d500080f0b00e030524038001040780c1e0003150000e00500460340c20311110741014110311645020303241c0c1b003034688500103065a0781c800c800c00030381024245400d014a070003d00900314a0003c10f1002003121458100e00600802e117000001c0d40000340c00008004170b40c50740696141d806950030059131094003441e02006001084d01da05a0f6100c102400e50301c1d14044090004c0d0001400c1c414416503550b0000031507664207401440211000000340160200b120b04000844450310b20090250f03040100300400300c0c204031020001c280d40414011f1300c6003481d0011800404158000031b415203e41815000c0950203604204105c1c0c1c080e8034140300000c424030001c0e40724000c225145400080900481640700e810626110300a84039203003108258816011 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 213786564 1250 213785314 213785317
    0x501080408090d0f031103040b03060913020901080705011101090305030601080901180f0b07080115031a06070c0f0902160f2a0915030c15201609050411190b 69
    0x481d41c48060b68078943c2051b401659403a0540084400356092a20300040e02865200049c29180b2460a54000602d04410000080748464029007038090700e686038842166a05030a00030a4007040d4002c8149500c46014051412100c1c1e155a44d2170554031403c0054841e6140502505d00c1e40d500ca107080c008982400307038840c0015018a208030101d801c2c074100760b0b0810601903c04401c00c01c5800c010300011100000310703141c1c420103150004be85140c1d40300b00041b101c1911085ca91115000540e0740500050340c0d54039050b140100b05a56000d40d80b60400b104030301c01c2028101c081c03172003080080f0118842005122003603002d03203881da111080d03090a6a02140d40d5003900808102410820b1141c5980f0344504003103a00c2c00b80b90300010904685840d010031200780705401468840392110410244108011200c0300b404132030b181014030b41041c40c9a1585500803040540c01019080010340322139078000c46000300c3d04803003000060407000d014000050001000000c51140507440014815203200 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 213787814 1250 213786564 213786589
    0xd031101110904050c0903061503030c07150e01022a06090303070b09010b010c030c170f0a0306242003191d0f091501030609020403050d0f030e0304050108040809 71
    0x101c610341c2c41a100007000219240a00303050580700003402866030b00d03100050309941005803800140d4590940340c0c00039144d07218000b59a40701c0e0142040019800745140c020742203041c013a40b00c00110b01c04d082c0c01280d94403c0014080f00107040b02130802c42507c07040208007803551029010380d14120909001c00d14541c04100100d460104000810410b80b0081c031410a42e29030901c1c0030b40101c245614018803134210020081c1544211040c0343c42041031000c2210804001d00740807036111a40c20a0280040280d8460020201d451040e40550f1168020b00709000784c0c203e46a00c4c1e4000d86a1001d50f024402c142402002c42c0f01c10000e4034100983c0b020316038005411551030b0150380f40c00c1180200b02c00c2c0741181960241d210544010425039881d816154045c41da108010040c00c0c610004802600c01070b40968111740c800140403060140104195032200030700d860b1a02c024020768030403030484030903d000003500e4000780018022588034504040d0018000c030b0f1164103200840c00007079204820700 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 213789064 1250 213787814 213787841
    0x5150402010905180f0105030f03090f0d140607020d090e0c18190801110403050a080a03060f090f0c0e0a0611160801060e070206040201050702120f010e01020c0106080304140d031101 80
    0x100421590b401c614117401e000d040103402910b20800510f500598902400d0740a03407041125200d20402625140095031119801c81e112610860100603041c2e111141070300c040d00107000c1c88036415401801104040101d0320b60640d100ca150351403410490241d000844650b04144841d2959031b4140e841d800780e40d00200c84041e081c006586458141400c440351400c031040112400c0c0001c00101e0001716600c070040e0b404c01d060030390340e01300000c08400400c1075411400401075154000304001e1442e80c01604400c01c0c00600b0065100215003d6a0440b020005a03a00003046403080c000f03580725490b030a002e50405000c80e440c1c01801800c048078869290490600c1d0f1b07548201c20000c10405200c903a0b000b05039800a40503d080a40008000d40718910029014524189156021410400400304e800350001c0082015507a0416840d0107944010b803402000d42c00c20311b000c43e00c03000200440d403c54403d86105203a003054881030103844902948140c081c411100c1003843c41090a006034007001841 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 213790314 1250 213789064 213789109
    0x100204050a0906080c060c0a14060a0b01171801020d050903091c081210240f0e03070e09010902060c0309100905060901121d06010806011205150402010905 68
    0x100410701090040a9101d12091428000200040800800e011950740f500340d524695504101c0310f403901c0c0c60706200d1b0040c00b90041c419452044000032031103e010300700c480000e02c505420807004503018940c00803907007000c083c04c1002c01d02103040c3c032804001e5800c0b924000750502a24144100032600d04503a4420603800018110301c0383d18004c11082c04c00c500700c01c0c400d110708071244c48000c8140144214101000705a00200782c43e048250b54600c010014070350303103540449010010034030b40b151a01d00c2e480402c1c55103c100d500c80e80a1100e00741c904802800030f001d407900e403074414200c0350005011200c0f507541e02c09140f80580c5400b40203082c00c0d178110000750794074010502801012904441081304218a40000b8000c0c0c0c0d864000301c80540400b4641150301c140c000c480d80300203102d80c0d980d001001a0700841c6d0708886402050880c1210351710b07002e0766440daa03928100d201c4e15903c8500240700741c0060100480144100308002d0b0054018541020b52503196000324110440351603080300f40c541c8 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 213791564 1250 213790314 213790319
    0x80112201c1b0b0309060114030106180f0b01020c0328020907170603030313030c11040f0c0306150c2006030a0f1b12090201050c0a030503250c0206030601030905100204 74
    0x198103081d01c0100043c25000d465440c0074a130040e10f521060150401c000041002c0c5030320366409401210240c480088001245910407a4040003403170411a440d40d15410047d01c920302e5030000c180b00c130700090090081d00d00c2c081344440e84601d1510540d40701940d120704865110168803000c031014842c2c0403540b2115003d074441c2c120001103140c000d240d144264010401c0006140c1031010b200c0d10503a00d81020800c5000030700d08003296407020142c15811070b00d1300001110206540d080300361000c915450411103141c0f202d528a0100038040300e02001708110329200b0340000d240351149070501c402e20900b0306200180c0740019016034010f41300d03988616121200000c0030f10403032040340d512080f0716051038050b24810750054600d0340b80ca100074101c103503104010029640203800301c4085801c03850a40c1d00412070b0740340291071a081518a861080742d01494000030024544038401148442d1301c50300d110b103045a0822a1030b900080403141010340361152200010400c11403034044000703d20000d88c4076030 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 213792814 1250 213791564 213791603
    0xa0924020307020f01091a0a0e0604210305040f020f0616050a1a04050d11070f0e01060212040b07060b1c051b0a0f0506070c0b030702010c080112201c 66
    0x16440c403004c9000d03450a0072100004642115041a2040618480000c1d54800c8502c000500304542504060300402d8108003c014140c420170583da403050749106d580e09641c4501310100c440848009001140e1520344102515040040415500c00106200e140200c0031440306001140144211840c0d84501c03408010031540001c0d21044104040d006015403a107034680650300d0b103a46081409020804256504a03402400301101410703100501340f04040d501c40c181d00710b0300c00c244584001805071031100d10003548000225011950740d403144504240098440c440101801d10925070302540003040d00750480002d1150005942c041d038082e00b00580d918003100c0420308411041da01c149046d200600c03400c407169002074280e440548545482c3d00071880c3c103000d03041c025044000d88103070100070007001c96030541014105841654404600340d91b134100c0d0440c4189040402444000007e00c03030303002c200c180301d40c42102c904002c003903803c41183d40c1c481d0000b0345000740043e9640100000301c400d400 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 213794064 1250 213792814 213792823
    0x31209030601092c0c060c07030506070804031d0a18020a030c0e012a020a0b04060f090e01030803100312020a051b030607110f030423040b03060a092402030702 70
    0x408030b02100b4004a030080310b041d0340001d00f40480c0700d0200326080610030811010402c0d02c5d900000509115074844800b2841d5030385074414802122030748a01d500060b513a500c240b1005010304d03416128100e58003c0c0420039504107070030301841500403110f070900141c0d009004d4124051050220b1006940780303600300000f4281c9a00304040b0302807000014288200ba40e0090030000b44140b0b1490280641c55200c1c403043c0245003046002c0e611401e00c18001ca180100f40000703004540f450f449034505d212440340d00751010303045441080540d40d55407004001141c201c1d0000c6134070440c80c5580d0340c00f0684940d662669050302400f4080143c0c040040c0300c00708030b400c12003d4000c03998642803480e04154074001958542c0020042c07010012141c2c0b414050040812040140f0102c0b00192038132a603c603042c1c080d28404101700c00f40c21187c04103050000b400c00c1d00c100781c0c42810180107010b442e13aa86070f0190240c09144412200700050004205c803090044014840c100040e40002da0340e0709111800a140 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 213795314 1250 213794064 213794069
    0x70b1b011506031802210a0203030d02040806010806060901090c050720040b1203030106030209011806030902010e01051314010c0f0c0e1b040905040204180c0905070216090b030309031209030601 85
    0x52042c0301d140c0401598440d86c49403000154840d0744002003002103601c50500720041c600035018400070070b400b104800325070050800d0341e100070210b071a1aa44d401000d6640c05090329015089940d01e8018031450300e258100f4aa81003070381c00c0042c84c0a99980c0c0f80c0a803146455005900115492100d500602d414000c4000c100800c03245101507154a81c10300c0d880740b1040c0304920030b05500103041c0c04c5a90043e818043d0116005025000d0f40369030300805005030a100300e0490025801c0ca00000e0290b0240b000c0e150007070000303002f4003001400c1000c02004280c802d10000e0500140a1030600010682c0c19204070443c8201c658aa0032480c08421508840001d080200701600000401c2180b2103101e0a45040b91401800401d06407101c0c00030400a00c0c05079000c10410090b483d205080c03100c0d02c10f02c48215800c00104011580c0d4080080b80ca0348038100074a4009109084200000082da400c42c1c3c0d40c10f407004094920742050040002d14189040700c0760181084041a02e104514060144900 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 213796564 1250 213795314 213795341
    0x30e09071e110c040b03070506030a05090118050d080405070902041d0106050403030804080331051006050a0b07060f0203070206040c050d0201080a0e210711040e070b1b01150603 78
    0x20b4041d0710846030781e103880c118601140503079941e1882c050550303402c000c1ca41c02080302528413542c0b0b041250081002d46000c4880121039828100c035035441c92848440604801e4010303000d040704404040301100c0d107040181040d5407a1046600224044145200800007088010400e0f20f60b082c007803011403d0a60141d00c44070a115040c0300802c04203400c1520241e10540c4964000e6480da2008494004e4070510426013404039001d2032681141030780c0d03003d02e2488178004c03000c440d40745d4902c00da00d00584040d03002e81354101d0036001e010072000e0111000b40c142c0500c1514041a0200c000340c0d841d081380c004070b4410700140c1c40101480140f101240514014041c141c45080140049400182c20700710094001902c1c40d503244403000d5008410310002d4030040c0c0001d106030040e50700e0502e15203141c01031001625034040da0b003640109498a03200702c6144800200117042c2040c54100c00c00c030365800c840010035035058400045484110300b27100e079000500c0c3c04600001e1403030500000a04451900d0710f10070 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 213797814 1250 213796564 213796577
    0x120d02010c18060f08180714030c150418021908070f0207060f050307020a0b0106051e03040c030618060c080f090c031b0604091d0c0a06050a0804030e09071e 69
    0x1080d503200310b401c44030311007038140444a521046c0d00004041a01e0b03c0500319070007a0b40c4085a00400700c00056202d003000c034100d900d42003a0b0760400c80c03001030840c1c40d00c1005038108410861111000110210328151202c014180070201300290300562a0881d004005201e942c02c00441c5904212001a517002520041c080700c0d08050000e402c1c10b850070b0104081c40000301c002001c25108008040c0c0c5c0c680d220010f00c565594411001c0c06a8001c2d50011326625075501e624039004030001b054a1040c1c0e008006651201e1035a06e880c0300030700070214000800d01200a102001c07603d40d000c0c60109014981d100703480791078030103410541b005003d41480b640b80c0005c1e003007881640c0d002600102c5c01c28007241500e0201c1c940e5000519a04c120b60001c40c01a08000c40203082c00c406100d00224030301c0c080c09417000789401e041000300018003809a4004a0014081302400d42c0c4210900c41d071251081c10038400c8070010a00194050754115a0740000604400c0040c580b0040c0c505100c1003c81c1d0b41c00c099 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 213799064 1250 213797814 213797819
    0x4050f090d0c02061c1505030a03081527221a06040f0e07090e120d0504060b06040e0702012901080a20070507050613050d02120d02010c18 61
    0x12034481c049000c1120400c5030851589081d5070340c00080f0390100e070f00c25080020400401d2240b401504c0002c0c107482e002d511040002819040104940c81d109900d0b603900f61260340d84500c8504005040c802260700081030042245010042080d0468030780c86a0014a07502d24086814540d0701145096480c94a0381030010f4000203104014005910b40e20520401c1d69592a500800e00518101d4040822107051070300b0000c09074000b0800300d054442c030060511070401014030161751a010307036508000607002046411408103840c5d00c8950842e1003000302060849604002400d02c0d0881c2d007000c4103c40d20b481c144035600d502440740402550280300018440c1034502581805821146c0c006814441900c0004228030780c1076000c0e404554001001205d02c107996280c51189400c510003c4402d48208040482d85142a9041d507403140042c9000c85071140c01c14060140c90b9029400403a004500407480507440d01c1c0510071154105419400003038102c00182e0b00070115011908081464131004005 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 213800314 1250 213799064 213799081
    0x3070507180b0906010302181003150e09030f030403020102070f080409140606030105100c0609030809070b030121020418110f040207080910020f030a021501050108060d170409021804050f 82
    0x40f1540b0650034280180c035488045000c3d00100a009401036103c280c0d000c41254081e0142c0c07140d08401403101c04070b090503840d0b540070044654141c5031501c82d90301c1800030300880501a002958814400d10016007401c1070380c2d807006035450100c00d007150245000700b0217014403d16441550401c828241c502042410041c0c01718120f0710043c06403900030740e00710b101311110750300071030031038003250351164040144183e1400d005115900954880405006103000024914918000d07a416610110007840c000e880043d0952031040c00810126005030700c0d80400d6082c82d000d021070380c0e036040c018903e281da02d1035075104100308070b203000c01114400e40c4184a02d40204541d40180d0b400402d080d90580c0012030034020603403400501340d070039183d50700c03000942b24a4254041a048039904507450f154000340d890350015601034108075001c0c0d8000740b000c004200070602c0f03031218101d400010f03200c032860300d81c54803132241c141ea01c202e4080005114118029480e81064800d0320341c0802d0b200c0ba81011414000e89 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 213801564 1250 213800314 213800329
    0x4060b09070e0f01080a11040b0d0e0a0b0f070c05060703240e01091824060e010605070204090c090608030c1002040605040e09030d02030f101e0e090a0503070507180b 73
    0x11628100b0502c0000546c3c80040343d48951003051100900b182c40c0d81c1e80d0034818000341e0090400b860002c2c20441c1c164550782e80000d00c9448540d00410840b06940d440e80200901c40004001e0741c200440c10b40080c011540912502d80140525940070407511003007865040b00307030031000e0800004856000100040407030924024156904420042801d502420000c5d10714030b10000040d00c0104218281c02e001c4001010807004512000010b0010310b0303030f40e400c043c1010342c02d2165001042040080340c1c014038090f4007000010307201d0581c6001c26915004000100c49a68118400d140d01c0010929001802040380303c2c05030044001c1580b400781804001041400341e8070036800402d1003000418444c61081c410342d140011115011516840c02013610011044203485150035080c110001054554249203032019800d0602e1180402500d010380d000101c00c4001c4c14143c1b40d0255610140c0043c6050004003041c1e17001c4c900603d0024103200e4003005000700481c51860651030845480b0f440d496040 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 213802814 1250 213801564 213801589
    0x1030f0507241101060b040b1b0102030402131d0d050a120b060403140c030a0c05090a1116061b020d0908010204120627050d0f0809210d020304060b09070e 68
    0x1601d60043c0365004101d0f030241c003207030304080340c6d0100106010981014840c00b0344000c0702007105001403128500001800c0344000d03617000e9004880c00b000d61100500a4102d0104030705d0340361003103101c0388401c140c20f030410038411808000034500080c209101c2e0380c04180d81e0440c8011800400c8144040400204244258030004081000c01407042030707084410702640c441640060180c2e40d5000007071400d000b0805090003201c0c80742d265400801e0310380c0141d110300c1400d410503601440ca0300441c00841b010141003058110f800c030362140310310028550b4115480303204094540007042c20a609033800f074106540c9400c0f40105a01c10300c000c10101c3c4240c1110703142190040d500299203d20703c1c2d40c1b8400f010040b001040e601c0e220245000c20480002002c4d100c0005982da01d441410b07880c801200e410300169481e5985500020101014401949078109402da00814003481c144640c1c0b460401d81e0011134003998100c4d41c1d008406500d0070115602544030b40145042c000844890f00003880307218041 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 213804064 1250 213802814 213802817
    0x1a09010e10091b0906080f07030203060301060810090506010e04030f031d0105090f011b0905060a020a021f032319061a0d0614030d03020a0c0b01030f050724 69
    0x4001140c0c0302401c0d0305440000e07003a503000500482c0040c4100c50303640004506500005080e107a8005402842840800d0003049070b00b501100a07100ca60048001e901701030007256041d56900b20004011170100b01c140c131100e0f8800008500d5000d0303800e06d0307814004141d109480440c40d110400000036409665040e074600c940c200015000240c0c158290034143c1940f11072555864079048c04000080024800c220081c003000a0095800c2c1070440c0110040d00700002012807001c0350240420718000b0054404c41e000d0384111801c00c181e9400181d40606480d03540c1401026100c00740c410b080d450f008012940b0048181c603030000102c0c007400d02e295107005001900c1c051074050b00d1001c018003504080300a05120000b12035034840d400451400358041202c41034001d1500b0b02c00169143c800000074650380f4000c000e81514184040158065403290000c40e042000d4a04948006032680d0041c0c0e010750b01401c0c2c3e04640b40c90500d0054a0074013690010300d1029203142480310400d980c2105200c01400d01d = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 213805314 1250 213804064 213804089
    0x109060b06031b13330516080903030f03010f03061401030213090f0803161b0816050a020a030c081504050d0e0a05100206160c0203030901051804060b0309011a0901 72
    0x8500d465007100d1025040000740390701d85c03c3c1d600c6140703901c070600548400300141c982c00d1440c0281070a4405104a02e503074000c0583c00010030002c50109005040c1010700581a00d00d00010804c0300300c0940c0c401d81001600c00ca02410610170305c00b08bc0306074010401188640ba03042c0d41140c0004000c01d022090820002d07840703000c16010040849144140c643d4804100d913100e040c070342c0800e00181c0741c0345140400140030440207602845031103001461150440c5119181030300b41c3d40710103003400000000780c3c2e162017040c01d04401070715011420001140110704400d1010f00b0b0103209401c1c50328441d1013001200e425400c0c080859804520720003180002c2c100f11084c80300d040302160540449a100d01d511052100d01c180040d5004601c103440390950b030b25800d0301000028410b55554100103000ba403d94418031480c2002d5018800400040d81022490b0b68071144210010f03040d03890340d4004000c5d4075000f00034000380100074000e0412104001104004240b0303001c02180411b01c0c1403056a600004 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 213806564 1250 213805314 213805327
    0x9080615060f09090c0307180e0406020c120409090b0108030a091806050414090d02060412120204090c0e0f12060c030c090d110f100f08040201020c0a0303020109060b06031b 76
    0x2d4031044412925000c3c0c4550a645030104200310a500120b410a0109403200d440302070b40010229042c0c1524401c40c101d440c1070b2110341380c9100039040000069060702c5280b551344022103d81c80074000a2040b441c0100b07403261245070200d18400d0682c0a01c181744d1040c08000c440d0b5401580d16400e070f8068a015491280050308001c002d0a40d6500180d003292401d050000d250116450b035511480c1c40c01c04480104003116800c0703a07642d1040320080c000100b034200703512925206100501c03d4103803005000d4106611071412600f100c9020030000c005c41d803829a00001390424000307880900d681101d403000064065036071685c68402c01010340030351000c004001180d440301c401c15502042400b5004400b0080340d80392a030391030154000f6451207480200c0b071010581ca882e214004c180000c60303541d08112411010305940c4074002030030072415802040995002a00d032100d551004501070b07230010910500d00e080c4007044400c00c0703182078040c8804008001040c0c000292504600030380f40c2c07049a8078103 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 213807814 1250 213806564 213806587
    0x8070c0203010f0906020d1104030515060411040b1b0106050d0204020f130e0a0501051c020405281d19081c0203010b030402030c04050417090105120a050103030908061506 75
    0x3220309000c41000f840d110400c1305000107a40030386480180f154041140071540b0746070240341d0055200040c11b50380052484102480c07140030340b94000030040c0000c0385200700441c12251035007080d04a00c1c46454081802048599109103074840d0320708031402000110306040c00300c0c1100c5038005001c1d0045800146200124202c181280c7c0b81004145102120381c0d00c070003103200505400c0d686620000e05100c0089481d20741540c06180c01120001b00c0034410b840380d4240005850006c21031080c114000c0140e0034800003018420014803a041c500151260110b001c2403c4403844224440d8540e0001d607242c00540c3c0c402005c0103d25070071544860322116041248212603940d01000070440d8008800090620600c80140d405076100f1025200383c07454160a0200301ca80031200a0103420003640924000c2498400400300700c1c4040c5400d51030702d507101184c0ea508044c1614507003c0d2550b904010800d142e40180444082e049650181910341052001c0354800600790b11f005200d90000a103600010 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 213809064 1250 213807814 213807821
    0x605090106030213080607022a01120b030102090904060507020f061003142503060c1e110a050303040b040308061503010e070c150c081305060406020705070806040507051f08070c020301 81
    0x14016581180c00134601035070001d4440c0345403421000341654042802e8040030031030f09c00d038981000681d40d0368801c1100070400c0c400350001142864155500b002860440c3c2c4510030441c1c0700b580035140c0410203007800700c40249400d40100100740180c1250090003460140d001d0b000c42201d804c00c002c4505076850413503030b42c01c0601601400080c4400c0000c00e002d01c1c0119000182120700070081000b04102c0c1800681c5d11107e8056100c1c0d000b803411482c9004180140d00c0c1643c800481011642003030313230a58402d0300d0341d0f1041c0c800352010760001d010442010340c03040100750702203c00d403100d41e64525900606c21040c0410b024080d0301484101c0010f480c1c40c800c2c0032505c09107400c03070b2840b00d4800c512000c0000400c0d2028100b80001d4038000060b105c0d000d04000300351a80e030300100410080c0c0e0340d922007100940201780c0490302d90003a0b0720001280390041140c940074a002e4000f40c4880c1d8030300000c01168124280300c41c8540d6000f06041030b081134201d81810303406552828021803826441c40001d004 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 213810314 1250 213809064 213809069
    0x18010b06030f1f0f060905151204150e0f07122105070b0408031614070303020714010203091c0f080f060d14011a0d02090112050106180207030e01030605090106030213 73
    0x2540483c0300c00070f0030034004401141241c080b5190a1150398840051201c1c1952990041c0034811080298580300301004a005920500031800640c2196038040070f4000c0d01e5100c410680c0b641d0000c605412840000c2c070140b4014030518209090100305589c41c0011806404c10340324442e1800d9003084a420700030707801c487c002503002503500c0043c5007518003414550001c1d90136003050345680c0d004c442010701541401e00e180b80c08034001c2e0b0170b0403080e80c1c0480203548030081c1100e00d0004080c0c241880d120900180d03014148003005451070900b0440c40b1011007040d80541410041c50740d4807100040d40000d0728540144284061120f0755545401040c107216103100c00a004903550000c04461708170640c48000e01581020078108240c440508000858110300006135104040c240100503042c080c0e80f0491160340310380004100e42c1d035141d00030401e481071b42c40c20800742ba4000070241c080651000650703400e04024202040694140404182110414000c03101810b03130001380041148c040c100c0700c500 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 213811564 1250 213810314 213810361
    0xa0c210e0d0f0b0c0c010e0a05060a0b0f040204030501020a021b10080606070c030c3b04020a0f03050c1c0c060302090301140108030a0329010e0a090203070818010b06030f 75
    0x807500340f1401000b01e0b540441084d02865180101c7c2512100001c51105000368000006103603c0e00c8282103c4e00500d012075005038401070403606075403191074a0019000543c041d000050725165580c00103030030301c00c40c04007850103505100a0f21074981c0d6480b108010905d11807802a010303582e410040f07200d0f40700c2c400010f084500503080010070841000c0f040b005880140386501041c1089451070b85001e01d003607180c08035690358001940c0441c1400e4440390341c424002032000601c40e5427180c00074492146034200f40d48581050607644103504200c1040a00d4502e10342d405245080307141c07070b42c800c64801402460105600000c012040795000d4101c0040c0010300655000e041d60350b45003007a501d62107603450341c0c042030030440700d004107000602c0d03024070320031042e00d90a01e00c0c1808401100d030301290003905076028110700004a0307500d0b00361010318441c000a032101e480c9810b00d40c40c1b2448060030580c510310725a0505010701c06940300d03002a00e070024420420b110031078440012a000c0e070080005040e0 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 213812814 1250 213811564 213811583
    0x1805102309010902040e010c05030f0606070206040603060e130f170d0c0806100201060324020f1207030608030310051201090f08030406060807050a03080304170a0c210e0d0f 76
    0x3103010701c19400105803910860341003180414403030784203081e6400390070000d0110780180001114015441441a448130707006214514003070480e40041c40b26081600800b001035614a0140282460405070a41040031130b41120403000e101d86d034684601040c800c00a09c143c60074404a044c440d0020152400b042914800340721040607140024103082e02111124424201c503e02e9220031f9006124440590390403918003101900183c44d80c40b140f0b0310288851001e15400c126070800c2c43e090001038840981c1c410810945410150f174020b05032185a008891990070400a1100300400a0034480441e607040d5466214400c1ca4076105004021201010300480c0104001c44204034920005610440c45211704005c05602c0746040c0340c2d21826805411303044088614140041211003000c0c40e071240c41030914a00c0300c080306112a01d540c0050894501244044044d482000200b02580c00b06401c3d111a2142004031281c0040c2034441c3c444109006146400780c140074440461100a5499000640b10 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 213814064 1250 213812814 213812821
    0xc0f06050f041716140a090603020f060708120f06010e03070b0306120c0904050c01090b1606090503091e0a080118080a140f07060c030509101503021507030318051023 73
    0x110400e03c0e401e660144a1b849551020441500714070078542600d0300030707000c03005030300b003040a2007041e51203d0400c1c0c0b80a801030003089201981c0c3c888503449044101100656070400c0300c005042c01c2c500c0724050307200307410501040c00424460307000e40740d201504503091440780802c90311050410007008011a08602d111042006011000400038100c20003031b0703184003e95560b210013481c41c0c080d02d10446400384048000c000401c00581208a02e0f50058094070b140508542c000f0782d08044802450100f400301c0d9200f8082450b0189415000384004c80c000d0109203070495828075000301d00e0f4001056244081010325a0512685680c1c0d140f1480ca0321140d980e0306a1100c0b5207454014100403641c803410401e110b10031510a00a03d802518540c0003464200c0d0344440b400040c105400821600385205600000541e031030041c103a0521030304034020343c6d80d01e5a60500130305071803200105031303180584001810000781c00040e82e01c100c0f98460000248200d0340882003022280b031041c4010205aa540c1423 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 213815314 1250 213814064 213814079
    0x513061a030a0b071119020103050c1207030603021302120c070c0e07020f0c04060e190f020d020304020a05030a0503041a090a03110a0608070c080310030f0c0f06050f041716 76
    0x9181c0125601e40700c4114880300100c100707581d124162440e142101101000e01b0040d40250021500302c00c111000743c2c10021010060180b08030226172400010b40c0f961402c00950409610380c4000700051201980742005c07655050040d03040151003130304100000240d078000d000b0303100490380c003520240a510101b8106030701300a42c3e0704030382003404403617005101c588081882c152241404071002006040b2040d502c860620340d2014001d038003042c400e6240c0000781c2151071988024141d4240c62200184c03a400d09006024210160750030403030096200c414000c01144002003540c00300e861078000000c501e9001e2001c14818095190100c0d0400140e00000c42081820540c1c1c00c1c04003016038240700740c1036a45404943c0c0083c10303100e2a004c10700303a10f1050b0204507664003c41c1c1c014002102500d2841c1d8a944610000384a4281900c00500300c0900307016440700c2124080040c1214540542418420480105203121754420703034481e03280404141c0003548051240800d92861a14286c454aa40300310 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 213816564 1250 213815314 213815333
    0x1506070c030c06020a0c090f06180c11030405061210080a0f060e0c010e011107030b0403030b120105010b120402180703060807050603041707030c06110703120513061a030a 75
    0x803a81c0b107096401c0440c42c00c0c40000c14102490704641701c80310300751070426068000e14850010200b11921003101240b5400082c1d04090351107280b02c40020701e500084001010080810101607503500100b104101c0c40d6281e4080d66094006580c540d0265103882c07690604044082c1d10403099400741c01310000500085061075928680a41014010300346a200c1c1c01c1e0b102c80031001e9040c0410000a02c21185501c80c40345640032030001c0b4111200d040d101d86441c0c4c10b40f20215422000647c03244203000b82418040700e4038420941403c024000d40d4100351403002680503441c42211044101d00c000f900b5551540f0248145229a8108980b64140741400030040d02c3c00c1d0007100003a2151420000d400d08040c0226449950408007000040319400b0081b8950784c00b000e8107408000403540d00b500824001d00c5244c0742541210000c1c0c0d0b03510900d00c2c000d491081d00740c0c46100c05500e1300c020048031018119103119580c1d80101c00194109a1502c1d40180241c5a03144607014443c45c03010404100c213070305 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 213817814 1250 213816564 213816569
    0x5090c0307170127050402030d1206080601090c0201060501020a0b15040207021305040311071412030f0f0904050f060f09072105010e0f06210102040531231506070c 72
    0x21a80d0301d6130a413079400e190a45409480c000e4142c0d01c0311004038407e07031049080000d910419140840c500c0c0d0740300d072040d1034810282c02241c0c41d0360382d41c60701031034107902480381e40c00034582070014040d2000203464403d00440000c248404444841a401d0784640d02e5030b0440c0c0200c1e60042807443d40f40d00a90740b64009100c200c408a000c07400800c00303140031000006180c000c4420b1030b401002c04641c0d01007485950102c41c0340c1891a0310003070080c01e00b004120800380090318241e0042507201c046820400c4182d91001d010080c1c0c007003685048c00450307101c8030300c5c2e8402401c003a1215040354854050460740c04901090f0046800900171502c2040142ca0f040b085c100e5505002284454464299043d4038a0b429030380140d11184041c030340380034180202c000100150280c4001400d10f650b801c0444d6540c02c540820940c5040700c040c0c106111030203900d0000000c03d2002082160f194000c55140c2c03240340124018a20380c0f1090005030300050610048010004050b120b141c8603001403400c980400120b0 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 213819064 1250 213817814 213817859
    0x302031905090108150607060b03030c120309210702280902180301050c0702090a060515040303120603050d030b030703080c030c07090b130902030f0105070503060f0a05090c03071701 80
    0x4d00410301d80303074042070a00001d11004201a151002c076550f02802403078804621074240c002800203810b044003c2c8140c10811082908940d501d15000e01c1e085e0070302d40329213464101d48150078050100022100d0503141e4482c4d050b0b0380c0c626819103d000c07600c0301050102030403d400c0160b94004c502850f85401400301c448110740c0700100000f01000b00350036500221501e640c9550180b203060302510b030550030690040c0300f60b040040c0c1103450300041021181110030b041850107001a0410070954449d901c035001101446081020a0659407503545441c801c0e0412030030507407504080a5141e0302808400700560303000451541d20070f01c800f402d0303841c1d400c404440101d81c00782a50000705c24681d030180381001c850041400580c00e900c1e07569003004080c482c20587c0c05104000c007540410300f0910440c0d00651450300c0d8907440e450801c0400603052001060740703015448040003000380d034036405907064005041c01c01d600d80f240d543c0401103541c1c00e038a14000100d26064000041c0c111024403100c220750f0302e80d = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 213820314 1250 213819064 213819077
    0x80705010e0607140d140705030a0305040c03053c07051003021c0911190902030a09050307030215011509030b06190303210605030307240606080105030d02060106090603050403020319050901 83
    0x1b01d100f260b0b864001d506010b0b00c9900b0820103010020321950000d58054030a000441e82c0315200e07201c091030480c504c010580e108070540b00c5001c0c0c1070510000140a80c1c0101041d0b51101242e40040343c130b500040c803405000302c600b94400c05440b0f0107901900d500c2d05901000c141010502c0d41004040d140f410b44c19030b480000003d030249242405581540000d066000004890f03180400c004020750006100721102a540d0b880c400002c1c000740002d1807583d001345e0040800a82d0f0210000713420741c040e0b001200d4107039000300c0c50f003010340c0049100d421250051007145c09561064081494000801010000b052000b1404020160002d107400b940042c2401144030090040d202c4104441d081d0085e180e040d131040c07050304001090140c0c171041c00715400360788442c042e9040c82c1c4801903a4007034000c4ea0101d21502c00500150408215000c83d0900c28401442954940301014200388a140134100400d52902c0000301031500800071104650072840c0c072540488941d403c010925004900d030030740001d40 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 213821564 1250 213820314 213820337
    0x402041b0c06060f080a1709040501030b06040c0305010510261f050a0513090614090f1b0f0108040507030b04080a020c01031b1812051f0501080705010e0607140d 71
    0x4d021440c0360560f44100010601c15170540c484080c42c0c000039969138400b400811842c54680c503103004060003148259a80c030312a050042c100019681e407002d50208061030100104610340d10b6003620000454141401500f41e10301d2088203424240d41e0448c045010841421300080940032010b0b10240b0195108a140441c0c4620402582c1c42151040e60f501460500c9603060303051181e8070a6010a121f0000014404500c84031070991280894005215800c1190203880300c0030f040c0130840c14540030030114620001104009004400d0000e030070740c100603202000804100f8100310f030703401658110070354032110720700780c5004000e41c0d02501e00540103010750b5801c540e4950003805580c060031441051840c110f1090030088904140241c2c119200c9000f00000164201c001341d09245524041c001400c0004005001803132100e28a0500300042d614110041040c14404524001520000d00e0491005c54010000a106000e030581c0540a440388002c045c00c02c0b4400600b503060010544c4400c001d100 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 213822814 1250 213821564 213821579
    0x4030b04021e0d140115080706021002030f0406090804090908071e03082202190e06121203040f021201050414160b0f0403050d050406181d0402041b0c0606 68
    0xc081d850043e80211040001000140ea01d11400000030080000000e81d0541e03c03040c01d0302d505099021507202d404c5000c043c405c050b411f00203c104603d0a040640c61030411220694041c0d00050014103c0c56039500600200012081182c0041500c03070010b00c4810030303038102140b03950320845048509060140c0b8028494014a07942100703a50944c4603144140c0d91880602440e0f05c84030703131540d1030050400740c0310016503962002c08030549800210054050610f80b030130040250151890b84129003481448400c0d01e00080d890004411400d41d03142c607901d0700d160013500c12441d0301c0029400f0403222803c1c4291441540000d00c02c5000302012000c0b02c030020909078032a00f10410203e03180c00030100a0100c850050001c06962803000c09aa151a071f0340d488560a1500510b03500c0700256000a0070008036911014590003c2c1101c81e11405d40740c0b41507a000881c2001640014540b11014005400c3d07580f90362000b040100664548054603004400c0144654051002203a83e10b14040340401d004 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 213824064 1250 213822814 213822859
    0xb041b1202010c230d091401080c07030f12050a020316180905060303040b03070504150201060605070b04030e0a060e120610030b1f0b030103030e030a15020f0f04030b0402 75
    0x90350181c541582c0380d0b4840e00e0f0ba0100c200201e284c0103084004141e5001228004c0044040b22801c0d643e40282c0181440100b100030789920b44514104260364007440715440c80f10b0100c4a0180c0d150a10703804090400a0555581c00e4013080403a0003844d240030450b00b415642c00030340c0302d10392140c0703e80740030741c120075090354600070007002c0c20b000244c003120500100300c2d01e511064005d00e004003200c0c101039855844001300e910844110000600200381003040c0d1b044038002d0b41403280d0600085c40041c1c100600201070307000340240508020801000f040616018001202140300c3c09014803505a0302c1d03440141041e00f049001e54012080c05a11107c60100814030900034448480c1540c2c0030b52079619104039a06024252102100079040884110100308100c00000e060f0403030160f880398903604010b00f6820f0499047d50081d0400401c83c00042c200c0780f03240d403d4001d18500140c8a1a1030a466083c0d40580c059140054400142c040103210380581e1152086108403803484001c1e502c104105440e = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 213825314 1250 213824064 213824099
    0x204050108160e120f0a08221d0c1c02190305151216120201080606130513020408100506150c0c040c05071a0a0e19060e0a0b041b 57
    0x10303034543c00da1000c0380b5041480c2150000e2043c00c031003015000044c403c0c00e00d2610b40e402c449224001032405074806646101d5030355841c2c2c419840440501d03240d420000103104400f0755200395100380c001107403004144180c40c80340f00d10802040980c22010440802580b0000320b070b0021503808105c101c0694424011980700300b11851042a04041260a200e0300c04141c070603442990146910316555040800131050041810104110104400d4000980010400f602d214000d200130070007807041c550174240b101c045440070740e804024004050b038058001d00a50f0891a00703402044100d8100c040b16420550040d881113491608034440c8001c1407150b80b28018000c0c00c1da800c00d41e08c003034040c981780c0d104c11002a400c3c20401d18000b450395131400d070540e403a40148072115031101800044805da100e62801298184010301100b038075105007402000740c3c020010545a142c201100039850305200d1100f0541d0311010040c020306061419895036524840001e41c00c0d403005100245034180b11201022 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 213826564 1250 213825314 213825317
    0x10c2904060b0609150304020123130b120711031c020c0f070509220c06020a03030c021b060705070306060806011502010b01051b2a0405060d02011709100c03020405010816 75
    0x1145d00d410500c4000e1904020003d906122881124400100c8601d5000001c50380140c685961400341e580c0750310407055640c00003400700b04280144a05010540d6000340c00201074140070400c0131040780d104d46144603c0100742515030008007224107440140d005443c0c000b104605880071344020902c010f075148628411141e011441c1c0003c03e5815440d42e046040340c000598406042300000c0d102c0c0aa0001140c0c40400181d2001c40100240b47e410311540480040a00c060202602c5600b8590601d4804034031003031162200080490030000200003030002941c2c800c03801c0c84030a60340c890380c5455401c02d106e1002c0281180003060a414030600c146011100161501d80c181b0380b0070704200c21005000e40117000d6074807590100c86c100030350402c440b41202c0145002d40c050398000009010a6400c05011140565651009440140e800404ea207851502ea020100c100e550781c9400036181098441c2c0c10400e86182804440d007141d41500208280c2e01c0a8881c01420340725116000c0e100c00c56599100c0 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 213827814 1250 213826564 213826579
    0xa020f1c08030a0b030307120e040b060a121409070806010902031918050109122a0605130f031707081b0906091c050c03030307020a02010c2904060b0609 67
    0x1410140181d41c200d1a0f9100010380a03160708040380c51980003170000d840c0000510307440241d6650180742c1500031281036030140102960a03000c5450350284454120a004050441100d440c8469002440c240700f1600804040d04200c032100b41c640409010300403090051307100100350b800090003124044e00640d01100c10194803907920390300400303d0500c2d81c0d480c00764103600317134000c520301340200ea2900b405617401e20000382d030460f4090461a2014201903245d00701c5480c07800da00f1040f2020f041200d40002d404101c036030347e041e400f900040c0201ca005043c140440f40f03980038554090b0002e0700210419440b0f5040b071715455429101c0c100700712030410007a80100d046030000100302000c0d044c03008018080e0b40c10080084001400b0607185da00b0b030510030784440301d06814000100440440080306a02540c598244610020744581c0c403140013034140308100801104010400394120ba442d1007548141d41c0241512100c00113611055405440c81d50926214210925003241101d005420003040300 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 213829064 1250 213827814 213827869
    0x30b07020313052115182407170a050103050d03020c0c010c05010608032b020304021e030a0f030c02030114010533041806060903030801090203090f030c0a020f 70
    0x2104034095401c10181c03a40040b0041c160b100400c800b41040f400d11542e15160301d4400d8806d04001000f101d01100355100342c49a10310b074000004261218510026142d50340e546252090360902c1200c03031000d4464403100d00304003552803a0360282381a2440b80003910800b0620800440690103411002c0409804c4400841c0c9152b00989200302080d119030000f0a956a407075031070fa82036410040d8404c0344441c003408481140314005c1d119480300e0302c0307240c01141181015004940580f501000c1e02c00d603007002c43d040703588541e41000400744103607011603415201d03a018580100302080d0304004074080e60800d040c040204440a80d180d050311009044c14139904005800708413141140320301c0754040405610184417909080c4000c001412101e02e04c00784501c0301c2041c20045441a0340501c04205881c4824400030342d100c0c440c89d045030300d074400143c0c41c3e443d071910321814101c0800181c00c480c840002d411004140100390f506905000721900303244044a072042c0700e5210304210061140d0500c88104 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 213830314 1250 213829064 213829069
    0x60605031009180b1f05030102190f030b03011e0b0904031d01030209090403021e0c0d230709060f0602071805070c0c030825240b0604090204030b0702031305 69
    0x18052600d400c1d1640d075103403070140c03108100d80400313481d0f22420940705c2821550b00600000f044e4002c1006400031480c0202e00d031284c030060010380c0e249a040008a409000f007051281d0402000c1400082c020454800d07110540e0740b402a08003c0b00490b1802d058080810707181010910b40704076055120082c0e14160001030b0b00e01803101c6000e1606241d4280140c00140d120302a4540c451031080e0020081901d401c402c101402c800b030084140c0b81c0d0f01c80e00e081e802d9500d6030400064103947c0710f078580d4103080c00d04050f03d00e00c0410321100c22040c8502100010240404d0700420210782541462900c010384a81f0100d0f1101381c40d0150aa100558882c43e800b14076285d80656804002460103e01000c442d5507050b408040030b50081e50707401c00124060004500b42c030070001c00300d0000742207680582e04030743e1036a03c0d510030742c12907480484503007a0403c902140780d00041210b1400030300455030340d611001240000d400a001c19076103042c0d0140000c5c0c290303000000315140d500c601c10003c200e05150008 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 213831564 1250 213830314 213830321
    0x1090b18100c0b01140103050610020a0807020604081b011206050d110a05131a040b030d110c1201090c1a0403060e010605100f020d0509060a050d020405031609060605031009 76
    0x5001c8100301000c200140400d450350321a9010300240b0600b000410100300006098600c09824984100300703041c00348401a0b00082d9820f40140d209401540b510542e0001645500540d841608070307000d107104001c1d041030941e84862003504240c81e40c006100444841c2001c880103806055080480c4d6407039030010a14400341d02948180040c0403240c1d031078545000c103500c46213402d90304898070b0f03d074a00110f060175001c883c19050311050342d04000d4600340d100082d41d250400c0d062241807290030100000407080512080c40c5415000e44031201a03640421020b000384914003099403d050705c820702190040511400c00103070400c890039581802d0a5407a91001001d06001c500300d00c0d940c881e0006031681729406c2d05030301107029494550f403103990340c400a0704001c5050f40c040c0800c481004051125074441c030076120a03d2851500e5a2582c0600390440020711a43d00100e0349032003501d20451000c3c10100a9a0030359000041c01e20007596140c009aa0900080d04d0701d40c0d80070890441440201d49950 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 213832814 1250 213831564 213831589
    0x30912090b0a11010204050402070c0338060112061d0906101a0c060117011508031602211e030703050405060706090b1503010606020f03040504051e0a020901090b18 72
    0x80005283c0380e0f447d000074080381c0c0403140454080d2041d0100304284004840f0a2214018060401c0e074640240303560500e00c81048840f040300c802c24132003c9405644102d103d45d000503000c54041103c1c9446406c44e000300d04241c00c0c540d13004822400010445107003c00c115008010b5050005403160801108400500d60080c0c0308089610a0194150410003086580c0c020702c400c4ca0a54003220300704a200d42540c007100e00001540c41865020842418000100c0d0a04005481c038285040b5080c40040c1c11064003c104407401c0c1e00034404c0310700c2c1507c041a07880c00985003084080035005001e80710341c0c0340c0c05080b0025022850902c01000182060f1004110080c892440020038402d07035038800d25180c409035a45501410781070009012401c09125400242800f80020b100c410308410031580d03607106901495005584410106541c0c801910900144050140181205107001042e1600a40200306100c0c0045c030740c82000a00f0f442c1c90011903c94078508502c0001c809400310a202d6001c0440 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 213834064 1250 213832814 213832847
    0x5040c0921022209030f020307020a0303030209040e010515012007090504151d01050106020a0f020f06160b060103050f04030c03110c030703050304080105010501090b2b0c030912090b0a 81
    0x2a41c11039010f40488907001c020524881d00040c4501d150400815244810320205e095510400800d001359581c00d480c58101e80d890305c1e025030398a1242020030701070509040d0a511640c00d0a003800080645480101e04245080ea907002901720224258440807403141002d01c42608080c00c02e2041e4015a00410b40c000c0c0610700036025502c50300e840310201d51481041c7c100c840f44036540b10b00106002e009450040003a44010329402c9081d4403041d00380c11110400a00c18000d030206081d098440e0000d94100c040d071100e000d07401e02514288100b06020403520980000c1c41d240004114048491b00f81c0d0007650541d8580000020542d82900c480301c034001e401060744910903e149059a0801491010303510071005180c0300c6162817026801d40d030040e0812030502115000501c401c005041c25107010000300601d158042c0c1ea5007400d030000342864141050303e00c0c05c00d0480c2f01e64a8141d0081d0b4080c511480c034403c41401c821348119001881c1d0f00900300005010001c5030349441c85141c000c0c6214018 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 213835314 1250 213834064 213834079
    0x4020406050d0503032e05010302070f0b18060c031303030c11120403030e0306010501050a0c08092706030a0b06010309020a0902030703050105090705072d051605040c092102 76
    0x101c0d00020502800068111030755403000040101800c00140711000e007071030105189542e214a180810400b0603d40200d5040640c041500400e1006c4e02c808001d1054100c0c04120711803d146035102000102500c65020611a10012800040c40d08048900c603084844c0c01074542d00e40361b078040b0080e05207005260100880c1e041c210103a5a0107000740c441490480d80841d80d600e26601d07014200c00070140009100b0b41054004201a0b60090b088035800d142c071b40750186a00300c083c9000c080a01520b080550003120380e01d0900100000f90702c4036005c004403020f01602035a0f83d0b50405039102e40d100401024000802c010881319400390b04200140b41c401400c0800749074540504108903007044030803c000a48036001006a0706004c3c4507603402400700e207000f5280503002d0b1504104000c010401079015000040fa02c00c1c2503050203d4640c2881d03009058034140c18000c50108000400d501440b4810b07850b02e650302c0d000303e00610b194400c942d0400c5107810303d20fa0030485c401c2d88120501d001e9070403a01 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 213836564 1250 213835314 213835319
    0x20f150105310f2004031407090207111e0a0e060a03060e061510050703120603050f1006060306050f0603070e03030a020601060f080c03060d14010204060804110f0901030b04020406 79
    0x3a01d080310b1a030a800b031000041c003003861aa070310040c0da408a164030300340d1010380c114224030b07861070040758152600011001d031088201c0c19102d1a000d5907500490035a0f201080c10307800c009c891042a0340b1910300311884c03d4144800040c030441041c042440991003201c3d410100001c0c260580450fa0111008104003545a9242c48110981302042c01039072154004404200c1c06442480c4c01a260b82010b07903c440b5000d080f410042c00c00d00c00d50301c015040c0813003162040b119800c01c0c2c0100300074551090a0710682c0d40555841d40c0c1d648180440149014280314002c2011441781c40b03141c003154001041010690016828481030f0781c009403080342004030740707128014203440c10801000a103815038001c0a06600d42200100403076603410128040141160074002402c16000c05d0703a03040403045a245110425901e40391510b010301c80b1000c02c2a500100700003c0c0250402d0352180720303d02592a55050703446940400c40c8043c1b030140700b1075200c078a5030014000302d12004809580584080c8c030000c0c240c1e4 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 213837814 1250 213836564 213836629
    0xc030e0303040909020a090c120b150c1b01020d0207050d06090c030b010315090809040c0e031c0e0307050a06080a2301090f06030b130203070f1401020f150105 70
    0x602070f401540426844401d541c08500300302c1c80000041c807481c01c04101440f10750800400b03001c00589441401c544a80c2c5c0003905036607108904491202c4030012a6031240c00d81005512f500c0c81c640328401480c6000200140d5500125046585070381a03800740103003500340401c01403003003d040415501540d8810b807900029818400d048003860142e0358810640d891850300c004a058160300d490500d504003c002070008440c1d10030b0700c1c07492100b140c0204505031401012900b502d000198540d051003003080d148a07800340100400b207800c2c00c50b5500390001000c082810795600d202e118040d00481e080c90104841d5100350031454100c03031021380118104944160480c0610002907a4110040502004020341c0a9902c04c4051801ba41d0809102b8280303581c445081d2044020445000e030001601c107102150303414420f040c0540f900001418505483d1900040380c00041080d00780503109403042d403002d1030320020b0709c00c20780b00300b142050079242c0c01d080c140b0002001e400310541001d03c58000c0c0c82c0800 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 213839064 1250 213837814 213837817
    0xf020703031b020304060c0807032105010503011103010305030a140d0905060118140408030c0c010e1e060906060d08040512010507080a1406041107021509010306090612030c030e0303 80
    0x2400390760007141d00e8038560415181841d1800480040d540100010403140350007110480da8030b6007003c0320720f4903041d150600743c84252409031200c10200500f4a16003c428442e8031040c185d4109030003c000c400a01030340295188420301001d00701c0d50003400503191581c41181d00c90341c121100f039415800c00c00f502c10ba88003500c088030401c851980000303006102d803003254119440d1204550105020b081130303080d03286440c00400b0f0b101034404000000011145140c800c1154540f8a00c4002013120b0010301d074a8549440041c022204100f842004070843c0100025000c0e000308500000b820254070784204000b503088011004881c0c50a0134080007a190761074403020180071480d0000071a80f4680048002d080d400001e0802c92032518041007a0704111005484030340c00f0340240c40019500f501040ca10000b0701828a0080d070114200800c14441c00781c01c0058605001e0a032000d0008a480348038442c1540c00b54001c0905080b1900740081c0401e105214507001e4500030705110301c101c525100031a007103 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 213840314 1250 213839064 213839077
    0xd240e0f0601031110051801021e06090c060a091418091b0604080a02040b2806020d030603020d0f060e01060b0403050c09010506030c0315032d060108060c0c010f02 72
    0x5802000c01003003884151258043d02c4403040f21719541c2c01e9403555019015004048000440c1404011454400d90007080f80741300521010620180319440101d0003030340d803101218044007a0094000d20341c100d080010940384074000d01d88414940c6800c01d002000304210071300d8119402080c0c45030000c94243c00713400460280c0c44480140c04156503144840e9020003040f50640e010f000c003000108030014001c00c081c12100d50480e00414822402800034226000405900c541346200350851030300690701c0d4207000c00702d0b60701d5000e640b01207941c44c000790102c030a1072001070b42010023130758010000b502030300300c50000303900c50325001803052445c0300780351308643c0d40d07400c103080e5403600040520500404020032031141100300c821038231a60521000c112140005811000349000100103ea0302001c441c000e194107003c040d04880b001080b0b5a00320006010240010580c84440c45c0511070581d0003054803810303141020700404a585851104030352681c811600c01c1103035540e0780d01d01d04d1090b4941c0014000c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 213841564 1250 213840314 213840343
    0xb0f091228020907021522061107120302030c0a081e010e071b05100905070b1206010306090b010c03050c0102040504060803070c0819080702010e040213080c0d240e 72
    0x70100988140284820090320240c02d41d405420440085102c01103003d9102403113044d020341e00c8100b4207074054001200000140203030704000811a09003081c2c0050b0606900030031070101d041d2035181c410780891005072440d60034264100150807070a4003401865401440c901c0340f0600d69150202c0c3d0000c400703000c3c7c0040c0400c5011138180040c49522141c0401c603076100c0c1840083c080c40c0381d41d400b03558407076003554005519103039401d4105108c02800075100a0002d0000d65684000d02600b00381e04c04011900c1034046443c211303002c60b480c00c29104000c0c1003d010f07115482c000002d038070107482c00c0e00090074014080d0340030400800c4c1e68030707503000b424020700780700e40150b454200380d10380203100a10035001582d41ea80210200c070301310301508040c18550b503049220241e4410480c00100d40585608418942140c00083c9010074404000b942c00101e841c1307a0207440341140070404200d81454410350150884c0c00404007030f08908071102040b0b510103448032002500302e1040100c81e0401003d85007454 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 213842814 1250 213841564 213841633
    0x7140a03080c06070306090c0503151206040809010305010909030e040b06090d141b010f0503130605330609061b01060b130806190f06091b090b0f0912 66
    0x54035501801b8600281c5044a4248601c0c0c41c00c1c20010710034000200f0320513582c0510504000c140d1a2510840f00000082e0b098403031a10b00343c02c00071055403001e8045030000e4540800040e40c140d1074494000219030668a184600d4245c40c2080040e080200615034054000c03c4500c40715601ca0240f50201881100c00d009414401110301c3c0c10700c0741c000700b0224540d1075502400300d0b0703030307030100142d1013003500c03400e005860351a0081c80740c848240070140105064544130078840320074800c004c14500c07840c0c8046400d60051100040c1c0c020460301d0301d0410303000502880510020300d0100e02034542c0a00001c482403991005010003402d4030840c0e80301c2042c105000075040c091031142404c0402800c00f5800401c19802c10071980440c0d21407245100d024030341d494100203405903194020300c0040c418001c0c2844180c0c0920b4488216030410082400400c0760640700080d0408404151920040c20041e041e0a00d4004030900074107941404090b41140107201d0b460905450705102c203001e4100c00c11841 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 213844064 1250 213842814 213842821
    0xf0301061706060a03020913030e030703060501080d1106060f01020f0d0e1e010801050105220305031b010b0604050402090d0602040915060c0f0303020a0903150906050601080907140a03080c06 84
    0x3824110003524040c0a061352107001e20240e01c41d07041490b0411101c0c80300e14140f40d040d0804940c1c810b004410a0740c14040c1d21000803d001450704180d06032030100083c0c5846419031b182c25100c04004819480842e042407000980920784804040341007527060040c0c42c1c03407014502c7e28034201101c10f09a00081503551189600138188040541e803e408400c81c0303210390320b1485001030300543c414403405040000c0041c03068088180b070111086103050100249100342c4e01d0f07140040e06e94024159404482600103240031074503105000d00d9440800150604d403405003810144400fa40c05000020703001180c00780b18100151703240c8020401000c003500001400070b075410340b02e680c1c01c1c1c607903020104000c6c4001010010400080c0c1e60400540d01d4280103a4170700e041d00050701c408d0496400540110320004030414006440d8000c0c035215449580104642d40d281c0e401034130600c50645100d1003990240c074040c00a040103c04c00da1000c600184107520b03190f901ea440840e280d1101260040300d40011050 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 213845314 1250 213844064 213844109
    0x10e032506020708030403120903080d05010501180e04110301021c0b0102010f05010632211e010303080705250204050723031503010212090d021f02090f030106 70
    0x2444080c101610181c400f041c64102080e950340240d000244c60b0400150011502070b000d104418000c0d540300048070307141c040d00568000108030911580f40070480c4240e422550201c2c5034581800c0d102801500101525640c64a2803e140070b50311158156500f04890480c000c1c0c154035801200100a10100d45450884002030a541c00003010791421820100103104007608050230386135103c95490000e051840c0c0c03100707022085c00902e02540c107003500064409501840065030411440030031484040c1600d07441100c03404001c1608880040324403000061001901c1110f100360804160b25020b420079010f00c0140301e1180c1005000c1c1303101c9111308440c000b1420a40186640441c260804040a11318840300001c0305004140c614450740c8c0003c0060101490034481600d52003000c1c008544070400c1c6c60b6410100c1c84161078855451003142c0d01d0101080c400211030648200e0011144001d80d0003c00200103500b1060415a000300e02d4000f00c81c41c0d46003403003450b006107070b03001d1b80175103078514030341e0 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 213846564 1250 213845314 213845383
    0x72402070c080c10050a080a0609020a0522060203070b07090305060112020102101e020d090c12021e010e012a05030301150309170f0403080d020d06080102030402010f0e010e03 77
    0x1d015028031510ba8004c10110b0300001a640c41c40c5090910006946e500801c850040519070840190a44080b50081009920a0151003070924484d20350480c2c2042c1000380004200b03d22648005a108010300800513481c5410160880e0341e9040105019449176510360070404260050814401c40012070001c3d903904108036440388070b5a0001300100700d141c5498400e5000045428085070ba00020690105e02c042e5011500303060302300088020f00e60301c803a01c00030000b0100310244d10601d0740462100c803005091a60b488504016182c49a6800c01c0200555000d0740c1c00d030406500c042d44219000c043c1c0d40e02c40032001c1c1720344690701442c0d4940c1000c0038042c9441143c40d584080600d010350410000d550f100340c8a614424010795aa2110246101224244180c0d0001041c210000c2190914105680c01411203500102d0381880342c00d8503010040d0803800200d40190015216040041505000301102c201801040c900140b101001c900404e00d42204d0f403598003011141c105402d22036281160 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 213847814 1250 213846564 213846583
    0x607151d030a1d0111060f09100509030301141005031302040603051e0d0c0305030c2d0a0f031a0f04060504090305040f0501020a0305030a0c180602160509010803072402070c08 77
    0x3e000c0401c00000c01a40c2d0346c0d0000030420346080c84640d0200d44903032001c200b000000034900030b013400a031414500017501c0e50000c0c441e050b10a07444038207604180c90300c288000c0c0c01d160190b0307440341140d40f9801c000059680800050b60000d80c0c8460100110b0310a00810401c10014164a03e1340410a00c40c103180607450001001005005004980029408821682c0003881c03031103499111000c1662240400b500618116115030006500030404909413001d016500d207180c031108604031214909038152007440e518000300307030700f00c230303c1500545000d860141580c4405003000070902e8640c00450b0440d1403005090f404603002140810500190b0b44e43c12020305028409005908c940760380240c268013001d07104407900c9032176540c07440440e072082071802c003807034a415180030700c0541d5854065160ba4031501903425140640101040078242a181c0714120b80d81f00300110b16003001900c034001baa60074401c1b00140380490300029520a2042d0000c2d01d0701c1802084101419460810420b20700950310 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 213848920 1106 213847814 213847817
    0x1110020607030f050c0307111c0e0405010503030c0604030c05160609080f010e0d2f0706021e0c090405101103010906050607151d030a1d01 61
    0x60824015020340d1400c01c020039410f1100c0040d10b00894102250003c10808100a18451884000700c0000c072401e0340e008407180070144440c40c0b08038524200107110b071003d065062800340b00715401000700310000c62901581400d41a169100100068148282d031a8601c2c14494140000314107400500000c0300c02c0c9464003c0540317190b207d800342c2d1103548180750100c16a17050501ca1082d10782c181c0c070018a044040000102d864241003000c00c04062604c110001d003c07101b4800b00c200e45540a009064010b0a1a1000707103003c042d13600309045001d201d031070400a15408241c100c1a0001a142d0013103550340d90a0061403c50141600414140b506800e540741d001c6100107581030720181360f42030151550311303402c01140d03001d401d0010340400c0460546220100b84c592020307003120f01c201416414006840d05a0381190071a510010200368144000c3e0039001021010b070280c81000d = true := by decide +kernel

theorem cover : BRFrame.Cov 213669064 213848920 := by
  have h0 := BRFrame.cov_init 213669064
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213669064 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213669064 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213669064 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213669064 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213669064 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213669064 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213669064 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213669064 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213669064 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213669064 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213669064 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213669064 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213669064 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213669064 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213669064 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213669064 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213669064 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213669064 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213669064 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213669064 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213669064 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213669064 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213669064 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213669064 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213669064 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213669064 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213669064 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213669064 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213669064 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213669064 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213669064 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213669064 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213669064 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213669064 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213669064 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213669064 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213669064 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213669064 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213669064 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213669064 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213669064 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213669064 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213669064 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213669064 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213669064 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213669064 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213669064 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213669064 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213669064 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213669064 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213669064 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213669064 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213669064 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213669064 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213669064 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213669064 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213669064 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213669064 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213669064 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213669064 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213669064 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213669064 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213669064 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213669064 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213669064 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213669064 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213669064 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213669064 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213669064 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213669064 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213669064 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213669064 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213669064 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213669064 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213669064 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213669064 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213669064 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213669064 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213669064 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213669064 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213669064 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213669064 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213669064 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213669064 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213669064 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213669064 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213669064 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213669064 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213669064 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213669064 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213669064 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213669064 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213669064 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213669064 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213669064 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213669064 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213669064 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213669064 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213669064 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213669064 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213669064 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213669064 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213669064 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213669064 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213669064 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213669064 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213669064 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213669064 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213669064 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213669064 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213669064 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213669064 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213669064 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213669064 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213669064 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213669064 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213669064 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213669064 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213669064 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213669064 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213669064 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213669064 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213669064 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213669064 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213669064 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213669064 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213669064 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213669064 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213669064 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213669064 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213669064 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213669064 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213669064 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213669064 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213669064 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213669064 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213669064 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213669064 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213669064 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213669064 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213669064 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213669064 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213669064 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213669064 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 213669064 ≤ n) (h2 : n < 213848920) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
