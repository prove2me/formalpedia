-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3157
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:49:40.894389+00:00
-- url     : https://prove2.me/submissions/21389af5-2f17-42c2-9f2c-4faa1eb5dd95

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 567625899 ≤ n < 567805755 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 567627149 1250 567625899 567625913
    0x20d090b0708090a030308250c0303020d0f060b090411040821070507030602030f06040e060c1e040b0d05060d0c060302210a0f0e1b100c120203030906061203090904 72
    0x4207980014049010f00c0782e50303090003807d0110650f1070300702c0403a0304410104062030491101914108544540040c0c0c1c403290740c101d00a5101803101d60005d65644500c00e01c40c1c2950103010002c210b0701c00c40d161140007000c00c1104481c400c4080c000040000c11042081d05004030314105102186041c1d0782c8660301150154101d440b810704000c105024001c0040f0401c02694007035401401500340f00c40d9280d90341c4041c041107a2010b001e0500d140d20880006186d5184100148500d1884140c1e1070700d075010400342d20804c1e4003d078200d0100c006005c62004420641f510444c0d034044000c80c0c031206499610b40f1081c1a007082c030b0140a042680028800003403000041c15501049002c001c681707228a0316008080c010103820043c0f4440c0c40c2040018040b02c4400541e41441440c081c0030202d800c4810700030000796020b038503102c009005054010750081580d00240c0c1404842c1c50300030356501d1801005460405400806032841a507419050000401c000020344685810036203041c0c000752902d0400503 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 567628399 1250 567627149 567627157
    0x1611030607171b120709080d0504050d112b060e010b060a111501060309020301050f0601300c02030a0207060801030f061d030d02070312020403080307121b0305070f020d090b0708 78
    0x1c0c0c001081c135090111190307218540c4400c8483c1c5d0010b031003501d6084001203130280b20764403881e82d00c20324544207140801c264030080d0b00d85507401000d40d0080d50003160001100e280507441c0901303080d00070341008188040e42c010030a00008a2000304030f08480e9000150850096001620402c030000c415200200810084100e0f9030442d000e0b0f00c1320941e543c80005000d0040031604034029400d00000c20003400440044a0054005031541d40c82c0d11882d1058034041b42c1100602c800303000c001c5079180c002819900c2200d1049010358041c50380ca501400004c1d25111481c2e00403030801000c08010004a81036540101030f03d40d0111021407450701c2640c02040903d10300200b45258000000c00e0940030703030641c0c01000c200d442030722081c502401e004c4440049010b0740c44041c0000d0390030000070b1303019480b030b011011f01e000c840e210002c0c0c1d1030341043c028400c40b0050103201002c60b0f03588050005c1c6036041110b41400d0711140c8000c1944550507180146100401d108400c00ca00000c01c494080000c05001d403 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 567629649 1250 567628399 567628417
    0x30c0e1e0112120e010203090d030905090f1e070210020c0a051c0e03030903030a11070306021219020903100b0102030408014502090403051611030607171b 68
    0x18511558507510b100a4a011400381181d80211451404602c07034080c50280703141c204142c0142d07003004403801c02d005450f1141c8004804000d450b2902049030380c2c0f4901c946008a803da002e5401c58a00812610101c5159400200207034800b4010491401d500042218865180ca080561207003010401d080c5440b00088008106002c0d40310040c2a0300c0e40100e14408101d140c1d69950702480308982070644901c5400c150b160181c00420250300c82034000c040e0819120b00400865140b00e95039201c2030200e800510707030f540981c06094107012618144281d480c120180315182149005401c2c00000c2d51240d41614809485450300010f0740300340e00a000b03680c0107190403002030242c8202d008440e22903041c0c1601041164420070001202c1d41806400030300c591f0410720420881d03c1e015000c0142100380140114104041003080c030007003501c1170101d0344013540301ea049490303909801c0c1c04141c00c0c42c0c801041d11082040107400344e80c400da542480f190b008960300040800b01c1c0030520401242e84116221 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 567630899 1250 567629649 567629701
    0x61d030d020d0305010f0b1603200c040f11030f090106180501050a0f050307211211061518060411163f030b0301050702070915030c0e 59
    0x664003a5000301d140c0555403125601042681c1e283e1000d003804042c035002c0d00f000070006001080504004d83c0324000341030f019007460045804481601c0800d42d60341c94415085400000740071703040341407034082c102c0e6101404405000c02c8000f40001500c3d0300008180d0f1060890000c003044c0e00010079030007980502000c0c906030f51004104079042c2c02604013840b1f028041d014400c40007952041105206081d130344018007400c0c405151540070f05500d0141407918000e2112072480e90005030358085680d1903442140c903004a08000c114501c0e08007200104208c0e6140c2d900e00c2140043d65600c4c0d0314030001040c0303100b000095103403c00420028010401c0c40b0408400c0007554107112133b0a0702d02e40400c0b901c03030340c0c031602c5080e1010b1500e02d40e41070110740203400c4c4610640b006c16070031070001020004ce0035881c0008101c6608000282034031400c0e913580002d030708807120910220380d660040e0000f0b03601184540150a1541d51102c0c8041d01c64071880d0030303c0c02d500c4040340c55074000824005450402d00c0b0 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 567632149 1250 567630899 567630913
    0x1060612053d0504050c040e0105090408070831080f010b011e09050a171b09010302090403022416110318010504090504030e10020d0e060f070804090506010e19061d03 73
    0x111810151f005001d5944004080c100000750b6181c007a101e944502e9112080c14203140d2540c3e2005560703008410384850b81071f503402c400d840d00300d440100e046c24403c03a08000d01149240603201810400111102e10072030b41080c011014690b0087d2443c00b64902280003d100e01c040140c0881d81580a03400003680550092800101c001074064900d6464003840195806000450305003150410350050144d0407600b00c000410252a01200e17040e4041d02034010b40781c040402004150280b041140700321f2102c034031102030205d0350031251014007440c1c105003021100e20500c110100c1e668041d201c00240012400007104c004c5034441d000b0303140100700551082c000ea040c40d14002e0801e8030b00b80d005038029075040c1c170480303066880064100b00c40c9203143c03201c02c6040c0c4203038240081c0b903000c8980d410140400704028400990081d00400042514940004460030068001080940e07803400c01445031111414615084100d10007402c1118102d01f00384480b000441208071109400401031549406091 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 567633399 1250 567632149 567632161
    0x9150405010c02060c030f040f02010e03010f0f0608120d05070c0819030b0f090703240f050a050909061504060b0f120c0c0a0305160501060612053d050405 68
    0x14000e0800c4a04640030303944030344e45d03440c040f00d801c2c001210001421407220b004140400c0c004600d034030000e8018500101c03408a01c0e0082425504e088114901d1181c2c4c801002d04034101074030505000e0b1200c5c001a01c000d43c030541c083c08080c0039004c040710f03040da91440400c0406000d40381a4400711361010078241c59603000c28644030820820b60290001c20f0500b000c00c81c02e850814460307424424006c08500642c2c4402c5411001490184c800390000510b2000543e400003260859500405030020840f4080d802c10052000703078001c1d940000e018071000c5050000946000c00e926174415075910001000c28482c5d00040c0c090b05181d07100040e240b80010320b5443c540c0b130030002050301c21800881800d0341e485031039075103000d80b155040d24186500310b110100f0020340b080e4020402c513205501c26000ca101e042d11070a01f102c2c03003139000c2c50103d000000b50801352255170240c6644250492098003840f0002d0b50340924424aa01d441e8001c0020010602590308880c0159400303010050410400d034a024 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 567634649 1250 567633399 567633401
    0x122a100f030b04060b0706020706060506041e0b07050604030f0216173d0f0f0c021c081b0d0f02040815040c03030e0a090911090f0403080402090915040501 68
    0x103084000001c2e08084618849040c035000b904100c50040c114245400d000c0e4407420000c0d0801c40c0c1c05c54806844900002c2d131955040050005070540c114008a0302e4614544035100012907400b40c42d1840b0140032030004603002140740c580c404d405041000080740c803540101d00704505100f06c0d08007500203990105501c0c90f00f410302c4045100304000c0714640b0821202050803050b44c040c080d81204103841c41c50801400c1e4104e44801703011107400200384281e0850541c8265154102092035081c1c2e078100d07820410f0f03810400224940d14407080c521040f240c845000300031081c0280043e450400da0100e52021042100c01c441a60015010400c080b0a942d801c40703010b036009100e0b000740380c03050303080c40c030554014421180e000b203510040940c1d01e02d01d940d50580b40081c0001749503502451840740000c808215020710130394244036441e0125004144400c01500000c003614104c060143d032420080001d4101c0c1c2070f203812640440d0004c0096440710b02143ca0294160020403440003c0800d205c03c010301 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 567635899 1250 567634649 567634667
    0xa02310303030e0604151d030d05061014090f0111031305130204061d0604030218100e0705120c0c0111030f01170a060b0f06070f02030c122a10 63
    0x42550140010078462260f16a00c82c0c0c2038a01800c0d0082c40280c900d1802c0150348000d810031611001089028905a001d500f150002107183c1c039107a803254204415403034a091365551201d05410400301100011001070000e000703c5c0d070b0850141a0929400710710b0f03030141e00031407403421050003282d503900070618540380121154410213004509000c820500604240282c40a5511aa80381d0720b24216203150361801014410f001034105104002c04409600c0344040e02e01c0c0c1000c40e003605401820181c4602c0e0040400e5480250310741750709418003440c5684101118143c40000324000307403a849840c03003050a03104207010000650f00c1d129014200040e014081d40c81030091143e110740c50303a42d40c40e0a1000c800c0718100709885402600641c4006407442d0321141c901c560103090001854881c4d40031400e141d200e641c0c1a1400180180aa011880d0801203440c410b1301c2030702c1c01e40e48201005071142e910b4041c0d1046542c1c407128002030803940003501c804583c40c10742c000c1c0801100d24441c2c41c043c0403865 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 567637149 1250 567635899 567635903
    0x1e01140411030d030e190c08060c03070912030e0105090a15110f07080a0f0311070b03090d0309020109210c12050607030504150c05220f1d0a023103 65
    0x42c5880340c06409019100740d4410445d00b43c06072000c229510742d42007001c0341000e0221880392202c04c1c0030031041020000180b10b50509220300b596414520000360040c1215407000080c0800da0150304002a8407041d80e0303000840a007050303525000e4010000f00c0e000704640210f1200b02680d440180059400382070f1860400281c800d8403070b001300c0181c40da0340b40c10345801401c00e164850380a0a00203003880e80384a10303043c003d01c0e00c415042800d80d00c043c200451035000d07000640c00482401215803061149403900f0b0314a0400b080120030590010708010b200344100001100c5500a141e0300801403041c18082d10f40c465501e40f00d03151035652030105d040020303a0517501486031b0000512864042d05c1518011500840d0501e84102e800200901825043ca90301c41084000c3c01011105550703140f05100c04444002404c1030681483c110031301c81d283c15400b40300200b04440554030444e68005d02540c00890300c2c00c0c0540c0e1005080748071511403401d5031101500403440120550b80c0b01081c1c0120040e24 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 567638399 1250 567637149 567637153
    0x2010b0d03031a0109030c3303050712050f0c0a030f0e1e0303090303010e101205060f2811040b1204120c080a0e0a260c010801081e0114041103 63
    0x1008011103103081c03180002000e141759024203010044445200c3c40071034080c0724500f203c1c40040e00d40d03000f00c0e0b240340352004040f2b80c0701c3c000d0040890b0000070000ba241507088003001185000425031481243c0078100c8400300b20009680b86043d4441d401640c6840820074040c45444440c82c4403550350501d050b405011084240601803018034044216405041003c00850869003010a20388c0d080c1c0d0060001514002448400542e41c100075a8921036540202e025003014a85060440246200103010b000180e912082d2020b01c41c078500e5003070003a111a40b030009100041034011940c41d11880e003100c85007800c04211420642d20440360710307100c0c0d44611108818600e184505684c10310308020000c03e83c0724144101144a84035000e4950005c4000301a01c5105944407900707000700e101035000041100c40c4000c01034001c0310401003d480c3e002c003860105101e40c0f40055480c1c6071940b15a4809112142883d074441c9840d094009492404200c2c082c4c04407030074585080c0720800040140c05000b8 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 567639649 1250 567638399 567638441
    0x609010602010c0914010e090a0e010c02030c212517030f0c0c01110d0e1605030613080919031401050f060d050123180607170702010b0d0303 62
    0x80c0d8410b008007603008245440c0c050405050501302400050305a003210704000044012161940d01e10102900403901c081e0005292030113001036a0941e80c2803072014080d503008000c4001c103c20b0000301000f41c035a800c0c000301c2410b000041030301c1300782c4500c0e591026404c3e42c449101d002018414408d40d8460710481440c0d4880403440042d44003400300303d4210076100d044d5030000c1e80b1450729200501915545100005030306001e4199554907810548580491540e141c1c05110f06000401000b0120105400c554680c94a08800280c0e10400141004554442c101c3c00100b00700490090300c038080c034000c01c4c2204001001c41404000802c40c4000e0741d00c3e240c921040055418103206040c01148080490a61541d034042884401071803204202c0b555980c55040f82416000400100e654003040c070165100c030b003031a004004100c00c00d000c0b800000d030800e030305022000b0341104040100f0901c40d400242143d5801d18142d00603c407445100381c100307a280408808150b8150b00200001c00e2282c0030f200c030 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 567640899 1250 567639649 567639659
    0x31a100e0d0f050124150c21020303010f050402040308041e0314030d1a030d0e01020703021815060406271203210c200115080a03020606040515010806120f0303060901 73
    0x1754030b4140c4514000141600c2010114511607071060354914040c03080d0040c4901c001c074911003044840b0076124016080800140a2280349940c150020501203034254142411a250614113118174410003080c4400496518400810404100001c0d40c1101d1344c0303094011001d060544039400000c111001500d494a0354041a6841c824480a4100600140300e8001180c106441d0308294286640c190f104542c0000010b07074428100702d0107141d6541b603400301410010389003642c15807109000e61103084140010b00c0460703400484181c144c0d0b6954a80c0d03031211501944a000340110383c200864a0484600210506030401201600550b81a080c9040d0104000c9904100c8841c08002d41c00070b0350303051000380700c2c16040c42441503036000d8100009001d03c1d0a1164000c1c075003640c0c400940c44d08031070b644c20240b64040c88981c1c4c0c00001910240300c44c0c0752240348550445801c180c050705201c0701d072020508c16182c199541200c1075000084420048000307002d40d58a410858415119284031400403503 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 567642149 1250 567640899 567640961
    0x301090e0105180c09040804090c120b240d020d09060b0a1401090b0309030405060403050a0b09120405060c0709050709031e0203030a050f0706020f0a031a100e0d0f0501 74
    0x440c1100c0c0c10090102c54004c4410040390b020054403d6030101010b00c80801c406007188a03c403524440d2f0b48849201d02e2a454005e8284c51450101c00d1082080c05400d410681842802500312210b11441903035803509145440000e01840c071b040c1c40c50307514210080041000c0756112415840f011541d2218140c0e54008940b20407420300c0445001a0740c0450800400308038401664010341d00030203481c200340d2100c000c00c46c80c0d00664002d61b59a448040d4100038003030303070002a41d0070400703620250040301c02e501003014003440b840c4911401581f000507525a03e0314203100040141034010300910450a20500040c41000d41d03010683d06e100305517800b200201d0b8500c0d04d4007002d681c050302440c00c00c501c0e400e094500350006503501d03003082c400b080540b000072664401441509004050943c5035102c02c035004044032007448811704d0518082641407060364032096844c42c1400945817060b05040460013090ba54443c803400100010903032501407041140c10b4010952a106000944000c40d400f183c41c14 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 567643399 1250 567642149 567642181
    0x1030f0b151c11090903070210090e0408072108010f05010504031a0934080313030b0a090b15010f0f120903090e0403030b01030501060c11040c140301090e0105 70
    0x26600c036982d000c2280d11440c0c1400b01c05655801181c0d0082c800261102082421204840b4000d581c3c1001508204500e00b00049609941062070311600c5d503400d08111018403e0090005001004041034100400c0031030140414402114243c1d0858201112406011424203000700305403906242e8002c2460b52207201034a0880385c100002c2010400c0c0d6808140201801508a140b107002d0120701003100c19a1255146408070340480d000017100d11480080300b80f90264000f90180d403c1040b000d001e007a280100c4a06072074000322415a15165500e1900c0106800d00c0000c0503010b0b06020407959654a1080302442c500c02c0c1c80720104400f003142c088501c400c1091618000c10420340d00214000401c0d401a000ca40c4a4200100c00135140c0d000c08800c40e000319001c400083d2681000c06055901d409894018206c0d03092100c03440c1074980e203c0305805450503216000300c5d60303003440c2807400d071144d01562044a00e00120030350340c1d41c407900e42901419020880d00007544c02c6c000440c8a50300740c0d444407 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 567644649 1250 567643399 567643441
    0x22060c030e150f0a0e0a0504090b0f090313140a0906060c080a090537080703150f020417010606080609060907120213030c0f061704060207080301030f0b 67
    0x8001d500d0824030410201544110030341901d11014488928100d2a010080c080c01c00b49850703200b5014a0f00302041914452500114000c0b801c2c0b203180000550301072005908011014000441c640c1d9490615140d401044040000740400708000100b40b50740a80c100d0301110180c80c0052210348030f070520001e0703403020f2091a0006420409003c049154000500200d80d0249040c06906a44500252050003071001d40c3c1c0244002105441ba1a03040e500c00f86400500d00708544055442c09840c281c8995082c400600340c0d0061040c009400006a486010155051941191504d407141c1e400301d161100248a0b114a40c0380040c0401c0050041001c9032044400078101c4402d0f50b0703010140000b00901030540d006001c0203519280180b1540c0c0054800b4500445010201520307600b0441400c001c0750b0701c0910010848501400b12550241c02640c110005040055240d200e501d0848000d1040300006080c1c401c0200003c003c0000031036102101a004071090002611040c02c404000001c142507 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 567645899 1250 567644649 567644657
    0xf0602071a03130c050405041104050906011410020f03040f03170301050a03080a05071a0901060b030c030f04020102070312031a03030c0c010e010e041d01050f0f0402150f22060c03 79
    0x1d0204540c40e01e1000f0014410640058204d64079804502a03030015541150303103209040b418222400c1c68840c0c3e80e880b540070310091460754508440c440040212000b401d024a0002c105482411f008002510340481108200d80d03541356500e40c011341c2c00d01070380012960300e820a400710a8045254042c5ca042e039000400200d0300a02d1662002400d610214503501481801e0000314003141020b69407010b0099045425044e502d0b15080e60b6007103d0079504070002e21a0180140642c0e98641c45c1501c0c1d01c4001d605000a09407150300041c3d02d0030225520040c8800d001c5e9241c681d032181c0c103400c00c0c4c0680004200941d4101d2019041617228003074580c0c1103034507501400304036085610402000001d8441814a417608498a1022905032064002500384900f07543d1081e1489010902c10154056040e100c41c0919003040c00701280c40c0c0344003400191095414244100703442c1700c208101c840d00d00318816547c1da21502034a03a0040001c030751000f07445401e1003920025a860041b804048059450b40ea = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 567647149 1250 567645899 567645901
    0x30d0c030509010f090b0703020d1103270607020613030614090a120302090a09051605040308120a020906030405010b090711250503031c0501150804060903180f0602071a03 75
    0x1150a01540080b120400c180c94170000b800911400040c40b00a00a501805080420010240c82036080b61503605140d4410003201546241b0702950f0b581c0b0011101c1c0110391605240005410f074050318901030b62200d400601600c01d1715056001c1003c5074803580050100107840910105c6a02c0122089e9840f03400101d0040c0005a0701506d80004002d141801030610403018007040d0005103980109204959440030310903940000e0100c02c0c805480d6242a41c50541180d854200038000c0717046c0071600ca140300000c55501030041e0143d8101c95005040749460749000d0a0881c041c08902c030056026000070000b2079501440390100880d180c80340001000143c85141c0b035040060900042180c3e4001c0040d030100d07803540d0900081c460820b107040c0000d0642d0580740801c003114410f138408803101c401c001c900221a50054601984660050400102400182401d644150315000d4002c00400741c0500407808051151400e402d6411a40c201c9029641380c03000050041440d000780e1101d114180 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 567648399 1250 567647149 567647167
    0x609090507020c1302130e0a090b012c1e040b06010e0d05031b07080a080415030902130b060c0609030a1403091b030f060c0306040e0a031d0406051e030d0c0305 70
    0x9001000906c0c6d20112100e005a0340340c500d482400d0302591034000a94a5500600c144410055068090141008810145641d110740d445416072480b006181000440000480524007401d41c10a0700c0018103200f0b4191405182024050100310b03403881c0403c4900b10400720a00300443d01500440d80000118900200d13108404c0303644a5080b80d901081c8a0000c0c0402e100305c00b800300c00c0c1a140b1400006803030350309006000180040e0340c94010105450b025182000d60303513009440741c1c1103400d4080000c195001c2d2011a11038070800308214000c0c0f00d54018000d5001001006140368001c940e40c02d58200c1443c50340340020311040ea40e40c0102d510010385e9541b80024401c40001072680101190107442d02050f0741030400350100c50166060401201b00200307802c15008000f01001218082d0040e051181d8000d0702da00000b0004072020381d031811340c08090b41c845501c0781c0c0141130024116440c100b800c3d05400c1c950001110498000e001e13000c00c82404901840c0030703222096050302c2e0321741000011 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 567649649 1250 567648399 567648401
    0xa060f0c11040207050f07050405250e010323090c0a080c101803061505100f0804051f0b0f04020f030c0d06030f0b100f060507060915060609090507020c13 68
    0x481c036125806a820420480080c1041001e220f10719280d0f0050b01c4401c1c07500d010081120001411000c3c0a0042424000c0f4500314844111009103a814001c2d80300c5030890040f0010000880c04100c815413028903000300c920381e02000c42c400d840800858001c3c0e01d01344140585004036114003886540030030000107140c64200102c00b03a10030646000c10440039008514001941c156200340c40580e5075004a8600d0035400004201804007600e903032140310384485005080740202020501041405400f2408111050180c01c0044086801c1030318694240c0070004001c00303142039424403c411910211031a400c1c58000d41d15000b01e8008a103043d5a5600d60300e4019500c05a031411034260b45a40110000c1c0c0304200d0403801c81c1c058254144940707404010511001c00b603802185600c907250200704040ea5025040301d045035403041011840c81482c0c81c00f20505007a841c8103420060820001003030803640450030404940603000c0600841c0c4500030140c1e01d950020782481d402004900c9150000001 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 567650899 1250 567649649 567649673
    0x9090506150417010b0301050402010807030c020f0706120506120a0305070c0509010f05130501030b070c08130806100e060904060515120c0a0815010e100803030903090a060f0c 77
    0x10141c05640660450901010640c0c85500010007003c040c01060307098010910486208981c10340003085a03042c01d40000e080c200d80107280d1010141c4582401608600c203206c0e4031a00d0782164200d8038010b441c1d8001400e084012124410918a054005096840c2102e04143e54400c180054540e0f030000d910115542d61015070155601d200e01c40000078103440e088880d5009001001480050a0404d010003c10340f200340d000c404c03081c0c2844018004615039040b059082410790900c2d001a80d003500d4440c20b070780941c003894142480c40150028000b031001c074000344591020451001c002c0c0d00c5803103054410780180ca51580002100001400050300c691203590011400105094440441c1d0700180c2030314402114210f0346e410110506203681021807000000d800440c001c4e000750314124000d809400c40501c508826044040080355901c40a0308402c005401e01030240c0340c1c0d904c0c3c40680c241c1d995226202c458020072000c140083d845c3d20440c0c0c86d81d1482943d03a909804001651903038111040 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 567652149 1250 567650899 567650911
    0x2a0c190911070f2f0a06030218042a1d01030b0406080313030318050f040207080702030f03031f05060306100318060f050726100506070f0c080d090905 66
    0x804100c580b02094111944030708a6106640f025135040e207040d20b03449010401d0360225041c2224410000090740c40ca290394098a0f11442c006890b141b80020103404844002d04841c1c009182c0700740392304d203007141110b9442c0050301c40755042d1b100e40140340c04840c814517444003c8401c803203d60301c6070702a42c44bd800078a52550010408100e40c1e88441440f400c0d03600c404042141800480d108100b010b400c08007403814068050b2a40008916082c040303014500401c3d00c00c1c1c032450340014045d0420140205442005401400700c0b00c406c89441d02041d541c0d03100b41c609219010419003072081c2d50008070b102c4025224083c0502e8195200c0c00c0600c1391190040351710303409041d19034541101c862464902d0150300d6000740004203421501024040c00c0f030b000542041c040048a03d0402c490b061080350446101c0d01880ca84c510341d503100302d880c1480001c50b401280c3d11504c000340344014401070406881c0031314007d241d0740c11900c0d0740341116035880006208200108010810810542e813860340a194015 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 567653399 1250 567652149 567652181
    0x161202010c02060f0d1109060406030209040e03070312140709170703060c21050c07140102120c0a020105090a0c15030b03030f0a080109090b06040207020301022a0c1909 74
    0x101e66640041d4468014010f4802c2c03030304010601411a003060b001e21701d000c84828400d14a03040500b000b040d0144140d010343c078141600010b40c1805034807a40d002290720200305090307039218103080c50028404580b80080c0224a410198190707440340d0f0380a0b10901808042e00c03401000352415040c0340030301215018942085c0140000040032030018000c03180c22052543e2000c61405500000ba800d640200480d001c0c8a4500002c004542560004032424103400c0a020746034030080f12980d5003e07204080c1c082494400e90f00a02c2070300d110348009080c071180c10307800900c503544d40e00b4943c65a17a10b441c0400f4115403855a001c000d6880704120288801079140350104190800501092a6a11088181c624080d00003402401213510901031401f5140907070040c4280840d03520f85510309000901a1071041742c0c0011608115a000d50454035110070f920001021041c08007912400d10001c0140c0c10814007504070203841520703269210210819401e00d1120340302d400c2805050043c03014140c105030718 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 567654649 1250 567653399 567653417
    0xa0908070915030f1e03030516110c19170a56100608160203090f040605041509050915040f0204140a051006030501050d03111e070311010216120201 65
    0x14003039011750720714050017a03c022a0740c4c00d240181c12603480310103d5507020070640a2500e48090710115290b03a282d41c0071600c2d20b694480d4024174800d40e02c1d247e8800b690803550b28208d50803000707010071203500c1d1901420180c00303450f09045503091501020071016282d600d0fa000c821181d92492070249914004c0204c01803281e510307240440c51400410b4a1402581940710810007415501c85002640001c000b01011405810320b00046e5a80c000c1d00c0e6407500c540440d0703219850301e440d580c0c000c000500c4001c00c00d10080c4409403071a1056091402968001400c1c000090350741800081c1c00c40ca46400042c80750019900c0d41c40c2c030740100c8645002264407540310501e240c0201c2080c2d82546c021000c0a200140d181000d6690010407480f42d40100107250620004000300d980301810010140d4040c04c242c45802e8541c1025030400c1c414850110f40500c0c8508078141918002401a09491249040001d018020b8005907901c07090601d01a10320f001c2c0705024003840f44190303c034068082c410306000500c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 567655899 1250 567654649 567654683
    0x3130e1005062b0e0a120c1205030403051207031b020f0a0b0a020405040504150609061d0a1508010b01080a1416050d02030c2502010807050c120a0908070915030f 71
    0xb500c0642195640b151700c141c0581003804181841180e8100181c140404404501c0c0d881d0f0b1105030036607a90b002400004030002d010b042c01401258009a0030312144003c070b16000c4e401800606403a503030704851040502c10b021440d800050a40f60f081e0201c4000c001c013085035a104843c3c1d140090000b0110b940a010000b004d4a650007214099841000012003031041450640112001d542c000c50281c0e00f0500d08000310200e0007508854100741c60280442e0395520740d5070b1000781002510312040a02c00700c3d00041c0c007030410352010004240990300e0364010b48505a0a04c10f5130300d0f00007100112190300b00820340081450087c02e03818029410010706180a00042c64126001291900001900001c4040201c81c141c08808910040c0c0500f0700149019500001c04040e00205010f05002c0000f80c0301c07040d04020010701d0320000180780141da482070a108018008072185c420841e051140220111b40442180591444203000459030004281b850312440c030f41d04011001650303824003003407101070 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 567657149 1250 567655899 567655901
    0x40905030c2d160504020306010c120509180c0a03020703140301030c05040c26060a080709020406140415140d090c030b16090e04110303130e1005062b 66
    0x1950068600781e18030000c110900880d032040c14254941180c0c03c0454034008000380c0d5994801650700a031001620303540e40d00010f03078100c0030700b0714080c0030603584510340f0380d03027030b620400901e41c400f010380d000200c50070704c0c0103446d805a006030741c00300c040320080c028660007070b1103680688140c5010f4a0501c41c40c41d602101106242d1007a0001c0c0c03122800990140041d0606000f110340101c00c034900a03000c040342c0850072100420404003810b505d80c0c114007041d1169591a01c2d00c024050440a8640c41d641c1c0e1201c02c0002e50262003010b01040019100e0380030300032020207480447d010740b04c207031070500054082191443e0168240585075901030040352000c03001441401040c1e4410030305010707071604504002000c408000e00070922942c42138007640000e51301581850440718514200038070307030f111850100e020007a0f4203013080d0188004103420714601490740341c40048402c0880040c0f201d4840c2003040c00c1365403145c0203043c1c1048041183c5580880b0051103020041c10030210140020002c603c0d0070 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 567658399 1250 567657149 567657163
    0x605160f1e03110f0904062c1906060203070b0106080c120a021303050109020102010e06010b09091506030705222706030c08010902090f010503061303020c100804050d0f050306040905030c 82
    0xc0c0e2004022032a2035082c1001c0c03040e01f010300b034031819200c01b13203110ba14080c201c040001011a407401f0f001303008c16030205142a04900300c0c81f80380814002143ca40e10025501c1e0440301c81507030303061105400090701c0c901642e900c2e80958801022146400110742020a41180c0508172940042d800c001c0402290032003411207001d1403140c00042aa030015000081c2074410030300c00185150840c800400602d0300c1401200d0f04514191402c40c0e065641040c00c0b10380c0c40301d100c3d04135040b0800004101ca4144c7c003000034810308001d004600f5000c5011741c0091000000f90080100c0074002001c0e40098a000070760095032a00f61001c041a666140e588156100d40e00d5400f08032141e445401070001c52030b004601a80c0088565813030300b681d41c5440000703903460b04090080c1302c1030410f1810740002e2605c2071041981c0e511025040103c414400e69004081140885042d00d25010b200705080b600c6101350360007122083c2c1d42c0e075190b045468a504000c000c0c40001d604940e50310041084400d0410207204070 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 567659649 1250 567658399 567658417
    0xe0901200702012316141c05090f0a18060e0a0c050f07110a0e07120b1003050c1e040f0b16060e15041a060a0315050a0e03070605160f1e0311 62
    0x3d907840c80141c07000c11f03180081502007450314590b031043da481d02950181c1507428815003101c0540d2014407240209070650380750381000300300700000e50a0003488040c94020b50111a0180d12030a0b103540d0b4607006604a501c0b2007038950010b01704002c410403401100c0003400c40c2c0c03800b40c0020100c1c2304401000400000c210703846a09900740071810070141c140c00010075883c5102c03103441444404112000a0700f074418078140c183c00c1c1683c48020030003580290003600d4070140142c0e00b180c060052448170078400c0d0402d201d09010040c2801012851036482c80c00d40310046080070380c07118101015501e03c03000c1c000c0511000d586104800d8001a02c03070340c10064500541c0140340400d00c500e840019a030482c00010070f0740f40140c8a0140c1040000d901a0030a0706d400760241002445403196040880a80450b04645e64240700109005040c03115540c4058010004249203000003240c80c5410380304508a1400c200104140b103106c090054004008072040000624000618464401041d035164014800e6 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 567660899 1250 567659649 567659663
    0x606080c010908160b073003150605301515160210050c010c050405040509060108070314120a0806010807110d080402180709080c0a03080906070303060e0901200702012316 75
    0x2104890681511270b1002100c602d815000c0700d1810002c1c00f0745244640c3d05883d500b03400c0e031350001903a40b8000c1c4404a0f40c82100c03001000300d06181190300300051444140f244103c2c12180d0800001d6074040c01c5031804c900c1010089008000750302005052103a000003a014400304225203009080288108420020781d600c4050b00e4600307103c01c0c030048442c020202c22107a802000140710f41e40000422008482c1d01014400e103001c403032140f01d4180340680354a0701c0701c2100130034081c0a56802a10031fa00c40d0b00280d81c3c0c07a00607610304404803040c2000d0320800d461034205901034410b0710b11032000c26030b21a0000d40b2503550310400301c8556929000c04c07200c0400140480340144404007040c80800c0b41e1075011660032100c0350640c1c5034070082e0302c284140c003072064030006a540d042501a400c550000c0c10f000c0041d100138a0801c84682c0a8941c5008104000c001c1d4410310071426100c0c0250f07503030260107960f40358040181128060245181c0e09100b400783c03c050100c3c8842c41880513400c0c600074813a01c0 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 567662149 1250 567660899 567660983
    0x110a0605011d010e0c070803150907052d040b090a0528080d090509060d0b160210150b030417030c0d0b270c070606080c010908160b07 59
    0x801011109068214804e080f0302d1606004603440d00006a9000d150810981d6989498290080364945032414480d50402031040400c00016000005082007403a40101102000100000340c1201408202c83c10700003002400244001c5090758054894a0b8000e8400781c8015120700014500b40109a070003001800140e100c04801c10702000450700420254001f80048001c00d00301030303d400124056030b0b004000d08000501256900e1040b0080c0581200b0380034420f04040706c225000b01c0d204429000944030390303088601c2441680c40382e546800f02d00250040161305200c076110083d40b0103002076454612003501c0c07001031080000214050107801c10b0703c0c2d03a0381644076034080c103a403000c036055440b5000800c1150b0419611444d1100340008540400040d0f540384032160000d8064400050580d5280601c0410007071000240c140f0100004d0322000400c41e59201c01c95030b01c1040d088002c0440407004810000b81c0000400f5080081c0f007040d1404d200003c4920b17040c415040b80740c0d07505d0380043c410 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 567663399 1250 567662149 567662189
    0x31e051603150303080c0706090f1412070309090506010903020604140901050103020301030f030c022101090b060301110a110a0b040303021209010608120310080d0c03090f1203110a060501 82
    0xc4501400c41100a4000a042d49581c401611030500107000c92880c02000400b10104203050b03225042c0b16920a8940e110301c201402e00034503c0104040901241c0b00d00c1520805080030f80c0c007500c1d4055850380d0b419100385d090a4154000d800091309103418081240008001a684e40d0f0152024110b807000c064401d43c041d0003000720942044c4d0100d03050510410050000c1151a6a481a000d425041031103c2c83c101e13102045000c80703040d01e481d065590f9800d0880e80303480103401c100e15850259040c4078035074031588105401c0b9011030b001e520140d4002c02481041c0c40c002c00c0000c00704400c01e0182e036001d0030540c0350b0b40d612810881e021000031b135001518500d40d02d840726140da006004038008102841c01c180c405a9038501c4a900c0d06541c100100002d80100307506035011003d0003d48040e80c5075044811405041084a84412008900301c1d40c0040b40c2c98480124030700443c0e00041500103041a59103080d591062951410a82400b4004203c4e0205841d40101c60091000d013140000c1c80150b0 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 567664649 1250 567663399 567663401
    0x1061d0f010b07031407020d02040f02040801060e100302091b0703030606021b0604210501110a17070801060e0415080c01030b030a0506060609190306050403120506010f031e051603 79
    0x140c00c0150790032401d020840201740d0020180c5003964145000740d95500c2c1600008622404194000394410304005941084500c0b43c1c000d030044402c00e10080c080b00c2e4603824814900c04007220003d0350701390708a108201615020940a03003203031010466114903210805030350002c0d482500140d010030b1f00e400c01001304036410000718a082c0001110411703070004050000d00305100306e101c0c001c01e8040740910010f100484c0a050b190942c3d005000f080400501d0721803240c6a04801c0c0b1000100e004403401d40d50181101181d01e02c1180a0340e02d84800d070f800c2180c103860207010b048107150426980d03c1640a9900780541c0e020242c203020004020000c407802c0010103603850b4540060103900550a80d8000940c0040c0700358000c54211313040b54444500c000801c42a40035038951300c400301c10341e04c000000c0c00220740c003013801075000e980c544901d0403107825401d0a44105541b01c2c1d001844512440c2d910f140b09601245404aa80c030102c50000721205000303040d200151828000c4041c5250041d81c82901 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 567665899 1250 567664649 567664651
    0x1e0a05090a12050604081b01060e04170c030904020f16030e03100207050601261515060c060f0406061d0105030114010810021303060c080f01060813031101061d0f 71
    0x20380511000b101d2000d544444e2103100c0500010f01d00900410081c40800c40000850b42000b45040204881366844070a0030107658155130a580c04804410550000c16000b41115802c072030507001180b9114400040c40005d500000304210100000c0c002500b400344060ba4001c102c40c000d40d0b81ca680c1384242c3e81010300300346040c401e8100c010301c1040014001a004105141103500341c3e90301013007041d8801003180031400c20340310030455030044408079158028a210001e0103081e4601e60301c0d50200600703092003424801d05c0200b07212a403000d4002051840348404190740030b8410140481e50320758a1460815030081d440759140760301c640707100512107400d0901c110102d40ca140c60f12135002d545489504c0c0d880340580a51641c0040c2c0028141d0000d4017402180c100071a0f02c0502049035009034040207241003000c0d6904400131390305000002d1414071498009000e006d40031403140d030001440d54151031103d98640422029500c40c0000102c5030181e00e0362014110b6038205c041883d140c055462a000c2c44 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 567667149 1250 567665899 567665909
    0xc0418150c0c140c060301080d0206090307030e1e0a0902090f09060d141609090201030b01090f170f0f03120a091101081e0106020106171b04021e0a05090a 68
    0x441d0607402003101c0d80c03000d600c4007980e8001000c10003d04260358014240b2840c202e0316034000800000001e01008006400d01c40c0e603003d582651281d41340c0301c00f15034580c0720f076060203030000c0c0c0010855441490403405058a40030200c80034401107010101041d0b00b12195403200c0501e99000c00c000780300741458140b04031191800c903543c031203a1508500141c03145458410180445d2091408003000b01c80400c0500015030000035139141e440d94405c515005030082c080105e0010342420780c20301081d40610860029070304c0010030380c107010b814400c114403d06400c5580300080d12441041c54007944050040c240c0501456016640d9a80603001900b420500908410005441e2101c1c0c00b01207401c2c8454404001000d00c0e04003003940b0b41c0400003901050f40050b42c81c2c0c0030a4003000003100b80d01540b001040301c034000301102402011124060304c1d82c046491b9022500d204c003100102a10b800d50003400c01c01c1b480caa0803815011000b0306046150083e600060103d1400540c1e141140303022180c40c40182 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 567668399 1250 567667149 567667151
    0x105010216051008180a0605100806100b0901020709050c04060e030307080304060b01110d0207052409060702061204060902041422061d060a0f0905030f030601020c041815 75
    0x91805011034210899070f500e207020070440f10049070019414480542242c040c02040360410101410800001c14055511060381c0c0d007140b4002404500224400c3e1080c6820700e01c12580c0c44c504008054203500c210151811401b070182d020130100c8052182d580101030300c0c91282d48030350420a0140544110328010b42c4260b1040c002c034070004031003c049a60199225102051244130b0310b005a40c40f040820962000c0d00941440d146132580c0040c11030102c40c02100d00340341e04004484080702041001d11408a6404200120b511310b04050300180b240034070240049103850304200700d042da503001c20ba43c01c0f10400d8035001000d06500d0140181a500110300900345244e0030070040704001100c0b0f00c440c2418541ea40c041c85c101340700789548883d801c118030030391101030798848001541d114030f811200101541c1c0b030000f11204121442c4581a4000d601034011461b0410b6050b01422a0f00000e00ea54114415825808101d8442d4003c8003006840e0402d00c00c2d005030b40b442c2070b03d4001c3c840c002003aa99 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 567669649 1250 567668399 567668443
    0x10b0403020d080d14040302150f01060c0206070510050c03090c0118030209060d060c0f03151505030415020a11011a060904020a09031b0320010203040e150a06020601050102 76
    0x340e580d010b61090304650214615654241105503040500350320b45070129071030b070340d0000c00045c19000b003080b0b510350b54650b80c0d154041c0c0c2c07019a01d1075411028029240002c03080010140107080035001000280d01a80032a00b2604505244800b9036004461004802d40b0210511083d001e08000d105551602400c02c1702802412580c11403054a441c840a881646034901091280d02c40300c0c0e8240b56583c211000f88102c828401024004041046120703001a18100c2c0301c2c0810008407030a102036031801c604440341200a00750443d11504060020303595450700e6500401d045c50383c0c0c401811014501e03214000a880b04060660845081c007800c02c03a172046004a205959544404070344140504540c0142c480c880004221102d1001e40c0005201071180c81c01405488034005c2400c0489100342c803420f6030207c1c1951050f1540c81d8240c0d0f520b01503030007844203001146040511b294400040d0f4440c954915180700000d01034289a480b05001d608102c00501c26564140810016081e10100c3c071980d03 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 567670899 1250 567669649 567669653
    0x11031903090b13082b090305040f0e13060b0102150f07030c1701090c17040c140a120b04030c080d0c02061003080d0209030c120102030624030615090a030c0e010b0403 73
    0x281d40700d170088817020054000360446002420786a800f841c2d203941501049003145616000c0d0155004c0c3c0a289416075a505d000144d113481c40f40320030b119449008280d0302c01c86032559075501502185180605500400070303020b100d010b80d030701c1262007012036800c4059a8140400003504851604440c0020000120f01d01c00c0c80d101d401400340c0c11108604c10001d000070100c9411604404046a0142420740d100103200510265041071820b0728904032901d00080440003c0018241e207d10407100a502002041e0700883c0c03820440350303441806414490682c1d80503a1303d400080d844204000010b50742c0d0800803a00a504100095104c45840b82c0b050403103003162142c0714a4000e4203000506160001800583c0362800d2161100d145006800b100600030290f040d14081c0d00200c40c0c4030f00908111035141d095080074402c01c0c0c640503200c0c0e410b502c1e5444010a0020300b00184a0091200d001000254059111001d200e00298064414400c00324102584640002c6040c1c0c002c0c40b45503030510040c00 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 567672149 1250 567670899 567670913
    0xc05130525021e0a060605300c040204151e050906131a30160c020613080c0d02030706120f06120210090b0a11031903090b13 55
    0x1000390314410500038200181e00c12843c006440c200c00318021507691100901030700004550501611505013444019125002d02200300c171504111946042850402d40780603444c1c10451141500020070b07038484507500340224099901a910190704a4110f80b0303e2400d09a00100c0c04000d40c0d40004980e02040505400030100d016601c011032107000c000800710240c4006081040080842110742c2e201c281c241d420b0103100ba04500801030014002e1411400760980005030a1074040f515074107849076403114080d045600741001d02c1e100c18000d020f2130a01c0580d03a0a0054107540e40341c1c201501c040b50030100305901788010610320324024024071130841c0040e50f02003082003c0c1c81140c507024070010600d040c5800038207811540c048203d454107902003107105440070354600c1d2034000c0e2010904003529070340450b80000103100b01003c403130b014003203070580300d01c80c10291801030401402c60b8140040c0c000405003580e40c0311030b408046581d50900008203c80004100e03445180a040d0800340c507441c1c0c4801c0 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 567673399 1250 567672149 567672181
    0x6030512090402070b0403051b0c01021002090102010e1b1e09060d050715030609050f0717060103060e0f070305011505180a08030703030f0b040207210306120c051305 73
    0x2118050000c2441501d54565505039548190841c070218001d08050501034419480b04100d101480d00008a20140500003e0342c5c00e2800c0040c0e0041c503691400f0003c040083d040421050b0440d521020302000c0c02904200840324128090f81103802c2c2c10070b01c2c0800c001c040c10160500d424a80100108001d640c5000d400c0c0c4d440181035901160070b00651504d142050899040000c9014141130001500307580340d4061002d40c0d02500040050b034a60003c0320341804400c68100c00010382c2000710140c8000744054075034001606050102d00540c0b582116481c2c400115201105100c141c41004181c40d8580191401000c40814201e0084901c0340000e01502c1142902403005c0b030841c442c0c041d50b40302c45c0060001000004196901c450303907850018041c2c04203c91005200d420028200700780d1510344201d40c2001e40c01000c08030090000078000c3d00004441850900340b503600c40c4009595202a1140d501a500c11810460094108030402820740b0b618480400040c4c9003800708042008410048 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 567674649 1250 567673399 567673423
    0xd210e0f0f070608011a070506010e0402040f2703090f031b050108041e110907020a02010306080f0a0308061318030215010b09010e030a200f03031e21012304060305 72
    0x503590041b000b4030810f44244070000300180b08041c00050718441d42c00303000e40240c1c070071241407000c004c50400103c2641c1d5041c2d90170303030042503030400d116288241c00c105805062190600d42d0381c2d15a40c20300c250240e01e01d9402502c1c580c0006401c40054116081da0034050070007420490350509086c3ca8850112615158100c92011490341d180144001e1131403101d0f01c0740000b0b2a0500e94035012800035200d00c0e0329142240800c4c1486004981395101050800052082c1c0009088e83c0349a074408460f511001741c01c0a0300001145540c400b01e620780d01074403074400001c46004442c1c40107480c00901e0071155502280c40b00d000b820050209420100c21a0000c4c9001d18205213094060b80c006030030039044100040040714070204641d0401c0c1d4a000f24943c00d44200c4000b8501e402040a05440c3c0c8101d02d149000044401690100c0c1d03c0314001515080300c0002c3d9080b80c0454003014041014400e0704049200d20580860301001e00003100000d5078a2001d503820300002e851542d44640e0781e0044041 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 567675899 1250 567674649 567674669
    0x305090d09151404062d080a0c0306030c080325080904051504141603020f0d1508100515031b0913050118030807020f0d210e0f0f07060801 61
    0x403107201034032500515841000e005401941c1ea0313515007025240f20b9203103019289804141b40c0d40d0003101c002c05011803c2c4111138407500c44070703583c0d102950010700c25284202c00341035481d4808400300d6004d0103202e0182403440015962018039810a0041c070070442ea55019540c00d040071a800154241c040d03850340300c0156008a110340740e00c0b01c00782c9141d507a84400c541051500c0c500c1c2594480c560080c0780070b841ca0b070060503210880075804074280d204445080c107855100f003040014048056001810141042c8600002c050f2240b09842c00d0400080b80806103d1700c40d0f017400300000140b15513132103110089004004024040030403026840c810350344e891103000b2090000b4440e0054288005580c0e90240c001c01418613403040c1c010603424481c42c00c2e0000f85008000440b098000501c17242d130200440d0041500111100c403c40d004401d8040c51280e03640b80c00800020050f15000700c403940c130347d29001340000300366a608c440d1070040c03903d40c40c10003a8040107040182913000315140303054418140b5 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 567677149 1250 567675899 567675929
    0x3403080d021305030a0309031704050609130902060a02060702060c09090a05070216081b180f04083604051501031a1807032003070c020109050319030305090d09 70
    0x1889464094554409078042c02500170100425901500000030b9a06c00c84a190f6a0340342608410b805005501030745d5088101004000200d03d882c9a040032381321001c00c00816403010a60115032603811150341100580e00000074000300c00e8050211a90100240103214104540070002540740600644403001050b52140400c1d140380c428803e6410a448100e4901003081d0b032200305550340c0396414142d510b1080c9890300010f00303140ca100100c89400c3c49000c1840152540080c40c600050003070011100c04408001182c00d10f0784501c46528030b40f0121440140c42909141c2d1405002000800700e48101c0c6000100a40c04d070f001d25008075404c800380b0f0001021100400030401001054202c40d510810016400c0fa000c2c0e02c0300072062040445a5003808510303a11140484070328040a2200c080726010320008942c944180d140721111401450050007941e5a00003003410442682030071180070350741c0c039001e82c01c1c160107014643d00413201030b00500c4201e01501008180c42c1450040442c2c80d41602 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 567678399 1250 567677149 567677167
    0x40e0a051e0702160807030605181e030421060e062202060409110306030f0106060203162303043003110a060c0804110409030e01110f3403080d02 64
    0x1024440c10101e50504c14445601c0c0c03902036940e030619220444c0c4050410000942d5a080c145203406400d0030304000340304204078019450400810389a0354040d034031081c000080c0d1079100c3e51944109504450400200400600f4248250b95100d140c240c3d16510a60600000035102140e01880d422041c12032942082c03948000340b0640f055503c00024a42400000f01c54807411a006502414046046a00c0c2d1042c1d8480b0314240d641511510015170400c0c800c0c0c030195000f85584513603062042102c0e80090600d0f00d1901203140c541d074031100c030650011800380a00d01d03036010240c0013580c3c401c100e05d41203900717400000c2d403c80242c0002800c104001441e00c0d1000f8040260040c1154001c0060002d46c0c0000001041c124040790261007070b44922010745128109881380c006643d8140e075604c0d41030340c00000151900c5207a66800c0c0b24510848500044000042c04800700b074070040c216008564021000c08800c8001d1000c40f200429407846d01000040c000c02c0c110f072403c0220420260302c3d04051 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 567679649 1250 567678399 567678403
    0x1030b13060906050a06060903260f0705010b030c0402130b18030a051606030606050a0804080d02070602130f060912020a03240f050903040311030a06020f040e0a051e0702 75
    0x500000c08107801c1c0b0040304200b05140d001680b007025a035100b0090300380c0c0c0c0d00c0f04032140c0c41c02e0b00c00903003000056440d1a03424000c02003070b0245171640d801801c3ca8407c4020315480e265202c00c00944044e50340d50035a180924003444580c075050300817901903042010300d210b04050000c40f80700e940b4a040c1d00268040101c030b12642140080c4500030292810104c803810a86d4982c101c4080d061381a5141c0c0390007140440c007911845c1d0584050b96078181c14107624420569158402070701c140c40d4018140308940144d0060700007404203620840004d0f84a00320351100c114590819000300110071400002840f602c0e9010741c1c55400c4800e50b141c6080c0c05c0c5014008642c2580c11900090030a11489801e0300c026000d00001d032550458801007085840f80c81500c80089601c180c51400c0c964204101c04c002040341d140d1016a882d0004094a00c0e4005a584010482e404091945103243c80464108240d010708071005501c4044c02005120910b010540d10088580340300c804581030200304041040e562007 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 567680899 1250 567679649 567679681
    0xe010519020d0f1104030c05090c120601110607050406030b0409051218060a0302090f01090305061503011128081603020c1005070e1c050c060a12090c150309020901030b 74
    0x42100108106140346150842c02e61140c0030a940c16018031f80c00080314145280028410121400c5980c10130140c0482c0720504100a4140703030411610b0204c0d41104d07401400f17901e001d0032954446d2135680d45421000f5040e030384040150340c411440d020012300458400308203040950b0b10191026a034408042d01c45194200c507544c001d4005c200403a07031560844d090b238020700c01072000b00e69203074012280400446284495003c0280781c1c2c1c0020000c99035403100e80c400c1c00c40c001c20040000c108a00c1104114035039030424444900a9641c41a4504240100c1414111410428544940305281c1070496806501e20b1503144020954009000b9000010a10415080120458041c001403c0ca048000e0172039001003241441410132001c888941000040003511496010001c1c00341c5405c00383c2002250b0300458050000e000001444442c1540e0902ca8150143d2007195001081e81c14601d0f11500782c00e5603e092000d02d4508000500566100d02941c4e044030380c03200e50182d0550701c5c0404100c00d448 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 567682149 1250 567680899 567680921
    0x10602010606022d030d0e030301060909200f1c1418071404060e0f0109050610140d180c03060c030e0327151806191d060412060e010519020d 62
    0xc50481d80d942c031f2a002000440c1210b4241d55070390b050303d0301c4400740c0080710080500050728019140c04880140d4581c3d000d062055445042641088140706440c2c2c00750415003a483c0c7d540e03a9502449441070034000843c1d80180305881c0c9a10a00e14101c001650f64846018500d120640005101c0041d501da4000c04081e24100b203410607142085a03035410214400c1c0101040702d400d000025100e800d209088418074450b682d10380f200d840d641c408420156028402ca005503645410100d417841e0421642000344502c101c0b00149540d1450410408407500300300e000c810182019900703007090000000340d0391a16410100407009202c0c500c1d000c030b0401403007180d2507040801042095141413420005d4000b610f50b03020016420640442013000606ca401d0302140c0390b1320a003500b141c3d4603200301d086040e132894900540c1d5544440c8000901c0a1304241d100c5865964030141e490104100f6000e10a640f00824000b4815130410304560a401076203010440364203039022544c241181d034030b90000d0744030341 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 567683399 1250 567682149 567682151
    0x30622020d050f0709020c0304120c0302030a0812070504030308010308030a09060f020405010e040501052110050103080901110105060609010c11090a20040501080105131e05010602010606022d030d 86
    0x40c10500d44140c0b100c644903070f1038501c0d004502000403114524002c40c0d45030001880903610b400c0c24094041028560440d09441c2d0030440070b004001030b281040b110041d50700440c000c03900ea040b00000da14581d00c0041c040c0c4104a0184420000030790071a13070301815030703911080c2c180e01d039590007108030000d00c503507074016142e107044c0040d03c1401150355005100b40c92081e40c0d1100c84516040038031080c3c850a10035a500561805000b02d4041d80c4036801c44400c002c007409951700d00c064107034500f0a45400707030429030368600c0005400580d0745c0c00031010322603c1080c100a004624118000903031034001c98003a60b041c0010400544208000b02e00b52411410000b025010203040900d114401404001c0401c0c6806e0300100f807903a0702030788100a540858205075120740480c6e00740402e1100d90740c1c0c07202c844d08106458107030510844d00016000b841c8900c104500040a40c0340100090079141c0550000082d9002030050410100039440c0c803144040b09901c100e9514840d0802d81740c034500ca80c0701c404401c1 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 567684649 1250 567683399 567683419
    0x11030706090c081207170702120307030216080a0b0f06011710150504180b060723060109020901080c0912070902030103120f05071b0902041410080603062202 69
    0x402c650040040e40c040070121220000c10701064400c81c0303d1010083c0c5103010840420599501402c0100f4103140301400e58181d07080ca209000e0b01d144c102d03210880c0075030082c1d80240144407100c2d07490801440c8a40003014401030a80b01d03a000c8003000b1f030003600402c0c8007030006034a990080c8610310008009109000142c40c210810050a03000c2e8004e80c3c111181d4616078060b880c0c03048042d20281c070500e140c140b01140e107103203104004100305d0610f03030341101c014040000031910782e242c03601c1d5045054009088036981c8005603800c14405800503020715205112440d040c0c2d03400300c55164480f0b072004d1a1540c54440400144200184030540702103032060f4040410a01982d4000d58100c80c4552404100d04051902c03d84440b50882003840010703901b800080086081e40c4400301055242c03014912509440744400000c0e68429003107012400c0000ba04050700d03040100c5d40c2c100480161500054500b80400020b0700c2d4a000390a00c9042d480760780303603810413030340948050340155401400d0f0700d02 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 567685899 1250 567684649 567684653
    0x901121e0504050d05040806012c0a0e01060501180504111303050d121b050315090108070305121e07030e060d06080c01020c31020a0804050d0912031103070609 70
    0x500070449084606019103030903240741030f0103501640e082c0e46041000d865607030700b07000d007103528030201507a556a54079190389404580f80355000d60f140a8030400c00045001d070590070a090a480301544400d0401124034000540c80c6d000c0c15101e400d6540444000c58010041c917002071882c01400075a583da1003e0240000c20010f000400300300d10401134540080b0f043d0f40c0030b1010112407010701e108221150f00f101d50b052442c0b09500555000b01554401c4401140490104403005401d800c08019640410407d1007401410098102e0442240000a15081040582c250404248242d4241500300442c60104050003640901102203001c0c0850740c43e40140405000680700c544a1044d5a00560800011035440819030000801022b000c014107004032078550300300c009809104580d04041c00d100e01440010361b00007880c100d1955658850a8181130030804e00300045440c0d0881804072408040002d0a68140050002905402c22074001130104101504511410742c00601140c508000102 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 567687149 1250 567685899 567685901
    0x316060f030b012309090f070c0f0302012a12020f07110a12060b040501140915040e070905150901060e060d180c060e0102150a0c110f0718110901121e 66
    0xa1000d101b15840d941c540c0701c030850030401714000ea80d030a00055038070050401103000d01c801100e0300380c840d10000070304c86840c042074010a088841411003000c034001400030000da01142520038008000b500b149030480104181c0b030703075101c1e4041c01000b0b1100040100069514800c1401c014010215501c0190240d4680f42004110454019220b5840c00300041412224900c1c008420100030305140542c1e00d42c0100c8044290881c403d0580c0aa03d5032040c405950043c408103004008010010825007003241408102d8003c83c0d001768020302d01c0200401116901607010ad100c20f000b0303641e45503507c00101224010740040c2c8120781d1062100d00c1170b00c0810600400394811a40250744420180c0660801240c03244440b60480c0101030304071380480c000d061264021a441d04403400e250701918100003129041c800301d80040d85003500049400c00c07510b20809581000c603001004200900308400c0913207806800f0709440681041440c800c807001e501703500c0d40030071820f12051851509031580851844 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 567688399 1250 567687149 567687157
    0x70b030106140702090402011211040b1201050315040f030e040606050a03052404020c0c0924011425080f0d0f1404140312010e060316060f030b0123 65
    0x30014400c9001850040b0141040da00c1c0079074010400d00f0030f0f40366a001100d8640b01484205135182c2d0303900c044800d01607905c0090004000220030942c4520038441241d80440050341300c0c40c0650030080248030040e40c00700340e081d8420b501030000680020b00b0f0070200c4400c80401e82c1e564005150070804620260001c0190900000c030769410b02459840c082003d0403100402c49200d980000d20700354195030302d03158020700408008a811a00d031600740b44002148100c0a480c3c516901030240e4050320001d43ca40700072070b4410303020709044d00524484071800b800f900c641e4000d015084034141000c0d0200c01e1500740c4201d103907080080e898403000d01203052800c40d4407074201580d140e842c0100c511030381c0d0403500526501208204842c080d6075034686031f24101d24030a0031050180d0108000034070740310074a01d40b00c03406040343c0e81d03682d8260710b4090b00303251a2900d0344030404018101010f0802409500c08000302c010400d80c03901180400707075040103030790200c0080c40c2c524149140e01660580013040f48098 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 567689649 1250 567688399 567688409
    0xa050a0c0306150501200309040507170a0b03030d2309030d0608070305070603050c131401090504020c0d030b011709010b042909040201050403050303041a0c040f050d050f070b0301 79
    0x1000f82101c1d540ca190319126191113800e0100e400d40a00442442d441c000c0c40c2400a00d98080d81d240028101c0040d089407000c0392244081400828200b280084040c14207500160244042052066081c0003130341d2405010b00d05041c2c6902c0707039940e51a003040070034450491500c040204d00c0030301f04409140e40300d400510b4040c0d040d42c5054000074050b040050b01008880e04507024003c4541491000c901404009018503004002086034031800801c0d071428a004100d20501c06142c203850500040c03480c003103680158800c40c01408580b49801d4081071055001c0303501e0034002011115100181d03403004440940320225020a000c001021314107408c01d6a42450480d01084985014002c01c11a00c0e13866501500004c3c8101c2502d40c40d05146a62030340050050400c1c5080c540d0303c1c2d6034246540e008540403561020300950184210080e0720322560800b01ca0845642000d00340450400b5042d800e2007510f02c243c100f0324585081c000203016106822560000307813524039490300b06c056080e500070322070 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 567690899 1250 567689649 567689651
    0x708040b09040e01141801140406051b030702070305150c09040b120d020304050901060804031e020c0d06020918060f090a020705010c02060103151a040f061e0501111219020a050a0c0306 81
    0x2c511040406100e00350b5402c48404c0d03502e6580d109c60300d4000c01040024003c0c15088501e00048510354006005580304d00381560051046a09500e0128204594803640a8a0507200800e00a0040810007a00c06284c01a500000c00e4a88400002c10a000a2040c075806026406005492a5020000300240d41d0140c410760f00d02d90340c415003240c0c81c43c5e003114043c00056080e40780d4100c2d9007280c070320200d800c04184100e441c950712030000113440c040b610600b1180903030700081802040c01d1026130b0022013421043c0e80c414901c0d12401080030655180399441c45050780e8000150741d406290b050720700c4580c210b802044580c900c11800b80d0341c0c1c1800e00040d220042e0410300040280200d0090440c03444140250054003400f0b8418007002e080c00c0b0382940843d9031180c00200300885031340c055807101d0904440310f044843c40d110001d414100c17010b0300d1000c2c6da0003001640d91500b08a60481d49044d56a0180018503000303641300f2410010b0380f020052090140f2602c50060040441d0840141d0b4000d6030 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 567692149 1250 567690899 567690931
    0xb130e090307050d0809070f06052106030c1513080606120115060c150903051e1905030c0706150302100201020c0606010819050f1b0708040b09040e0114 67
    0x8403036601d014442006000358060144800300a02c42c01c101780d0024081d00841e620300d504c2d003450b1500344009030803103800103402203001c5000c0044202c500341081106c0c803064510382040300c0425160600344e40014003580c05a80901f110745c901d482100c001030782c2c4402214500d52a4850242c81d154140c40c0c007446001a0507480c3d411100c18030980108a0406c9016902107240080513142036198050640c0e849801d51628803140c05240a83d02075039200e5581c5596032403529000d1880b003a42c620010100306000d100000c40e5620520409900e0b5280d81803058403951104402a40c9105101008011038100403a140c0c00c00010000a0b0940c0d1089032941000d49840b4000c0b803c034080d04201d0311240c2e00c4500070980550048851070341000c3c03040380ca4118800640c0004040e260103503510044d003031030141080481c0311aa0054820020584070080ca4089540c0b1824518000c40c0115101f40c070780003503183c2c0555500e07406a24800f222030003d105100a11001000400b0201c80303901924030701c46 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 567693399 1250 567692149 567692161
    0x5091c031106150f0409050609010912020f06270d08011409160f120e160e0f0c0a09030c03110906091b160f230c010f050a03060b130e 59
    0xca1000c2c4a50304241d4190360b9500c03c4400c00c4282ca20300e6008a170032540e250005d2000c240103205962042012400115110749245020802d140403521031b00e00f190030140307816115580c080398964101500185501d4410400503c0c0051044446030b40e4100c1d1161319161071440707401c0107140381250300503a007001d145e5030104c0038011070310030844044058a94085170301140d64060100c6141700750140c40d11242520240318908200c03802642040c01c0b030390100203101d4501210100c3d02c8080c0c030440460341c8160420b0104628014000f4082000c0810302081c07166500b407040f04600c0c011a0401042150300d42c1d281488040c50060001085c010446080051001c1c18130361490350260482f0312500b00543e0007001406002e800101103a0300b103d030720308030f0440465100d0381c907422100d00030200055400c098074199940302180b02c2d000080d540144d003050b5083da8104000c006d40b02c41e5828115920015603100b1070051003e0b8004030b0700200302140c0c504286109100342d6054a88128040440d510b0341 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 567694649 1250 567693399 567693403
    0x6070b10050621101206052e03020a1205060403080c130308030a05100b04050607080408030a020105070f030b0102120901181401020d02031e0f07050f1c0f0905040c05091c0311 77
    0x45c043c03421041c039403101240002d8010f5102d1680103002c0040300c401e0a9460081702c20888240ca80400f00c103440040500940c54002a071000800a031014a202d004050380c41c07a031504030003003014007403014001c0022010707a404800c543d9107100c005e03000503946891b880c10000d2504140c80e40c07440c41e440c0000095200d505c6204003000d4419400540c3c1c14203150504105030355210302c504844258040c0700000b0b8000040002c4d081812268001040314542a6801400802d10800080805080000074481641c011510540f00c140b50800650345481000042e11900910344942086081c507030b23000190380580000d42600d52409038265103001045603000ca90f43d000b00c0c40ba200b0264a2485400f61210000c00108105c0841030051800d02c00d05071a01400d0020a0402c0b0105800c079003003010b00c910b440d034080304140d20103081101d00d0b010907800c020700303a0540703024075405107540b048034400441c01902601c2c405040100f48180303607084199540c8801103518021404501100c0390f0003104100 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 567695899 1250 567694649 567694681
    0x2a0702010210110d06090603030305061c0602070204020c03130302010912050c09060d0b010305030703090b190e0307090903110f03030f130f020904060203160305010506070b10050621 80
    0x141e0081078442e601202c284010b00980240381e03040501048400b94142d1a0f018030030041480c3e28001548070b28604024007030712070042002e07110341882c0a500e8420a241130864452541040d401600c031400d0348082002031180743e4065903140f002040728485404556206020740b8400c1e44d92280240d42c50350039240c00c07180100c00500c1c6411050088440b4209074045c03942c406001446918104a0b40c0c4451132590000c0c2c00948031a003000580320140358200c1302d008010900250480c1c5458169900c1a5042044810281c01c1001e1001010203654007040303240040e008030a01000640554500600074416031071403c3c01c00c4c0101900401c0e80b6a011003503a00ca50b04012030403c469448440c5114011480700048601450300443c0d02c02685881c87c00500c114401d00e4010381d242403002c0e80d8082030300090380c02020141080014043c5813503140541d00300384d5101c0c0304504580c032281000c0005042503000541c001c80003092504d101454160b0f40c0a00f035a001c9102c40103500c0305241c0c0201004 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 567697149 1250 567695899 567695903
    0x6060e01020316050a060c08011406040b0306040c0306030602030a0b04050f010f29041214060105031b031f0c08130b0708040602161202010f2309070b032a07 69
    0x900c1030b41c0f0707007622410455141e5485501503c9003110203664540c102c607905d03c0610001045440140710040254441d000e8007a0308079881c2e0305003440c00c050710300c4521008080c54016625000258000c6000f60004006141d018000f59280c1c94645030000051440c150158070980c2445c1c0410f8602d90710175051410b0301ea80030740c038242c086d040408032004c48136160400741200307030041e5080c41200281d0300900094450030000c008071a10740d0500c01500604c10004054a8000304010806540d0015000120b25108d0a41082d0a403420001905265800402d154441d98101c2c480801000b039074820400300515480f00b04c4941c8441340a20840703600320000614400850001c0390b146030117140b1283c1d10900c110000752602050580b07440860700d146900303c2c0c802c01c42e151780740c003813903020b0140d94103a29003100c0030040b01d8080758611902c1d0549a42d85580015003402054166809000740f0000d0b0180900191b47d90801450088841002d200303003902d1856482c20303003030406007175900b1214182d0b = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 567698399 1250 567697149 567697153
    0xb01030b150c03070b010e0103030809030c06150604030611040e010e13020922030c0501050703020c0a020f270f0106030606020a030f030b0d0302150c0a1b03050405090109020d06060e0102 82
    0x140d07035021803861548054541546444180500c0b800140840d1405002e01a92094260194510325000e0441b88016004603403940003841000440c402c0083c0f129132044400b000d051030404c814000c605188282d0708058400350038041c00d45403130900c16006000f100d2404881c42e51903030781e034510700004080c2580d2f0f211101143d14030700009868041041604500800d02a003411074166810300f403050010a41140401c400707110312000d014080c414242c0c020010b0505501d0511800c01c1d064540742500f40092155188405c0490b05488491301c040c80c07080c1d1303201a01d502c40b030b180702084003038002100d400988080358000401c0c1c0034440d0150710704a800c281c008011901466505a6429650f514454100759542c04441050740e100054002e089000360060720341400740b03801d2444450340041c42c1c810311000c02c0046a008590040c2c08000104100010040c503030b2039031404640070f1099034400c9074804152000800c00007025030080022102003141040b0542d640d10b42518000c804007140c42c05a = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 567699649 1250 567698399 567698419
    0x71404020f0f071b0602060711060610050313350405060d0b0f03100207020405090d0e0607150906020406020f0a031407110d0809090f090703060e0f100b040b01030b 72
    0x80041c00502220f0303100b02c40b081c03541c4000c400070303907006006070b485140182e100400317100c24950410580c002440f809800b0741030601c0c02d00003064915070721150362020000000300246011080c0e041e03603a070301a402a9120381100c01d40002807000340350b000c0c1406001c1c42113081c030064204507000300c60071604081c00e1a410050104c000d8401413000c5d90307031160003240c00c4045028a59091114481c6542039481c01030f10f52607103006000803600020240d072000e5001004600c002904284040f48080c021941d5550b9241d43d45007015411050105107441981804505002c009064005d0015980e45130700715148450704070081aa16228032a014001c41e201c100400e003003030400e0004007651401030110240300301d21a80415a4821100c006503400d6401050120030741c68500c0106403c4040f0b440c4080043c10515021038840e5218400104401d540702980304d9143c80903c240d5810001590550f0700d0320b92110a03030b1025002c0e20248500c11490050515040d60080c400c80754034007800340514440e = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 567700899 1250 567699649 567699667
    0x60c090806010609180e0d050a12060b2506050c0d1a0d0813080a1a010608150103090f120809010c0c0305040e1519030c05090f070f120e071404020f 65
    0x101010082c14150541754140b03060740c5e0714100f2600c1c18807c41550b525036901c0c000703440282010b54400c0c03045102d42c20200e0420401c10401c0951761420011007030303a0075400c0c68940700092040c2c40f840042800b030415040011920128010304a03c50700140d040c4541220800b4460003541501b0085500c15040d00441010a51000240071610741800e00c1c141720b5034031751201525080400001b124564142d0150380481110740f002540101004d0811864030301780b40c1030810701e15107025074007410140d4410f40e241c1403118410301c2418842e0400764146a40d241d190004140810132107100700158200210022050302c0f0322142c40029070183c0da00303410181882c1c0c01d41d14804002c0d000d804014214240031040d9562047c0f00c00000301d00803c460b042d1451032801c1080c6102a5000074461070110f4100445e0010005082c7d40c0b04065207081040e003038103201c1c1a5140d2400a03642d840062500e8a0398150300400255802900e1004240700e0807803001c00304101c20781c4140541103016210030b01400d45 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 567702149 1250 567700899 567700919
    0x61401050423061b0303040515070f110309060301031b050a080a080c01020c061305060703090201141303081c11030603120d0612080324031b0409050109060c090806010609 75
    0x14a055004003004d180c16560110303000076000d00381401d101e40c5c100106210401208001c00b842000a079031204007589440f00000c0c00700310542d5100414807420148a206a52051007161a00725004100c0741c0c46c0d50716400c2019484804803e5155841d80888020601e03140c6030884404981c0c0300760080030300741032a03035500c0f900d0f421240941c0850b6400740003900c064942802910300c140001d86a2120646260810034540000900490203044c6025038400150341e100c4102080e13816a1030003c1e55511140404041994480d0b0000d4001b603c0403900d07001c9015480c07491810589000020b002001c241048800300d803001b928075503419407100c1e0310429000600c03006462002c0710a034000800d503654404514407036032030140403039441d10000b08208a004952420b411820300b022620000220100301080c0d031030011100a031000d40b100030881d04190f0b40c5070001e00351030740c2c090300070300c41d80c20f5900c1c220703000e800c60240c2000401d0803400c010452510008800f8101c070b0141d501d03000c0032071508030140 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 567703399 1250 567702149 567702209
    0x50c0409020f0c01050c070210090e010b09010c0b010e15010203090d0209060a080d03090b090604022107170102040305010b010813020108060d0b040506071b020105120a0e0a060614010504 82
    0x620745180500c810319501c3e2082c491140b0544140e1445503445101d0300c10022440764800e40d0303c06000c1006c009101d42ca0404d134042341503a1400d41861b42d12400b000c0140d031104030a480040800f556040045001c2c442240d52500440070040c402028000d4000160388a00510b00c119070001c5004404070094034100d80c03003580002000d8042882540c990315140d081c00e480d001040007180d1150440d4040140070401c590b8450320303281c0901260b083c95400510001215038621058601c1148022000c01d81808100028403203181d0703e4002d1030107012414082c0d0414401a42e1a5103008112000c650154108500c250040e84840d04064416801901d29600240c00b10f5040301d1010705250000e10500100e900481c000c1004049920301103000802060190208101c0007840002110050f42c0200641d135141d07403403020801941c3d603030100b06002020022161a0f00d4400d60140a0038000698443c40691758a401451511801900155010310640c03003006c490000046d030100880510368191 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 567704649 1250 567703399 567703417
    0x1b02100f180b0a0603080304140c04091a0a02090d0516050603100e0405010204030807030c06060506430803190524030c04020301061701081b09040303020702090a050415050c040902 79
    0x400d107031240c0700c01d032547c1c0040301c04443c1129030605d8400f80002c00c002004083c0d50440c1d0500c1101510b550b25803180c55105400d954981003540032074080740b11901030b2035406201500440c485002801d08583c4c80c0c0104181d103201c15400c07500819141010800c603071081031403c585603c50fa00d00406480903180090058400755070900c40440000e030200010003a15000f542c0d00311a024650410300b0490704180d004c1c41c4108010460540104d0b9903140307520350301c0c030b408209021540000305c02d40c44801e4001031700390310303071010b108040200700140000d540100351600d00d42c411801c0c14a80003049031030540300302d40d105081d03c0c1d0340220340c00c00034494840f94a01409440c0c1001e0003d0110341030303030420382040002ca250154030642000d50f001c0c01900500049000340319051512001029082e985070383c041c000d50300b450000d401c1c54042e804480c84658085c11240c80c42c82c045591074001c0c8010340e002c0304e9066080801281e13000543c025540101d05040750304c0d240900d0007034190000c0d44000d040d = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 567705899 1250 567704649 567704651
    0x1110d0807050a02100c2a030e0f0f0a0602070e09030301180b1c060c020d0e09041202030c060705120612150a0905010204141906211b02100f180b0a 65
    0x10300c101000e15400340212625660300e44081707983c8100640d0001f480c0010804011002485030070000caa40628807040001d030550714241d10300500030210f10604140404c054000c4480140000c205a002030b84808440180c807820040d62911030005e42c0303d100a1040800c8041e1250301c0c0411100694828008402c009110f042c4c011603c048101c010340c0005410749000703503900d01e10310724242c0600c420b0341900d0301c9181c003100d140c0102e4001150400040c1024180414a030f80c1010064000c004540d48004000c0407a0700c10f00c2c000200a20552005440405070344150022aa450509034104252051480040c040c1c000c00c0810703c01d003510700105070841154440d82d0500201d0020301c0188058054110303510704000c001402d000740c1000080314680c1241100c501000030950040c8041e500c03410700c9005e0040468917081e10742c00b030000d220800c06031090102446248907000528100b100e07031504800d228440b044507600c01100d6160b8400140000002ea804001640022000703900c0624880 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 567707149 1250 567705899 567705913
    0x60b150c102d0507092105280f0302030f0d0204031a0c0706200c071d061f020309090a0c120203010602030f0c0111041d1510050c010902100e01110d0807050a02 70
    0x42501c55441442042c1c3c0c0c0b036049404808414880d0622903a00f20402c680204041c1111801900c8e521740341415000c1c082d410800d0100040501c01d0040701d401001407903080380c45403401f001d403030002d500a1004440d0041408030001ca540c070b0300208180f0940c911207280b4145442c548402001d001d00394003060400c505013001080c801c030b10710701420601400000404643d400e103a5040885c0402d4103c002c0c58000460811440d50703074420080c50180306040700f0407811402e0b184184d145001e400b4641d039100251008006c42c4003103561280164102075030b034102e02e015040000c0d90880c03000f8050031b401a0810003800c0c900624000060a240814000000b140700700385124006940007070b0085500c0d02200c9a0310a07600028921664120114002d01060840180b0024000c08043c0200c1018014041859524068290701148060350003400d40441c0821120f80200072038035041615002c2000c034a08004c10000000c1e4030600340079151a14885a1541d04003940c1c2c2d600145161070031442510 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 567708399 1250 567707149 567707159
    0x1801110a0207080f0c0f010507050a020402160201020607030c05030a1107020a0b0406120e07050d031806050903011416081003060f0504030f02010504020d060b150c102d050709 77
    0x440100328900d00c0d5400740c44142e003002921410320140d24482045030340a8a91124156201400000d018a0900f8800e030f986180d440d0481c00e003840b168001e90302c60303c04910500c20000d0400d4204e0aa4801d81c262501561440015422038401407002d000207481400020401c40c85036104000c5030314411161810591240e00045844189803c80c40520030b0100d4108030281e00a60508000111042c0c140004e001c0d09445650744d008500c036861203540f0b009540b0007814003504140c12000c45080f548404c82d40c99040280541c0c1c0b00c44e001500a40c64510514011100b10224a0043c203881e8104105200c003141c0880e40f100c000b400065850640108c0040080c0042c8501a011042040086110302e00340c103003e030004d40c0f004030000c15a4184070403c8011b07581d0b02d1240c0c0a040d444000080c44509801c0070854440c00d4500420440c003000644c0c05601c0000225400440c25000061040030403138000c41d0342000000503c52060021642c520300d807500c0b41d400451b405000307441e00b62803440d80c40b = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 567709649 1250 567708399 567708431
    0x191502070b09100608190b0c04080d0903020f1c0204020705030c070303170606030108060f0c162a08072709080a021005010b041206110a080a0501050d0b1801 69
    0x107507102c0c055940022001030036008a4014840100043c0010b07140400110050f003105410321000103020105000000302110781e04025600034082d12030440c0c080001080e00608880b03003a00050703116810300d0b500d40c0400d2a000004e50385035403d4140c0c081141c0660750a0001a4009020480b07603400b00b03000c40c040f00c0d0000c1003a00002d5010343d0399010500d050824609a00401410303d5000381010001400307412000552960029420001500c60341c0e21034901040c0c5019061002c02c2c9407030003500c070780140220408140030b003004126012030582c952880741221661144200803213500420800c0007000e001d0204441d0010030141074110142034400c0d140101c40380404100c0e0b00c064040764410802c0e9041104c140c2a415070709081155505003401c640050269100f203004000c070312101d1004001c22a0081200c84030010710352a01c1c0d914442c0302030306102007140c0321420b00e85010000075503440c180c1481184660009851740c000c2d29a03c201c000e0020304480d1841d840d44d22031844861000034 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 567710899 1250 567709649 567709651
    0x60302090f070e010c02010903020108060a170c031204050a1a070c030f0b06040b03061b070b0a0c0f080c040308031302090c1b0c1005032701020912191502070b 70
    0x2809000000d807802c840041c002c0c0f00e40741000c0c0d0402c0582c5150a0060760452a5581134a809007094100366031010b0004201d4170306034000c80e003284c034491540251508005005c003001001201950344044505035902020302503445816405581000c3c208202d000315420310f01480c240807403c80c64200140c40301d003079450460f071007101d40310103540b01c02061000301c00c146074104c401102d081c00100303042c0000030381d0344201514203160f0840204507080094041011101500d6201c00380000314503000c1d01c402c0041c038425034076401050142c2d407a0b844051150300482d200702c2c030700c00003241005d003580c580040c20341000b0407090505480c03003d4880136070f60304203106200310702c041c2e100340ea145c0081c8104030000211800500e10b41c3c0c08966111000d90311100c1e42d03081c484043c980182c803903441c2480c010090399480c041016882007001030762890032043d0010800d03203170181c803100c981003080e280041c1e07640f0070f8807221030058501c4000d40e00081c0b5000402000f8801c068000360801c0d0040e1030b0342d005010 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 567712149 1250 567710899 567710911
    0x103030f0c0609150b0d0c06050a170a0e060c040b0a0e010e030609102915070b0103050a0302010c0e09070f020127050606030c060f031e090a06060503061b0d06030209 73
    0x7540400e044c8942c00395001d05500842e040d101580b5446140d980c04000650b180943c8080c044080340044800384941d40140c00012403100c1442c41e41003034001140248000380320100c41d0b004100c0000c90300c1082c482260102c4406542c0c0525280c030803403044412810f0605054100803e80f06942c150759020844d10340038031045006000b00d20107088400c4c0407224120038003115481c0d00c1c19514002c02d0044101c2e01003413003d8800d51124449021124450f00c10000000c01014241c4004000d00070006100a01c5920940003041440030003e019182c1140d440c140503070107200900003807809441043c102e268060140000700d400648031541000e404050b0201400b03541d11510701c4014000d04014042e0044000e07009400b10300d2406012580510840103003242d0b0200000208220107608940b5505078842050700c0001c60500c102d025403184a40c20703041d5a00f5080a01c04107940c5004a88580292502410117503800c0301440c0500c8147c000e50310100c09903583d104000301588610810364030800c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 567713399 1250 567712149 567712163
    0x412030b03121b0c03071404200a110f0a210c0c1715010e060108090a051203040201120501060e0409060f0222090902011d0607061103100602150103030f0c0609 70
    0x1c10b44200728908079107904c0441c80f96000800411840880350119840c480e010781d40441c10401810725441050704c6c0c4005a584114005800c2d020280e00509510303420120034107854088140681091381e4541010000e841005a81d4194220b0b5900e07809040c01c0c200d00c0d04100586800319140e50050490750b40c400228400341150000b840c0740203000145800c640c2114100042d410800b0407099028020f0055042c0410540030806c00001000b20796512175205e0110b440302c950400c007040040d0002d480403408541010034040840780355004441c166201d550f2024210440c03182000003422031028240c0d0710b40e6590681889816403800105181031a0390001ea05944058030680f00e4400071780d200c101d40c20300c1c10140c940181e038042030100511110b012000780c00d8001c280010380600c100400100b89610389200744041003003041c040d52141c841c1e00d03083c018003580e0b040b041c0d80720083d5a0084800c1040d01e4011310020380101400448071400d4035004010b1811a40c400d41281c1002200755085 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 567714649 1250 567713399 567713437
    0x90405010c1403090607111c020a1a190c03060509160f080f040201050d0204090c09091506020a0b0a0612030c060605150702010e19090915050412030b0312 68
    0x15422401e400d0380314200e80009460740c50100b138a50340f2500040c001c04100310701e4004209100f0703420410024400d807001c805a034001c1c46040017964507a840305c01200c5c900b82882500b107440c4c190420107440b03144034140303041910030750350b1010004050b840140c800f49070755460045110b46510b0f40852046003981c0280081c1400200080c0c01411040100b100304510714080101c0060161000ca40141c2e0a003071064843c061510004042d004a42102400c0c529208860f1030a40c0e000c000c9900302d9046050805c44111901d01e8100003520304d00480c00540d010308040703000640c4443c50369500c80c2c0180000a200c0b900c810208596903041c08040d00000c5000c505401403000300d101d44001000c044404000c510242061f4460300e000c0d015010341401480344440c40d40d41c4840c4a0f8a401c8100c07030000c0060036848881d040c0c01042004070640300090300c3c0e07200c00d49600c2940304013401241c204a1100801c02e010100301d0161151640d0b0075003600800d010200541060000380a00204421205c002 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 567715899 1250 567714649 567714671
    0x140d050c1326010c021e07090c080402040b01030b03070302060702271008060402090610020f1020120606131d150316090c020a050d050304030807030603080d021809040501 75
    0x2110480c9000c214940c0d00d405041301015800150301603551403034520360b07086101010805820300c40940d001000071410002924006944120342900c03c4c0d108071404c0080d4101000111f0480d5402680650542c0c4030311024405481c1450283c14502d100a080040040d601024210308100111817410030307881031418000d43e42c40c1c4d01c0800b40940014070040889141680000301c0103080549401d0044440291800303c02e0310a00061280c0d4400104a402c4039030800113160051440d0780c074807250f00d0900403610040ca100318088401801c09011240303066100d09040000c1c0743c1c0200048100c03100c030702d4000107103490703001c076002c21085c0d02e9121003805150070040c0c0e030300780380302004d802e4401c0e080500d200c20b1009081c10508180d50018000055409103488182d00d03100c10030314042d00c41d1045111241c0400d0b0700200640c1f280d80b10380c1d12400d80307850790b400903819209039000050642806121821844007298040c0c0342040c10180b00e008041c0c5c4110106164090a44080e031313070340e5119101020703 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 567717149 1250 567715899 567715949
    0x10e0714040e030f1314060f0702010e03120306180105090105120f0d03060306060509190f1122050306070c080a21060503010509030c250308040609090507140d050c13 73
    0x8010b104181c024000101c00c040041d00d2445448d0f000c010395000821014196482403210480c030040c098119210507407001c41a40180d00704481e124030805414040001101504d14114126100640030f14016400d060030002022407411140d80e65105078a500c0d00610010480044030782036a841c0060124110b00f0030300140d030125048280a900c8020038010745090284102266145940340000d0052a004401c8043c1902031100d801c0d50300042500e00001c409518080e00d00d20f441c0180c91001e65850302456103e000c2112440c01064140d11141d0100c1d000c41c0041c10507451030314008140a24580004c1403c0642054164455589036014400c41c14244605030300014404000c50030018030b075800c80e80d40e0590104210124503102004210803d404d6401c0029550051407141c40b0b907242c1e4401002c40c080c51140c072040720b082a0200300518000c000301c107991126240d0740c515040c0f803000414040c18020b480707190b584400b0030400c051404800e90b5040540000c081040c3c5460f02c02ca1076138 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 567718399 1250 567717149 567717187
    0x31305040f051504320a060501020a330c051809012108091008040303110f030133050c01050a0e03120a021309060512010e0714040e030f 60
    0x10120364030700400e201d004200251001000f030380448010450300301c1074003009a21170303107040741c80c15041c60a035035000c002100c3c20942d0320602441800f004070710780d1500126900d45402102801011041c942d569682462800a0403c00009099015440c50220310081110301d1501074a00103000070032007420000100e16903075641202142d00c11110350401c07417407440c1d1500f45a54400c059580c1c542e8141000303680d2040d901801c1c0c3c0140102e0818000040c09020110701311400c800282c58202610408101030050326881582031031800d040d6801c0c07500c59008507034280702015413080301c02c6030740084e240360100d048002d00803640c0304c0b5203811820080c00d0a40c0d2001d1312054980c5e045c9620f9600781c00c00081920344001c1e040001d006a83c440da190580248240b03001a0290400e41c40007040c200140c2c0c01407400c4134001d0310802110100105001d08841060048005036080030a0400005c07428005500e2140344c01440082c4a00001e039032545154414a01c0191480c00130035040522a0844152 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 567719649 1250 567718399 567718421
    0x70503010e07140a0e0d06140405070f0b070308070e0901030c090627050601090306050c03060a0b030402010c031112031503060702190b04060b030105180c011107120303090503130504 80
    0x9504841600b0746990000e00410140600700301700c13039511410a0ba60f6100c19016150017450400000617001520917003a901202c040e80c06200b042000a007241e9100c0d554000c82d1101c260290070201745540403245000040c060a0802c00c0303510f0584841e54509074814002c1d445018480c001034a800b42d00029162268071409038810b801120005061002d4625002c035030400c1d40005a907522140140c8509195820140a4501e03000401c5140b801c1a0000e60180030115096190781e5524040034496120445000340000c804008481c0000e000c0c0044803043ca00c914103442c911100441142c056400c126181c1c00720003190035504c0c2d15810103014468015005101805411010460500301150088402025081c8000c0000c0030b12056600420300341031f00800070b0055007000000040e409060202d180c40600a600182d100b17580070b100c901120940e0040a0700c4143c0c40c18007402084100c070441070b800e02d5190500e08001440a00c0100210890705410512283c01c1c0810311044a1042c054 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 567720899 1250 567719649 567719657
    0x1503090309051207030602030a0e0a06060e06100509090a0e0d0215010605090102060f070201110a12050109180f0f120c050c010512011203020705120c0f0f0901060c0515070503010e07 80
    0x50f03000d8800c808a00e00b01500e81003080503941c0e44a0380c099800030300e030040000829000e109185010410b064200310201c1d1a50800d03001c0030348444ac01c01007a54000a80140030410400541105040c15031402d81c3c84241510f00150322240c1d17250f1542004203451041c00180c010030382c1c10072010f5401d011180034001a161050501d03201c0ccc1c0000c1c0d038990000e0040c003046500a000128194800d40000701907500c1242140c0e02d85c251f030140581824450030042c810f990a0400208011780d2920410b02100d99081c02c0031521040c5d615131041014146005482d22a000b100c0c000115081c90600c44d1410181c4d41c82c0b28241995003860350410070380d0500d0350f04200c0e0820806280c5000e40400905403107140120940c442d5540c0ba069140020710f6003e9600501a843c0e1000380520200341c40340c50768002e1b15110358a81d519020040e505200050842d0b0000308000140a02403250019203d807030b200d542101d048103004940c4050100040351040c0000c0c2c8008010301607281070414040d0003c4403814 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 567722149 1250 567720899 567720919
    0x507140106050312030901060b0a110d020a080a030e0102040308040b0301060906110c1e030d051e1303111c050a151506050f070b010b1908090d1404150309030905 71
    0x1c2e8031811300c404481da42000200102d48004000e5106100030114250490b590721502381000e09080d5000d400c1004c41e00034101c105000500104064a584d43d01042c00c1d172401c0003918003640204003c1d40344014541d400e11021001400800080002e030851198541c0c60b0f605d0200001c0070003007580c01480800c00c0c1944900d903000d0b0000b03141c06200b0740444202e0090191071101900c20359014980c030b54503218045840c00442e030014001d000300c8070444d16070f5001d102c021210740014494030129400850480c83c041010620f10038821305100c4006100f1360308a03501d01400548214242016a51074120b034400d00100802c4030030b0302c02c3c0310f40054000e120408100d41c00710070495151080b80c05001c00040c0c210140c405040460f88032943c40070701664070396160143c00003290442d00d81d03402494100201c030242c090051013001d104030500002440f25880003501154220faa0221104115400384403b28420301c0240004214440070794000a00d24400d041c0200381ea01503034072850080f24020 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 567723399 1250 567722149 567722159
    0x52a040e04020d06022a070807241b03050a020c0913120e040c02160b0408060a0213180b1503090d1110091b09111c0b060a0507140106 59
    0x329195038803640484404241d0b00b69030414030060311401c2200752120070003281c8002c4402c811040180300b260000c3c11500212303100e000443e6030f00941c0c092002a4004108502e00480c0344c0c00c04555116068074002034503001d040000000c110340d1400c110045200410f0504d541541044100c01c2154121b8030395a150400c0e8050034541e08100c03002410303030907402c00550b00701e600840150780380c0c0d08041c004000c480f00030340c4025210760a50303040c01c407601500032001a215000d0001d480c01c2d940448084c001c1515901c01e0072009601ca41d450b0101310031107003030002e519007040d65110060840c0d94008a0748102005c20003407081a5448808140401803091007404803002865241c82c10840c00c041001d80c040031000e500d4221042e40b001035a07418144904204070b50041d01c401a0049040c64070320541e15204000155400a4220007c0280038850f00401c0032071300340a60903120742e00200040002c8034a0203e029540884507081c00315200140140412010b0100c10740707820700000c020048203080c0 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 567724649 1250 567723399 567723419
    0x9140a060c060e072c06060304020102031909050303070b060306060a0807060c0804080d09030b130308040809180903130e060a030807021306030f0b0604090308042004052a04 76
    0xa4401401c116034901c0124050b00007006400040d0030740e044258555158200050f18124805d0750003142e42d003540c008125030b420701c03006690040b40c0c141c020754245a20754103c42c00c002503605260301003000400b00020310f500d0a10090841c46d00030145080d180c6069401e0510303000c405020a8018500035408103c8004c021030850240d131240d20b0003101c2a10036041c0548280180d4104d00264000e08007409000c1d50808901002c40384110300401c1566075261780007498050300c80010300407804020018000840120040c00b000800500b2001b41c00070fa410040d00e00314003108c400c000d55000052540d00c94864a690310001d10741780d480da4803286170141c01f05904074918070004148000c0852414110f6591400c5841600030301035081110507a207060500800340b001e00140c0718500000b001c240241000d001c1c41d01025050b484225064aa65648801c00d0094282014440000b4508901960744600070b0900403034a01544485054450040449a501c1e940001a07501000c001c1000b6030850 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 567725899 1250 567724649 567724667
    0x27031709060741040b040902071a090619090602120612010911040b0a032906150306210d05120709051309030905090a0504150e0a0f02040e03070309140a06 68
    0x4040f2000b860a00b1003200c040d054002d94101c0c0d140d07981d02007404101480c281e409009864003820320b81c060455803003109000c204003078510a40b10703000300000905610600e0041c0a00301c82c000800103c5014907113070358049070494542c03006400710b01c90611542d89440c1c82d919035847d9821008210303d0450380d5509825490728505070340100d440b188045115510070300202e0045811a820400c101c810343c1840c00000c0b02c440321892a0b2102c40d001c5961400c01002850b090240e51078510314640358142000075040750104610b5400c5503c44411341d00d4038081c441c9400e0202035884064075280c074070303070b481c04031901c0182500200603024000308880e903110103482c0c0c1d1560000d900066200c01d1070604441400b001c0e0802c6400c58404001d000e980f132031903070009100da0300030450900c0d60507105640f00c09803684858684a2a4448500304000c1550406548801803000f80005002000d01d003085055812a100c19808210040c030200848071341c80f40c0441c00c2c0c2604980c0717030380c1c10380c200072004c0c140c003003 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 567727149 1250 567725899 567725987
    0x40608040804050405070503070315060e040b0a0f061d0f09060616061107110a03020a06030f021c0213090506010c080714060114030d03270317090607 66
    0x808002140c00c0c488048111005081e0280c4180664a0712886c09001071b4010f0360f030000028500803000640e43c0581130310f01c040c1c90441c0e45620b20b1804200070040079100c800812a4410452100010a4510201448020301254660682844030741c16001000348003100c0d914055000c2001d0360201e9a02c86090941c045012103a90303840e0f208000300011410003080c0d000300702c1850100d4034401f245602d00600a0386104442124503030800c1c4090080e40e40d50f910000b50441c01507101840258000d41203a04c00080e500801410480403081546003541d204003500c0c181c640c000384d03460144c0661403990014204100d4140301500345080000c0040c4071031030b809001540040b40120030041c0030014201100d48e090100c3d0101d50312603a0701010610b80a0f803c0c0c0c46032141101a46000d4001d0180740c003003603040107170541c8952004025a80c030f000034200c1201040000c500c010045843c500f5880e0003a003542004005ca85070002000e0600c10307400c2c401d1030078000d40b564101c0b070301c01180424088000c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 567728399 1250 567727149 567727157
    0x301080303010312140d060512010c0909050903160f020f100c0b071e0e011d0310090c05060d020d0c0e030c040c11030a05070c2909010203070204090f050f120406 71
    0x1440e03113241120407002000b16210241c0002030140200981a00b00350287c8404890017000300d442d204206080705c0c3c0040c210b00118003142d00c104442e41095220319400b044650070389182c0740d64201c1c030610034080d0120848069030b030340d040c401c00c2d03003051142419000d074103076200660009100d202030025001c82c40003c00362118040091110392052900000c4142c1481484002041a1801404000000050030300003400340c5034186020000d10301e041c000040c080c0c0580107035080d201c004406800e00900644810008100010709a1680c10090211032515240107031183c1c0c002c0300240a482d00d42414004205020300380000b180e8020507008400c640c11500003a0032401d181007612007551080c4d0307d84060001182803c0e0850300701c40207108083c440c101340c00720755484003810007642c0d100d050080b020180c0e5582e040211204e0000410302000705004680c140901e84e0300080035680d40728004c0f25810400151541088400c00c40c0380a0305000702c001c5c050041e810a074034902400785100c0e1100b00 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 567729649 1250 567728399 567728423
    0x30703090b0a03142401020106140906210604051002040317130503070b0a181a0304031403040c14010906120b010e0415031a040b2809030e010905040203010803030103 73
    0x80c5009502803180c4c4e4002005545161400755050680c100390140700800c58000302c580002d10398410300c5000c00380c0320f000800c0c5075003065210a0080c62440102000d81080690b04140000c02246080da862007540d28024801c520382441c00605218450710344500081c0140428000112038915030740e40740040f180c0c00c948a001c00c07581701102d0045584030340c0e0036001e00d0300c0c04a902c07050480240b5a10400340c0340c404541051600140d81016507105071200c150241e0010300886442c80003c68000e4000d107031040b60381d0b84281203a030240d823007600c0448400305101c400b00314495240b00c2d51900010242006c0200b24034000c009062040e08402d10b4880035564110004107a0040d40c02081048024004110014004000802c07080107400b083d103021100000040b40002192003141c8610307130128409034503441c0c0d040001c000c1c103440341d0010704500b8034a00d2808042100d200b03d810280c06555201071400781032001400044441d00806d001c0c2e4010801880f8581e40001140e045a42c0401d1030414 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 567730899 1250 567729649 567729667
    0x80603010216030302090a0503030301140105030405070305010e07091a0a091e02030a05010e1b0703050a11030a08182803090f0803030405070905090c12030d0903031508030703090b 79
    0x81c41103020034005480c64442c04010301d903041c1d000d44003584042d590001c80320703212800c07d6524002403040d0450032000f580041e245500c90005540c20510590440b0002512039480754291611070800c1c5499501186040001103058010045440503c41851040d200303280040f07540c00381d1a00590070042c0d00c1d222010380c404640985090259001c07002103440b07040040000000d0701c402c1c0300c5c228030b00c01030001180d8228402c4800080012185040c01c1ca42103450380c01740c8543d081b00c08580c3c103112903900000d40880c0c05100505500141d69107110480c41c000500b070034110482801c3da030640c0d2100748032500100c5064103a1110803206818039110105529040321100701c2a0007420300207800080000d900c6070004081d40c0214415011f0b40c11041e160700d0400c00f15003040741d4440b0a9030054986001508041c1e03000250300d03005034207407442d180481c0003600c00e45007440012000681d55005031402485105003070700c081c0490102a42c43e00c42c00d514018207a00180c003c0030003c0c0000100074607 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 567732149 1250 567730899 567730901
    0x21030f051314070b1204021e030a060504170c010207030210052e08250b0a050d09020a0305030a0906090816060807030b042340050106120519030504050108060301 71
    0x2001289144d41c1d44100007140d82074007030030580c1d0484c0124100c01aa1070f40c08242100701c058410054000e2100d0169510703048041d290181041c0c2c0c41c1d050080c654983c66220701c0007400f040302640c5c00946d0b40c41991800070310b846000c9419500c45c4d880c040a104010700c68a0550760030000040c08400321003028401011140547d50000a05104590300541034040035006a5a20030422003500e41250b035034180011284500041840081c0c010050843c03038a0081d400241001d002038031104845440707556092850303101150550119020401c2040510740c00100c62004e424448054000e0580c407042801c0f014a6900800c4140b000800000300e40710303c00c0d8854600180c000b8418001281040c4241143c00d0300180c4600d10000c80500040200c519085e0591841c07000440f0b082146640a0040d909080d00c0b5154409200300007864001080007401140040c1542c294044034440b4249040d0b883c1009a40c0c0040c0419030a9a585c80801c0c1c0101c2601d080381d0003070901022076914080064 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 567733399 1250 567732149 567732163
    0xc050d020a110106031109100f0506160606170d020a050303160c0803040807060e1f1a04020c0309041d0c040903140310060908030f220321030f051314 66
    0x24039860030800100f1b00c9000078480c1c0b410788003a45e110741c1c280c450b600f00080c1600903010340d14460912400c100100c1c00d000c0010002244808050141550b960b5180d0040e07c003154094034032900c1840302c6d4491034105000d8502400308a000422055065075030710303922808000c005803010b000c00740307440002a018100e1702001d07940c03182006079030f450285455451a044541d0960b2500e00d0300d4a141282180000c1d50308a160010b070003004501d0390281200090441100c2c1150000130111210f002d684850001d800e0200b030420107940c584400780184400c0f10f103c071410105691300030214078030500700881e03401e2a0520540d00802d1010441c14244d90010282c105402482030010420a500307101c09150029100b130703503171851400e641d1000165503c3c081c002c0ba41807100b8040002805e540044101d6102000300014041c00c10760350b0ba00c2d9841d08000c0208456045004203140080060745803040c60b0344001071440030085401c01000c3e2001400340d0f11001042048020400d904040c0204180 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 567734649 1250 567733399 567733427
    0xa0c0308070807021c050601090b0f150903010204060201090b0a0207080304080c1c030e010b0102071d1b12040b011211040209130606182c040804030c09021c0c050d020a 74
    0x24024200510b5803000c04200745c0b401078070a809204004100080540240f18000c1ca00038042d2646224080801c400060035010007402ea850400400c28161001c0c0043d100511080d000010610741c541040750364850000e00b043d085d20310410401740040c2040c8141c81d04190000b901c04c0d124101c054034146042c1450141d038844640c07410000034101d42c19004090720607103c20081c40004400e00043eaa01c078918054100000401600e008414401042c9982c1c01040c08206211110369000110384990010098112003000481000148040c40a8150051000c11000050350781252103031009800c41400d0301c0d01c80da0b00014141180d40d41e203031117008108201102080303038642e900000f4090341c00c8001d0501802c1d201640c00114200c1c04809450665002401d96480b00a024051a0469030040c4204c4000e181804080042680d90715020040c00c442c180060703686040016103a0b11170a20300108200904105403000d505600c00f003540e4034080c4110016032110071307010341550200c002c4070345 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 567735899 1250 567734649 567734659
    0x200c0303040b07150b010206160306051c03110c180408091306091d10050603030403050715030b03030703021002030a18120e0306041a04030908061305070501020a0c030807080702 78
    0x40450b0260108004040041c4650038600a400ca03840d001c0d03060b10381041500c1c0c0560002c2c400118034682100386400d04074250b01e4002120b58071000040c0180620500d40c0c4401c11000c0080c05c101034101035074688412004009041e1040141e000460f0305202c14007109024203201c01040c00c0001103c2512043c040092013851588418000710b07000300024881e48960034180200202006100c0085d02c003041e10102c05040f40211640c0f160b0042c2101801954040c4410000000881d1041c0002000b52038008000d800c0809584001802e8580d54600c00388250810080400081d400190504840251280241c1c9a0b561000c0a43c010142208090901d00ca1030784c405041040d500c1001c00180f0700c607240e01c3d4512003014140f6565031300480703008144080c814611803511005509860703002e480303440c0040500380c85400035030a117001030b0303450400840d180340c0e040d08100c018412031010741028401001507502548400c40ba005c030034400586400400070f8054140019041202e04494010702 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 567737149 1250 567735899 567735907
    0x20f0604080306150d020304260f1b1203070201050105101e0807030e250b031b0913091101021c050d0e0115030515160c02130902270a020a200c0303 65
    0x3060b8a003214917003091b400c090344c010315000102c202c00c0192b4000c62002d0f075029040444183c00c2c00100b0310600306c8264544540c4c11082c0c09d000400c401103120318242d900200325945400140800d00b4001041074092010304105603095041d00100400c0031112440c000c0c040e501c0d01602540281880814030800e030145000c0504506114421b001740c00048440340c117a00d0380d44080d40b02090000b6108130701101070107003d0a04007501040903101c02ca1000700640100c000403006242165030251084a200c180450f024070b440d0380510080041c40d501e0701524074111a14440184948500c260316001035590305c0791417260800941c03020b0802049105c5048100d616410250b070360307881030a4100c0303141d6000c00c00546151480d4021200f0350b003442d115494071000d15401c200c80e03040e150700806041d0390b4942c1c41c4005682c43c0c0c0c201c0007888074070b00d4010300301c0101e201c0d1403502c481000b440b41e40090300404c505202503602100c0f0400d8150401c0a0140d51440d003c411410104203865556052101203 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 567738399 1250 567737149 567737153
    0x504111917130b0c0a090506070501231522090f080f1207020f0606041e0507080702010b030a0b0609061504060206060a060c02030c01140d1407020f0604080306150d020304 75
    0x2080c0040c010f8000d0080c0c00095480075000c2c0e10034898400710b04000303043c01e0020005410241e0103045000d00c41c1d00040f0f4001c80c13181d00f4003101c0342e01c0e82c01c41e0f83d081d0020050040031212101184403030501500e541480c004201c82c891440b40d42c1a444100c0c203695a0740100500124030002c0130b6035507028006e9640c07101c040c800d03602c580d0804502a80b8030100c680c0030400701c5000051186210804a01620859a40c4010031000f4138182141e001950000c1d10309200000c6144652403140d00b19403617a582500b00090300070f0869240d03005280c042d9019160202c007140740426469440b031000c8034445015501c11011800c5202d1544010098104c0418042070507600071070458402c0e102a00c100351016600c1000b15506104094040d401d0b0304000305401c110351007004108201900f0780000742c0303480c400c01201c0c4200c800d0702040781c0601a002040c40240e41d0b06120301c12124078800b00910281c00e2640f07401c0c0b868840917100030701c600c0d078807002c000404003c98295420410b91150454407490a4 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 567739649 1250 567738399 567738421
    0x81b0c010212060f010f020601060513031202010c080a02070c1a091c050606010306030b0a11090d0302030d0e060105011209110a031101111609020904020723070504111917 75
    0x50f60070743e1041c04d0705030f46880a540704443c007101c01600c0354020310260340303041d00a9580e9406980300003031074104080040045202c40407451220b51a80d4000210310318106c8009107800f201034403140591340104464400b01c0c1902c007201c0240e0f24602900300c468040d404004a4910880e10a290400181c4103802c001240303440b880d001c0c45005070255085903071180e00440c11a1458003000f4286401240030400b1607002c0e034004010b45401c0792900c0c1c6400396036000106000000b190440059000123440e074501d800c28042e000103050741c41c0003080d195051030000790101d86200c0e03202c2d8015503500c4819090004210000c40d50f03a01c0a417a001c0d089844e400c0c080302e244051304005d1301184086c0c1d0400c16441c000181c169403016030a14222080342045c010340003941c40f6081311940241c081c00071001003001818941340035140078942c560180051034803903013050101c0e4803840c8610302d00a8a954a000070300e045aa400e400e510418040c100000c4082d07a00c110500c414907080c01d00a020440d00c0f000f1 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 567740899 1250 567739649 567739651
    0xb1e010509132918010608100302060c01021c09050d0522181404050c0616080a0f140c0c210607050315090613021b0604080d0605030d081b0c010212 65
    0x8a043c50580c0341c015000e002c103c3d07035110350842c0702c0360480d0010041e440c807412000b43c0002e54050a60003039603482d000a405a0000d4848030542d075400035a808504141070080c9502c4603040c0030500c00f1241945902d510794110792014170600200060200b00301da0030842c04c0101c54110402d21003442e8851011a1010300103442a507895450481c8104411500104980c4120ba00ca8005e1000d090070700b05104068001404820b50580219660bc001802e0a405403200d41415594a2002d00c40c07684010040c000d18541d00c540341c44200500c0c102880d0200d004031410900369016002140001407082209410840c603c25600811060009180e0300070000d500402907844180007000041c010819070b203105503450f50740000c42e401c000b0700c4485150054040002d6400304881c98050040b402d40c1007140c215030450f613a500c005000c0340c14440764841da8000c0c09040c2c0052951401000c2c02400d91a07002e0f146918080550100c410400c001800712451011b00344025525444420407403006000 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 567742149 1250 567740899 567740951
    0x13030813050913110f01200114060123071113060303140a05091507050d110106090507020a1b0519080111070308040803100b070302060a0b1e01050913 66
    0x40d900010a1007200b4403500c1c0120307203810075480f1300120199400c100c00000b4a491036414005081c0ca402800b0080030803140004c4050400459500c0e07000030b64294400004040e9410700903074140305e1505205000c2000e1420507150000c950f280c00c107081541e030351030303010f901a0342c400301c0d450458200714419002001120301c2601ca00c800d030002c1c402c420b5514042d00c5007040004206110f04c0c40746161a0030484040381c500324400e40780020070380b140e50510010301d10400118141001c04039131440300344920b10003030469040c100000e04242c0402900c52140b603070041c08401000b0480c46c4455048100007005007030091240107805086881d20070010824820890765504e0444103007900c4da509002c4600d200e42c03650321405031359030b2599520485c4d04041c00c2a03940c0c000310310000c920b1462400081540d43c0c0641c00800c40e510b81040a0829554041c0e22940a4440b252602d41903400c94400c17242540001d080094841d40c242010038003104078200040070280c200091555001141035401d42c5010b = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 567743399 1250 567742149 567742159
    0x13020d12020f0304060507020607020a0803040b1210032001200a050c06160b040609120309110d0c050103020d0e0304060c02100807053a0b1c080409021303081305 71
    0x603086039020384a001358480e01c40883e20411031f6100603d0300f0710043c09480c0c8002c28216046481304c2507203141d40c001d600410610140001c4505100c1720040c60113601c0241c0b41200c801c60750441c4c2c0e03084000861071340181600300c00c1c904079202c20303800750b611a11088081240400c03507892944074036555200040040d00e160040412807159401d01c1b0b000c548070301c00d2083d800d068a010f0f0356645804040c0c014815070318580c0d10b411070310008541c9141150540003c2c3c0c0d0108011010307003000300d10302c64800c110b02d1080d0b4100c81e114002907207240d120009c0303030f00900b0b0040c3c5405072241d850014201c004404171032400700040100304e4a03082980d0b03103507450081d5440c8a40e945d1841e000d40c0c400e001540c0703090129106001e110b00c10070b009415044440005005040d41507692215a460541007000c0e6000940d01c801c201c00c428105a410000c204550501050b0b40054588920066108500a4901a50300080c0034100035110715003220041d580130150558410403030350049030130201c030300915202d2 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 567744649 1250 567743399 567743413
    0x605070f0e0114030106140d0507050702090f060d02041d01090c09060608090a08090a08060703050a0c03060308073003020a300b130614040608010903080f13020d1202 73
    0x82d4401d82030300410424040c0214075507400d0210969845240c81c1d0312030810442040f8140f00325401c1d005481c010f950a0310f40301e454000c3c0d8410441c4110300100700d40c01e5070040d0010401e040d510341040f00041a0190340c0001c41a01c003001803864071000064000040d030034203610008004003022207030101c6044040130042281c9500c0100c1e402c0300d098071030804661004171441d02062659000b0600281d0040904600319030301e4030036508100c2c2c01c4980b140826550010031103001c0050040002c031081a107410845981140e0b5030844900540501400a540d03100d0000b4500c018808081e202c0c1c00391550000d100205542c004020303600c86c034002000254600d8044004099068003007600158801d600b21041036140d218034014201401c0c06540041d01c1080501902401d100341c0010f07110340c50302d0520780e1400c00144000d943c0e00e980000c05aa01d40000500440d41c0603111139000000ca0580c55529140d070b15040251170741a00000c1e51241d442c0c8203140030403c070308524082c818000c2c1c00752441 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 567745899 1250 567744649 567744677
    0x1506040516080f1e07120e0f0d080603030f07080711220c17010906030506150105191434080d02090a0f0b04031a0105030c0f030a0605070f 61
    0x101d02100360300e20115070040d02240c1e6074106500115840f2604024003584015034925071095884140c03034103404601c85429041204d0414018038004c1d17a0004018150404100740c00c50352000c028484404200c030304000706041e0341d001d20846941128181400781c48050741d08000251f0303440f01e0001c407483c3d807000031060540d051084c10a1003140c0344c03100f4030716821240c400c0d01001d4016419050100a0203040c05c04401c90855041406050300300c000051082c118034150345060000303402c20540305c450240707818860b0ba100c01100d804c03015100c80c1401314074461200395845c192020341a06180780100b11003003101c14034402c03800c0070b4005402461424028008101d8800c3c4d000074050301e1860104180181e9400c41e4000380100c0c0000707000080440d54801425280c820340341c106180040c40003c0c1002440b50170400c60001103031001e0141280d514080000c0d9031004d5101284c6d000d1802a000640c40307607410b220201586402c8581405640340c843c00092516601411134404070313110f071014802c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 567747149 1250 567745899 567745921
    0xa05012c010e04060f14180601050f0f01050706091a070e03060a1815090c05060301060203040e0c0f0d27020603061c12030e060105040b10030b010e0315060405 70
    0x2401118000301540d9003001c45101140000400c2a02c04503210303902504190390501c64141000c100c098240e41d43d007400316504501d2020700d6200f4815034040e4005002c40c0e5a00e6540810b1004203d951005c1d1211620051303802d4064040082c201d58a408174907818041140400341c0004410051b00e2080e96464005644240b000c000c80c0750158000e80000703049040a86c0b080d040c0c0b64011750741e903440070025902c9502c424901d9000c103413104c1d00c4081c0081044080034146010f420704443c050f05546c10400025900e008030f01ca501c10706143c1c2d0780450746220f006801c8a5810080034121903035101c01480c407c0c06040c1d01c8800703115404003182026113200110919184850f4014000392540e111401000403003e142c441c3c04120341508a02d40700007801070042071190000c251004600602e406c20554182a4164811800740d406d01120200595030916800c042001c641800200b440c80000101c4001d586011059054130503089151240f003424140c091082104490502c019529100040 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 567748399 1250 567747149 567747209
    0x8090d0314060d05011b0e040b01020703050607050a03020f0406180603052715090601030b130b16031517061f060507060b03010603060b09100803030118060902030a0501 74
    0x581c188030918007040483c5082502d00c000300b80070310004540c4040a1107801d01402c0440c0340072000c1340104d0b150003000c0c209030194007c0c0c0e010900107001d8a0303185495030b54984000a005070100000010016101c0d8041e5056411030301e840130350359440c1c80c0c0303c54018000b003224807034681c2265500500011814824000e15101e42c0000b010a101080d0106034451704003c0d2070440c0e9454001c0601e1078980405042660740310b50000f100400305545103060041d070031035001d03114401e881316082e2060041403a00120a4014031541a00190180420f4040b0010500c01c50808034106c0300b50f00000d5034000801c2e40c04802c9541401307450194a50701407900c1c401e8501c4405002000703104100304105030142e406170841d94018038021400d869800700090845016800403100c680da2491004a0b900b00650815403101b46281c0d05c000c1d540c185181c03550317240014070039800c1d9038115028003045044250811402081c00075070a54076820090003840141c6000d014181d59aa403400101c0490401d00c1285 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 567749649 1250 567748399 567748421
    0x101508011b050a0c0f02090f10060f05121503100f0c05090d031110050108060708010605090102070504050c07080706020a030e07060c02190308270109030b0c09120d08090d03 76
    0x800c2c0b40440e820401d94104040304c02c10358440354644252809a03d40b9000240308000c0d80d40743c0101407a08601b080105560790f0860f004200300040c100c0c031a00c3c0c201003211103544503051070042a130745219100c09d840c1502c2c0c2c1d050307416004421414079080d42680083d0b4840100320000d0190301d8100314111014007a6041c03242c9d01840101c400740c003003030003104640c4600408006903440b0041e450610415120203902c240c40b01e5204000f082441c580c81106940900349501c7c0803403801c00c0040c0000c0d80d40805018840c880c60760748001c030b2140c1551500b11008039900a000580740c40d6607050910081d0001c0c8150030110341051610003c1090100740c080035107103a601c0c0c410700e08a540c0c0a020344160a505880d01250003110007001241680c0080c10b00400841c183ea40d58400c01415901c010b44010303444c6040c45502542440061a01441154800c0784200c10700d03190b10308003000608180b1035101c0b00b0720301d000d082030b9800c60562051000344264406402c860000b4004402201150159010 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 567750899 1250 567749649 567749657
    0x2040b0f06031f080303160912032c040c0e090106050304120f05130803030601031a0303040302044701170a0b0a0e09010f050609010506090d05101508011b 68
    0x70341210342c2d035580708900350504043c0060580c50303152091540d0b2080d10f0032840f07207000c2c01c04d0240c02c50703110340464050072070228010860086554044c10420021030480840c0c080750a8880e4001c80314a0f40011410703000340248403e0300c0d942e80c060034909244400c10300600103d8008182c581c0100c0843c3e0045a01c600d924802800c003900031620341e02e1810500042142c100194007403211000c41038005000703c07902469490801138009407c0715405081e0103d039400d00281c1c0f41703041c0e41c00f02c2034404680d010354003c256880c018110b2104403200c0940140c000886002061407071400448000c0208000b607903010100c1d800c84015145003989445c442e007071200702c40001d0901c041da0340140304402c1c00a4040d10110740c03100981348003010308032804080d683d9601c0c408402460702e80101e54000c4c405450107589941800085140c900c2401010ba004518903122001000b10030803c5c4152890b021204009100102010507200c0d50b40c0d1283c0615903081141040250540b1200303a400886e0301c0d01c0d = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 567752149 1250 567750899 567750901
    0x5150603070905030a080c0c0301110f16060603050705030f01020c0c101806050306010e120c0105131a1c050f070e04060f0e0703110406020d0c0606030203011802040b0f0603 76
    0x411a055100800c0041048500350001685441c100000c1d500244100d140742d8584602e01525494541201e10300c6109a040201ca2080d00f190070381202c400180c1960840da0b0390b02503541030110440131800090219192640001c203200300801d5420585038118140c030808a00d01d06032500340d00804078007003120703040f01c0d18404641c0f400140481c501c2c0024103200c41000c101d400807400c0f09590f68804400326a000041100f0342da4400c0404042d0f041c129a001502e00c4030b0a5083d60701c3c511525494184640020300c1d405105011941e40010b00ca17440031040040100c41d1521160b030055200911406014821032011800e2401418401c0d60f214680860568610600b251520048000a41c2203680c07a0004558034112011480c0900304041246c40b4904010400608940480e21074008214080c042441a1030f03000c100c1034070744402454407422801c1e0398140034005002c160b00095145d840c007814107848101e0301c00407010b00e5008a03010070030340d414002030020a01c014406143d00c024200 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 567753399 1250 567752149 567752191
    0x30406061703032e0902070c05120304060203030a0e0a020d060606081b032806060c02032b050307120c02152a0c0f01060b0c010e03040f03020609012309040e0105 71
    0x100c600143c3c07810700c21322404140d90300c1c00a00c040380d024032030654840f2503280091080342001c50700a0030461103200154501443d005009403680030180140c20301986940c0e11a10080041006000c80ba400070010005e0049500d006001040d8030321031007002c41c0702000001e502070000c00705140d6480c85451184d02d180d40c0c0b0409075110894440c0f0440f04030340e4030705002c40c00d07020a12520001c1d103165154192480c0d41350040620308000151840300070301032440119202016808a80004181414100e480e92600c2405540c100c1e080c0022003503e074038094060500c69400142203101401100c4401056101e030407201050004122041c0e03044030b1a18420044030345032900810f0b10203c20810b558994809504040c20f64815500c8810504800314145450301e50a105c1c07215081c82401c0107514003460407100c5c030003281041c44068400c1d103021400c124542d0180b14000d0995006900c4000050070300341c0144e501da0003643c65203005915080f150b45440c0e01c1481901d009000b404c00c9090444a44 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 567754649 1250 567753399 567753451
    0x13030f08100314010e0613031e0507021503060f03010e0c06070f0807030207080d050301080a0b060102030d150609051509150d020a02011e0504031e05040b03040606170303 75
    0xd03001159501c0d00c194000081030191010110079800e400000c141c0101c5003044520b80007019000b2104d201c20b11030700c6400240c2121410750a0002410001d10882e403910701a0b806018001000c0e4000c11410305441046150600851041000f150742d1154007101e00149401c8a01070013a50740c00d030f440782020030981c0c0f411902511085101d104003495040150b5940c0805408c81d2900310003580c0160024041620144040145042545002403c56260001841d550500d034400070703002c41030080c0401d615910901c1242c01e52251035000303100a504c02c803541a110141740c400d50703000454800b07000c5401d10302419070013240f000e018203007400c01001c0b0b001c12100c00b41c40030040b10310758402c0040785a201810300250507016020703000003881c1b03915119030558104078007107030000082c50003040000007500828a03004c849107928051000c0105a40d060342c5138400c9400c411180e10010041008010064000500790f4260450499140c484040105e80c4c900043d5002c03d2512900640c51400e100701c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 567755899 1250 567754649 567754651
    0xc040f0803030f1803070f0c03020906120309040c121406032a0f19030c05040f0b010c06110c010e1e0d05160204150e0f06060414130b2713030f08 64
    0x42c0d001660b20f070421580e91f01503c10b00302c2c0b0080700d81d0705081400b0810b502c0c240000700e0340410280c400c0010f00c800c04210503201e10600b014a13100740d940d0300203005003500c224080480520203c00400010103129198950001c048500c98030a00c500c0c01039070b484000c21100e00102807075801c0507000b280000000c01ca400b00941e0403540e0001442c1d043d0300140c0443c040603400841c0507001305000c980c248018481a2800d01e90038a11142c10103020010507640604a0091503403c60b00c0054501075080608006118014100c96a076003400c0000701d45450100d440d40800340c0801140c8000508109519204c420080280010680900035140d4022240b45040c8074144020f00000721001c8584400800f000d80f90080e80c40c65901c0b1003040140494003001c650014412500385080516104880c0caa80c21f14441850080000c40381d0329807070310007a0f00290b005900080165003c04a03808401102e00340041e0040310341c8000e040404c003004c00010411280e982c060355900110b00d040c910554403118 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 567757149 1250 567755899 567755941
    0x711030a0e1c030f1814010c020f030f0d021e0d110a0b0a0f23060d0501060b0703051306090303020309061c06030c080c0915040b1203030c040f0803030f 67
    0x12446240000400c611501d0b910524841c1e00ca41e5107030009440018002c400710b2441043d169481780d000e000988020100c3c40d000102403130801901241d600c0443e022205000f40a41c06204400c10000982c402090040c207900b0f40d60b00f168402942c0250041044810b120041000d03005941d040b030b405482a414121f0040b210001c403002210f55540320300305848102c50ba040100c0d5502d10880c0341d10307014080c2c0107034181f0410b4010040c440c20b00ba000700f4081c010b019a403003a00815000d0081000c00e400800040103c01030141e146d248608000e4400c1d441003000e9102c0031b4910b900820303100d000d40c0060007031341d40660046061070300d040c00f8800310754021140003101c07001580700c0040d00e00700e5005400207144903c041440c5a80341c09900c5141c1050740488510424050040125030440030046500003441140d0201d02000464041618003402d40c1240340c03070f40800010800401005801401150742032540d40710481da40b070050303031784070f002c107560044c003001080020856644c06824500c5080c0c4e = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 567758399 1250 567757149 567757159
    0x1005120a090f0515100b03072007030506010e0717090303060609010512070e210303130f0804060c02030d031a010f0e0d0b0a0506040b0d1202120c150711030a0e 70
    0x182ea992a070610300318806000c0c82d002a180700400010641c5030309000000c0c4020702442c1d04505109802030480003148803646003425841c1c11101980d4070801100e40159006001d54615503107420000c00449412150640821148103001e600845421207040c803a540507000345065440742020068903a220210040c1000002d0104844020801308040c0c002c2c00303203850300c0d5900f00040b41802002e071051404070228207044111075803552404003c4940c06006400c003905041c43e01d20300264031058200d8090032039040072602040c0e00d03402c04902c684181c0202c1c200c89607902400d200718203583c1c600085c20b00100ca428504205035005401881d50214203043c02d091940484001c5505600440c206449824044090060361601e520030140c120700705480611000ca1140045041100a00030040c0920210440004824030138888001007a9003020040d640c0e65131180b0050f5030300d200404000c00e41c9a00b002044000307000b0345d03007180c00b2500280a58141041c00b80143c9842645a020503044 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 567759649 1250 567758399 567758423
    0x603110d050108030318010b0a05152812060f03020409050a0506090c280e0a02040e0a09060b041526030703020102190f02031b030d09050c1005120a09 66
    0x31054019a4064000c03a8010741c0c032032030542ca400100c078690544075034a50345041011040f6807100358180060303e00950b0b12074450b80c4241405581e9226100e005582d02c2c0c0007103010422482811a601d01c12002030355403e241140340b41c0d00707004031851803156850b0081040e83c10401410aa00014110740c0260156458125a61942c40c100041260307c4030340ca800200d2003400390702d030210101d40da00c40309025424481a062000348007030b5140703010300c041400e0030800040070740311240c0441c2c010300100441c903501c07403c1c0b51411300b020303003a110001c40d8058240503120f4001d04081c821614451818031000703c44901d061980c2d00800603000c040c06030010a019661406d81c010801001650b02c6540010f81c2c8100c1c0045804c0e9841038620900100244d02402c03914080c0c4c00403d585411180d64210048400c513001040e195126410034024100d0802d1101010300c400400d20800c02c07842070301c1e244e12109400c03c0480b040d1041e021000d041200740c00200d8459081c5501c0860802d10a0481c4148 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 567760899 1250 567759649 567759667
    0x9090c020c03060a050106090b12010501080603071703070b1e0403051b06150a0602070b070605060d05101a030307020a09020c0c0a0b0301030c050405190b1c0303050f010f030507060311 81
    0x20a83c04840202c899922103004116076680810b11000400c1310b040102c3c01d000c100680302e50301031811320410741004481e201103040c42e0350621444004000040200742e0480081a409403a5000b08006480103041d8400068650716600c8682e070701c445540003c40c48540d5145c3d4180d400380c00071186070201c3c2820540e80005640d080094501500a0b00901400301026204005881450360011401c54001000401c030500ca01000d40c0c0700268818000300f2141c0d01d890204e8400b5803607810240151181c4101d03080d55440c1a4420740c002d5170790306007829844010f102450340c0c0b03204803c00203401c006811001c000b00c41255015014150031641900d00c0720b46c40b100081c080d084250400341038020b000004204010120602c5402002c081e2800c2c0524a0466490610b4250703090b102c0100645400c100c00481ea06c1d060f48660031290a17851510000701410028000c003000c59503200d208109800126200d10446054000c0700d60000080110360704000080700900824010030308465018000e00351 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 567762149 1250 567760899 567760903
    0x60e09090f10021c0e030a030b221b09120f0c0b0a021c0801060503010311040e06090f15061f0315230a1a0c0a0503071b06020d09090c020c03 62
    0x140500602c02c056203078480080c030841004a01c100c1e8503081407804140400344c850100c182d85005110b4100082e07841100c0001c1181002c3c10100d2134100c81c1c2c044080c0c46800e540b82e0007008000a132103200160790501690548640c0038500500d801d4440312101900001e44401c20000002e1013002094000f56646080700380c240c1014a40c41d0258201c4201c07032002c200521100200c20700741e8640340e078065240150141ca00d10043c000030b4400345c025016003c494907281c001d00c1d9034038005421034066240c908001900c1e0f2250a0203800903003c1d8244c0b00a03c01440081d0601502000384024410180c0102c00c400401410780314009150b01c071a1580c0c41010074117003110007880c03080c00410081344020800c400321a01012141d10404c1e4044080c0304c400f01c40312020141c200d90055166440c005c88070079034600000183c008100d0f110014040d0b04010a8040c0103490b5503407010040b0849490301010707030301c6140d625070410000380c3d2440d0401058003560411080c0804c1c9006540740c141034000824 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 567763399 1250 567762149 567762163
    0x6090d0c05090903190e06070213020d0e0a080d0222080d030b010804030f050a0c141b09090a1b0902130609050f03030304060b041107050601140109060e09090f 70
    0xd40c105550480820450810840d003ea20000500c0030b5850407008410303044c4040d2050305403804000785c1140304900e540390141100d000c140c0040030300c94002003a581078806980700245d004101410701e81c654000c8000010032003240e55010442c00d08000b94191008029082014a802103074503240d410b250048184404801611824010f014412030644001d420782d0707021400341741000b42090401011a03030200340150120010310707082c1d03503800050a040ba41d24408640140070500900080000d081c03000980a5050401e0b821622010501c44200301c05844100c0b0510f0a035000100c00b900010b01e409540f5a00c80a1041d0600b0040d499000502c00c1340c21005e0001d00360303451100244901900001080001c05d01100d200c072540446c1d0f00401d4aa0001400007403580c1d40302c0b0b60315440c0d9a607540101155640c035211180d16607001c0c1c00e003183e40355800e01ca96003800030340101c8103d440d4400c1e100d10090741d005807191160920418240032039080300500e0781c0601c1c0201e91034040c042c00107001032 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 567764649 1250 567763399 567763403
    0x30c06030a0507030b0d0809010c0302010f0c0203071209050915030a0f03050309010e06190f0924150f0e040218070207030213021e070c08060705070618110f06090d 72
    0xd00b031801c030801031304407100004039500c030b5030100815400151561044580300c21003031130116580042e501d01680900704440081451900780340c032640103140d0000150052038094507540c4040c9050300d1068070000d040340240e64000745602d00040e203003001c0c060010364100010b07040b00c01b22000368680300a80310f244102100001d2001043c0136034482c09000350200e0407201009806d9500340b82c0a40c100000c08044030b00700180c2c81f000030701d90f083e01e03560086810540110903188220030800c2d03c45248480d00300d54001c014981601032200c0b07150558601c041c0d6040fa54181c104a0908000000f140001402203030b0145841d103165004154508049009502c5038000f45905411481040b07560307040e032211113018510510135021001d0422000d810422807024146a440881341011000f551113600000d007684210014020300651005c02041d403540545402c2060a8503003120f40d121041182c0c0203418000c004001407100d03e0204c0c010380c1c585200904561906c1d02400109101c0b40005c102 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 567765899 1250 567764649 567764651
    0x61308060c12090c030d0e0f06040603021216050414040207023c0f0910030c06020d080a140f310302011401150c0602210108010b06041211030c06030a 66
    0xe00c004940300d02d262a500088200b000d486103290060229540e99502850308080081c580040f0000351110341060325035aa001d400d55079a90f407601c201a01942c0b05803280001b0f8082c800c00903001249600c2d4201c2d0390702d0950383c1d452820349040308280035001c0d001640307070f0312a130b0802c010001030b56216604003868201d1a0701c0580c01c000e61801018000c2044a032581402096070b070040c16594181c4030745294a0121100d00142e142c0308450004071440b0b03000100403607402ca0001c84d034103400040c40c45101801b0703076034954280d641301d07181c000b581c99882505a074480300002140d2040030704d00c7d050350700c140b0700b02c2030300442800d10400c00311008111010001900c080b100e04428158280141a200b07020710702c198606504d401552000312030015640d500304130b00b14885108005094040b281d541d02c00908414450000392003c0c09010020311440c400d961030015484410b04000307040da0112003417140440381d0080c55032200d0800b680d83c4c0c03001603814099a044919079031740c0c0c0f1000c1d50140c0c4c41010 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 567767149 1250 567765899 567765907
    0xc150e0108281506020d0905060d0b03060408070512040501080f0705090d0602031e010b030703050402030a06020a02010e160b09120a06180303050906100b211303121406061308060c 79
    0x40d6040003c1030340d04001d0031900440c001da4141600130b0f0b04142107400585a8660b20f07081d0185210007000d000b0085a8107004460510040c402c0c10700c06806000c0c0100c1c150b550360000c0552001d41d51156125031804200c0d6040000c81c0f00c0005559154803a240381000c0d491700b10300c0400248501c420041c01c58a599011080c4a80c2c1e1415040a4481d07003068124880c0310750400074101d4007400700401d0740f0201900c0f80000342c115142400510000e6030b11200554860310b4040e0041c0c042c14040440d03550500c590b0705000b40c04256030039201c00310780c9800081c51406010409002e95030307038102d08038482445200406da001880e584203043c007508110b59034017486055482c0050994102400c0000144e020300144042070050100030412164030f074648641e1129070100000040404c00400c1c03558820540800614110649498000e0352007aa0381071640b0128242a000310b442c94048040040b10302d0001425904112004144001444541b94105a591a08185442d07012241e02d125103001207 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 567768399 1250 567767149 567767171
    0x308040b0c0f0604051203130f0803070e030a031209020102151f081507210c0806011404030c030f05070e0c1903020c060f1503030c0a0c150e010828 65
    0x400700700c80400b6000c018101c107042c04d443e03241c1c0c2c1c0c4045200c0b1580b000400408a0020416076408920940c4e02c810b143c02070023241c0c10314464540044500401064107006920035502d40802c1e02c840541c1d040d00d03007001c1a407000051200800005508905611a01e6040d50040904c112820320540d0b00001c008441d9400321038010b2800b241e80e00480895024030241c0c3c400204043e28954008000e00c0c204510094105a030710110807a205141c0d40b42c1c1c584030300312b46030703e5000c44194031a1500ba22400c04511040319a611503108611000d40038000b601810300010b02805030b600c0515018400f01c9941d503458182d110300d0003000303480c442c800c0100081c4003140034140100941095805050071030a200605031300700d031070700d02c000c0c80b0102c030100c08400160303603900a044131234190b00080c0440f6200c1041c9481c0e00d980c0c040c1084281c60350304407032030002401e981c14484810418415030340c454007691001d005503100300d4090901c100346c694401d401c1641520303220050104c11210100868185414 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 567769649 1250 567768399 567768403
    0x2100f020913230a1409030403050f0a030c031817010605190b0f0c0a0507170d0804050c0910080102070b011a0903031909050d05060621070308180301110432040509070308040b0c 78
    0xc00a030282c0222840740080b94104044201003030309801d100842c401060401e000110b2190002c24051007094001d14740500150b00201c02c0c0d90060300d100b29080c2d5039948014000c0001d2281440b050750811158198162940107084030f922030704220ba035500d001d07036a02414103203943c000d01120041445e0102c919081048651105502c60504095904154840c10346801511808074018810107022484002e040c451820040010030021501c4144525044000960138890301c01c151511a110710350032140b8108071180410001c0c003e40ca0949542e5071402032244500b6048180190400005170f00d46691083e0740b45c9500ca40050811807030500104000080c070038807031400081c00928401d07401c50700000c4200540c0c0d000315546490349a84420b290300b40072220348040d015420f10f030000340c080c00c0e468007920030b481c3c8051401d0080c0640301c0c030103062490307481c191240d001c03444400d140071410b00c6d5104541050002c0e041d661156100d03140e5007055403042e0300581d0001c0000644917850b0b241 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 567770899 1250 567769649 567769663
    0x270e0c0a0314070b0909070c050f03041409011e030318120602040e070207060206181c050406110a08030f040602210603010c030509150702100f020913230a140903040305 74
    0x1011016030400c245e50b030201e80c07100300040c038013820b01c6504030100003400b07000c0003031400c0450000d040700e6440e51140104005412041c42d03040c0500b1000002083e403900070440d04e0000da8411194130219465a102140d00d24416034004001030215640800c0d803050182000b6140ea00a007005039540749818464500c410004101030219040b4038424028a50302080540d0003400800401c1c035a050106289400d04100c400c2c000310f05642030104200303058104010703004030303501500c5000d40552008200d40d00c0707902c52240144503140800c000f5258500c00e40c10160814019000141041403030340075081c491590309188040181140c0c10042d06203000d0140e0140c000451400303112074203250340541e0381d40340040030304490304e4141400110103520030041da030500c6030401c009101d0800300384001e6009611a4400600868a030714444180402c140281034a4100340456651b01040041d0360001c624005440480d0180e15000403042122024217071038007c5075400061a500c92551034403d1170252 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 567772149 1250 567770899 567770909
    0xb0114070c060302030a0e01090b0103020a0506030708070f050706050f06040516091221090602070e070507060c05160c0509090c0603070e030106030b04050a030801270e0c0a031407 79
    0x20400811000510040105040394514203015031291070780944c0310007902010407003170b51540c038254214050040c44200181260300039501c800a5945032000d000640c441180c103100400c1c00e08000c5a19030344102e0001c40c40020302d142981c1071900c1079440e01c1c2030ba0350a0340d591403500048424031459281901c190354114440c0300800290748205900a0b050890782c2c490408040000082c007014001c11083c46004408000881054081010740c054403c0516000d1000188100c04001ca01d000041101b02e0160049442e414282425a0385000140c800841580100074051040030400e0a81d80c0215064901ca04254a01d50b401e16083c0910f2083c020140034480e408805a110b40303480b410300716600f100d503c0ca031411001c021040420b002d44041c1d03000074100820101000180500854035076070302e620a660310030150340c2e2100003180040b0b81c1c00301d20100710b060802120709951540e220041c40000c200030741d5081821a00051201041d40d4002da4408070004030054507800d05116003400f40c0 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 567773399 1250 567772149 567772187
    0x1401050a02190e04020403080a09030510021315090b0310230603010513020c03040b0711150406030c030b10030e071a030402101718010b0901030f120903050f010b01 72
    0x2c1c0a114480702e580080d40391010a001c00400300060b561141e030100c03005107411205059031600750640c010a001c41c20310094485010f51040d00043c50040d0080758401030040000d41704480c207220351001a0209040c0d04014800003e400141c000074071005036202e280710401c4108650314004007030f5608015111508014802c1d01503c08095032114281c82c1907c4040d200051080c08440d6140024070500440510701c1c48045000079230340c8050390007081388a102e9116056500c1402007441082d486441040308510b5081c002800750324401d5010410302e0040385004500080414003040a030b4030b218016500207512880c909004000400c000b400504003003215100a00d11080c012200d8000074100a107d00e201c03220100f0039610030045220b141040d40800822410040f0a1401c2104039800018595080c0200303e0b595203000e915a5049a42240b8491140e07501c90b6100524800d0704220b101c248041c127040400810390811260810005480c0001084840700700050011300804516814030 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 567774649 1250 567773399 567773407
    0x509070609050103150b07020616120306090216060507030207021e101e12021c0e0706090302130c1110090b0f01060c12210504121b030f020312041401050a02 69
    0xe8040c005d0304000f1070380d8031800252159141c0c0f000078818440c90741006a00401580c5000070b10161460340003001c1c01c151030800005946004c410141c1c022480d40e074008400100212003c19820340241c1e9100b1305904e001450864142d0028000d030601000e1100340d110200441c6a06007810500203401d911942401014007002e10060319040d85407105900801110368462140b038030154040e00c1c1c00305070b20303941d00c14034843c6000d01030700520700c0741800c000c54400c0c06000242180115185000c2d41e8010707110011400304a40c0741405042c1c0130400b40204914061002000741c001e02900303603aa0070800d03001c910369845041c082c04420002d03000c20354501d014030040080b160000903100c056a48180c0c048030070201c4680c20f554862200072084515a1000c200c0c14204040c0d6120f54401d5214280c5081146161001212120360b4a0340e01e141103c1900c5007400824040c0c04c0014001401e031040b00c0c944100c0c400c83c107c0882094070111140000c00c8034405000701c081c021030b40d108003429011410 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 567775899 1250 567774649 567774671
    0x6050f07111b1807080402032512110607050616020c0f19090e0a0b01142b150507030c0c0308011707051804020306101d06040902040509070609050103 66
    0x482e100240d1120024544811810242c1c41d00d11070401c007006606090703115403601020250100c9400c5504134441e00612800400307011112881521620440d40240d4400c0d00b401055007803020002425500c0840038031001e016a660a0014100c0341e00c5480074080c941043c550380702008802c0007114040d500b050020021584a00c28001000d41049030444078800c1d00c2060000040c0164210446903400c00c002c0102c0004001440204240300b03511901c02a0380e1440c080d0194480d504019501001268146440c134800100740c1403154a131151a0340b410f1840d6541d403590450102c039203808ac585400400010300d826225016441d0500e082004008003165001803044105001d10a12400d240d06c0600c0481d00400c000c81c0504401790104001c0903901190034007013581250201e200b031048000198420030410041c104440025050460210b8160360900c008031000300000c0d005507a0b1181640035940f107006190040e51000050000d00d82407a900801c040d10b160492410325040c0894011 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 567777149 1250 567775899 567775903
    0xb0d0603032028060c02030a11031201050409020310050f040c0603020c0627060408130609030c03120512100e0114010804110a0312020c09160804020f040b0a0306050f0711 75
    0x858408211800b160504058854400c0310390f00c0c20141c40caa1809128541403a000001030401030041e40383d02d64a07008034000300d80c0d00d104082841040d00700642c010403550600d0f0b0403200d000c6200501356101030614034070203000c807101120500450313402c230f60a10003400148038000380903001360310f0250714000001040c00d941e070300043c0140d95945001c042e401894001c1c204900171740c81607441541d065080509004685822924100d109120b502c0c80c0042c1d541d01803003091049a134003100740c0200c03501d0742d15020f42c1c9503d422001401d200f020000303014000e891501c2c45120720310310341d0580215403c08010004284058007c10a280c05c8d811504940703a030822012a0b1141e8801e8001c91b200d210f10010400540031584001e01c41002601d441d4801c58010032810410102610b0b41030840d544c42e501c10051100c5144180e021036103160108001d13041000c4003081d00d10010300f002c510110000042207183d1000e510541e062555a0144002030150601090300300c1b16514103101042c2041101e10703 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 567778399 1250 567777149 567777163
    0x5150301031a09160303021c0e0d170405060c0115050625050c041d2b0e03120d0606020c060301030b0f04060f0606170f07050901050a02070b0d06030320 67
    0x28082ea0750389400983d03110420451140300d0002404000000c1d642e03842d029590f05009085101c50096400b150f0701071503c5100781d80d040c8980282801c402c407046480d0007184945a0000f001009401c21011075a91540c10040113010042400003a00006401c0b846904000c1c64010601c0b50808001c201880c1010720405000785890701003181416000c0e02d0701529065042d046140c005d4200128540d0281d00500d10041044009068507801003901e901d02600c090926101080c00003980340a0241d6071180101d100210805170840c1d08880800766405202e0300409030408025440780030030704c00c541d814024401c0300300c03040d0740b19400c41d4110f0791103224815000b4880b650078903a440006040c040ca6070058116041405410002075480355070007041e06807e2103e001081c0c150741c011602001c5813990031403241c2c85030792716581030038030750401101c680d1b010025a00451289520114031007184100520b10010b10160000e221071461070007a1600498240c2455598400031200040c4c0002090213 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 567779649 1250 567778399 567778433
    0x140105010e12010507030504050f03031e04020f180108011a030706050a02071a031006050702013e15060a0e01031502040b0c07061803030c1502120a060515030103 71
    0xe51100c041c0465003503140c00b511035210f5800c040900032140c0c0c25520132401113000314242c611406207a4215550782c030094411030326840d00c000c3d00f005030010451180c0e41040c401411000c10781c841c01c0000701c2446403483c6403078441b900c1c040104a44102485032010500d401d60618003c441aa00009d403070320180d21520040c00400645440d409109102d080007403c0c0d4400103645c030440403100300c8040e0300b045490906100a9407000300703040d4003030400d5408040d4165a0315465054070400010095081c0e50350703044590044031101b240c0b800c0f205203c1c1c0c03503a0608008080800354030700082510381015003180d0003048480b0ac14080c0500302014079042d22f07001049130303031165140c460501c003d2080380d0220380240d40c0800c04010000c0085100400c660081e581d20040e1803032521541e0032441b40b40702c01008144420018030010b52040600701c1e4452003503400604103110414440300210044035440b211540c0c0315410720032450b10014100c41d00b408401110b04640c1155039015400003050f06e0 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 567780899 1250 567779649 567779657
    0x130b0c0a020309030d0c03020c0103021c0c0e0d03020318060f0f0310091404030201060b042702130807150f0e0d020a0b210105040b10201506011214010501 68
    0x303680e1425000b0811a904030b00098101c80070959508402040c00c1d4000c04110010f01824000f00c0d050742c0b2900030f0326035141802a01000300c0710240b0410005220381e52002062150505002e06c0c90380e540c517034401a89000350081d59403a0302d80c248040c0040c8424064030321401c410306c6545050b408150590300e078144071130fa107960f51740c80ccd0314a1107641d408190310400003181031031071514101c50000c2405000c1c6100b50024086680c50300d0907036030315015900610700700517050f40302c1e000e50021140c858118a81000f000528151182c2c450790364005064102d041140c0c0a46010000080c41c22013803000c1417102d00c1c014460740780c1d00000510414100000c0c40c49000e4840002e815952144078a50080010940c2596503446980e1329130300300030030440038812004409000103000c1c203046c0605100c0300002810000c8110300200281e51400c00040c091032162019070a2140c40c607410000e804440703001403404101c61910f80f00040c803802002c2c203504411401d15822040405078200101e040d9142424 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 567782149 1250 567780899 567780907
    0x307080a030f0c0206270108010b1c0f020d060314010b01120c180311040b01030207110919050a02030f0705070203150a11030f0a0b1c060f0212160305130b0c 69
    0x482162400d18003c00a54042d80003e145001c03100c440c00725806164007800400031202081005481084003440742c010854403c02102002c0800b00c0c44880d40050980c000040c0100010f80e0107040381c00c030311107002489668000600074031100c8940c844001c140e09009000c0340700b0280000b0414482900b1500c2001c1d1649032580706140150000707071008140d0807181c22225174908117031002d00d85102c1038600540c50547ca4070190351180c001c1303a004917080580004c0284008085c4420364400604090b841022100a02c0d000a890300841c1d00a035911100541c89017171940050401580c09403040c001c1c000304208a40050701c011a00001407101007005124a60318820b0f920050704481e04803900f0414000204800c01c840460000c0c000c14019108101c0b082d8aa42404950b030050f01801040d240c06498030000a402d903042440c24030001d05015060040300452081000410f8400006580300007441804c074543c18441d461340320300d0301c000051501c102e40d1600030304031001030b2242e41a210001 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 567783399 1250 567782149 567782177
    0x1211060a03021207020c120f1e07030807080702010905121c1b051b010c0c0e070905090115080f060d030806190f0e0108120d0b01030e0d0507110307080a03 68
    0x94195101c0a01c003400f10091880e24400c025151440c0350701c014850562085141c8804000040c0c2c03030100d260020082408650341082c05000c50101c020051036403050202c00307c0020850009018004d01c20f40030785071039101c144005400e41c00305400c200e00074441200c0c0030f003001d200010850b415801880790710125540401c005c0b907920003440b0942d501d548000018404001300000c5045050140c028800c05010040b001100c041c074079110090804040000103100c3e82d050345d08203d401c01c7c01c508008000b03c0e42d5a02258614809a1144541201c800c18490301503401c85e4082d43d10001078034031045149000400204d00c405203c1000d800c000e000c800140d49611081e2410f841c2d1712000b000c00c444580d50300e6000444034a1400f03810b441d40075030390000841107000500c3c0b0f200003944401207402c201101d01c84d01c1c02022000016410140c45140000c110441070040a20722015544c0c0c2c1966941c1604084d55480540210140260f00035101080311035000302e86040f0440d070510b040c00c0354070001 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 567784649 1250 567783399 567783401
    0xb012606030a0602030907050f040b01080f071803080a0f02070f090b0d06090501051b0702030d05070213151401140304030302130305060702031c05070207051002030f221211060a03 79
    0xb03000204500d1000003800a0a040000d480c003c131081182d11a14a410a40611054036100a0814007044514003c15180805c10340c815520001c28a82045660800d080302c000c0d148031a4070a0361503901c00200b07140c0640d404101c2d02c0c45240b85000501d0550725110f802040725840b0701c00c42c0f40700d81c2c2e01c1010030000da5442400148044d0442001c2c00820400e04241d8001e2034150741c64621141406030140e11814003600f6034101b0f94000b406055004800581a00c4a0344a040103d91108002100e003506110303501c03031884241403040c0300107003603810106100744802d06175403000d041c03164850085141c00310b4603088039403065140c0703405615221041c0303c1096a00700c40d040281180a040304011b4110b5001000d0071100307109440100c3c40f64415501c3c00c045540a54081c8016042218180002d04111141412120a51048034909680280201807a40211001390b2400b0000c40e610306a20103c034a0f010302070603907450141c1400c5100d41ea00c846150011802e0f500805000c075000120f00e000f = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 567785899 1250 567784649 567784663
    0x70e030703051c17040506070c060b04090b09060603010207170705010e190204050604110a08451c0c0602090918060106080c0d15050a0b070302010b01260603 69
    0x400710840d0246680c50f210b204a0316403800b0007000162072203030003028051034002901e01407a081030280c882912414001c030b47e00c0400702000c0c1c03409a01c640000b007007070321203126590700170303008020440e0340c1c0c10402d68090030210068241d600c242e00512a44020545080708180c3c0d098605003815034800045c80c00b280541000d2800100e240100044005d002e00141c0601220a03c2241c00300302d1a07592404000490308280e42000c0d51050502002d500180540e4145030405884500c21b10309201050a0304c103040c5081040080da6440350300c45400c40904176210055407120040903110041d0845584034010004422410400c070164585109010b0294100c821454000e450444581b8004101e900440c0c007900f0055072a01c242000010414440c00031a801b034450740107142d1418481e10051805002e41c58004100c41c0b810410000711607450a8405004043c0c400400c0c2d00c2d00c4180c2400703400c41e8150311a19051140d40c0440c8000030140382e400c034031600b1840c00e00100300d8650801107450044 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 567787149 1250 567785899 567785903
    0x11808120d050c04030b0604020d0b03240a0b090601082a03090f010e0c040f0b0301020315100c110103110c0a03050904202505370209070e030703 64
    0x240c02290a00406808010100960074400c103004030b80b141c201c14056407080e44009484440a4404503415240c107400515130882e100030301045880c403010001e410880c000700c1c420700300c003101c098901a178590003000b01c0e0b00000c0302d181041000d110b440070a0714204002c103443c4c10080e0300400a05084841ca889460001001d2904034081400780011643d82d0b10945401c0c21a2181c0c54103006046d005000d415410741e010800740005201c1e20040c080600189400f0512054441750654242d0304c091024500c00e1007440039912951200c54103103d03050120310350302c40402c450206207001281c148114000000d80130b01e80098450881903011019014040203600d0b5800394400c4c42003032581c010040c10342c402c403c0300c081003418244100301a003605401500100508103102101181132281020b1214261480a8046041903941c59030f0401e030030103880c0080030036100810300d001c5501001180210100012007090781000b500040c182060040c1035000b0130400741c0345c0040d607803800e02285000715 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 567788399 1250 567787149 567787153
    0x405090f061501090b1309050a0f1103010504320a060321020616080c0c0a02030628090b1324050a0506010201020f120604020423100e0f011808 63
    0x10805402000c041900042c186001620007040440d03880322140480b0011400780da00e07026028034206842015040081203050b020342d80d04d50040d5184128062413001c4280201c41030b5996040c01304210440e652404103a990106548480c038000d10441d81442d01548800e120407401e9850b608080702601340c1e0b420042c902484204002410004104944101c0780150203850340c954804032031810000e0482080c800003908203001ca0860302251000306840600b420a40e81071841b203802003880d01c4429512928a48070300a0b111034100c0601d40903050080c1d2410040c024851251a0000c0a070b0000d0039032960905421f0003071041002e160a04008602c03048100b140c40140450140f000304012039140180310304140010316690320620031150043c02030740303a0700c1c10100c03406215003440c04014404da0700650300700300124002d811000c142100440c1c0361880341c41d1704a08802d001c4125004407041c400d00400c030f89008040d07603c03401c0340c0303612007028a040400011001907441c1c02c1b58490f4814802c41c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 567789649 1250 567788399 567788401
    0x602070c09140604051302010509040f06060206040c08031603030509071710140c12070210050112050c180a090c0b0c0717031303030302091f09090f0e03090405090f06 73
    0x51001904102e01c08402e00c2e461280c40d03640d110600094400442c0c2820318841381008800040d07010300c4c050004c4200c0500001484071210f15040f040710000d41081c00580c0c091700400041002000c4010013911b41e003805542800101e45900f4012080000000d050540360720000388025810850440207210010020010381c2c00300c0c4205403542c3c00400300644450070050f803691124103200a040c003510300503401510b050100a4146d02940f0042c120100314001c1d03900e0113805407014001d00340030780007040c4280f4030034400d0b1900c245400d605100050051a80300c28060150b1003011f41e07180c1c0550211408280108180b41408036082950024070310701401160b8100524030009101d010b40c1e2840d51074441d2108400c02039640c4e40105e5114ad4280d2907520741c14000248207801525030b003203000d0040c043c04140d40b52103103429980b0800420004020b48020090700e43d031800785005d00b100d03003481005240c032441c50b999100e104260316640180c0d200d402044807110200456044502148165842 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 567790899 1250 567789649 567789659
    0x1112070315090501231306030c050901090c020d180504150e0f04051b04090f050d0801090915150b0705030901030f020f031602032b061217070602070c 66
    0x41c408031400301da001a4401c1c0218a0340070350302c11070f816509404400c0c0c2404d41c10100c2c6003e0780b074415031901e401500340c2035400c9021030340e4060000a0361040e8100100c0905040500044500582c00303561001d081c26410040389801140c0c02840b5441464072a8034210100e450304030a04c103d9101e10b420620300102c41080c056503149190a84510002c3c00f070f80c540b9030306004001ca9506a9024020f508002a881040090040f0071009050042e201195160300380c0ca540e00214000b49064503103411007102404c0085d4800307110750151010b02820001581951609855040155402548a07603030340c4840c0a56015043c2c03020042004041c02a03440c1d00601c0c185889401c8000c0c0980840e08000710341d512102c2c0c900942d940700c040d0a40890543e85c940c4100e040ca00340035008502540002c2040c0c90741001c05c4c1c49210100e60800b8259522803040d14a845c01300e032115800b50a0050050050400049024411603107441900084548411460609000070f01c0746c61030040c000008501c0000b0 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 567792149 1250 567790899 567790901
    0x4020c1209030c0d020109181e0203090d021609020f0910020d030e060103080f1308030c071a03040305071b0503010612050d0804170715090b040c06020f0d0311120703 73
    0x4614030040c0d0a40c0d0204500c442031107000380011304000d000c1100003100744080452030081ca4403660003000003007021905100c0e040c1c013100c0c8102000d8141c036000010800b10202c01c102c82c3d41001d0031403006000c40c0c071903c4240017402c03c40e030060303405051300090310120559280c0c00761200d0200082c00c0014611203001c2c0a9501d03004409080c01081c107049032000c504c100072070150304907900107918628101380c454101155072310149408078141d09541c0c010801000400160120400810060078a942802401c039282c4040c86140c0c60066010020800020b0740003060315034207980010549013031860a0102c8240440d01c2e0400d6801d5840c1540008514075545114403046000b07030252150030508110861324540c040f100034040070210386003001d14a40c10001480590b00a03030014600da5a09280202510441182980e003408420280418856003090030360040c449400201950760f0703c4050b444e11071202c2d00ea100c0900d69980800c1e50b111005c1c4c0212151044e11182c0c03403a051a000034060 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 567793399 1250 567792149 567792157
    0x60302122109061c180b06190513320a0b0d030e0f01030204092405011d190509072f03030406020304020a15090312080708060f04020c12 60
    0x19071224031201011010300100d541002c00030380035a00d0701100e0350f4401c804c0b66241d1440700300c080e039030903a40400d20303902018201441e02c6501c00818505018080020030100307503c1070703680c00c0040c0ca000c004a0751132440101408048541c0841d80303482c080b402e100b0140842d4104950000345004001e4400c208c104003038271a07444110200306110b0403009100c451800d42d6001030210b0864030000c1ca0320b181c8070794411120305052501514041c2c1710b50445003690101c90101e160402c0d140107044002da19a161031003d040c00386840726014098494510012481034059800303120300c0141c103c03114100c40e003800058800a030583d8031034100000010726890950b07030024403004081030350f45035007406500f052405080c62002142180c0f40c60b00d450009610144c0101c3e800303c015440068a4400010b903000c060300b040d102c0030300e210301c3c508040d0140b08958039880d04002242d000c0100144c0c200d0402c940180c0143c0307040c0860b08100010400a104400c5007003454416142c01d95184001c0340020 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 567794649 1250 567793399 567793423
    0x912020d0804061e361701020c060702010c092304020f09091501020a03051b0a120f0e06030f06040b060c0c01170c090d0606050402030408280906050d06030212 70
    0x4c2100c03020340b0b400311821500c03010850030740110100b4020710ba2081d0b4141070100d0130410802c07105250343c0d5080072049000e160010035543d40215600e00c07200d105004550b0b1001880c002404030b2030b40400700034403811007401805e0345280c2c1c2c0d02040402404032411600031040184c800c40da1848442348032041a00580181445542244005112040460b5195083c140103030000c0000c10204e90b4195a9508201c4080203446440a0016410030701001540c600f40d020f595419000b100510008140d48801c80981c0240074903007000c5401e40e200d44089aa01841c1002221042d40b11000002c000d800c2801d0700030307030080c1d0200b900c42c046038020580800038802622a01c2e00d4254014069000950450f409006110103100d44a1076003424142d02c50030350301c42c0000150380381d100c000080032030f0403c2d101503030100400b060300d03800c1e28003548040c100503044c51410101402c40c00382c02070051a01c1e00900c0204240424078091514198004d00c02031075005240d000010202141141d41d0b600441704 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 567795899 1250 567794649 567794687
    0xf060605030c010c0302030f16020901030309030c0905060d1502090a080304080706020a0b0121080304030215010816091503020618010e010f0f0c0c08060a0b030c010f0912020d080406 80
    0x703520b10b250302030b0481c92580c40e80364019608050801000507229007000074001755403c52250310740016a9075041003406107201c1c0d1a5440c034281103003440300040c1240c0d00a100c0c124601300030b00c8400d50340c003001103400c01d510051400c0d86542c900c80400c080c0c010a8038103600083c045070301007245400840034209682c20390341180c41e40d5917038403001c1b80d0755900d40c5e201400e226114001400b4029043d14900c00108003894143c90206071591886803d600c121820f030016008556000011202149468014000080106401c00008800d002082c81c0c2d4400e0a907603d9907039031545034188600d90500010b580080070749864101d00e6074280c1012007039014141c0015215654401298040c200003443c0c216695610340204d2003140c00ac0e1042c8024101c02e46545209600000c1c091401700020761241881c0b034000728640020506041c5009078000714641031085072440912000c3d07102911034104e8003c40c0e540314942300c0300d00200340b0550034a600a05000d10008001c0380703454014115140000300f00034 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 567797149 1250 567795899 567795913
    0x10090507020a060b061c05070e1008010320102709090204060504110403320d08010906081504060228080c04030f0b091006140a09020c120f070f06060503 67
    0x10022036120310b41c40048201d00d510b621646c5459994811907104100b800c100c511b070b20700701000074581c5034828482000180054014020400d00c0003400780c4071442c048031440201030880014607810300303501502080100c0c50030700b890141d509001a10818155000302c04509440d1100140070380f0468200ba4001c0341042000903075030800c0d1050403d544612405c4908190455403200c0c14498082004014066441c14044500c25000031500c800d01e2010001c002c0e80d02c0011015081d840c050f440344404a18182c01000032150103e04003554480c030b1a119841c903510b41c40d00342c0007400b0f516600c0402c08280c040581c1402c820031021002d02c04070341c95080c01c80c1da81031a407030703102d01c0742d030000404500500c100381d0700041d00c03040d051f50412418026556106c049400030401c40d4010380c0041441c501c4804500d2480c141504100080c0500003010341c900617400c188195584003030030004140349400070b0481d040d076a214040e01c0700340e90320110320350003d9418241903001d406d0700c0c06030314401d000b208 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 567798399 1250 567797149 567797171
    0x90a0905060c0702060a11010908030a0603020f04090c1a1218062508071e020318010903051b1f03061703120c0c0a0501090f0605010509010f0504020310090507020a06 73
    0x4410364420b594010038043c0380c05200f10040787c24844a1240c60010b640305c9035008005214ac0020b140b00d101d040c0d80001c0c0310352035401003010704079081c40c80d01d0113146040300b084040b415110501c81078441c405031006410301804400c3c0d005114407100c800e1611b000740e091080f06000501d2203c0d41d1102c59044600c3d580314840c0d104003d0288604044680c1ca4041744142c403140680c0c01c10f540161700d03041000344190152107043c0b0442c40f49401c880183c20012b100c580c119489110440304c40428070386140c80f03604503a1461360340e106051030200342111111003d100c5985040d4010400084401400d04002c18550040e002d000240030b40d038181034000b201000049000000d64001c10300c0a006401d20ba11a20031210041d800004107092501076000350f08003040c824010000440c2c4100c4002c3c10213082400c20204442042c0c01162003036208000401904100700c02c0401500e10403540187e81e525031440203010040319901400d0403a00741801c00c1010354000c0741030036025001c0c50b018840000d02c1 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 567799649 1250 567798399 567798421
    0x31207120305090d1e0e03190203012007080f0f28031b110c0415090b062803090b01062006060607060e100908071118041e02090a090506 60
    0x100802002803a80d120304001410080b00b22035501819041440d844040b0a021032309100000c43c9405030394030381d00a1a0214103003407240030b508089054040045062251740000580b007110005405802c0214501c1c1000e041d1804450040190380241542c40d0f0703c0005201207020304821442030511010f0100c10001d0107030249102c0041c4500019284140308803040e0f8400c020610080c10622403682c10686545443c0310350125403800d4001740b00000e14104031401070342c40071010580034550902c00701d0741c1c80302e610000f411100b9580c3ca400c440c0d182601e03800c60003004085000380c641c0b40400b0002500740d411411308100100780b949a00f0203c03101c0040e003569214242e8810740c0084c01000f0001c0441c1c035651000300500409001e036030040355414890070070b903a19940c05481d10040000c1c10f42c1002100500f01d00064019114120002a0800a03142000c0003c201600e4003000c1007540084034040b1500d030030200d43c010520319203418000d98500050000070004c41c0e4a12800c1c0c0442c2c000681c0c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 567800899 1250 567799649 567799663
    0x1811030402010804020405182e14010b0313080a0804030206251b170405010f080408040b09060c010f0507090603060305062a07060b13051003060b03120712030509 71
    0x10f031100c0d022500c856003071200030f000040801c0c10407407000c03510055500d02444500b0b07015484d035452070704a80321401392410790019803075056007843ca440c00c400500c0c06802421030440c0d00301c19111b52280d0700c40c440810003041c0401e00801250001403a1900990455034150066002c3ea007100c41981d1481e19010300300d1041d400044011022020850403103104040e00c500c00ba031580da22001c003410a039601260a00a01600d0000780408070702031155580c0042c418103c0c044501e0a400b03281060b864880c042d03c40da00440c1d5181d0b81c00520100d076911080200c13002124254000c110380c58401101400401042c0c0d1042d0008072500b10020310288a400b030281034903000001b030183d50300d681d030001c1d0200e041140c2c3c1884001e01104030598541605c40034040b00c1740035120110707070b907041e220802c841c03c1d9844007480e0f181483c1c1824000c41301228402c400075a80d101c0d0001484508100c0001c4c1351071700c030300c1c84241e4111000a100080154041c2802081403594409101d00c0d15640410741d100c4103 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 567802149 1250 567800899 567800903
    0xf0d090506161220010c0f020a0809010309060618090c05030d0203180a030c081507031a0d050f07091b03090206070618080c06180708070522020418110304 68
    0x408940060b0100b01010389046240000f4240328651048098981d10010f1410f448103c080e55160090700c0c0c200c0c0c11540c0070f4000c0280f071003e440001c0480d03940941500030814940d04040c0d0b6402ca80c020000154400d40150940c01c021402d0390310000d08180c05400040411240600d1000c00015035080c001341c03d560480301d50300510700701402d940000e074079038980c80300241d8003510b0101d0000104045940e440040c00811010f421070604800010903529006000b51003058a00255486400d4165a480c5c011003000c85a110041e10f942c1011481c000180058220724024491300040d01c1003e54400380941e02c0b6900100f4680303588d82015401c46001440203500075070200035440004003035034001003594000040820b07000760f5903280d2000c141c1080e0001e080300d030301410038050b003132042c84032031501c140403400205180c41c105190141c543c0e0080c81074034003072010503010003a400400035080703070b40305001401151170305c0d03075000c01c55600c0542046c0003000034609162006d00c00700010840c0e1041e5 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 567803399 1250 567802149 567802177
    0x50c010905121216020d0320190f0203151003060e0111120405160603021b010606090501120216030221070b010b030604090506040503040503120301030f060c050c0f0d090506 76
    0x45100380264004e80c0b0040c099800340341800307012001642d8055030019124007a41c0d0381c1d80d1410407907981203140c402c1400100d50310b60103890111400c00803c0d00071071010344e0005980f81405518400b0a2400700d9100c0c0301090030704150100282038040a0381ca900712806403201740b045405442c180c41c01c03500c1c0f03030000c50140d0382c2c204015441138004060a0f50482d1294044800305000c400001000d00d5994000200085e00012511500401c0c101c98281280d1510020884186000005413083e00c8a21545042c0041c42d16190010345aa074140d400026590300e041c05460390703510f0005d496601e1000742c2034060494a00181c042d45244080e58041071344648034102e282d0810442d40002e8100510700c0e540076403103441c1031001410600c08540654030480c000c580300d509040c10142408401609000421024001003012500d540600780c002c60300420001401b080200d070458251143c040d006000744120684024014400103510b0000102c603a1485080da45030304c1006514480d14042d0310401c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 567804649 1250 567803399 567803413
    0xa1a090a060305090d090e0f041a0708150402030f0417040e010305030c1501140415260d02151302040b0d0f0c06050406021b0303130e15090f0103121704050c01090512 73
    0x2603231140354060304580546070880d205c6042c40c00110240d007045030790400081403c0180701c00f4040542032031452050865041d415850100055038100700020b001800c09203c04c0c0040124a59640486000d0100030213414040d603180d0602c195664400850312400b071062100440142891000b400d05079104c4010b0f00380d10500d0a0200400f800303040081841e1542d0040001072162200e00f40c415081c43c0400340700101030140a0a01d0400d5156407400041d1b4202c1c1c040604541410070584c0d50224010724004000400f40c00800c0c014a10411801d4004c41070007292410300c110070300d8910907207101d80d00806200f91250700441706c50090340304481c00340c0c0c000d2004a0741d5104020403c40c00c0b01020f41200d0528005c000d07540c8482840da804005034825900601c2a0700c00c500c44466150b0106444070000d508203158004000b1344140310103403e200d083c0c015145010303c00c001004412401ca445200f0600309410060b8844e00c0d5414694003050100d03000045c00d0170b080f0f51590b10003241002074001 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 567805755 1106 567804649 567804661
    0x406060b040602100b1512192324120c1302041703090a032d0b060f0108060108010b090103020d061e0f03020a1a090a060305090d090e 59
    0x82e003181c00746d050600318a8011030b40030b558600088916035951074090f40720400051f000c41c1856041610a0401c20501d5403044c2031b0076482080c4601903122004003440d8030440c0e0340640d040b03005c5024800d6181c80c0400d21900c1842245c000d50395030140840000f10456052220f003c1410740c040741c01e000c203c4c80701ca034880c103a00110004602d408510300c0090340480151000401c4601034101c40704690381503000c040701c4001060803a12201d00c451411002c0d13001d0495555009614800720010190b100c1e0409900070041030b100c03001d03141d00f4490104520352012480d03505140e02000036050441803131040100030605000d035458062107036494446102d050f5400080100355450040c8003680d00c1d003d9103411140e41d041d03450130300070800340148030b0350044541c484d41c00000e82000041c002e0305500080d100c0d40c0d900341600d044a1404000392200c00749406000f501651600015070 = true := by decide +kernel

theorem cover : BRFrame.Cov 567625899 567805755 := by
  have h0 := BRFrame.cov_init 567625899
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567625899 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567625899 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567625899 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567625899 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567625899 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567625899 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567625899 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567625899 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567625899 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567625899 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567625899 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567625899 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567625899 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567625899 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567625899 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567625899 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567625899 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567625899 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567625899 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567625899 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567625899 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567625899 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567625899 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567625899 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567625899 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567625899 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567625899 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567625899 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567625899 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567625899 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567625899 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567625899 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567625899 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567625899 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567625899 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567625899 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567625899 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567625899 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567625899 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567625899 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567625899 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567625899 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567625899 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567625899 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567625899 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567625899 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567625899 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567625899 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567625899 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567625899 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567625899 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567625899 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567625899 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567625899 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567625899 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567625899 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567625899 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567625899 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567625899 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567625899 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567625899 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567625899 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567625899 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567625899 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567625899 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567625899 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567625899 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567625899 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567625899 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567625899 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567625899 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567625899 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567625899 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567625899 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567625899 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567625899 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567625899 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567625899 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567625899 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567625899 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567625899 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567625899 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567625899 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567625899 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567625899 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567625899 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567625899 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567625899 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567625899 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567625899 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567625899 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567625899 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567625899 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567625899 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567625899 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567625899 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567625899 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567625899 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567625899 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567625899 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567625899 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567625899 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567625899 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567625899 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567625899 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567625899 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567625899 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567625899 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567625899 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567625899 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567625899 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567625899 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567625899 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567625899 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567625899 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567625899 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567625899 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567625899 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567625899 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567625899 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567625899 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567625899 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567625899 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567625899 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567625899 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567625899 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567625899 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567625899 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567625899 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567625899 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567625899 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567625899 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567625899 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567625899 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567625899 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567625899 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567625899 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567625899 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567625899 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567625899 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567625899 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567625899 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567625899 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567625899 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 567625899 ≤ n) (h2 : n < 567805755) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
