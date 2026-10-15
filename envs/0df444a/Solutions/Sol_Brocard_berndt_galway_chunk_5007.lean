-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5007
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:26:45.267707+00:00
-- url     : https://prove2.me/submissions/645eabb7-9330-44e3-91ee-65d91c1f60f6

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 900359712 ≤ n < 900539568 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 900360962 1250 900359712 900359717
    0x3020904210f1202071e050a08031f061b06050c0f040303050d06090506060a0c05030904020a050a020705040b0f040e01180803040b0606070803280c1107170304061d03010507 76
    0xd800b425035000e000d10b28400000b45041c0c0c01001100301040c801c11902000f08241824204100d4036810580d09000140b00014040070b40003003405109800d100070424441c00c4864958080e03503613920190340040c0342c0c1c07101690100c2d11040c4e800200b40c90f640b042c0c2d485840c00b036000d490040c05440e9800035a02c0340d04224003107030000c1250301480d201031007002c0292203804000c010f40e051900004100c3c0c0a10343e0303185e080100b180031a604221051055850511000d40199141d4031003040140c201c0d0014507a280040c401e400c0c0010b11031a0500900d51280342c09094000d0542e07244050001801001d80700002640d00c440040c50020300a41c1144040f42c0681c007840e88078107180c03030300003c1c4110217017405120301c0301032100801280d0390100700ca801c51080c804002007003000241e48041c00c0e150b143c4e50740f10a13241c00151145507800442c80c030b00c0084c004094440c1140ca405115902c003250300381d9070000e944103000c00e000071409446c0d4101c42d0060500e861040d8454800041c0c2510000c8641100 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 900362212 1250 900360962 900360977
    0x315040f02210c040315060510261009020a0513060c02030d0e0108060f041508010203091006181e05011d0601020a0210080613090b0f070906090302090421 68
    0x103907141512074020100c10780c121002c2c0c0e0782408850030405020310300001d071822000c0e0701c40e00e2117000c5075403025004140180650b881c03994000303c05130004505500c0d1418000740420f00d00140784c0311034a0540b0840040c0f00000380c990403c89560001e4002c5d02c10036007032200411054801d10740c1500d85a00400c6280d680704000c0d03d50744141401d080c41681618144280c03001280100d82c5c210500681c022415101481342000400010f80940428220041c003c84262008a907400041d0029072081c401c2400703c600a59840340c42000b1103042d403143c0c48d0f02d820316080419003200950054180240ba901e20b1390340f200b00444000044802c20ba1010180d00b205002180e8510444684035a01580900140070254003079004508800300c0c0400082c00c102821000030700d1641c9002c401a8480072100e030130044491580703080095520305a070524010007541c00041c0700248564030020554041e6981c84001e14596070030b001b608034004d0800c0b00d15144125a035041a2282041c2c80d052407000d03660050f = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 900363462 1250 900362212 900362227
    0xc06050a0c020d020a030507170f0d0507020f070f0e100510020d080703230402011b0f020405011509140609060d05060112023a0203010314060105010206011503020315040f02 76
    0xc3c5400311810030f240a541041414101094012041d40d004a4200c0b48850743c03030490035402d091910400825614006000c0340364481d20546500032441061280c0860b41035000a000081d6501d40c00c1c400e040241703910680a01c42100b0b4410070a40010141080d010710f9134560b0005580b0311014800d40c80141c2c48480d0020031198040f040d2030708a925030808003d1215502e0341e2110948111122005c1e81e21108041f90071644a0142c0300380610054030016800c00c62440c2000081d030622074107a02c00e5040c04008940085401c415030f0115a00381c48030310700306281030081a0022840e2010540c009420f012524640d1100b100510b44001d400000040900d403000003d01503040900304442464814028145074070000041c5075103071021a00c4041d0581504100800381d0100d0380f01c544111400800000100084480703032036000001c040540380320f0f0380c031007004a980b40d1003441803103001c40003045179409860090380150341042c000741154200418420100b02580c00c940003441c842940000c114 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 900364712 1250 900363462 900363467
    0x7060c02030319060b040b0a0e130b04060905062b020a060c35070804170102090a0e090c120a020301090b0a0b030705060d02090a080708010605100f020615010c06050a0c 74
    0x245101c8030f0b0540100716050906110102902907401000781c004030000d5001c03d00303409828019042c0300018038103c0b000103902d48450107000e2980eaa42d0040e41851390101e00000c00c2c0c00748500ca1030001d40446000e00f44017103084035400b841e0310010010b0816110351005030703c0d00500b410107004540c80351004006e0038a030400034003a00b02c40200580182c000c1d509172200b81c1c800c11402002100c0e0701c2c0c0341c92303541c1401d1910700303449680e100406405560390240800700041d00030b0051800c0440c0c01034805a510510b594440c0001c07902460542c00c15804030b051880d0040c484402625044100d40101825a0109003100d1032040e0544a0352050010400040c14074015051010401c0d80580000da142030003040560240004a112064012484039020307141d01072500005c00c030300d20403038000a0303451104a00815042c09480e00420070308114a07041c2e0702890088081c0f10942d401045141d0718129410f08424a010116040014510411021514600981d4001c4a00c0713a0000740207555081c01 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 900365962 1250 900364712 900364741
    0x80d030219180326030a060905010f030305070605040f05011505040e032a0c0d030e030c060f090d06110403030e19030305040b0d18030f2d0309060207060c020303 71
    0x400100954001c80b4800388481284002c1201d41c820101c0352003000c08419141c42584140c3d07407a190260102c100140c840b06504003104030b6031407103004c01c00d5036220301c03000b103284009000280c0420300c1000780b54002201139000720b50085c082c03803044e031482c03c55545040c00e40d911442e428161030f04a540901c4245040d10403200c542c9a0f40c2c0c001c0d0300e0b00d507104280c20032075840c100ba0741901c5180140c0c114591901030110800005000f03202c00c0a075130440c580506092402e290b0310303000c0c0c854061035031514141001120540e160038100c0c00d0610414004020760503500b0030044400301e45540c0441d90621008024102642c0320380c41d1018001d000d4002d00075038941290070a00d5981a010080000c079400000300c0f810744d203c0103030443e80c4460381c6400f20003a02d64000c280d0503840c0610003a0040c036a100c850310300146515a14040c072a001001c0910008501d090b0b8030758002c1801810002c914000e5105020062160b031003d8140b840e15180d12040b18512a8a00c016803c00410483c2540a80d001c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 900367212 1250 900365962 900366007
    0x1909030215031e22020409140a050c060702060732070513112208030406031a0f031002180618090a0e0d0f111023010305030a030b0a080d0302 62
    0x403c0007528020308000292406140381e1404103076a204500e0540d151500b1000721709402c034210040b80707421603002580d0b8005010b801d03910b9000ba080da80d82c0c0c6181c41400c44100741e030018005410140d81d5151f00801c4084e00030892000d0b22304440816640702c1500500d240c18001c0c101805015242c10240314040c18060954070740c90703150220b5404004040c105942c400359050280b50865410f5200c0d910040702e40790446445c40c80041000520b142d8190050905403401c13401d445071056490081c40306c086134500010787d00d50004111003000c811030754041d00001000c0902c08918180000100300d05d40d000a080440b41210300a042c951400c040340400e4100314035420400100a480745056180d4180b4842c4800300643c1c41142040c261055400780078591800302541c28804070403804000424848001c06007120f070201c208001d40a40e01c24481c100c940003005146042c1014404070b0003050f00361020760703000181040102c0d00b0b031410460049080e8498500580d02c00c0e840d8034049200c00c0411 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 900368462 1250 900367212 900367261
    0x310080f10022b1b02070b040b0304030203040902032409040f06110d06150206010e010f030305210f040c0510050f03060d05030408060114090603100507050903010c050403120203090105190903021503 87
    0x2c1c1b04200145116045401700c89076802c0e802e8803030f20303240b400700e043d48201c0e8003c00c85a030010060040c144008000581c8800d01741841c00343c82050300c024000c0c20041114003403c01c1007000782c2c80001c50040e403c12044681500340ca03500c0c08101c040c40100300d8402ea042117079020f55460b00c0502850301040303054050840c0390074081d01c56141a65001004005000c0242040408241c50909160031500d02075130070102100003003030786020340820109007002ca81c00e440044485e030001031541010840001c192030704e40d03030301c52401180c800c5c0803074107900282010360000c801440340b801041050000d003001e400c201e80a01400d524001c88100340c211040302c007611401c110014440c0c540e500040300403403503506503030100319a80c4100c0241c4050095210304c031303015400c068056050f00c0e0300400a20680f440742100d20a41900726000701d9030390240485803800700b0750400030302104d0500085c0044c00e1202d01d2501d0144a9103c0c1c1c0400d4200e103072080141090301011060090f03001e103c55084c400c40440a = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 900369712 1250 900368462 900368473
    0x9020301030804030f083721050c19180f05010507020d06060503071710200c030403050d0906030b0f030705010c020303120c0310080f10022b1b02 64
    0x40c2c803214128491444010982c040c919002c10030003030808159094841c420000d00028025050708101c40d4541e82c2c810f20041c034104000a0380507003d12415116820451580d03807451011000c09401498081c000c00340300201800b9010480b00f0401c00020380d50020340e1049041081c0f8030750200003081a40049000070a035041c1030082e40d90082c2542c084580403550040080182d0406a004044913003081344c26004055022804581b02c50a10650040010440f03a03142c0c0c1488581c021103c00b112140600c0880c038800c03150308403941019295882102095074030f007560340d50b5842d140c00c00ca1101c0c000030880d035110411020b034051140000321481980c0f542c00c0500c4040000e91215030714025541448910030380101591001c05c20f55172109181030f002492410a03d842c422107420443d002901000d103100003260511021602403c8480680d0081c4208020210300701c02035002080ca2090351424030510030094800990468044402f02c440004c080a90019032520b40340a1071701c480a55011 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 900370962 1250 900369712 900369719
    0x6050d0c02210a080726060d050a050c010f050304080f07021504081506090f160318150608035d1e160e06030703140106170402010c060b130203010f09020301 69
    0x31003883c101c00c0d208546015007c4d6a000000741c910710000d070001d13081c1e2103490002401c000c40080d02e5240d02d0340036201d440341d403408071004458603c002c4400628000d81407101d56220710620010700012840142181803080c42d180c00c1107015001980941c44581c014071128006141e40c0d4840358110205848440092426411000c1c0c007500c0608200c240700c81000fa031b141400e210398001800e13000b061800f40008005802c199900041800718142c10720710b0088001a19070b80001112011042c2201c1d02d000d10200c0040c001c0c0d00481002000390048400164400300e044d22450360410000b000c585c00094000c0c010f0b0840c02e40c100504000c000c540311000704125071406118039510040400c400c90300b0b8200c42c2400c5519182540c400b80c2c1140300407050141007900b640049682c01d8ac48902c03041c01d0381c1c0c0c5190807038204000c100500c101c025100041000741d44105490704025020f0080450594840004161900d20200c11000e80a601000500c1030044590000005029008040d406c6504 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 900372212 1250 900370962 900370997
    0x2040305073f1e0503070b06010233060102011b0507020607080d0e010506040606091a130f17070506031914072f060f1f0b0703120606050d0c02210a0807 67
    0x51b0078400782001c0811000030300c0b075030304c20000000d50504161794012a02881e00b01070441e1010601204071071003040000601c41d5105115200c2440141060070141954024044c2c0e02c0754071101c010780c2c00c01d00c10043c02000c01d856800034148001d08507000104031070302014181c00c49501428491195080038000c02c1200e0740820440165000a5905102400c0e9010172203082d106811540e00b804c0c0c5504000100c1210070090102281c44c1070700106001d50020014948400f01da00460740e2103a02407022410111060300c001000031807100000440c0c0381e0074541802592400c81d803100002e490803190300d98001d04142c0c8009409052000211520060b4a0280c2c480100800004d44204214001201c00207401c0b01c482c5000c821081d08440b07652180ba0303190b56640084026404030701c4041d0785200c034040c144200350845089030350301414038007013580503030103410000211800c5200e84003103a02c6107107004d513412020b1240440701503610b1480340c9000d030210000a2800c0305221200c4443c107071144 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 900373462 1250 900372212 900372217
    0x5060d080a050c01021309050702061303050a031a0909010506270112051e070e0c0a0807032f0403060c05031b07140f0d02010f02040305073f1e0503 65
    0x406070502e00e440d081c12815150090003000c0140081641c010800204103400381c1c4418042c842960943d04140d4488031b0700e010043e800640280050802c100000500c0c0c071a6004607400d47d0303c80300002e03d1410200001c0c04c01401503a0f142100d9560b4018001c103172400c0c00010500d0902c111043e10a01080f001c040d200d070f6014070810301d030000c0e00e0a81e0801c201d0203000821240221000500341e89002d918140d5543c1034500800100c1d80700e040214500b081d500003a038040045c25522188140e66400303040700509250407948007803844801c8110081c0d880000d5002a0005220007187c855196043c080d0030359041141c140300703000c2e040081c0506407070000200c2d07051a455044499a0b81643c3c43c00e0b03000100c40808000c4140200f000e00d00c80c0c00c502003155800f40d0480c0d8000e005106144199004078841d0348001070040c1d1181004110082c400c180400c00403445100c1002103400303a0020044e89100c2982013012008540851403c10502441d0301c500904022803094900303015548281e82c82c03 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 900374712 1250 900373462 900373477
    0x10c02060d02070c031403030a0b01030207120e010306080316060c2313050a09020d0f051005040f0e06070f030c0309150207141905150702030403030f2a02010305060d08 74
    0x2034001a03483c0500144009140080d07502410032442d07910303001d180d280c0300d400c01c0e140414900d04200002196600c00c1c026150b405030043d0381c09644140301e020a8079a0354000260b10b041c10f40305c90001031020030a1010708a10041d92021140d081c0052502104a68049110606106180b01050910902d0300c0ca44291460340031400743d6260b0300c0b5110355100c0a45640b10503404080c15201140100094015119102c01c2a02c24408009090b840e841a11000c9034441400345408070104501c0c0b41c15004a030300d8640040000944600c4d480c2c03440d062440071a0310102103a6904804040c23181c0c5442184014160340c0b4041242143c0c50b13450419900300358035609442038020035108280040d0710b140031040c0d41880c084440199503111510440118008103544a0183c500c407030344100d0910354010300c1054140e000d186031a04644c0d05072119070791038202d00d040200343d81e04242d07103045030744401d04000e181c0c2001e0300307200740248001410f641c4000c008502680e04541c0310000505850180c0d481c5 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 900375962 1250 900374712 900374737
    0x14011407110909070306090606030b06031b01030b0112090b1e06090a0c030f0629041409071110021e0c0705010f020a02130209011b0b1506041d15010c0206 68
    0x190f4030749040c41c038a0400c0030741000d0542e624041c2502c080029503440001141c1c4240b054030410b95562040544411021072100d039080340030085100998440d50200a04031014101250703800e2082c241242141c1c5e03c0402158000882411f10980c0310540400d60080b052800c6001c29928000003c2040480302815120306203450b100b1600c0c0c0c9501a03007102140440c840310411440307079611040194440d01110074015104120045d0205618000440701034560f1b0002500200000d81c1c00e01886250003001d00040100003c005808120140b1901c00c4249644401584070080307514001480c601c0d1031441d91607180100943c81c0b4140000c1200021510242403008a403603003200d00342c1c01d0840d4041c0096200e141c544070301910310714584c00f5040d0208280c0c0d40c081c501000005460400442d218090100d0451500242c80203146400c43c84255401411603401d0a5580c45860043c098031007038498030b68100d03c104205ca07220341021524801c002d10345005010310310717001300350b06110b410081000b = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 900377212 1250 900375962 900375979
    0x151b0903080d060815060f030a0503090d060b100c1a04050a0f05010f021303061b20031902010507030e1c0305091213030b060d0803070806191401140711 67
    0x20400b82c19486280100100001c2d0b403100c00b0040720b40030390000201c0c2c940d48a5010008441c070700c2d0800080405031558400011850100c00740c0070450b00212056003183c0c10744c1c841c881c404035522152081c402141181e00c2d4280c4601040c600007103c0622840c40d00c0702804484200070204e9000075481d10815000340002640303503a1030801d14003605a04010b4020f03e800012610501480b00048200f140d001d40340401c40e0a401800c44240d0345101c010103000260743c1c1865281c208002080c0f0010403800c4011245405c04a100c0c041c0003060f810158400760355903000f000010398040c003800102d0b00d4448041c00c40c4d480c91511041410300f040d44000f0400d580c800c0055558081001180a810300290b0b00341c2d268201c0c00315110340c801c9103020032504403114102061170b505040c404025074a40c005512420360380c4100741211110304c0100320541c00382c191607101303295440c4401114050314440b190a100c0003080c3c4005040c1000000c0603002054040102e000410822900c643d6904000c80f080107 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 900378462 1250 900377212 900377227
    0xe160509070c06110703030e15072706051809041205090a0506190f0f0221070209010f06030e1204170f010f05060108150907080601110703151b090308 66
    0x20b95008404900501852918204115000c1450080c0009512a640a010010300c800341c1c0307600c402c0b8818071a0b03a0b9079418004128010300230b409d00d00d040074100c142c40b83e142402400d840e0010f80341c0e602500200d000010481030b101c5480208000704081a14218041c3c00d040d03036031305c1c0b81034401284802002008180f0500070350300e1842e900c004100003062242c80c0c1500640405001104a045c0c0c1e000c42d5a071064500918094180c3c2d4071240003036000b5005001ca0200c40c80310231080b224000100707010400100380180e0718002c4070b42c084c1062200440070b8604100002d800c440c207221444c0383ca640308218a00d207103255a000c0710251440ca510103491400c2c1481400d1a0000c4031040201e1035003841d0b0040c0c0300072040c0e0f2040d072054a0980e41c0901544a800504107084404642d0940140b496000501482e0181400340e400203018908282c0c50f104040200b400c0485607001124036081504030034070b50500c0303805a040e080c180070340300c40411090035201800349400791000410301c030404600036 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 900379712 1250 900378462 900378467
    0xc0207050105090f0d05060a0b0d0302191722050d020919020408060f07090e2e0909080706050f060904171207020c010206070809072105010207080d0e16050907 70
    0x2110340b101d003d810403554540d1860300a449450448805003c1c514140100649d85016180207225035010340241c44245115801207144a0010310292010301c4034000446035002c42c0340080c250101c00946002c01c0c4c1090a0990a0160003a4402441182440072140c09aa1685546904a42c6000c3d40480307032400c01c852000640940da20500490180c0c104111100004a007024410320303040c0e940015940d00c0740038140c0c011209903000004485050100c28810300b0b402d00c2c10702d0120a400c8a0035003142ea480722001580c2c056441100c0b4200042811010440031303001301c5401c4441c0b01e10304611440c2032070204010300c00081c8003400040719100c1641d401045501140d44240700c508898440e031400c90f00195940c01e950500078018450700000401803845500ca0500440f409800b0b402e0304e40c54140d110000040c4400840400800c02804400040e4240700a12400748120301d10360f183c034001d40c242401c4517900a10700f103040d000010102107641c08c01911106440c0115503410305030b1202c0804 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 900380962 1250 900379712 900379729
    0x2120a14070f0b0c0f060c1201080304120308130b1f080606181302060301090c0f030b0303090f03030f040807080615100309030c14061902130b0306060d0c0818010c020705010509 78
    0x40e070308640100418486040c7c0380c54000c00c0e54400751004030070306980c0c40364007a41d00d210300d1040c500260706440403440020320840409810200070114070016036010344a040b1000400d4941d6601e40e404200302101c0d112031b980701e0344014029500544a0742c80d042c808110840c5401c0c0c00d10509a41500c0000e0300344c03910a180c010b04a4000d00200d407a5a110100c1d00300400f81d2018a00104003291902d8064a100b4061a50a8a4040e0241d8240303030105091210b50b003c40c080c840d525000c14852282050f081c000035000030711074900105159498000014140007000e03203202e01910080c80a50b08a0320b81c45a020b091012901d80040d0314115410101e440c0184000d005103440b0618142000303100740000d4842c0108100104400516076a0034010121300c6803400140d01c081c0091020002d458031540035607806007000d051649403880d504083d408440700b11a00c1790210f60180d007400b00c3c4000319000e0f0351001d002d080c000c21141d80d680c0c401942c0d60300e05103e05410031400007107007800c40e11260f86 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 900382212 1250 900380962 900380983
    0x130c0b03010b12163216060e03120c030705040305160509130b0a0504020418050616050c031b070504180b0a090804031502040302120a14070f0b0c 64
    0x11454880d41c42d80c0d03408070158400c11000010340041d00204400c0500d03002e035900d4024843d105c8403c00340340d5a076010015008200c1c40070b80355444410301034140c24903000803c944150440d901c24503809a141c102d080f1503071812440321070b504c1440031322031030907030074081e907400c008006e000c1622a43c509200300da0901c00c5400003440340c010700398042c080d00b12201c000ca090341c408a50034140c0343c1d540d9030340000161b4000006022542c1c80c001245001c400c81e0b01081d04140081c00105000043c0c429a4202c80d200c540f007201c0c5e42e48241c04200ca9000704584208180020303144c003e1400340700040c441e69078003400c4010300e82c01c0d40f18190280c8001040003036034000d00c40680f00b84a1551441c0e80000e0f1516040d0041d661500c94000140034150144207c2001d01d80c001502801e0904544540803440b450080004040b90b003000044056515034102001080290000300a0702000d40b0b841150b00c030040002d0822680314400901040c1c00d402440c00589900ca018640c0340c43d06004003a00d04800c990 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 900383462 1250 900382212 900382229
    0x50702040b060d0c0905060a02031e280e01050a171e09070807050d02010c030516060515130e0c060a0c12032004030b0406050a15060f020f01090803130c 67
    0x3c3d41514610203908500500505910380032000e69984040c80064441c0303c2e00c0d0001070b001003080c0081560011a0f0003a44000017600e14108050b503801021400000c00c0c5210740c04a14440d5030440941c01000f10802440030300c0c0c10390402028100103401e03034280c0c90025400f1071030000080c2c0360300c4981001e141c42248080c00da14050512181c410345410342d50140c40b40c140104207000c244c03801c0c2030f034400e000294182d541100c0c0030301c03c0d00c00310340a401088840503100903409501000c20068002c860150f11415410b14401c006102008a035140112182d0030150514220500014001c10001c0300d4450a03900c0c2c0303944145507007040721b0401460100170007010780da92103003030055410360044404112a144030507600c002c2040000c0c640c09180f0008001e09034000000f40011503541120382c2010142d0b10104586200e200c901c024200380c0d1304100d0002e507401001c560311a904026040740483d8060081101c61265125002c113440000e102d4a4000525001c0c101003243c40a0703400003c0403241c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 900384712 1250 900383462 900383467
    0x3080316030e010c080a150503062a04032118210b0901050609010501020615040c0e040c030b04052406031e01060e030706050c0c10020f01060f2102090403050702040b06 74
    0x703d01501a503001e51b2100540c524203a1060458900d20300c000c815100010020401a6144524501310701400903204003d00021900b200940000700098005980b180c0d280003a07030645198000c03281c0792004800010000307444081c200200ca404422010385116001131107039581401c00b140301c8201050360040c11030b8403820805c410008194005405002e00b1039020311140da0350f00049035141b000707441d0480c0c0001e420030300c04079a207000c0d804508481128140900310030b50000c0054100c07054400d10102194076100c6282051a0a1140541c4071203c0f049a003142c00c0c04004030200d00d049c41d881c050045500102141d2503c0e02c0710100c10b5240c1100c0200580e540c1c4861b4010092504424224082d00c030382c8802107482d40c0148103580140b0101d400501e0700f100000c0400c4540c0c020701c0e5030340c42035004070307070320421070000a01482000c0c28042001c91600c074a0b0000704090480d805541a00526460340f2a40050340c0d96660160003d40625241d5194860390000a0092501603061030b400b0100 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 900385962 1250 900384712 900384731
    0xf06120210260115050c073005150703060b340c06140901080610030e12070201020709050112020108090f061e1b0a0309080f030a2403080316030e01 65
    0xd80d50150582e43c0c04d50306038007185900c20069801d8050052825070a8000901c2440001d10140c0c400c9240f01080311242c4650340000702031580c1050341d4400b0348142c1c0120144911480302c0d02c809a812a201e40303803c00606141140e60846070094401e5071440d0002c038a030995148a0352005065920381c504038040d040c3d0b070980381624a5130348a106482c0441d444080210400303d00070b0555a14100c11b840301012659414100280d5038040c6042c0380078107954134009601c0c140e04000301c0709a00f4105403019681d200e60300019203000c103a50321091019040c03200500005000c030316101415682820881c58a032900d040c9c6a0510740c5804454001c0e00c1503c0c108240145c190075950300d900e120b415038080640f0340b1030b10402100c07250111020415003c1261401161107035002c2c3d590700340904101400c04005101a00e02e590051743c4a010407a21901051351487c0c0c0d00f45070040c119805000800c02c0c03403a580d01d080301400300a1084da07040100007104550140a50026100c805104008010708a030 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 900387212 1250 900385962 900386027
    0x80409020301031b0b0a0c02030a1209061205152b0c06170717060a17060105120d0c080d0f0f05010f0504090201140702010903050706120f06120210 65
    0x910040d81d41121600e04401306010050790f181c2511a80b0042510700818410240c070700c0c0c515030004903058460384c009074010408028682507590100d603101e904403882c140707000380001c0e500e148192066140070240081e50551301c0800c1c0d400d21042c0c41c00140c0740f82001702c0403400002a1001e14529050f48d056500b0072000701b0468068402a448002481d00d41001001100e00100d8801020603440007601c021140101c021aa0040e0024030700190a5201c00d1a0603504401c2c102983d0942e000200601803840c1c00400314003500546001480b4001b071802c0002c0c001c0140140281c0034040008215524940640103019031001344901030082102e10440c41004003024422400d68a40603007000c0b4284c5810302a04601d00e405039901700d4072010303a03650328021780c4c801d900480c14041d60000001c001181801448000d16041e02c4450240e01d50449500a0b0b07840c182c2806026850311206001c040c1d48040400e0045030183c80b00f48402c0c2c0c808400f83d03005101800d00c401c4243d0400402c41d007030300 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 900388462 1250 900387212 900387217
    0x30e030d0e0c21061e070c170d0207110d1a0603070314100609150e060604030c12050c0913140f01020d0f1407090b0f16060606030b0901260a08040902 66
    0x10700f004120b41450f07441e94a49401d02d499071100703068019074034000c5003d4030310814035110b826014846880b10b207805844407400ba40c1c0040c00c0810701907004224001803101c812400d000d84030043c0c1e0900c038158041e64a80c00d5903c6503026000324041e0340c02c00300d00c0d07944007003084102560340407016804032401d400f4155507861060030052141c0d0b08102000c10074034018006c0c008513030000d288650100382030107050840c0603c02002c1c01e40050080c80000301242c1c00d0140300d001054400543d1238910180d060050420b44c02c001c1c81805401d003070041c0300d001074240402416461308081004a010041803906050131030416810700258000324070b0481c080b2280d4000b04a00f2134a0008000e00f80140c0f10000e0005022945400440d0451004204030886d94000b001100741c2d40c0002c40c503104c01101107294040b200c80d42591a10342e81c5600b4051207800d4401e8200d9002d0489800c0c060703614024003c281030905102030481c0b8540c21000394915542040241d180301e0748041950303103480d140d1078400002e4 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 900389712 1250 900388462 900388519
    0x3021e0a06080108100e030412110303030c03070813020603010b070f0f051c0306050d0f080c060a021c022b0603080c0a0b071e0e13051603050106030e030d0e0c 70
    0x14091101c0c10a0101146d100d0303024944040d030061810640344c030b0052652090a424140c0e019284464070745c465030303401d200039807164281401d406e40303d003040710006024100c001d20181000c4054100e80300980d032014152811124400c9200355030705801d141c8143c15007600705008082e41a900484c0c020018045109032503008961003e603440c2080c0d14045041d10010f200e207941008820000d0004a2010b02820440e10f0080e140185032142d0a110203103000000ca4018582c0c43d804a0120400148806100003d05e90980300754208203400844021080443ca0414111000c2103d04040700e40345802c400c0066800618807515a00d03000c1b00303580c179032146190407103c0e001004000f82c0e00324000c02403a81c1218540059001c0341b80c0003001580c0e040b81952207154411280286030081c0a0103010760f9200e9806418080458200480042c06592040e003000d404e0500300032603801161800030a54541070803440012400707140440e449820211100b250607004011403040f40c0c4100107240b65080035 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 900390962 1250 900389712 900389729
    0xc09080a0b041509210903021c02190e1005040903051b0c040207030201020904060501090f1a0910170901020f0f161704030c0510050a20011805060a05040c03021e0a060801 75
    0x9101c10340d03070103c6e049445070000952101040c0c699010700c1040e01104c0003030500c068003038504800c0103820301c1510409503005080c000d00e04002c0142000c2620030070001003005460506c44840c0740c3e075000d4002d0107914030b54400100024902e0307013581c00400c50b080e1600d801070000c640e01e49443c10000c3c040d611a0314020b0040d0308000000449501ca0f0845108860f4bc2d000c045120341e0610f1010b100141d0395403c45071308501d082c002e04105564814404080200d10348501d400c4c442050b01044c00340750010b0404000e0791040c0907100b4240700440483d03111045403403c60365a04810700c061030f0076106007403008c1c084e0814924954880c0360303d0350041080c0c0b07024030380034804940d8440811411b4201e0084400025209124121b03031140030360705401b514042141703850008051680418211107000460b664100343d99186e2005019003030050541044560304140f1035458241c551050031800351100074003400000d008441c4100300e0780740e1070311024002400003814a6030703090001e103008000e000b8101c0 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 900392212 1250 900390962 900391013
    0x218040b09011202060706150e011815060e120307030e0306010f0503280b160327030f0207030b010306090c05010503040b04020f030709020f04090c09080a0b041509 72
    0x40d858400d194034100c804500004000c84001e0b400c1c07050035003025000315101512404400410246000028054900d600c0080c62661416004c40704642c40080c018901c94600300e05040c0b0444028030280c00d80d89541410050031210901140d003801c4840c82c01d004601012031650f01b0550300c0140380704d9441040b801c44801d070740c175043c0040c0702d10003a100710f0768907a10000b04492405888051040a02006c1c5400d07014070f40141c89407841c0107001c0700c9260500f41c0101c03544004a070940f188100301160042c0c18003544070811b80000d8800081c40c005001e0004010b58844d10a00c02c00c8010080c582c00112002156502e00c1c2040142031900070403207802107401303404500f030351140050b43e110707039045075001000741c49076001c0c01640b500c03000d806a01401000404204844607000618030b2682c0e08010030f94451402000d50b0803240b80402801c1040706d500030422044800080d0b00c9001e6400440d0240c00d916079142005400d18021354a00c1a82d0400d4480300070310282052407105a06141010307803 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 900393462 1250 900392212 900392231
    0x503030c03090d020f1f0915090b150f0411040f0609060914010c0b101a07020307050909060f0601030f0f0903090905090712060e0307140d02010203010e1612021804 72
    0xd07141c0d014140c94120607800720b0240304201099182e46c0040c2d90440b0350024440e10592038029950b09903090499200b51a846078000f000392080c11550701c01c1d091811140001c046800081000c8150311403c4e2140351034454082020086008890040c0742104100106c00c1d6a10405494088217110b0040403c0c4040320006014904000c4a804404143d6424140304c4407903850b00301015000c2c0440b05001c202c0a40810740005144d4100c101e580f414029588075056481003524000c003d42025000f0b8a07610b00784601d140c0300007039103504180750340f540e602c6640c0d88034012001048005000e101c0b590429030329144101917a030200d40028026920340240e2174031801c40c001a200142c48580c5144d001000410120f044d520351040443e1044002180c04084045107510b16048500203443c1020740c5a0528503001c0100001003450b40c95000940c155850078000032028000208548481d01d00c982d0150400d134400ea00390030070740b940c842086440d101d541856200c103145041031180a03a28005004 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 900394712 1250 900393462 900393467
    0x1401060906022a3c1507031407050a0f0305221530020307120e1024060302030105010f020a02060d020f0f030f0403270e0c070503030c03090d 62
    0x80b203541201c0d4106941d40b030100103001c02280130100400c814440c0300d00480500800c030600c0d140c07610501e14021401c440039000c214410221000700d4030b8041c1e080040000094014100c0601c0c1070360b1302000d903100d121a082003030612500660043c510014a40c0c084101604200600312650380b402d5064035a4520024207001c0c681d56000700c01d8031000304600720007480d114040b0026101c85400b44d541d1082c490307085040c1c0340c000552040b02c4454000c000c20641d031760f01030141d400c0945090001d0100701401381400e61201c840d00200c844a584501b54082040c00b190070010040300070703180f40c0300d140d5034800c0c0080003500300b80550b42c0002c0711401c4900c980c03480041d07124076207a0010101803815180c03803c1d03e002075000c50311a854013031081c0003140d5201d03089030196100301c0c050700b5908081d1626160041002c642c05c503c0122092000b4000c25018590005940607205505816052502e40855802041c010050010711502c4000100120000d004015600030f03100030303040300c400c0701504905 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 900395962 1250 900394712 900394753
    0xa06020f1903052a0d0e0102071707080708090d140f0c0604180b030703021003061e1203030b0402191805150a0c0201031409012c0a03050904140106090602 68
    0x9901c00075050f00391080e000c01010b1021020300f204c42d0300e818a400c05424090041d0f4400d003a2041580c6d5012803034000344070f0151424450800303103455040c90000595203000d1302e80900f160150ad01c1c10081042407041d2610031444100b2030300503d9550141148944065450300800304e04107090041802031a0b1a08104099800313841c083e280800650040401e040d00804158580e1a0715104800c40003003d03844d080282e0f40780c00e005a07400300b01d00d420320b10340c5019800c040003100e5807070415807000c21508015030200b180300d40e810324011829154000000b8007038020940130500385503002081a0101c0c0c0c22540d448038402000b4204040241e894040290030b03c01560b01c2c0410a80802c01410b031a489100c0a040d0603105060000e0320a07040403040c424a40202d6504085a5590302514071000e18551043d03500d2440700400041d07c034600e042179407104140000102481000315090707961b541d82c0d0704a8a81c02d00c0721400316800b907030354034801400c041051203090058001ca925070b04108020310203 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 900397212 1250 900395962 900395971
    0xa09021903081b0309150903120c0a050d0c0807200a080102040f12032f03041401081303091806050d032006090c0d0f050d0503060f01020f0606120a06020f190305 71
    0x14102c610001c1c6c40541c4801075055150040b0300881c102d04007060003900d100d29850b002003c140e000707864014500605c0d04090000d22604080c46e00001d0480b408542449602c014110b405c41c0c07000c125131050b002007030201507202543c0d08000c282ca030030540c040c0088035081400c84202c0350356508240c52542d8070500150001d03004030141d04503000c00b02000000101c00c098041441140c0d400018116006a004080c00d0300484010128641c2d00c00a2184c020110180c0341e030410809603000340a011992182026140c11144070104102c3c459004000811003c0c008501c0c170142e40c40d0007802aa45148110b13281c81c0c0e0503160f40296000001e15520a045207401030070480903040410440490101c2d0484800d5005041040050018001415401d1054075850723201d00340742d82000821408002f00c1811503100e804900c10b172580001c1c04c02d1b00a1020f48588443d451071050580c24a06c6200010304002d0000443c208004403043c002d00d10340c0030403156a400ce80400004500752401511b = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 900398462 1250 900397212 900397219
    0x1512020d0209040206040801110d05060906030a031817010c03060b07050a0809040e01150e2802030c070f03020303010915080606040b0112110415030b06030a09021903081b0309 77
    0x600d280060921000d03080e003041c0024015400c0a41d200381407030070755491900f801c505e200081030024200c0c4c200e010340303900100101c0b0040c42c0c1e8076251012076651950808058200044410b00810094403414000c02500d981d0208001032515070141e107002e00904c004d404002407400c01c000407018401e405070340780158090040c001c01401a240c040700c6030401c1c2d14407a84165900340054a00600748a4040c2c8000c00169038102985482005002d10038010482c4c6c00310700709201c5040b0501c422018140720010003a000603240d440f1162100b030346008800c4000c05d4510011001014160000045c40c12500d04410502c0361410034240c901c02d00d8014480d45032035601c440003282c003a2405070490700351018103140400b90041482c841341c095400e030300c03440004040001018040c0580c0040001d1164856080c03d0021040d000040f404900c030081042e82e01c00d5881402c2421569040c40102c61512280546840d03e41c4074100b51005a101741301040074100c0050b45402100b1012043c1c8841001c010b = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 900399712 1250 900398462 900398479
    0xc0306090709201c0b090c07140a0204050f0f07140702060706110a0f1106010e010512010e0d050324030706030905011401080a1a0c16060e0f01151202 66
    0x1010107005801c5020081c508024107180c4580c681c4500d00161041166a10600d0500b8401c0c3c1303c0c2204585003040181c2c0034030302c1d0004200010588208030317210941e00c5512080005048140d580c00c1619044009502c54200004d2044a4140310707540c5008081c025000280d031b403140441511290020b11615058034028800302c070161600d83c2c048c2400b680070748400f00d9030040d5252101d00e154804060600841c004051055590303074802600c9201b1036121000340703025410090101c100744014894035100b26264004c0c40f240000030b41000718044070340b03403c23a0194801d620029007240c000720347c0d0410191813000e502d0841d400461030111090000f4000d0008039051440848c080c100240d4162015904d1302565207240c03080b00d100ba80241036240103440f2200c010f103404e031107003c481921400511444814003203c40c840764122031a514400c0d0740482c18200300d02d062400b07800c604000045501030304002503020003041d0070a4601c8604004810340d01515001042071410000101070740200e4030 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 900400962 1250 900399712 900399719
    0x100903030b100503010807141306090c020c040902030a14101b080f040b0a050c0408030c1015140607020d02091806101410090f0308071106030108030340050c03060907 73
    0x71515031004100c03009c0d00c84000d081d6417030303c1501600c106138491415155a801c6006441e5414040707044203440c11501031140d011542c00080e541d911242d030203020540001c1000030f840c0e4041001188143d620401030004003e42c641c40182c0c04190600301c404540c0080c00212002c15881c051403013a680900d80c0c2049032104d230980c0c8000c101c005c2c0b0030840306208000210310210104044c04520900000826481d1a11024074040d101c0d011040900c0145d20b4105012145c1381c0c0308442426031042d25100c2d02e40c02c00d80001941c81d02016000303500100100148004070f801c10516409290070401114801c0c1c40d0b040800e500c218192282c8034800b039294031143c41600d40800d00c0f0b0101c011600d4024065519200ca098480d850755008031226900001c5141c200a262412038690600031613082c1d05661400040c95204e110007483c0c0e803038052500030070081481d0b21074500c0080826041c45501102050f4031410441485003e0545039031181550280c42c0c0c1c82c00260140c886c00428001d441e21524 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 900402212 1250 900400962 900400979
    0xa0c030515030d20030403051f1b1206090c030209090601020c0a0515040b0f300106030203091002030a02120a060b0405010f02010f1a01030c09032102100903030b100503010807 77
    0xc000c40502010070345481d00e080c1c5130310401c040c0c001386000d00003030260015010030420990720300c0e40351400800d0a041d00c050080c0c0d0200c2450801010b141803207100700d1412040b80000f000183c002d0764000d803a0044500c599a4543c1c06013520b03040c155204043da454140040e80c1d5215642d82044d0300a107c03040034482800c1007400c9218546094100c2d5041c661104120071058100c0702c840c42a01401080c000380b40c0003c02c00310b1420080c0301281c0c0d640943e0848400c14501014003c1c24141500000030400040e400c200c1d2046030f90407014210344900f403940c414000b03503025980d00d80f0118410b07000b28218040d40c0c0325243c1141d01001c40a854545407030010b440e0400c03480b021a09655035298180300d1140b150082000656902070141d225000b11000507003140d820103141e070308000240b00c00b440010078004180340f107004820034030300148010001c101c0c038007c202d580807080503082c0b032510010907070035810810b0400812603904a082d4404002190113000c244518603c690204008010822 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 900403462 1250 900402212 900402227
    0x15020c030d0e091014040f0209030616091703030105060714070e010f0803041202090910090c1a191101060329090303040506240d030809010f0603050c1302040e0a0c030515030d 77
    0x1c2e0010400741c1009c020800281c00c043c01203420885080365030604403012980100c091028140803ca0059401c0d464189907039203004c14003c01d070080200040480602c904882004000c40380320007101c00e0703161904481920034100307200704150381125100129105001006990541d0120142e210b2810480c0d003c010310810040c0462415008810844240004034080e01211901641c22101c100d440c1000d282000c15103074801d200c29507004e011a0184106403150300c07420802d1858256055280d014500b0f00400c0c243d44005c0c1f5440036001001d42c0e0000341c5010251501040d121002603548840c0382d03a0700c2e0b01c0100c2e001040d903000345000912400b00a00c0c0350440c0000011b80603601048100410b042008014058003c04c0c00302d42049a00c104c01d000d95001000c5c420014490203103140c0d1001e90301d0074001403c620480e05643d242090804950646004200114407140b02d41060400c4800400c8070640301000603040000280503100760030421711102c1320142c010300c00c00d62134507000c44110 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 900404712 1250 900403462 900403481
    0xe040b0111061501080606090904140313060206040c060c02090708091606170a110a0302031e04031805010f05031501020a02040c02010e011a0a15020c030d0e09101404 73
    0x40c001036a02420401c0200c2c1d84151103074403800101c40c1035000007500701000100b003144248010425001c20340c03a0410141d0b041503104000c1c00d0081c0c2e90401590950080e400d0349080d01141c030b9400200c46500186550003103010b54410b014080d25041d08850319071801d0030107504000356070081203030705218060166224090707000380c0d484102000409101d20125a00c06400905030040d044080d641c4202c400d60060110364081040c80e807400d25290309401500300c2c0105142e03010002071141f40c070b111948840340394500650001e43c07400e4a0060685c0c0c0308804980341480c4c140030003051650003a0521003030b400290300e5040c00d542e100b10401015803204080d20341140900110400117032641d0040094441c804e0b0004102d952440c0c03041400c5802c034a407400f08840c420501100b05882c0ca11034501503407045403800310300c4407000c1e10681c5002d44031106150503106508000d00c0c815030007490004844011500d03001aa1546e070401014082c141c0a052000120038000c0516450560300c007141d80d = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 900405962 1250 900404712 900404717
    0x1202040f120302161202010e101b0615060c1203020a0c08092202030114010c1e230102030f0c0a0e011b0206040306050421170c070f060b01030b060a0e040b01 69
    0x6481d50480004030304c513440e841180650520b059070313401c56030400441032060b07605446422000720354182c0105a41c595149120040c0160f11340d00302480050340000980780c07605406000801d94a8900405000760003005803840070300d07100600002442402102ca4005256680449000305901c51294961100c550a98031443ca420081d2040032100f46500c104c0010038001a02c1f03626019690380c0400b103c82c034150405c46d00e41044c8001810007000c1c401c50b14800341d440107820310742d4682400d038403001e400c00c29482c203a40311516145480540081d84502e140918016480c1c80e088a03022890141c07084220104000300a000081d5224020380c01516858103110701100c961a000300f01ca9500035001540d0f100d40710420842404510070502240d0301c00c1c0301e9000c1e5140d1104600170003070b003010000002c8114000012880f912803400a48400b142c1050210480c0c043e5403070203900070002504482c3c0400d040400b0110103283c080240c13a10840380703842d02860f513030003c0c1c00c020040503040d400505 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 900407212 1250 900405962 900405973
    0x1701050f011e18050303120f100b0706021306080c031b2506150b071127070306050a0614090303130f03050105100b07030e010e04050709061202040f120302 68
    0x30b40c58081c501c03a800d20003946440c2074401d500c009509003110a50081402a44100310000014140c0c1c0c0b00c80781d204a0446004034282c44d10403410f4200844c076442040e4840780450f401e0709000c5a0360092030301460340344002d41c03030a07620030f0150b5000340e044403514004501400001c0714180000c4540c407a6082d10a0000d00d003a10723090081c9016583c0d0b9a01010390105580c515081220320300c99802c050400b031070004021860034825600900c180c40c0d00030400b00b904109038034641c8600c0b0441540c0b180311b01d41c40806a91707080001c1c0214604689610000c1c0c00d1400009003400c025912005071000b6588840c1d440403c48100b0350380f503010b17011043c0c252104001404803052500440d00c007400120160700c615501d90b080c41806d6034804cc120b0b100101d00200204a483c5202049440c5103502d170400c1c0d40c0601840d801030b200c2c1461405030540007801c000800001c1c3da8459250000d503441a03c03509654503a000d0b940003240118051507600c02c0e000241800a50403c119200b41039210703104498 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 900408462 1250 900407212 900407237
    0x1e0e0403050d060807060903020103050a11031611070603020711040506090c0c0705180f09030412030806011803060e070806040c060311070f05010f051501020604150914060a0c1701050f01 82
    0x2d1801d17286511820010b00170110900031903906008180d00901078440c107200300c210307080d5440c0d03141c4009050007000c0341007880703014450303409800f0503901c001c0440b0a541c0d000b5616503028019500103c011030303403c12191682e5140e458203124150044001810840907a960034298144550103040f001000384121040010580e1b40daa051094004a460350031300c040c104011340044003400a0903001041d00b0500c0140701c030a451000c5060044d80500d840f500f035403a104016104020800c107603601ea44a03c42011007800816046803540750400d03030407500450381c1c80d22119140c48003a9001803100710440c070b081084c24031a070044201100c007040040d1400ba1165100d030400502080c044505075124004411030704030710301c1041d03408000e03d081d001c180c801000c0000d4986000801c000c0580c0012412040910a03a0703024060950340b049050800c1c10700c500e6580c0d51500115020f20300b05080402000301070340f26404400b075420154140e54840d074281400c0003c0e900e0314940031030400c034100c1300c0702d03 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 900409712 1250 900408462 900408479
    0x110906060909040f29071d03010510030506092802041d0604030e2205090309030336060d1a21070b03070f0c020301021b071e0e0403050d06 61
    0x24001d0b03204072140c00c1c8076101c902d401150901c0403181820342100301000d04031410300415961b5448141450008150100f40b068900940715400c4c555401d5860030041003005032101c3c0d414000d8a0052084503515541e1054055484000740d001203e00140059284108c4000f2240c14215a00c002d20101d4400030b0301107a0136039000002c0c0301003110390016090005050b0402140d80035400306850b080a42884501904285410b00c2e10000041d03686400041d0151014429184020401000e89541c0d085010714105030950070042402118075941180c070308000400c00c19012920081d211a060241c86403c80c03005250704519000e46400922142045503600f2141c2071f090b1100500c10703160100a461a54582580381d00004036801c2c0800c1031005051300030034000a239018070300e042d844410503480401d019002c1d241c5241800e403d00000c1510680c000709140050f250f29426010314a150482010032005146c0310720a042c60181001c01c0110344202e0060039480a010004585940c1e121702c0c5 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 900410962 1250 900409712 900409729
    0xb0a05030607080f150f060d090c0b12130215030a0609110a031a24040503060103030f180b07080a05090d05030912030c0d0f1101060602010906181109060609 69
    0x245000500c00c441000241e1304011001d940000000a29402d01d0603090081610200c00506031803041801041c050042c0e1041e411504000c0e500100c125488e40e42c6606c4000c141c3c01009a0000007103038007000842d003410710124403c00342d4000b01580c2c1400d0301d101300380d030003a44007525071003c3c151140000300e29403096002d03100301d0f00040c500c4c6a6458100500040c22102d0141c026090006801c120702a80d9849520018440000340842c3c4000c4075800d480c08400d20841e0f020541500510b000001410303040826100b00190030f440303048103980315032825a01300b0f829002d94000d00d1070920417540401d40e51405007803451a681080d0f8034020324200040c441c22000b40c001c40300d0758400100910103080c640980e91450259400540c105220106071503115241055103004100c48288284800f6126405a99003425014008c120007034582100a02030204800141c59031030910f114803031900c0005091111858010781181800c3da03041c0c0c100000880060b08080d40300b0402e20a103010713a6078079070300d = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 900412212 1250 900410962 900410971
    0x1030b191b080603010c0e1309170306092203081513060302032104050405060d080d0e160305060708060102010e0d030504110a06050d050a092a0b1801030b0a050306 72
    0x80c00120745691900528080c402082c0c00e0185e4103185c0b5621901d9003100c075207950f8020840b11060300700301d141660001070055010180c1a05083e580082110003080001d41c01084280c900c14802d98407003000070100198001c0320703c000010402c140d0007191040349080d4100303400b54030030303030304203e40ba40000c05013030390260312a44c0165250300410842c6030401a0701031a800c0048140181c08101c203107a02030380620b00c03445008036103e9001644903603500300d852051a41c0f100c41d55844520303108030b0f94002c00f5060002c1e4201c0c880c1c88250380c8245c40f0418ae003030840341c0c4000148075030750300d5400c21544641e0117000e2505540d2281d15141010710117016200c1c01d000a076500080501e000d040ca1740b06544806441400348031640c10030311045608c80300300c1d43d860003651400f04039519101c02c42c000501021038003030030b803034011900c0842421900340851203082e0320003091712429440d00000b1085100c0c141d1a5800e10041c00101c400550003904056515640140503c0043c0d0f90344000c03d00b451001c85 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 900413462 1250 900412212 900412241
    0x1140705010914010f061a090d0f0b180607080609060d0c0f1401020c060c061b121015020c0a151e03050612070302030703030c1e0b100509090601030b19 67
    0x442c000d17000c1d10343e00c01c2000a20745803504646070600c142400440380300c5e1040d450b008400030201602171000c450031220003150302c100350541610b816080300760b0002242d0200820b6000300000325121a100e01031080c001c0c400140b90200303e84800341001400204201c003110410060a400201030548455500080681381c0003103559000d400c0009041100003449540f04d4001801103420607030000800da0780c401c0240e6000c10300b803c08010030301101d0251080e08440448100c04020741646e4245152040390505201120500c11160044e40c076110080d1169411409840c820040c0e0404801140840303201170905110900c00007d03041206411541003001090302d1340203120340c500f4a61004950803640714040c080b454159400207813141944e10020741004000401007091003410a60160308040708041c104c07a80304945006c4c032003008211201141d0001110001441e410030544807486252040c01400c0c90343c0c29550362a141501c0603200da51900a00701450092040074400c0415123000d46 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 900414712 1250 900413462 900413471
    0x31050a1805070f061107090b03070306020d0c0912050606100e030604110307050306010602030327061003060b0a05090610030e06090c21061512011e0f0b0114070501091401 75
    0x10700c00c02004603e90b002038100410641da1000341c00300420142c013a80e9481402082c00c52161001a140c11010b17080980064400954040d0042c400e0b8803c000a9404e40c4680b908540e59512641d400061124050016003018000940714079040c4c0d030035003501c50f09060021442400c20046450b1407401c0f1021100ba20312010b03405002d240412044004100c00c600524031581003000003902c0e400080c1c4094958080585400300301801f0703a840c0b21140f22440304442c00c0d850030041091150b11688415603d10749082c002102c0c0c0d041c0078288c2d005603a00900644415100c102c1400f41c0000ba82118804050342c03486a18031006050200b11700403210240180507416908041100c2221091240070188829030341c1e642c028003021806541c003420303900290781d2414054021802c2020080202c074115440c02400e4410328001200c0c1d000d400001134030070006803048000c40c0c41200c4462180070302281e240300d55622070108a60041c106e00344500004101c6002c00d03542c07880045415800800340d40d440c1d = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 900415962 1250 900414712 900414719
    0x1206090105060a09060804020123120a0213030308100906030b0115030c09050d031716021b0105040e1003020a030807020102010e0706080703022b020931050a180507 72
    0x1a05240e01510048480d1031904100d19805021141103225100500240400040540e8040c12030b000480140c44049000003c03426141d601c142d024080c40c0b1102e40400c004140130106a00c2039402058075130102140ca01e0a503141914000c4000b010329505141c009070109600bc10384c09488011440b5011449a65040c40d0000c1c0312990000500301c2050302d8881d108145683c401d0380d0b141221810b0354030030111501810f0440302caa030590b4940c2c0400700c9000c10f00c0702031104442d504d40d48070038540c29035480c640c6a06070030314694900b0070482c1c00a1300c1480b0030300c20703061110317655500455000c102e4420a503a981c041207100040380e00590b000e80011903443c055580a0007035001041e480006440405d040c40805081106c0181800c003c141e030104500b18105503d030303885031074890103041e6542c2103280b00083c4000395000e100c420b80140c1846150054080d52010f000c0b940c488954010800e0150160154005000040840840700d4603484041501c00c400d91110240e28001c070080c100c80c504 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 900417212 1250 900415962 900415969
    0x30412050c1e0a0504111201060f0207120c170a05060406090606080a0f060509010209040e071a120406360606060507150c110607180603050712090c0b1206 68
    0xe480700501d0900342036414590b065448803442400d0392011500020341a00c0200d001c05c01c1e0040849401c03d09034460004524250403002d1a00710030115401c60703850f90b0306d5071030807502c02600120052042a040703605120103135611118000c3c400e400011035003002d6003519002d1400c582920f09407911a52181e0341ca05200d41e6000300009030040b40c006254080c0c040e41c0341c1c4400c102c00107020380440d40d0b0302c0c0480d203140c00a4040301c02c1c03000300920074044075406004051300d03000644500da0031412041c5802c526164804161210301942920700354407075440d0744401003e841c4e600b6071003191140300390b090140c1c41c2a0040e41009140b986400706511402840d10004480d0301c1c0e001751040c02014004040007400601003030f513104940c4840441c41050001040d28102c2c2c07a4a2601900e0040800b08025540d011942c0760710080d035007690321079581e81c0701c0341030f800c0318400d03100c841c0044c07030602014042003031980011035141d11501482e00b070140d443c01c1d4541d05411080607086940c00d8901071058a28 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 900418462 1250 900417212 900417229
    0xa0308070e0109080d0c020a0b040306020301090b0406120f1a0a02030717010803181207151b0c1203090905090102040603060e100e0c122707080d050903030412050c 72
    0x10001e00b050701400c0d0130328002650340c03c190740c98002001000d00140d011500d500b20494020890705000c41d0311941c50f07140c001d001c1d400074081c80158910309107008940b80b07818020300c0100c0e80c1c0002ca1540441e0709031107400c44001c4220043d070318510013081c840b0a013a0b0b02030880e4801c01c268880103850381445480102545034140c4503144581c0088014800c0840220807500ea1091007a20f242010001030089483c9a104010140300741c0034115001826018045418044030707556034400c8000c505d40c01c00708440300b01203000505503218405c2c2c14006000e030401841070441c00b03814110151642d40c408034003074510440e1044c0d00f41c0d4010504020607a01405100b011304440016040503182c99443c00f040f151482c403030520621001800302e08101c940c48102ca18500d048400d50280f40781c0194910501c01001c1c8803400c0c000003090340401c402002107044015580c01101408030041c0e0000704031044d41218000c50383c540403c0000117064091210700c440d105204001500488079400e081001c40f0 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 900419712 1250 900418462 900418487
    0x12081e041415090318030f0f070512071a09010c061d01110f030c07081306051b51040b1006020309040906060b0c1b040b010c060c050c0a030807 63
    0x84030001d03c00703115804020380e038040300b01030b404c18200e10030080040c1c50308a01d044260b80c00c0c0141c1c010510110404601e240c141d8009441100050410b0b0300c4669440001c1c5c42041c060100240d40e10190012110060103811414500000e03080c045890b80300880740903c40410104e61b01c984a0700c0801020b010b8140308843c81110503080c1000070b0400800d40c4030040142801500001c0c000c0204a11002a68100b01c1c0b0344c01d032104016119040944a50700585511001d40002d20b0f9946030768030002500a200180c0d03500c020700420880125509541c030411040c600c4110b82c0500c0c01d019400034408202caa42002401804e5044c5414154022803015003214142120754000740100764000049840010741510b0000360015541071040041203950040f8111100c00246010b05500001d80f4803200199280049221140038080000310350018a80c1808070340c00120080100d55540d20141310b0310b485040c100d24100008036582c0c105209a20220301080040d0b007030104490f4004040d1034017 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 900420962 1250 900419712 900419743
    0x3060503030a1e2f25091b0c020d06020c0f06041e0503030403080a0b060309030901030608010b1309050708190302010b01020d1710030813080c040912081e0414 70
    0x400705012000110440300c0f6080b03014855012040c19110401c00c005c12848280c14024000c000043d110b034448180c5500c24100030600b0994101c0556540d01905054110562100013001c883c0754244142c0d072848000c1514460740c2070242d84c0541d182440106426810342000c0e0480b46440c0c40d00580ba0b9946142498090801800b82ea000500c00000c0303c2c2c00a4050030920740d5581e40c42c0002010340042c0c6111070f0441408000e010b0b14070b00020107082400c800340c03000d110054454030910708a034003c40500c0c9d4440d0490282c2e01c1e002070703654003109401d0702842c1900e541c140c807000894034050144181c1504242c00041007800d265080c490300e0002d81d024806031a21002c4220001c00c507840000214010f0f00109000c9039617483d0b00d0000400441c0e0000c00c4589075440e264070980e600c1c10901c60612280181145030116103420f1181d90a4150b000894541d1203140e03030000c88415100405100e1061500c007140340c100d11440d20760714801c42c410700d04041403032a52240641819044041d8142 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 900422212 1250 900420962 900420977
    0x12050a0606020d110708010c2f100c02070807030b040b0c090f060307030e07030602041e0305120a02070b0d1506020102090108220c1e120b0a090303060503030a1e 71
    0xc07a034042034650319041c482c030307110211034410314409007844c82e940d1020000c7e6280c5181d1002d0183c10031070f114529460503072840c59000070710642d250303088003000d500380a6800c41151003200300d20650041020614030310450b0392039500c8038560391402d80d40ea0800c0d903424000d0410442084051441642d0000700e1070f5800e410013081c0c401085104034401d444a00c122008400205118881c2c4d00142d402d01c007502c1200d001590f2414584002d40c8140203540200f40202c0f150381c12403000a04060859074440001c098020b0841c11342119a0083c04d030045c04c50246000000300c80c412500604045103800d14000742d000010000c07401e0405040d07120b0400d59006000d400d14a81c2c11441c0564440e4100c54815040b026131800c0d183d9480720010000c00c5c02c49641c0e40454140d1840c1440341c00448030250f081461502c48003000510502c2c0c0070000c162300740c280b0001d003400c142030300005c0e1514440c1c02d020802030f45440010b400e641004448000081c040130300b80050303030050602181c2580e03a0382021503 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 900423462 1250 900422212 900422219
    0x803180f060a020303060f12061303020606031b040c0516080d0b011d330301051e090a020f0d021603090614040b07050a1b0e0f100608060a0f0612050a06 67
    0x13034980c04010103a5105090b2030301c0801c680e481e00c2c0460444004050300380c0748a868804034505032100d13400810b50040c401c1d5000207140e4100002c0300c04400030701c403000e40c103021844800c101c080d0850780e10410070000e0611145a940020b038219021103840b514183d51030f07401d0003004204845031818001d042004920b2080902d00d290707121290100802e4a080d0609002c0800b41c80c010f040103521805a1030301e1112096403107800b0005541603480c11a5040840300c80d40a00c0411044404125a40f1420400100e401c07240b042c1d008004480c48014200d00342213508403d1800c9070028180010b2032070429103c1000c2540c40f0625601801c42400c11101c0c1790824150301c40755001d58010024000d0340001c0840521204103c0f806080b68801910100302c4003040c09221740c00a036100380d840c60507002e404100707420800d0105a10906460103541846440c04004443c1580040c0200d07070032007104080424114a0304100783c002e0300c41911800c480c6100c20806000320368004140050903450b200051 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 900424712 1250 900423462 900423467
    0x915040501081c03020a0f1b0203060106090e060907021504140703060203040b0901050411120a0602040807030b150310051312052a0a0209040c0e2403060721060803180f060a 76
    0x407207e80d07c10703140c00440d0264800d904015001c5040000c0d515100d0140000b580741e40c88411013003a207200400c1840252541c00a0041d8001e055800ca80942c000d20359030352051480c8200d00341c1c803d02881c1c9034180d03601c0444071b483c20500036410546465400101708420b00001e000320341e4118503690020000f600e03058464540c18040307440c0c3c0030302c21018a0200c41e41c0c204108650100203800c040c08550703981e51200b6441c0d55007140d100460702c000b0240c0c005200d0008041100304070104c06400b4008400041d0514001058005e0040a80e02d44a020a80204410150034160b110450b200c4555907489034442c28010701d20b04494005140c030340031410301d0f031680208244400c1507068590007216256440c200084642c103410a042c035000e4203081103103010f902c00c540d036202d5440400c059280d03107401c02031546940084400902240368040b032581280d02c0b40c0005510013800c140001000c6844880a50450b0b00441c52412191700900101c03d07149401d03040070011802c1151414607042d60303050701 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 900425962 1250 900424712 900424727
    0x6060507061d1f060e091e0d0c060f06090c020f16080307060209150c150a0605030c0f010315030b0f0703060e1f03120513050406050f0915040501081c03020a 69
    0x2a82a01c81d11442ca6652a550f800c40009005c0420700d03240e940c034020303c0465031506044403071100c000ca585800b400b10203004c110035890114580d2100107848050b19100050854079140602d1036549010018203081c0314458000b5544043d4054244402108221072418071000c010480c1e4821604003008403d030000b04550b0000c0c2d00c00c5025840e81e041400044801c081d40e01d480407036000008000d03404060104034410b408202d01052403003600c407003450100f04d42080c02a942c00d0382c060001d0000c0761600341e03010b0902c16014500800c80c40003145003011a2081c9900484a03522600180203444101a421503401405c038913007000024603001c14914030320006061400c915070700f16030300041110f141d5419806035400c007002c482d212000f000010420b0344000505020000c021501007941d10b824001c2c2011124014a09440d1852000c200075007400068a0780d10140c40301e10000c101600e0b9400b9150007000c0800c00b61a1201e12600702c1c0d010719210260750010144100b18040701316402504 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 900427212 1250 900425962 900425983
    0x90705060a08130b010e04260d150b2709130f171305010807090302130b06070203072607050a06050702220204171908090d0606060507061d 61
    0x140300c8000c0d100d0f1040181c0340400424042e202c2d00f914000031400840320f00310140102d02c1007048940d2041001400c58161a4845c490070401170304010040045001e50400a007001c1c400a034900200d41d5040c07840c0250f440750740c03560a822030b601c0c44c440702052014041841e83e10103440404880c41c0407907812a12800e6280020400d18250303045205001e0310b052600350301e0500d00710b5135545902d50404040410400d11450340042c520031300181941d0701c00d8400008680c2c0c09000c456010307190080c0000640308078040148c200e8014440100503903810000000141000ca044003510750304611200035803440c140c040d100c0c40d40104070402c041c0c0c40d04600c0d031040383c002d4680140c13038000510020b0514054421981145440300c00109010960342e030041045512001718000c80352590004c6540f40c4900400b554080e150300010000840e46442c010007191400802c0700320103400564484c000c554031504240c0000c0d80100d20300d81000000d114003800501c64645842050307010800281d900e0480302c0 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 900428462 1250 900427212 900427217
    0x40501050a0b0a11060c09040b06121b0c030f0703080105010932091f0801060608130c0302060408101103060f010f0e03300c0a06020906090402040617090705060a 71
    0x10b41201607510038021029001c00000c15a11a800c1040a0000c580c1240c54683c0c451450301142441612b0309200700d0303640540c440091207290350b5000480d120341007003907114802d9800401c071030400b600c41800141140244080c540c2d81b509040e08005103a400c050f04000d040c40140d0205001c90910341c10112003560f420350a210400011104164a020740c88032036542041707060051010641500e0601c1c10701e60005103d0303102c00c42d950103c150984a1910032400411000c90120320070440070801038401078000c110442c48180d481d80460b01c0c0e80c0c0a5400920113402a00030074500941034003603452001202c102d80c506604102001440000e100d10344281030007000c03003a000f80a80130340999021680c00074281c0d8421010000c12081d804250b014402c42283c01e900c00780710081041d0151841107021500404980c005540c5450096100c140704d40e900c04c00501a9070496a00c0b400140080c0259a6514519030354681100081c0079000d0400c0403160041a8244074507244d240a4889581d07062 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 900429712 1250 900428462 900428467
    0x190e100b24030a0c0806010e0108091e0303070909020703090504150906060309030e030a0b01060c060f0213050f090702061f080102211608010e0702100c030c0905040501050a0b 77
    0x34800507048003442254000c503484241115480c542544000c0d600c6404810000d0100c40fa10000071540b251085070400e002c80c58552040360309502c55282558040a088100e0351351b104560083c40145010003d88040c41e880041001070781c6038009030702c400401c0500010350800390b5680e00542095018041c4070f00440d581c1541901880d0a942442e008000100041006030340b1503030001e02400d4042c00640c007048038140e031802d007030030009440072611340c00241408950342410001c40e00d0141401c0192605070b11a14040c10340000d9100a03c007241d2140c40c071541c01032074001031000f2001c4000056110f80c602e1001c0110b034603000700d03200c0d07444802e40300201c1030855030f2001e1000f24409600905c46942c13003c82e64841d00c107240005000031821f40702c1050203e94441c0900300f0f445800f01c0022001030004030041113015103600405801840900688280c003070b00e56001c80c100c900100200b40001e40340c007030030700c8419002486200a0300c0c0540e420b1000d5070404021411110191150b0b05030b07500300 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 900430962 1250 900429712 900429731
    0x20d0e07050a1e15120906020a020106050a08070902030601140a170c070302070b1b01090605010603050903070c0308030403121e1512080702060f0f07050c0402040302010f0e1504080105190e10 84
    0x181d10401c5c83e0020506042100071654204000250410b50041c1d01640ca80b6130007107407a282c150b40c450101d4450800074020b550800c44008080d4101401c01c906001c0f119060381000b09401f8040e0002c40d00e16542c0d01004050900381d40704500f130140900c40001000c1005901082c0d01140303420a840090845a9881088000700c40d03100d5010404003249510309000b000800c9004d8015034125005687c1c00e001c00c1d101d110000780c0707034860341e000244a40c4d454070042000881120203107900a000e400c0c0782e002d604400d0710702000d03205500c81c81e110902c00d6072083d0760340e006548101850044400342945032141440014240c0e0203500401802d84003020035103c0031543c800c0c00f10f1394207080c2598441e885143d01c89444004d5004080b0807144c0e8080c0c0160b040043c10144261800c46e07070160341d40c803171031850218203581c08000c550341541c1003145072029410418012004000411030040006003a1612995460b40040c280980b00c81517424822142c44180000070584c8100c8800700c4c000512030301 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 900432212 1250 900430962 900430967
    0x1d0d120e0301020406110606040e210f0d020307171012060f0c020303010906080c06090f04060801022a01050402010519020309040606110606030a0c1701020d0e07050a1e15 75
    0x4240c51000e5140d0300008021170203a5004542c02d0740f41524004880c01030f1251320030081642d2a00c1c00b10f25055000c5540d4280e1641d030400c4d140c4611001c5601945040103c006002103540507041c1190310603000414071421580c400d17481c28403065140b4482040c1d0900c40c0121000c1601ca114543c0c0542e0314038114000c0c020a60b2104102c1c03100154100442480318001070b4980d0030074030601485078685200081c400d040401c100c2800c02c0b0080070f01e403910007075030b0030050464001c01c002e03a0040c1d41e400021410b03a0092004003640865110140c004502a40d424540910104110046a4103203010b000c0182d8000b8240ca41c41d080310503890f152010740c220202d01d90f000d00e80603140e1181c20700398002041c542000c01c040030445c41c3c0040c1e41071650383c9010b0680c2e52000040081000b020190300b04010341c85150940001071080c8005407600051000c11000d4841c25480b505c0240c000841c1003005203015502c8ca802080d43c1c521070b00c002c0940302c024213034440f114420466800b58030a415a5102d1 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 900433462 1250 900432212 900432227
    0x10b0702040e010906050421050a0c0f060f0f0e16090203091011041a16020f031f0209030607021219031103071206090e030f0c19050c011d0d12 63
    0x110000b0081040c0d02140c1072002c09890145c4080c1c4d8620040b0f00b50125040c0302c1c00c80940700d0900e9403619071034074885a6045500b00900300c010307951800b8024038900016002d0242600c002c5032444003040c2e110300003820900b280d407511001c002aa00c4494803050b41c41c454510b1408494441100507143d5481040c0c99080020b81c200090f034451a2202c0b001e2590201d401920595140310b200203e400d0b0b0403808000103125103000e640c0c0ca0030078001070000503d04a10150740e0500040d095a07020020002c5003400c2000c120b01c551121034010070144000c1c1402c014440d88010075100408c50380071031400e03140d11889010700e950b50820205030a07440350f80c00b80c0c111114208245c0100b503075902d00108010030390701151404c0c4004074100b4000149900d0701d0701a00c110003804402652a005404c90581070940c45a000f403600d6000d103080d501c0640c551280031510250103503020307150308051000010004c80002504204c440c290b405010803179180d0004680c2c401d82e11054102d4401300149007681c000 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 900434712 1250 900433462 900433481
    0xf0303091202032106091803040906080102190905010804140c0a120b060102010c092c0705130905100b1e16032607120b030a290609010b070204 63
    0x16214441c4541450368000000c18410302e1242c00d8040703808010603034541100082ea140d941c88500302c00418106e006c18218031020318000400c40c0d140a941c0c07206401511650b60203129181d40c041603555901000c80c2c07400160b0075191134040003150400d0000307842c43c00040c0000e42a40500d070340000300c6400802942c1302c1814020000c035541581c3c1c411068100800c080c00b200d010300020701140d941d50050040d0105264507440724241241044104c00945030344c00d1030302c500319180e041c0f40e451244504000c2400f4628507961030b5690810003d07440100c45180e486444690700d02010880b100324410305010503103012514032035039021081408244c1030300f0070b04040e010600004032403044c024501c11f0000b21030310a8a84e40010100100544d0003940350400c030780840d04183c030000c2c44c6284a64480f8407442c10741c400c0001c0703034a1217402203440c0c001c24036002c0303400e04066002c900b113034803580c05d08124500d011100d100103071910700c000c62550301041c0715242c4401e07004102c83c2d0441d66280c05c0051361 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 900435962 1250 900434712 900434723
    0x603240603060f06090e07030b01050609030106050d05060f010602030405060d1a0a0e180606030c06130f0b1213020f060c07050d1248080c1c030209010c0f030309 71
    0xd40003c80750005140350b10404243c60b00c0d19007500d40c1d00070301141c540122600404031005683c41d02c4140641903000c00c0405525550303c440105043d55091501a0701c2d50041e801008189001c241d13408052030181c011300c05640c41840100066624003049139940043c08601190151050051468041c0e94051017036208003078041c0801c1104582c0c0c40f4510844005180d480c6807100424000d8464506942203034040d0031400305529a410600010034090348142074601009a59074141804107410390003204500c5000142521103141c03051403e0341040941d441071960014617400141c81c82c010585060181034081001040c1002c207101d00c80042030060038001510b5030514040e0303004181c02d030040c004500c40301144000f0440d50003008a54cd4603d00541035541030340f00643e42106040c2807201c40541d00c00000400184c0e89402814040071308000604400c44130516942d007010203071f51134070100f501c140300c0300c405a86c3c000c8000584a400c41085151800c8500341107000c2e00318918060003 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 900437212 1250 900435962 900435971
    0x6020105090a421e020f09040908090d080a2003090d080d0c030f0f02040f1221121109030a140f070b040e1b121e0721060324060306 58
    0x802c601d1508480540130a19000c0b12004030740004890407801030080c02080b40c02c0c248510992030509900032101da9000e0003e660511010348002883da801640e0100c801e5840811401e4403950002d9240111401c0382241404030fa056003007040e500e01401d112207109403185202803051094a404032542c44910010900021201450203400362501100e0000d00c203280240d140c140c0e44d0f80e4030a45060300c4d401f5400200c1c043c6003056603144901c2c0b141056800924105c10070600248242002c21119155118141072030f81c0089254115121006000c40c5040f042141800d42c0d44d0114000c015070b80e00078079818220401000a600d0a504c045c5204014801d26402041c548850b0002e082203400950080b2004d5032030599003607100e4803251085404080a00600c0040c40400180e2603100c00c6501c0d00c080302090051180c0c030800c40039105074000c5100f83c852800000e02030707043c1e41e100c4e50000c0c1d000d020340d9107147d85030700e007940380d4602e031100c0b803e0540801000b014603034000b0030040d0b400600921 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 900438462 1250 900437212 900437333
    0x402090f100f1d030c1905180901050915130c08030a021e0102090307030f1a0f011404020708180d0b070e01080106030c17060112020301090606020105090a 68
    0x20038604681942d10041502c10548030001d1a0581002941c110b0103000380c020790213240c00b03104c060740c0c0d81c0000d40502070b840c000c041155101c00e180c1a110902c03003400d5220906200c5a610308698002c2d02c410210340066900044001e1401020b64120b444030007101f01c08007890401d0a590145ea0304910000d0000081c0484c20315070004696000c06024940d07060364111900100e8201e1080341002605038120a10810110704d4444d0542d00142c01821100304030748131800b030507500c018101e40c0c42c1c0c0c4925041c070050114000b00d810507407009109036021071900340c00d921100c0740380c0206004054603104054204001c0e80794440c00718201d55000d0304004142c2440f84c030180007006030000c0180005e886000014001340f1a00507080d04a1190300d41c11003000911220783c481c3c0200901d05410310130420844019041540700a500030084c101000426a003018802030a4850103420740c0074076444549103002152401030389141d0b0340712960140340000103110f480c0b118600000e25401602c0300425241 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 900439712 1250 900438462 900438467
    0x2030109050a05100f0306050c09041e1a090103080901170906040b060a050d0611130602011a01110d0318140f15090c01050c01020c06010b04030614040f020402090f10 73
    0x214002c500290301480705660360011010250340c284140695100941810800f03d03c89a001c2c1c0e420520341c4142501d050701050214081d40c5203071169404d841031649481500043ca4070840325028180102001c0350310940300040c501c01c006000251645c1000210383e40181c1c01480c1803001c10840e2a0200c440386803100c040350710b941c4104c0b07090f142c0c0e038040d10009049181001c101c100303a490041204640751055103954009000400c3d86030600c0d00204003040c44d10180f04082e1000302000e07800400d12000351100309401d4545503140341d052003c101024800c110000c610031850302c0d850301c5e00040300d03495a00480910346404070b010b0449066007090002800d0302080c120062080103040380c40420704e540a200c620301c001c40d10300c01c076070300025007000c85984520024500380060b41d00141c24030445820090501e44282e0002c82080d000141c10001c00400b40241c091517020741d140814a0326103602e4140444a01600c0203110b541c0c00200344142e40d43d44180d00141d2440984034000c03079001550003 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 900440962 1250 900439712 900439721
    0xe0114040807060c110a06080403110f1002210103081b0a08040b040326090103111215120718111b0105150a240203120f04120f0917010b0402030109 65
    0x5844d8005d401c40007480a00340462a1411568141e503041c0c1240e549031000c54452101440c65006030090f8900128401420410805452402c0c4401030b501d01c0404540c10030301032030609030303240801c3c031034010404184034405590a40d0b842c03014440140a81100c0c040c200802c8801c010300640f004140800e040c0682405170083c1da2240704409003260450300b010030b075010402d04504019808102e101d4071940b00c0c1d007059410303103d48001c15003042d00b04200f1000340710044030080310001003210540b01da0314040044110451a0401408440c1e082c145550b8442000394007858241c0c1e11804019440d0f403900007100c1c0f41c400c480055414060181e010035010380015100b80b859a002052629910f1410160040c102c816003c44003500b491b40869540046004840c0790003503000500007110580483c1c0c440740c0c45215409800c04075071400b450075407582040c0c4a408800c00001a04284966400150540c241c6982e144c02440005c03e500d00e06014011410f451504140080000074908909402 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 900442212 1250 900440962 900440987
    0x20f01090c0501080c07021e0607050102030a0504060624030b0f10020c0112020f091c02030d020c18072106050607060b151e090105070b0115020115060e011404080706 73
    0xd03110080e4840300d8141065000700d443c040d48c0b01c04102503d071f11299910504400c0e4800160070300341803481603150309007240c0084039080c019588400c10402000014816034002c0c0c0703201201c418021540c40300c015038003a40590600300b45035460b4070b80303c41ca5803550700c80103924000400c80d00c0ca04400c207100a40758059400e026002c90703030302c6210b403407404885d0084e596001100111a42008080010005245420200c904a400c0c066881201580f410700c508161001c0c503030002c04030907102d002803002e4010014201e150601909041c803510641c00040c01c14119499403c1141d0ad110300d4007054000c0c110755101d00d03800f2758000b41042c1001042e80149580f000b080380c03600c50b49081c00c015403107984220b6a0803e80761032048440e00d4110300c01000b0304000d04040c0b4010b070411140b03035101e07a0074007000c2e0810304a194505410000c2c2503824020040155444851101000d1400001408007041030002c0d50600484d002e1080d040c0c05110141c170020507161046482c80e03581c030130000c1d100c28580070 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 900443462 1250 900442212 900442217
    0x190306030c120b0f0105280b030f1e060d0f0201122f2803090501020d0b030d0c051c0c081315050a090504020f1611120708100c020f01090c0501 63
    0x140003a24144c0d050444604886000d0801605c45061f0b219990515009048001c0e1020510002140303007002d0002861182e100303440411a5401d0003015400041d100202289119000030300700905611038480b084180e96000070708050040003440141c41001d4124044c045136881c1450910032400d01c0081d8081000804855080358514a00203032428801c00144202c510541c04007103842034020050640d0202481c070700021246066a901c070300f0380e0b2041400313825068650f0101110f80c6410f11034284a44201d040c490750800f00c40c0e03512074640d2200f441d034410034400070404003149400bda2040c814a64031402c4c0640e1240600d41c0307a9898941390007000c400d00f030400b881014090250003141c00784601c0f9282c1e0307a52640307031000300800780d4440c4a681d080180288420305030b40140c80f042807840e62042c2e00744040308100d5820b100c00381d031482c5448000740c1d000321020801f86001064540140181181c08034410070b000c0c5060386880d8610482d80410741c03070580004180700380c505540f4142d6100341d = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 900444712 1250 900443462 900443483
    0xd030b0f031207032a0803010905010b03040506040b1b03010e01030308010b07150f0e0d1d04090308060d050c0d0c030302010c090e130507050409030306080d03020708190306030c12 79
    0x4105269030b0341c980e0195580e01d4201000b121011074000c241c1488a49140320308404002004d1410000d04044004d007102c5c0104048010702ca9a445030003524050500642c0c41070451902d40c80c3d086ea503080213070014003036900b040045140340c5004140c40030100c4942d05c80c6c96907541e5074007800345468401d100039000034000e2000459a002407000316044c1c26004900c0d01031440004040d00028000c490180d58041e50701d4002e09110743d000d014045148285841e0200290380031588a9400040000e00c3d5202d640f4103580c5100280c0c20804858200b10180e600d600c0358180342c81c05514222524004551004202103130b50104184802540c0540e4070a9009000c0d440790f0a0007a50954110701408058805c080000781c083c0c0c1c2c10f480c018102c140180d0842d640d19584202240c11540c2c41c240c240c0009450f81400e00030306508000280c001c0200385021480c00701c1645580e8400d0051055140705480c1143e0003500311482600070001454110192000c450303030302c0201c2a12040f45140c102c40c00c0142d07 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 900445962 1250 900444712 900444739
    0x1112040e10080303330904080d060504151a1e040602010c02010204030f030e0112150302030f070b041a040e0c0903010f060b0a1101060e0a0b0a150c0f140d030b 70
    0x2100341c90080e40084914000c0c11441c914064440c0805200703d00e01c41c2850b4041201991b0f180c4007140903500916080e42d5030408005080180d4a650304110b001d20705000c40c01c1e490900a00840044810b41c400f00081c0c203141d0485035209119180c24203620480348001d1200c00f070100700c0100203d40003500200003281000100341c1c04d07401140300140c24025803c4200010034011007000b007038504140760103030481010300192800c490181648003106859001d00380110705007001055040040080206165882c0c00c240a039070744924003c24650396003004256405a203c078040d20090300205a10700c00c1847d049020841070341220900c14440c1d070809007a0141041e5601c00c0005440190400a03d0540480c8055507000806a0014100d65031084c0004084014001350f5025464034507000c1055079601c01006034400c8181c010564400795112400c4800b50000e403201091a441911126405414201480400c280244a440a020f42102401d0581d850351002c62004011245103030352126 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 900447212 1250 900445962 900445979
    0x30b1f0f050c100c090608011403100b130501060206190e100e0a05060a0929010302060a110601030b16020601080319030b180907090915051f0603020403030e01080402060a1112040e10 80
    0x82c49c503050b0304204000c0b041580c954100c443d521a002d442161001c984500680898100741c1c8501c006130801814054103544800085400114202c1e05102903201d40255540700c00709070070950b02c0b50341e0310840e1410a0740248240c44c0c0303107174100041d80d0407450002c454201a01d840c0104580f1004803440b5100c4c0b10b84400e00c9003d003000248645000c43e820340e400e0000c030b80d01c00c04031642801030140d2585850601049464080c0d4810000a801800d15414589080c0900010b40e019900013000520000b400001641d2802445850419014900c01804d0300101f0040418941054104180b818184d0041d4006e50082c202c43c4125441036603034172042001c0350b8480070010306052140880700c2d1006e00075040300b500b01c109160205a20f034008261403000081c240c0c4041c020035000705040040c5600000a0040f0746400c0c2084501446c2c960b002441074800c0840320307001d2102c040d44450064030208200c038080d20000440302d503140e032103002e1501c40803402c840b1181c0307010b1004c10100382d026 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 900448462 1250 900447212 900447239
    0x915040b15040e0303040f0c080a14010b01081b03190507020c10020601060c0609083f04080403080c1e0c150414150c0d030b1f0f050c100c09060801 65
    0x400c00f0051030a646555031440c4c0c101090860603554a506d40e0700c00b180c060014049098000c0c403858002e41c8030040b04110700d082d202074002d07440c144506501048044045040581ca66200440489607a903941080c001003403990b403081641080d01c0c040801a1146c0c000541449000c402c441d40c890100c3ca0b42001c0740c4d680001d000e1400041c2c50703118000d0006500790040d2038100c0c0304402d214100307100640742100f20b02800000e006840c0800802000850981800c041124076811a12181d03280a0300c070318400380f14500c0f0041ca00000001e59010250382800250420080c000701c00001c1650404c0781540e47e60003550a0b48100900c44c81c4e62041070040381101c0480e000c0c00142d0500c61100c1c0708110342d868003040c12054900c0c08006d8940107000502100480c0b41e519180010000c10790b0060004500907150640c016511a801c03070f010b041d81003c000e8034002c2c1c3c2403500507500c180410f2030500b010184000d20020ba824400d1541c1d902d500b002000c03094481503907a200c0183c2e0380e16135003035945 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 900449712 1250 900448462 900448481
    0x1080f011a01050a05040504051f08030301030f0b0705090a0308031f080c150c19061112061306030b0c04030506090a0c0b030606040302131a010f170915040b1504 71
    0x220140c4069602d50041c005400303da811410302605080e40c0741d02080903a8011a000b40d80b0b00b8003942806c00700c500309908a80500078100080d81158110361750401c441e0300c5480c0242c24400b000001400c2540300e0030458151200c05021800c1c2c050b641c0c07a0000c1e49405c15108505402011044030014a1700585640c0480e0500f07001041d18400d5071050001c0002d9002c4d080c10502c1c000c0003100b00d1400200314084070040400b03000340d86660365007040c40456520206407c28075008012012195060142854014201711102d60001079058034403c003c0c000c2c0cac1e00c0180304a60440800114201c400003034000c480c000d400780c0e921599030380407254940c4040c0c0300060900c90484000e0000c0c4050348099980300c00081c0045162030b13200e40000f11081001c0c0200400d640c1c494400980c44424103842d501c00690a0034500d05010301104c019024003650340a03007100c2452400054450344c4104642c180c01c0d007600300c41c80c11744d0509084c448a280c90440704184c800c8064114031006040c20322488400 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 900450962 1250 900449712 900449741
    0xd020d0f050a0903141516030609140720121206190e07120204090218060306012003040b071a010b12010e0907050301020d020705071e0b0a031e0501080f01 68
    0x2400e080da03480e00e448111800441c0528451251b40b0211805040f0101c1d0244480040c01c0c54940a0400001c2c251041c03a04151451418004d00c1c0382c0c0306480504142d0801864108000c04c00b6060103440b109503044002000144500f060066014005030014032404020498100c0c1d00c0d42e503c01404102e0604006c5500c0714107000c1001c00604004c4080703590030800ca03140101051000710502d4040c1c0c0c106810080109900040314280342c0c60340102d031401c0da902641c90a042d440c0110000c0d1048140a0400c07480100c00e060b02000301c2c2c070610844000c3c15003000141d49403500c07400c04030105011301001590402c407540c0089051105d007000d890710b1050000c03020b01d42d682088c104894000340602440f0051160304070205050b5400e0002c3c0105002c0003074016111210b50800303518022240e0702c42a10301402c1d4604500110100381c40c40e050b100c40704445591109900011030052071140c0700d007036403410726000d000106130103500003d041f14850b40031940141011070a02d401c81d0552400d07a9030 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 900452212 1250 900450962 900450977
    0x6130311162d0e0106020f1b0f01030f05100512010204080c0d0302010e0d02060a06050603010305070501031e0504121403190c11010e010f05010609030b01260d020d0f050a 75
    0x6440640a00049214900c40091000070100801ca8040080e0030070005000410014010030354100b040610499041000b00040246011500307410b841c0395400ca070042701c0b070140303040241c0d00907001088200040c100801991520503059214940e20313000c0c80380300b59000043c80d0340c0481c0500a680c1a600f58034060b24400502c842009006903a40d44124250b540f40c07004501000b109000c545401d00154010344202c0c60969042e41c220792a5402041c0700d00014801400840c0000611000b665000c1c00e001803c0301c150400c80c2e6a480d80d90122402060a1400300003c0140b5901d0103042c03010961644012102c1c2c82d09143d078140000c031062a2240b03000740410440c40302a070020307103400a039410001c0c0c05660702c1e800f843c02c2d540400300d254100e0b91100b00343d41c141009840f4590040c54036241007628070782150740703a85030810180300e0501200d00020302202841c440c1030313031001041140e10894948201d0100f0203511802c01c03003480d102140114481c3e10b2040d00070401c031050240295903900 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 900453462 1250 900452212 900452219
    0x4180e0a083a0e0106051206131a01242a06020906070501051006020a0209010b2b1a1c0303050405460b13140613031116 53
    0x100c41015000d5400301c0042c000c00000800c50100200c0d80c80e00b100300e502089003180f420000b801c0d580c165104500a1300c43c6009040c2c03a4402041c0d140d0840c20301c008507580040c85041ca102d8500d83d16040404842c150340000844141320704074419581c2010402140094900600755401c6c000c04420108440012500d8410301201c03034034160100f40704840040c05c2c8505013002c940035810020b8112100c2e950303071050000000f02c110000c0000e001500c01407a0440b855400b240da0000306100c0c0c901d90302170100b441084154441d0245501c06980342050090041c9203038a00042d04209094403400c001c0d04c20581d02c2070401c2d08181c019280e4508820518820540d800c1b802494014400e403000e0050521003130301d0880c00005100c1340e400441d110252a4401e20b540090103034000724075001c182d1440c0c00013000551204038140c1c017003540f03003180034510042e00301500d83c0c0c01031603461030a50084204100c0c240e848000141a118003c1c1e50308030a01c40b50342d00081d55040300d40d54003070f00d80d00d40340b1041 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 900454712 1250 900453462 900453487
    0x2111040c050705063301090801050c040504050a02091503101208040612060f0b0a0203072a06030b011704020105090a18061406090409021504090203010513090b0106050d1104180e0a08 80
    0x1161784418035200491903a580780241c03c5442c01d5840f08440b01d80000c0800c00c0346024001d16402008000d02149001207620004070300d20b074000024101e0f540e020000400304041d803040b02000308420503110f000c0707900a1400407120b47c4140a000082150002104c140e49105c5c841c480548400c0b5181d02449030425441035196042190100c003107200070000200043c0c804e5554003003180503019448a82da52440414800e000a50001004c1503c0c012511505030790050205a00340e801c41c1c4446503688032400100e59500c2102829600455003540c0010844002400308a807400c078048208001512850012805170109418551110080c1b014218078503080d4040d030708481c4000c00740102c42491000000280c0c004e948000b03070155002c00100664100b0070800401500c0205040154240e5070b503035040b12400601a010802601044081d034508040d40040045076185200c035454039900d42000049102c01d482030303100f03c3d00708000d24401c1107000404900c0d06901c40c64141c105662920304 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 900455962 1250 900454712 900454801
    0x608060d022407050a0203010506030607051905090603040f020406120c1e030510050105100903081803030d0204091a100f0509040f0501060206041403042111040c05070506 75
    0x1440c00b40b900c01070707030a6400e50320001800c207548641e015294001e9076004150848100904050103500b15004004485500c03408a50f00c001c0841140f19480780c4d003403801c0740c0c40c0c080d000c001500b00200005000a0040141121040c180308450601001d0303162400b00c41e9070700e11074000608078161131406018040b1562000d451340c95800c00030a40d0755981c0d44030b451134100180b40003080c003035850005102ca8107195071001007400d03040c1051448903245070368641d024450076400503101d040305403401400381d41c240115941d03403180020540d01c460b00d42c40c50301d000744481605402e00d0458040f0b00070140c104105e41d08000105500c40c41e43c07640a2100a0b1126440206490340c05a070b264207490103140700b0700c6520302912040d40103007400c3c50503180c411180b40481d851140301c1da00502081080380c4d40b42920701080200041803c80710b200c0e0f45402600030000710b003060b50041c2001c503054011980b0201034030206000e0b40444142e900e41d440c440101c03902000c103181c03c66405006252011103690b01 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 900457212 1250 900455962 900455989
    0xc0512041b060503150402040308070b1509091605040903091e080a030f1209110f040e01020301270504020d080a0203130e1006030b030303010311060408010e06040c0608060d02 77
    0x188101e01286001207009100003541003100854004030600203503001690084200c904183e404510381030030754841240e9401050b6000740041c0342c00c8002424450803100314024200302a1030000c941c2017107200980c03030f4070903a5031884003a00544800912441d240c0110100b00d605601e940c510b590030000d00342e02e1541009202c0d5100780030345500003a01d0310204440f440c118001e5036000c0812244c1d0000502ca10603411032090030074104005100890000c0d014000c140388122680440c00b20510081805050200c200b40101e51012000107042881c828070710810202e0071850300540c05c409580c1c0411074070265006900034a00d034070044002103841008140d00111801102c1c01d11010a0410b55495950340004002ca6107071400d01550f011031240d62009000f5504043c082405000c0119560b400144006400000c110000b0142c603102d0100319405404050b0003071240c2d101c01710355030307548480c10740e400c8a40020b10b810004c0c4851040c250302c1d02980b0014440b240c1c681c417a03000c10280012614 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 900458462 1250 900457212 900457223
    0xb0a0b070b18030a030c08070503070801060f090f0b071713060507171617120a0f1509020702090115080402010e010e0d03111209031c1701090209040507030c051204 72
    0x482c2d540d09140200050810650035690100d00c00c000540e0042803020040c0501c41404801c0c414003120325080707076665054403040d18005824500d018011a10fa5515030305c8070256011400b001f1501080c104000e12a01d4052001c2001c5254110402402031040c0c0d1410030081c44440310510000e8400e4004280243c001c2480c1c094000002c20980312a9012041c12116030b2803a032418000c006c3d40d10000d01e1010410400300c0c2c280030342e5402140e0501e074000d02c54136030150303071f00e080201503040f5502c0030800c4182190098152911429044002e601c5128240d03c50403030340d000083c00481e0001840c40070112a074802129860b6680150741e680707021001c040c140050f560700c68106444840c404e00700b0360b000782c2d0760149251410040d2801e102c145141e583d46000c040105615a840c005458410036030440c1d5001c03540b080b81c80c0220b0f100f050b1307240f551065000d000000205086280c0103024802d1084508102c0d40d10380180c01e500b00c504010344c01000ca0401d1242c08490640c0502441d0b0003030142 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 900459712 1250 900458462 900458491
    0x60b07030f0f02010b1503091005090706110a0b0106200102040f090506010c0203030a120506190b071502032401020c150c2d06150927060117010b0a0b070b 68
    0xc00080c106e15000c46c21407104100101c10001307014010030800c11680b441030b0040002d8200b007280035460301c070140a120144840709042215440d000c0040c8560143c00001c400c0036540c45103030081074142c0e00003030f0a143c0c81c052030359010320150610888046030180705010b01003030b18052204018001c02880c6034144000d0702c103074101689080c0000c16160302e02d9990120032112580028044581c05014240910310980c02c0d9508042c00d0705419050b1400c80200d2515602d491412000c2240720045003442c072400442404640d255210070341d40300660310442400440845001280e480461041d0150310240d19041196852005001002c40550308019280100b4006106880301010010402d41c07880c40300b800361070340c0e9009000b000c1c1c010020a8ac0030301e00d642d40c07400140070f030380000e8081c400030200d40e00452000300e01c0d421100355526080c07068459540c2d480f200150310030903a05c05030ba290f5090000c07690403440e0500c1110180c032610301d01c03242860401e484000303500d60020030940403ca01c1 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 900460962 1250 900459712 900459731
    0x503121006050712180308040609123912020f01030e1b010302130b0424021c03090b15030105070908030d0e0109080f0403060b040e0613062409060b07030f0f0201 71
    0x30a45100180d801480550f0713490b4508100182ba1118540c007925013004e10840702d4001460303204054504204050510030b8203980b50150000e0380740c52080b841c0300c8003041c2c42e00240c4107034010580c00701c1d40d000301e0780c24401d061040019410780d1410104182da41c0c100003201c2007030b201e0103003400030000d2043c54014100980300e112400300c6400e5030484400c0e40400300d02040072140404e000228500c111192000c000c024010103541c50610302c551001d21001455000d04043c469400000d01541020449903e401c00c0e80308000d0303418400c2501c1d800381d401c000008490a001c3c4900b0021580604015840c00320719420000081107002104a03d6549800010340410b043c03101034400080701c0000150358600c0d52501104990501180c0c03030040d4205510049616000b0070040c0e8001c20810f449510302c070707251078884020400f4821a0002680700f020280b04068080243c40a50703070f207104d0412000b62a6420340001d030085800040c001059072020044e0144105100e02d149211400017003441c000 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 900462212 1250 900460962 900460997
    0x1209050f0d030b1903030f0503070c021e1504121410290d080d020715230108011503020111070b0f18150d020a09120503121006050712 59
    0x10300000001c3d0321100314a03141e240055020b500d4807903128441005600c1c40d0b4010346801603a805c0c2c0020706c140407001404072800f076100885d00b00d9004115405004a07602c0c611510b81c1c080c85598001c0c00312000307203030b08007615204450a44034843d40c0704007682c200742e07210000001e404491040900031600700c901070489034050300c42080c80c01c06c204090040a0061402003a91001245208040400400740400c442d0030445241d002c801101603981d1201d070400c1c0620040c0c04c009000264503058844100c111045110036883c540d50f2400c2d909641d80e100380a080e0b455002d060f000e8034030265800c200640c0a15030030026001902c0075911040c1c0d40d030b00b40c980c0f0358105015105a00c5000102e04c4110491240c185c038000030102d480d14660000e58604a40e1801a5554881020f0380090013814050044000300010044103822802e004051301e0080d882e42c100c400c100484c58045400305da40e40144d58010003d40340d0f141d540c6414403003a80c5819210451041c070460a000045130100320904 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 900463462 1250 900462212 900462223
    0x1b0305120d1b0206041208070503011203022e060e060307380912010e0d030b0301180c05031e060402060a0c0503030721020c03040e04020105210109050c0702011209050f 74
    0x4102d0f402501035071616007040b00107200c2d4000c004040144940420829580000503a810f440315070720919032141851038140d140400300c0d02804c050003140308401c2d4420403d02000c80707440e4000310703040c0308127603480428400320442503502a030b05400c1000c080c042c04440040c1c41e45030543c2c600714150081022100680b28440b5580f00700300044000500511070b050401840312025903c6008210308076200c00450703221010744044200f0184c07220300c0f110070360384c00b50091440c41c044507000703400d0701071240b801039816141d51280c14064001c0710003400c082e41c0014003800800301520080c040f641c1d40c681c02c0040d6640503000e0642840340055142c008583c00700003561150019845050908402c00d421440c40e50107011540c503414010000c00640e46004000c0c1c03000c0318001490500c040d216440140c8581c01643c0e5416490722400403000c0c1c40408005201f41203841c0ba4504000383d0303d640b220340b961403203104c0d0068081203502100e6003ca0526900060181e0302900640d00c417505107a15182c10030 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 900464712 1250 900463462 900463511
    0x6160309031109070206040f0314040807050a080111220b03010305150a110702130204051002100605040b1c03090b0a0504061b030f050d090c03060501031b0305120d 72
    0x3a00c80d680c2031082101c52500101d40c89412500c415892402e58002913803900010070007400f0b44c800d000640e0415004007042000042e903264200d03111910390192a607181382360f105151148a081d080000c0d41a01071003000700d000383d184115403a100d44c0d00c5d4405081c14001030614400e8132a4a000280901990040d6000c1c610841c00f90031070408801c40f01820410240041d1180c03031800d5041001941800c0032642060340c1030314403040ca00f2035107240740c0007806142d000303075049101110803e01003540410a213180d0103c501d4204440c1d41c03110140f004840703658480d66004860015091183d100d54142209641d11903d016000c15440c1da514002c160010007000c0041640031500b408009c0d00201070010000c00c155183c0d02000e05900c00420294030620f500301813090010304115084029002480340c543c06c65112103283d5a03c3c1b80040041000344020703200b81c440085e11102d008801c550700c0040701d0700300c0002c002c1d110356190211260741c01600714422150750fa0000c032080d51070155011050 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 900465962 1250 900464712 900464717
    0x4050c0904030f08090616110309030d080910021e0f070507030605060a060503160302070515010e04030e04200904020d0908030a0605030a030f0f050c060f010510021506040902061603 80
    0xa0307560200580070120240105d880380d00040700b048001e4102d106071181d0400d451800c3c1c10031080380341626040d4405d8940e002d816006140000ea1407a03000104980103888040440e41100c14451078403080b8021241a659540a1505400300038400c14000d00404502d41100302c1ca001400d58901b4907064155100b207440d9901e030420404240b42138541c100c02010103051480c55440c0c2101d451b560448a040c5c0042410360100b01a81803210070030050a52000c1d0000c00200b81d610341030702005030802242d0840015100c880035010900b018014494840c2160540300c4407000038880040e01600300041c1150002d601b8440e502c2c1e40040360041c104460b000780c160765540d081508450080c1c40042d0070041c06540300c2d07072031000041e0780f041030100303010700c20f01e86940306044442c1d0403103503441102149549449400c062000071214161039504884084604124030401034000740e8540c1541c40c04241883e0f07840d80040c2c510308090300179080a91000b8001c5207001c0134411904000c401c0c400060f0300 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 900467212 1250 900465962 900465977
    0x50d02040e1311120601030204090809090a050405010f06180c1407080702150906030c031306021b010c020601050307170a1a0108061f0306020d0e1917030405120304050c090403 77
    0x5000386805101c3e180300055a001c400c4c5141a5000ca640360410320000380160b582e10f600800b401010401c0d00d05610700106810440e00300b11381c203a00540001d0303c0c150703210f51070b00107040405c140038481d89080740c4009034210380c0400b84c1d840e07050050030301c0d10200080c020320751008107040350924000e110742442400c0e15a26074110340180805982c0d40c030203085121808020148160352150252a44111071441c0395583c0e80c0c2d500b040c0d1540340c1502100500c02400841d02189408180140c0144051400c00070449410400022a581c1c0420700c11150990003090003440601c890704120000c4030044002c4814505080e501c15612141080d105056120b0b81001805908003d0160640080246904a500001f4020462200b4039288401410a0b40c00034000740300041c580c02a03900d046442c8250b6503580030560490100b01d843c1c0e44121015040c0702132040d01403000e6006e890056801400074040e0b4030601c2c8841c0140d03803020300103032500e03c01e568080c1031554920180da17200718800d030745405 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 900468462 1250 900467212 900467251
    0x112d041b020313090501061b1419020f0919020a0c0210030c0f02370213050601030f020310030f0309080303040818010c03020d05031008150403021903020a0201050d02040e 75
    0x10b00307508141c00c84c912050400c001002000e501400c101074800011544004101c0c1a00c3c0400a06280c0103500100f40120b280e8044680c0004080c101014000e90f0b52800d204c0c40e0004000000c80708480006440c40c0c0b0348166010380003180d001c0c0c2520a070906110b181c0380704640000d03202c9400d10100d0710010fa281c0c17502d2241c031ba07030001084802c4141400140809041c1c5001c1c100b002c02030140b00240d44117040e0140c1866201540042140b41d006006c4d09800003140740707414060001110b41501203030400ca060010001030b031089910982a03038400452117800d564035210001c844440c2503007000b1107041c0104182070140001c5d8069441803260550350012060003150100c44050080e0500840302541c50119030081450040000f046c50041e66a5541340c0c10400f420900b50031444440c4154844005488070007101d0a0285001e9001c85030130021415038006029590000180107820000100b4015402540039045181c04560090f062a403554212107940ba021115040309600b500f0000c0c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 900469712 1250 900468462 900468487
    0x10b0703020d0f0c0303090c12050f120406080a0504050114100e16120b011e02152214100c0c110102030414150904020a0507112d041b0203 61
    0x2003030000d003d05046030b90070110b01c4007401d1150902e40240c14580c07910344180c20004c0e038004030700240001070744052541c900c0781801c40d500e6101019080151044a030035050300c88002064400321207280d81d51408607a074002030840a004094421600396495501c00c0e03100c2c942d10352030548247c0d46d946412034007626020085168050181190380727050b1201000c40c0c007850b88103540c0d084078280c40e2004605500d0b07010040784c02004403000c200b07000d402c1044040d406070b07010542d034151010001c0c50788075035118043c101d00a0191820020074041030b5034441c1001602c0015190740d102e510340140d540d44049840c007481550f138818504400100020501010031804c1580002100d0003803008509140c10318003015060b03040c45050034400d182402c0b00195541e0400106e402551f409070055444c0c0001c0c0c240906a6040780000700d950740d0b9420480e00c0542009900b100400d80c103400a40b40d491b01106200d03000100c41c464054005454000400030901d2000c6215140081c81c0d000316920206030090 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 900470962 1250 900469712 900469723
    0x12081006050901080a0903090b0f04090b0603010501050421061103181513080409020c0d0801080f070909150c0e0f0603090d0e19150306050906101d09010b070302 71
    0x500900609001e02601d50340e01c0b032034150707104005c04000109203585003800c7d9505442a409500c1c214400510100c90212200280c0100e84001c2001d2019141c0300c4100b001501023409154001401071104206030001c81072011820060f2120304001c02e2072646810055410300402d2500d034100000c184605144d11b4100c08110b410002d014051644030a40b40d558001c00140003005000c030a14a171100b0700072140103c0e401440e0b1003400310350300c00794500110380f600440c1e60848013155a02c03000040700c0401080b000a42c0c0c8c82c0744041d21145041c0b150780b50050841c804103480107034440c0204e003031056582c0b0410307903010103986079051480c42d900d017000b0010780f15000c914040e41c0281300703200c00304a000605400d02101401c05100030304000c0b01240c80404d880c004d510b11140060f100203a0401800c442ca006400a0350f4180039698070381d800d102c42c00300142d80443c0c0041c800f22201701000c0c030079022145030840551a906021301d1030350005248540a800c6000f504100142000c01c040d0100003 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 900472212 1250 900470962 900470969
    0xa031d0a0b01090506040f2408060705120c04090c0206010305060105010318080f0c0706031e1b0e0f030129040509100903050403020a06202e09120810 66
    0x40414850607035401681000610481043d00d480c1c1d00410900d955641210b10005182c01c81041401c1c400d1054440c400b054158400a400e11900003065a0b000800c140744505266141e052a010034144102e100740c0c00184000003003030041c000420340300c449000704022a0050f0713004121550660400c00c4c20400e060b40003c1c1032600c1e00038400c0d0b0400380c00034201700264100800b0f41e140d60031210005618810310751464503a014104c03010840741e400d50b0244508007010021040003058100c2d5020481d090700e030700c801403414400e213880110703032155103200c0c02031a001c0e0500a8042c601404a030070350744c1194503040418090b441c0e0325040e652070083c0340d000c001c04440500c4923003440700c040c948805201c0280018142c86104070301c00d042c064412a001541c0c080d003030580443d6140d800800245800305082c202030728036581251120710024104680301c92070b540b0015600c1640c3c01c240d8010340070040460106844248081c041500d00560502154160321101d079503180c520a140b11003500b640 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 900473462 1250 900472212 900472271
    0x6090a200d0614011e05010c02060904050c0403060605030d1b022e022a06071b2d0608070c050f010e0715020d020a0f0f0203010507050901030c0c0503090402030c0f0a03 74
    0x1171404e00c802c10041d600c0c01210700a0038940d600d2551400424914030600c14016040ba040406101e880b0160348000c2c0100e070b00800d820010581c46404050b210040c40980c000040d42c0c3d59510031107401c01b02c0015200c10300c002c00d0400c4959000c1c4e03144911102264180c242d0b50501c483d00c0400e03030f4050100a24500a5200f0704410300c04000b040306c580315418510703501410000c41d11204000e020100007030351100381c4a052000c20350300c0d01d6074403810380584008420350240d400d039007070401e80c542d5000c01680c180382c0701c2640755922180110b030409140c3e14140d41d10310504000ca0702e01c074800c0c400d03044000b040074080d018036828624105001034407102c5220841d8800880500c03825404102c1301c0c00709512012054141025003080190f681224402030740c10352802d01403140c083d0b040300007050000b4080c1c80a2004215246065070b0600403005c002c0c05a0304104a15410340c0f50650003582d124051007100d90030030f410440d10b07640d80c3c0c00ca003902d5000300e5030340e01c61007000c1d894020514150141a8 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 900474712 1250 900473462 900473489
    0x2106050103060e091e0f1c350903070f060617060f06040207030c060c230403021f05070f0803040507091812020705060a030605040e06090a200d061401 66
    0x2100f0b0507070758024100403030403500b000101401940f076092024035442c032070398030444003403404420111041d044551080703800b00c4c00c0c1203882d200c0d03844011280d000c402361140480491004091000e0301180004020b03003c507000c20007224001070700070020044194015a000241282800b00c1d0101c00d0170b91020003681540842c0030003028035090020b40381d21400c103540c05038440d603151074159034900300e600c40102041c0c10042d55000e0694407802c482450004101d40602505000124085611480c003000c0c1d00700710340b121a01102e942c0c40790b03203480849075441d01c14038002294a61f42050880007104580140307001040c80280241080520040c081c10b10701000b19902000030640c007081410300051040705850f0f50290300c1c40c000e11800c002028040c1105a0b03031141d8820040081c4590300907248134500d0304096003105200040d000c1d01c5910100e0040140c806240c43d0b8800083c41100d400300c450b03410050060150701e410004844007403107484040b800c800080c40345100058140c00022220014 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 900475962 1250 900474712 900474721
    0x305040503181309050105090d090f0e06060c0303090a0b10060e010e040f150519030f0b22120206070c02090628031412090a152106050103060e 63
    0x12040b0707200082e07034101d1042d010b10210003182ca01d00f80d4882000c050b5241c0b1508909000c0113401c81d40c07145a58a059642810f200b060a5034000b0b068082d40462840140f02807200d4004c83c5810341c2c00210040c00ea60a041e00447d0b914595842169002610741040001c00100522600015040b24840301c0c420071a5003002401401400b4031074020341003040d140401c610944071684456149940f4000c14450000010388540c07403c400d510900b4018905c1d10a07920799404815a00c0e415654000505103041c007140c0c803004240c0310058002d0700190b40b04114460403d00d59600f00c058988100c42c1c03901c2d014181348000e4140000108500180f05600551000581d0f454044a503ca0720071a140c40c4440307502286400c100c0c003544008071070111000e4003c414840c0340307800c801e07041d00440201e407144035480d8031a503003a0085520681d08080c241406001003119080703121416440e500d406074401c401040b149c409183e0070310010065036a074100501040d64540114005404000094141d9040 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 900477212 1250 900475962 900475973
    0x15011803213014180d03050c030604020306060c01061e08160317091207080706050a08060d060207052527020318121201050d1a0606090a0e0103050607030504 69
    0x51002ea07010804003105040c22946254003107a100ca8402a0000b00ca00d8006016041c1e901e0590040b0780a10039111040c00b0a44603025403403244610580c0f0b141191117503418007003e03410141400b0343c00013040c062039250483c2481031100501b440d60303c1c42c4509000b8504620981c070707640c01a40141c1c00407210080344907013407007891080704d5112030f01b121018902405003c050040400c40c95000c08d003592034840c560000503401055a904406481d1070301e07600c40e400d441c40e1050303c5800300403402100c0020031503e0b15803484d81c403041c0079070000340c5031003030980c0e81700c1c1004100900c80039070a0641100348d0100c801419440060901c05242c40c101f51505200c1c02d885000200c0c42d6200c403a000400100c10031310802c4110700c038108074000c50300e28100e070755011205604003102085100790840c00024891a06031150131565800c20500c01e00515140d0f2000b5003001c00170540d03900302504101c50403190f16541c9a80c8010044640380c4151075044d441c0250401a000e00700400301401c16003800003044 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 900478462 1250 900477212 900477257
    0x15090b0f0315100c17160804050f09070906080406021323040605011413050303030420100c06092303040905090c0906091317030702190503031501180321 67
    0x145c019440d5011115440c80201040c49040111020780c90009000002c10103000c02400543e003080303402002500e200e0f03050201c4220304903900300008450b4142040b005014071029078100f40150005458145000c00f91414011540d1101c20746c0b1021070b0300704040c0b100c0c41e0103880e402c090442c2d0030700242d0301e4034000a00001001203006101100003a010140c0c11590300c803000144805000c1c1c07030300e9242504188000c030400c00d00e18002c013400c04500001c80d14203140106101c940d9904c601854240320b46030301c8000c1c4041101110b64200703900300358002030000103911807468150002503544138100b810000a49801800040081d84035050101090307031410384440d841030045d154500c0d640d84410040c000b0341da00c7c1d980640120940c1c0b122030b8580d60380d07400640c426145a0201c400020080c6850040704035040030142c115007041c40412540040e60860188481c014074003000c040c4000b46c002190049245d00440701e00e0307280038031000c20301905101d50381800c2480c01d00ba5200500c40400c0500b00 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 900479712 1250 900478462 900478487
    0x70308040b0f0915250f03030b030a06050f01061107050904060c05071a01170c010e04020c16171204080307031b231209010915090b0f031510 62
    0x201c0c08a0242400e0b4070ba80b00340c51000800404d140242d000c511540e585603406020a40d65041100700c61109460072060400c90190b4400d0498003504042e4a045000702559290b00f5458040e49901e000860503078002c1034000d030035000081c1699403610350b010303001002c114400e6481c1c1d04409020015513886000441d40a070700703d42c010179615001c0e1400c603618802c40100904d4401d03103811405045226400c0302e81071700c409810044600a0745583d4a40d10007201c041e06001071240c0700d0482c034034140344c0c015012081c120803c49241d144600b14040425800e5000303010380b4285074400c0b4a85210400854450b907000d8101030b85401e040885560301e0303100d602006010b0040a40210410000082074bd540e0141c01183c00400c00180c1c17201006168032660009a8a1089101041c0440211811182c0a201c140c5550081c50314010020945650f217000035802c1c820703203410010b80d41e0311140041507a00301000b102a44d03031404225407000e505c1c0b0390b006103015803500080e004600d6005040026203 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 900480962 1250 900479712 900479729
    0x606030c0a051309140f1005010b071401021c0e190209040308070210050a0b040b0312090d06060e040b041a01030222090212030c061312050a14040e07020c0307030804 73
    0xf8104480c00c58000b8184100b0020300301c40348440c0d0003403604000701c1c0c29103410b58903500707540c4a24078020f1800c0544101f8011220025420045840011046907425251040020015082104503103c030040c0d50500d0800382c1d10140c40d0410821099030510070084103001c503202d18074500d00ca0390080741c6410300080c00102404114404503103440d0003013014100184604100b8001417034001c00120140c510800c28074020382c1005100c001a00d00071074040c100514010fa0141482e400d0803c2005c01425000d081e1070041c0c0d103400118049813030403903943c8514000ca0003450303d41064541504141c004d5504041168040ca00510050fa1806d0911840ca611109003014002d2032036002001490305c504029849040c440d81b074800c0550200145c0342d440b510109075803145d55054601d842d4801401e00003844807550750012602c60380a400600050381e4585010398070540318026007500303680942c000c0700e180c0901600300000141e040180c40704500003903000c1c04500d0720390350b04d140003409240100e545 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 900482212 1250 900480962 900480979
    0x1020a020d0534020103050703060b0d0b1801090b0a08030a140a1b1b06020303040f12210902100e0915010e03010f0c0306080d17070c060507030e0606030c0a05 70
    0x40740d202000e03c030081410001c0500980c4039115542c924440307100300c100e0119040000189500303000c0e1180d8070444403400142850a0100e04100008008403160580e1020030301c0201d00d507034018501694003814040e070001403035020384410001d003a02650700004d01c0f60b00400c203020742c1e82d601140c0802d0219501c1000c0b030301e521070108182d6400000711110340490701c0d00d4a0003030030b01c008150f11940c1c0c00302c0000c16801d140d0719024100e031a8401150081c180200c64544400010716007903480105e443d052414086201760743c1103100100c2d051b00c0d90f001109450b035001d00c0c01e40c544074900c1c0e800c0207014204611400b480e00041080500300030502d21421400900e5004c941c0d024248801400c4002030003040908803490a0800a08103107102200213460b1400100c0d0701c0e8800626400d046032151518031081404000031550034a00618040c1003103c0c0c43c44a0380011541d01a190290119440200d88421050355080c50040300401032442540403401040d41611482c1504058400c240d82080 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 900483462 1250 900482212 900482227
    0x51c0c020402090604080307061b11151e0406020409050f060f240a050403060615020a060c02120a050c0d0e060a0804021206040b100f060819060b0d020d0e01020a020d05 74
    0x481c1e50186038046c0300b8500002524a0810080354051001e90441112111084001d1441101c07804c00803500342016600c0010326030100d84600250507408000d5803c1e00b000520b1701c81c45001c484405039000c50b5025004541070006045a0080943c0030341c1c5050000385a02c4e0060009617107a404800381e500071603450b03211050004100665002c42e101c0c0d48101c6d0ba6803039060b540200594007910041d104180b51640100340b03580c00011806c000401503001b0400c03a0102d0721010000c001000745c00c803d40c071407642c0c1068504540800740200405c1034964607240c54003010021f06050a08118900300008240d806190b44d81e00c01c00d40d514440549044442c030b40c3ca510100e0b044c0e00b000e20061083e4400c2e0020082080701442140744205c0440401e040e0841d5148601100300c071860150b64003060000700081c4400ca24043d99103406c8921401c00f02d0703070b140d58482c104c81c50707440790f10f00040c0c0640004003403001e8003c2e40900f0058221500086141c0640004003c4d150003100b03006000700440052582c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 900484712 1250 900483462 900483469
    0x602061f050d05070b13170604050d2604080711030111161b08010b12030304110d0201020c04060e06010f021b010f140a020102040614070c03030e0402070b13051c0c02040209 76
    0x4502138102400150746c0c80310100305610354040c551040000b14041c110b01044d01040228040d4000ca038050024400d1100440094915070640440d150600740d1510720b4048484520102038020f90088140075612207050610381c02c0d04808101c3c0d46c0c06a0b04148841c485d9042010460307090348001c800540005141d4980541d440d0019960055910001c00c0c01045624042d8410745c00880100c0d9511403c1c0c00c01d1010320348030300080b20060070b4005100d002007281d084c21440da07903030688144140e841c0948860000740449040b500310f880380420001c204151942c200d01c11001c004d17141e000400c0d0042c0c05c460600c0301058114039090401c804803d40750501405800301c04c400884d07407081c5d00d403a1000310324000d00030f4100c2d11a14000032080311301c00d01e20344c48100486448a400c0382c01d080c0f0311411918142c03402119401c2e420381040d03003004070b90081060787c00a540110b42a420f11522101582002d5191400c40b583c0716002c501c0c01d180c0132140369080186005169419075016803500c0c1c1d0803000 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 900485962 1250 900484712 900484723
    0x4120504050604090b010816050910030e0d0e040605060c030315060f0c060423030d09080c01140609010f060203160f0b040b0414121602030a05010606090602061f050d05 74
    0x75401603804034003c200080786030044002100d081c1e0742e204559891031314080c0c48005000c41480480d00070081c0450900b00884240d00c8502c007410041075141486003804d2805042c00042d90000c0c05c59102011f26241078081c0e00c006006c01c0b82c181e81071440501e4540d0700d03888007404450071301d00e40301100440b50b1591800d403101c0d1082c1030801616661482c0c01581c8640c0100d07400c480320b07500202d81c5054540070100c40500910b0000c019030400c17024008560007130150490507610b842041c411a001278009011b00c0d2014114159982c03200d040c00c00030b000d08000180c1141a0001c2c000700c05101c500d0380081521f50100000704010464051810014000e80704000c0180080c00c2080c200030510a41d001c185008502c550031103400140c0c02c491b126100c2c01d04101d070000e0380c1703800c100444400c0058401c1c5502180005e00ba50488400c60f9240c07421500507a000b40c2c00310b800001d08000464060104c603510003503110b0001c0b000b040d06a07903a505021580601d6104070309010905003480340c200034 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 900487212 1250 900485962 900485969
    0x30e040c020303063f031809070f031a060412030e1f0f092408100305120d0f0c020f1204060801030b1305070f150e030d320d0b0108090604120504 64
    0x507170450202040c00107880342d03c02e07010741003c003042541c0b02d50f0074240202007610a4159503540d08500c250341804801500404220103851803100c1c0c0440c1032941d4002c000e0005000c015120b603038103034071442d015040c0c4401002140c4500c0d0b41580700307480c0020891041c61580c40500d00000310140548007510b182400b500038501d00030b01543d24040031111010701030303081540e0391580506555036409920300e60009000061103500a800303200840005213020300040119000041010101d58609400f10365030100924010390100c003001407800300a00003180c80f00c00310031140703242506000c1e000c1c14500c1c0605c80144135013226000512184040300c1003824890b8064207a8004a036914151890401a402024288030b920350001805500441c1c0c0b07030503901c0c000750203041c1000c1150400d40c3e42d02c03500210955001c44010f200406508450490109640b0501c400b0b0785801400c00c10404540c030240e169414002c0c02414040c8051001a00a85c030540c00320f603054640e058050115418001c5a0 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 900488462 1250 900487212 900487309
    0xf03050121140f010203010905060f0a090c140c01050105040c0c050307110d0618031826010204030b09070e0a0c05120a1b092d140616030e040c02030306 67
    0x7121203d00410b40042d8101c4800c85001d002607280e000c108141e404000124a074401c1000408102070b400c140c11114040c1d0a50a10641c0d84c2c010354072038a6103601440c103654481e50359000500c40c41c500352140090450062406213089025a1341c0c55039070f445010000740c044901c0c04c481c525559204040090341cfc0e0745c401010300c091103000401094401d50391400300d001c11b13000891903103c1518220103d0440c1c0c007103c03000e000e5400312007805030701d184000d034110403a540800010010440001c2054021010340c002444031910b0b180301c0e07220006c000b5080507401030030703c80000c1106d507002d07060b180c1c1e4418000e0140125190780c49840001c2002d4489401c0d0303041c0e001d0030140007640110b06641200e0401108200040d40803030301d0f152a100424948107050b802907400d100030b401c6404024103100c409402c00c0c1c0b9020342c0c0031420340304140032001100010f4481d0340c41a11407c043c0901c000e524410300040d8114207005d400241b14114003815420403120900d40c1d480b1181140c00440700e45203504 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 900489712 1250 900488462 900488473
    0x70f06030e2416030b0a0501080c07082208010209090106050307030b210c030c01080f0c1c050402040b04060501081f0b041d0114090a0f0e1c0f0305012114 68
    0x1080782c081c0d2840c1264500c0140c0c104035000100e841c000e0007030010103c0c009160604031820030005640d07461000d008154842c83c18014800082d10b01c1000304502d040340c2070b031350742441040ba000d80b0700541c40303402030103c41c1d0061014031070b039481d08240e66056500c581001f507100e039034060707084001b80244440c5990146244071640c0543c1e43e5070741e0b21040e10240304c090780c801e8003482050555030340040c031030f5600140c5101d00040c84040780e645500c1e002995105c146182c11404e000b8001d2002c20260b66402141e0307102d05003c118503191144640e442c10075641445100c2c030b0000081c1154000a1446601d0006800490031456860107a0f50160803071032042c07601c9507144c0302134010150b85150501d03c00c040c080c0000c10302d40545100c3c051407503001401e802081d034034110208040c00300c04200b01c85030380e04c99002c0910114180442200a5a8100c0c80d0341c04000404c0c004000125206416051518000060100440300c10034045001e0228074584c3d669000c2d0f10380700700204204408003505e4000d5 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 900490962 1250 900489712 900489763
    0x3010f0f050a110405030a021011060702070f2301030506360108061003020f0a05100f030f020a1d03151326030414072114070f06030e 59
    0x1680910b0060b00c80c0503003004401d00480a0380c5030362156000322030f810740c09041a0030040c60300f14200c041c00d8203503103001c0d0380d103030414020641380c10401e4408402513000003000380100150200b0351401840ca103031044c442107941c000d00d004164503d044650416488031700040180d1203a119070100c820380791118505818003c008002d451034400b543d0340b0f084410000025006000080706802000c84403444002d06195908000001587d003207000d400c007154000019542e41d65110f506108843c0c1d841e2103043d244520030080458201e102860665441800018420b0703034045000c4011442da0062070085038801c1001034130381103e0307000140801e1141420000034000a45081e401d852080ca5041d036038000e4402042c02280001600780f5074a041400002c01251942819600e039640e50f030103a800142d01c0d403d03042082c500307448580f0003611104411000b0402e0345660f56450740098009000120f0810080c50355440d01c47c8a10340815071030f5805901004e0050000c8120345c00c8070000704c00300291 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 900492212 1250 900490962 900490991
    0xa3c1a0403230d0b010e150d06030204020a02100c02010c170c0d020c100e03070b071b020a1d0610050f0a0203040503030403030c031209150908070b25020316060b03010f 74
    0x943d01001c1c2450801c0c0c50401030354050303e0560300716000204a040122020a800405904603403d29005552201d4002016031038a10040c241403545501921243c02c64502c2310040c1c4000c5400e030021a0b15260036112842d6001030300004000786403c81102d1501c03010500301c040d01482c040300c2007080c40010022401d84000402c50140c0203441d40510040d8000b41c40181c0b0781c050600c0292481e4042e0700050b02a6108804c0546030000c503400815040b17000e42c0219400700225040401c1c0c000b0310035462200010101d078090f034410804c40350118a400704c450010624040c1209242900102149810b0458003e20070f40c3d028010103000c42e91900e54a09000b090400c0c503050a038049800c50b51000c0b0405210b018088034160030001e4860001c40400340304001f07000c0c0100079103400b0400d00a00d800140da10044502404040640c10030311001e010b6034440031001201c083c3c09541c810000c00390f124920124444074103420260001d050610107010a02421011a11001032417030b10700f11058010 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 900493462 1250 900492212 900492217
    0xa030905010609090b0a0501030503030a09020d050708061902070c060c02060c01050f0708090316031d130b03070e1902031b032401020109150e0a3c1a040323 69
    0x170300406960020351a003180160440d0003c0c00094611381041001821009c5187c00150f1040e02c080c1c2900c1200c00300d62162420305645410102c1950031100c284240e840408100b071030900c10810b011803600b0902d981d0b032030704441c41c3d10446d03062000200346201955540401d440900e4075100082c0700d103150a07110710968140485001010800d44400b0401c241e10010554800e805081c907010005042c1c3c0e141558090303541f1b8006c03558500102d03841c81441c0c8405a410201412040b004542c00043d4010142401800d411038103040300482c08002513030260401302141c80c08103410040c0e0766111101c425468440724043d08220340000000d000d01c0017884488ca1a640000540b01ca82300e85400d0012030903941502805000b41caa2840310a6248030315611040c8126500c1c0d0465600c01d00300c1c1c0d00e094540d40c055004840e5014990300c44410b01c500d16000c0025601c0581282c00042001e41d1400d404c800d210b11050f840e441c441000508040c05141c40c0e400f8294080c0310315100000f502010401c03130307 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 900494712 1250 900493462 900493481
    0x2070302010c050406021509030c030a0e04060b09030601031e0606080d1701050d020909010605030d090914011d13051902030f0d2102090402040605090103180209010504020a030905010609 82
    0x198a4541850095482001650103a1700141c0c081d04211307203c0d9410031410707075028003044030030f020810610f11014810001042c00800c0c43d204c9103d006150410041100e9440c2e1003086a00300c100140105581c0c080f6801341503941c042035000c00c485002140e2441c8454064000b0200340ca800c3c00401d000c0c1d00091462089000f41d5205500001703c0071080c1c01d051028402c00c3e800a0807032086000603c4e00c0c2c4c0103103910004840c00000c1070759035800000e2400103c03058040100e201c00c00300388407210171030241d150b0120030a140f0104075450000a0801d13554440f40801d01500e00c0400320b44c403591001c0411144d80d800004503668224030f10081b10705900f1600c1d040748070744208640510b0700c0102060200015100e9100c09105840308481451400855018100c1080e802c00440e400c640e20f51004d8400781007940c2c1c8180c0c540e140b403000501100c5081d000c1c000060300c1070004500603500d4681d018150351068501681724503e2460940142c07242c003000401d00d501b480000300740042640d1040e40907 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 900495962 1250 900494712 900494717
    0x406050711092403010605130c020c0d080415141b0f10150e160e010c120c140105060d030f0302090402030408070501061703180a08030d0c020705030c010e040f0b13020703 75
    0x1080c44020400d800c80c1d02c5032062940200308504825406119270f4402d203800680ca0040d12980005400000c2c01007413420802c440183c804142880001c409034038008861007941041c1249880804a05050340512a04a00e07401503691403850f9541080c40b041c1c0314261082c04481943c0c42a180c150003410300c42e103141c0c4002003013080008040c0c184540703160003503103082c101008000c03101000b15100681d0740b14050600c407082c00030300c0000311800c0d00410700301e0541d0381713107410744030030b0700e44020f440910300003005840c1e0408051202d540d803070f0600f0780103159150400240c030956000c0c0550183c085c101d00542c0c014408402c00c000c0c0031410004001480c4500e00800000b600ea4001c0c142540c540f85001150750b00034480012403107403c02400203000f600418049078036580d92401441c42e4801c12012604980f030703401c1440941e404001403000f8203012000307800380900d200c1c0020304821070011114442c50f1a501c40443d901c09030391004060880141c04001c0c22424202c094010b98001c1204400 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 900497212 1250 900495962 900496021
    0x1a040201110d05030109051312020a05060a06150f140c0c0f0907090306091e030f0311030115081f03120f03050c0301051e06040906030c0911040605071109 68
    0x160540410951400c02c41521110f0441c0d0800c01c0b0031000b000300910608200718041d191502065146849000d00d41b86a4018008040d00c0d01e4480c1c10113401406074030000b030818409101500d40d030780e4207542e030265601d00000c1d120190f51044a88034000646840c42040002c0e00162904006c9950100742501ba40c1011300c0d201508103110061904803044400520424414000600f041c2c1040140d240038940840342078031421080c0307402d040c1090b02240410b0124401081a6400d80640182d800022001c1415907142150003040010307040141c00801c200000080e503022041c03c01011030841c120b031000441c03626840d01e01504041485c003400031410068842c6000c900c00c0c01800e00ca43c480c4400c081c1180d1800052245200340800303103070060f14079440b400c0d010b41c540001901c000c06950300045135a40c5941042441030107070b60801c02d480d13400d061000400c001003904036030440c0c0551501507078550300340c14414961045042080c2d231041d240b0062004250303001149180c0400c05060803070 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 900498462 1250 900497212 900497237
    0xa020738010e06091305160609090507020f1f14040803010303091e09020f0909090606010e0d0804030f05030408070602060a0b060c0a0209060d020405040c061404080718091a040201 79
    0x70030710b00c0211040380d4410151000201e035580655656030b000c500c02e2048540e5820124540010480c00340c02910008102100403c0001000c0c06400d03002910341c0080c06116034614106030304d403e40250901c00185440f0940340c105640c42e4008081100c10004808450500f46080c00e0658000c4c88142c00180c0c1c541404030701d01200c0030344220b000010f0343d61410b00f079152900032000794100110508180c0707828880c02d0360340e86030310201c00d2103803042001410389840c00c600054900940c0d1741007103010320140d42c0c07004001403001d41128181c0341c00c60b1410341c40b4101d901d0103e180d84240d4001040500036000f000800701e8000402500811030345805018002078101400b400d4010030b501c100d0b50380d11020784031000d410511900c1d80c12407400361010042844a0f00031a0664005450403143c24503c070104010055200922001900500359100c0c905440d1544850791544103000b1a038003800182c107408410f4045901c0201540c4e030000030304540e42002c90309203900d444100ca050b400300e2103620181c03 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 900499712 1250 900498462 900498479
    0x6070e09071704030e120703050d030b153004020103050f0402093402070e0c09060301030b1302041d0705090108150604180c0f0e0f0a02073801 63
    0x184214403039901c1d030080307a02c101c030307601603002c400780054081c0210241e1412003a202d840041d103800d2509802814028038500e0601d151030905001e19041510345880c900d46641c0e040e50f041c68000c000011079813a55a0490450319442403a01ca04d83c050161b20005000f2017800381c4018400c6000340c8080040743c3c0c80f08001d1031500c0003190000c0d0b200c9084000507981402e00f05a0304000c00d502004440c00c1e83c10310610b00300d070707125035852400541d100b50001c00940000e2050580c1c8a82d9034142103040221030000b2650f40c1c0410b020060828006d10b00280a061a0b40c642140b6030360014800c4c0140044100407400c842c040c1d400040c540c0c002d40b240880c06091501d141070403036620344000c0420b002d40d10503c2d07856600103000b05500584501c40f100d0f00340440b02504a256000c3c0001000c510300e000e07070803580682c01c2d5101131601450344040140a90851524580c48104008056901d40e030a1904840840740c9500c11000341401c0034441483c07010700b00e40800481405c242584e070990700c441c02e5 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 900500962 1250 900499712 900499729
    0x60f24090402040f0b12032206050703051c0203010909140a051c050c010c0504050907030b090c0a1107060201022208060612070e0906040618110603060f060c06070e 72
    0x12504103680002050050401d0341c4a01c00c0c024403e640010842407401c0091042d20055a135101c0d0342e4808640290300604c03400c070740c41c0d288844804c203034a00362a0517405015030242c1e46000d018404081140344840381c50702170f8982c40e50035440007150b8942c1c5501d113440040181000545580003180c0c1e044600c00382c0061072074200c2c0d4000b0024511015000404030b410812a8880c1d4200b01c81405180f540010034002c100c003620850300e80e19103407810f2205106014000406480805040050780c4c1c0c0e40c0d85411407000d400c1a100c40301203564041500c03080c0c0710024a40310510380791040050025456506502800e00c410020807025519064150f0700040b00180b400b1b108410b81180700400c9945c074102498010343c1c01e08806480340c0c2c1c0d5590310340901550f01246c519055070010400c010401426201d514072114240e5080741c111a03031522114002e4980482c014007401001001c00c41070341d51140940044d00740107200da80da80d55400019522000292802c10100d414020302d02e03601e01c1c00214 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 900502212 1250 900500962 900501031
    0x2030d0507052802010905060a0c02010b0105030412031122030611041404021806030403090305070501210c1107080a06050108010501033309050a050d030c0e040e030c060f 75
    0xb00704503001d00b000010f0007014182c0444005540d85d41c000e100000e41c01340032042c41000c40b50000982d02210704000ba00750340ca070a40b400d04200d0100708000008140306822105101c4501d030010b18a254625050702ca4400c107120307684480700c9848000d0b0508104070051082d00e1103075005004440585054007160f0003240a00c2c00c0d00d00d803d0a906000b0b04050313001d0100c03004000451105508044080f42140c1d1041c0e03000c1c1c0001e041d607001402408400c01100c0000e04080c46d100800c0d20341200803011141d540740040302c84545940c00c840ea4540b081d0382034880c0000f0300c01034902107640c0e841180c0e5242d40a0100b00d480f41e0800c8c0001885082c1842154102e07501304001c95112600300300c0440940c03c8411942801d1008100410101c011510511148a00c07401c0105095001410864508000070010b80101810b184d68003400550029480720302800a8802091608280341d04906500505000f641c0302d210300d030300f003265262000e0180c5d4003484071a50789801c2c1555a210100d04001c80d2034 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 900503462 1250 900502212 900502237
    0xc0b0c031213061d0d0806010503220212030c0105100b1c1404060c11160623030f0103210503010302090405012309010e010e0c060c03130602030d050705 67
    0x40c6814034522110715548074000701801460481c4950ba10003c48820858000034101d603d00c24240d4480100300c0e4184446081c2003070704c440e103001c000080082c48014021004038040000c01481443d4114450401e90f50003003091150301071010102d41d0320b802c038002d029440d40c00c1201041d034405040c4600003da42c03100b4032142c607040111402e020f0145600392072007181030340d428086800e6000200c0c040e0003580720380c2001c1113642c09038500816099070060708540581104002a00c48800c8814079011205207091040030844800800d03800d901022103c1e034014a000010080c03110502d508807410303644940701401e0080d4074601c0c07a01c04924004a0f02c1c010400800042c005868600301460313100780700341c0012032040c9220040e03a04600c40a010750b00c401c0307048000c2c8100804280101410341d24080c000b001250980400e903a40c55032070001c401c0c020b003000203c1020041302481194040c1c002003440c1c0c885150b860000a540e85d201c502100c04080c9402c01160700b40744250201c1d00c1d040d0400 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 900504712 1250 900503462 900503467
    0x1c02060603160803180d0c030f110612150316030b07090f0803040915080319261503030403050d0e10090605030a150f03060209040501090207050a030c0218040f0c0b0c03 74
    0x9410f1030b0300f428042d0003107035118080c11191b20006400080d888091031103210000100b8070301341303840d4203e80b144d410040d1290b0310504c0707812003403030303d64100ea54014210071095610341d0103000400d050050755410245159207844010003489850310415000b2585070360303054a841c1c0c1e900034030320a490650044800796001040104142c0c1001d4220003940c06102ca1080c50203681e4240881c5168041c00416512802c40c8404004035508036420b0003100d600b40d0409400001844a0001c403040005c20700c195000803a06502c1e0603480400070740d00a10f611038100c034511200b03074001420304403c000c4420b218030713000007000c01c100d4402c0c00807004807203050300c0b8a030031600e42d10340000103046040c050900c800e904400010340820503851140040d80103400059a500e00302c1c0038841a9101600117210b0140100100d1000500010340e16036019018501009140c0641c40009c00301c840c41080c00d056071000b2005d0205020550301c80150942c8120551680e09680c0da000d62006d000e1040d00c000c007908207 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 900505962 1250 900504712 900504727
    0x307050303130909020f060a0f11010e0d03020d0e06090a0506090c0901030206031305070f0807120809061b0109081210050319060e0a03030b03070e060a03141c02060603160803 77
    0x8036080352441605c010311a0041e65032440201d4955040b42d21440000b41d81ca008216010350404912800382d03440301c0c024042c4582111100b907895050b00c00a408066002071810a00076541d40304000711140c01c400c2c1d45207420455003265480100e81010303240c0e1b00803600030030a030386000203e01b02094405040c21100ba0328603000c01105801c000c0500102c00c80034003848001440901403000940510b4420503000f90070000d80e2481c00d2895000008007841170000c03400030071518000e075070b0001002c4901e240e0ba0310613169143c29003048140340704070541c00c04900404000c0d61001900b2000c100c4d08161846135038030503002c100b01c612803140a40580000c200329006051820a45060902500c40401c0c2d4030820314003140781220304001500066580d14501c00649028407003030004103544400f400d80e45c01c0000004856690758400100000c505091002c0c4207102030001c1c4085264903a00d40300200c1204e48083d484080c1201e225101e4000c0c91541c5002c0764446a1b00d2080e502050021414540c0 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 900507212 1250 900505962 900505979
    0x309152a020d0b0403020d020d1d0607140106030c18020a09090e07080a111504150f1202070b01050a05010302040320150a09091b1e0e130209030705030313 68
    0x85503000707a03041001c1a02c0300011404502032203008500c20f0307000307203a1000d0300e05000303050441f1204640d04005c0c2038903d580500c160300703010201140302262942d6644649103440843c044044480d511a0f500300380000090000c1020040126030703012542001c0207500300c0b00e0908034480e000021700400c04154013409070045580c014044020180e084500464032010b034646400c031206400c80d040c25143c0100d80240c10070300c400d0043c2c00c0847c0c0d0342d10f00f0315081074102079400781303000485030400400388201d82245101c3d019100000754891400c55546800d424210901c0c0302c24010313540180d8408000180301d500c24401c0740c0c202e136045080080c9010761090100190500d0940066001d02040b8061104541c1380d402404d42405644541250700e240214400a80b004003403080c4040e413800206034941600400090182d84010b030211841302c5c0a12401d4a0520a10803226002010301781141e90030031599000300044d020031011a0724007030380c40e001c040c1c0d40d103c2c84211400c80c2c400007108005502 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 900508462 1250 900507212 900507287
    0x2010503070c02190e04121b030f230a030b0906030c010c0501060e07120c0905060f0309010f02030c070b060a0b040e0a0905010504081210060518010509040207030915 73
    0x80c4020131182218202d49803030700060016810040103100c50a0a01080000810340700b00002c043d405c03c00f002240c80a051017031420340c1d80b0f011b018804500c1044122a00c00e01203030252610b910b11107040301e602c1d20350405181e00065070fa600482d28000740309540b0300d0b14901c41403082d10001c00605002c0c60300c138011038444d800b40004441e02c1d900d80380d000c2550b0840d07003041442283c80307aa84000d41c68040300d141c000d4412002944050003030201051005e80c6030501281d8122003003a640b01ea072510b91004d00350060910000e90030301e16101005018070000800010a5410b001d005401e00301d40b1200e081140c3d4440601c0b44d0601c501c0c080004100c852856948164402c0b4012030005514429440d09401d440707040b60201c42000001030364540d000c100340007664101b43c058a00002050410b1800b030001d100d90b0795000116082005090301580c4148220b504064004d84255201c0c0101d14019042103414056403655840501400044600c1421520011001540d080c01c1c1041070307844001005 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 900509712 1250 900508462 900508487
    0x224060d0c0503060a020307081308030f040212011506110102030c0301090902061312060c03420b07060501050316060822120813020d140f0601180510030201050307 72
    0x14082a030300254590f428888184900010800036a4901d4100d000600c0103400525000c40049403000140c0400c0b98841540c4d8446040341d0503200a49990001a55883d41111024000e6003004100016000020007840407a05d00e43c4811301d140c41d050705054241d000c2210000c110700d200703100420411041d900443c5c01c0301d00141886240c410050b49191a101481c0c0042502040320742603001045030038820b40f011402245410031420b4114034100a485201d0840914000300c150500c1400314801000c02c070260461007420440d00b070b030b543d516803c2c1b0b401011041d02c0071450a0000100c03401c1c04540020f0703000e020804003540a0801c00242c44400c40a000c03d145881d00d404c92003030070184440c1601d201c6000e0310100c01041c0d07a0038002880200001d041d54040380d47c0320f2510700161101c50650310410b038801030181c54094051926881c2c6241d41001e14664400c4a00004045004100e28000c0101c406030503c107554030006100611303070203480000d000072002c00028555520521092107613 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 900510962 1250 900509712 900509723
    0xc0f0501061a090d12090e0906190b061c0b0d03030911040e03120705040902072105040b090904060902030109030909051005010c03030b0f0a0b120a09080f0c1002030709060224060d 79
    0x3403507101e90a07124511f50813111050542d20800c184501030901d203c2d000008880000700b8003200c030b2a5408185103020708082900005094500e02c5900c400a401002c2071142c060a90010340515007401000782540d2203058031154000455076081d810603001e40f008600d034000c0110318000d190455890760000051001c5c0c1041803d01c40810003607102d0004108140c050900c0103085150284c0c8150304101074000c107420b001d0b0821081202100c0380096800701101190100d50903aa1810046c0140a101c94000e42c0741d4a403028005c10144c1100001c0280c606900c1c0400c4941d80b60000d0342c07101d100f00c0c003c40d404902d0300b0340d16900092090304401c845060107005c81c091010a00003003854034405401c102c09181c40410708170051800c142207983d10540b00e8406000d4401c064032803900501c5509061003e4030340c00980c8c09200c1d003040010201c0c80350340c260115a00d241c45c0d800208010f17441c0c002c80c00140599100d420410110b54203144424020f90301030141d58443c00e0801079204a250401c440 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 900512212 1250 900510962 900510977
    0x40c0f1b02100c1b0608040b0f150d0503090a0906080d0f0206040605130b01081c02240408070f05010f0c020c03101503081215120a11010c0f0501061a090d12 69
    0x113002c900f2096400400c4503448450f250304040c94550601d05008041584459581d020040f105001c40c0000e2032690003503030302d404540402c0c00e005040d07101d40041550400c440c0c1000103030f0382200750b128204880d04401a0750b80354111440449202601c10503010041c3c0c08072001c60045502a400550044100c2400020a0341030b9620741c1d080007401d03800345407603030080041007803180c0d84d03080c01c5039840c103061000d42400410140c0039a042c005410401088842840c002020002d8030382c125504d00c0e030020402e4140740081d2402501070025003015414880c14405121509400041e03043c0715074038000c0c05000d01003d40d050b03030300c010300e0307090071403082251070050000210380705038000c000c6e8070242800305103239141c074503401c6040101c01c0301035a000354411000e001c0c1b800c902258100042d070b072085045c041086c2c6407004840000319004003a0448081c00500306c10000154850380848801444400348403645042c000a14010444a10340003a00213111a000850044003d0014119800d0560 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 900513462 1250 900512212 900512243
    0x9040209040f092003100f0b1e010e010509090a0e071205030904200d0f0b12010e101b030b032805160303091502010b040c0f1b02100c 59
    0x20180d0300003040001c002c9644040d040705111001c524010801500d21600804a46110110707545042802d0b00d035074050740d10700e44030340030540035040391050b460010300707403002801c2c1030702042c1e04c0080201060303010070b00200c6202015401001070301e020800c02007040f8001c1e074030007076080050f28501c0c0c4002100d020703100e400310769290340c014803c80c82405400116125174100c01407001b211443c0c00c810f1690080d80c00084a4031103900211001d18514280c04154500c1c0d4000c0407015010360f409003a44000c0d081642c1c0d09180d4154010440b00104004880050400310200d00c115410050003203081034480d4024540640a80c00c18400c2a0000c2c00f218007100c0322001c2c80d03140c0e0080d03400780104000d000e0202418070604118072825520412000a030b40ca02d15a006010500c0382e10800300400f00f81e0303440c0b00c80704d8000e40c08001c50a9001c5c0051044c0d8003609030040c1a0720186901101145d0b40c204c83e10352901c0010340d082c4020360f024280e991640718400f01070301c0d04081c00710101c55000780c0c5071111 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 900514712 1250 900513462 900513469
    0x130213060305031803100e030a0c050115062604170702210c090a0b01020c15090a060e10030902061218030f0a0311090904080c10022706030708040809040209 69
    0x5100820b010040e400808451208140c10481840c44080c0141d05103040d04007d03200100c100e42c0740b20421304002c02c4581c0b01d49482800340a074805100c9141864200001d0056003242c1a52400e429086280194000d249000c102c1c0324016600a8848003580f034228801044440040400030300003403c80030b090f494183c0e0340c41c1d0840112100e01c040e400030303038242404e8104051001d410030b41e0101c0600510031000c000039500c0b45401e490700d07c2040151071143e03a01d40c80c2021503c0c0b002000e008000010348070310340607044140c1c090005008426a15410000d035110744600f0a203a81d0040c81a4640100110380321002c20014001401400b0a40c02c042d640d51000c0006041d904482ca810b01d41350010600041d048801141c51103550000c104180300403680d9440f012640315038031034076164a45d4164928946040a1810a9406135100084989020301114504141b2a03d00310f101c0c4044c58031003040c0031035800300707451100200d082c105c041400074145002030525170030701602c010305003075007603001 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 900515962 1250 900514712 900514717
    0x50306010b09100f0c1e0807060b190b03160201060b070312200706050721090b090a1e08070602160308060a080304031106040e01081c030513021306030503 68
    0x4045203600040d001c1103070309250881c2e00510206040c441da42000320800580f140c0ca00d005c00801c60502c403c04542501051a00600b080b90080d50080d02d802c560b2501030007e00151014070712660f5002c9180c48100d03002020b03442902c01c0160741a00710389801840c84840400d02207220155500d501c1c001c1200701c07075480606030302d0f8001d540301540d40c024104442c4c1120f403d1041102c0d0407042030240d0702c0c40c401030011030354500c0e408440099555500d040407074540c429609050b001c103092001203502100780c0d40048210034000c03024940b00e0344415801a59034a6201001405c01072100390707406800124000076a68980100c5e00030389004001d07610041242d20009400e034403e100000e002c0289a0300000c025481442924100021810031148941c1c034051884024800703d181c8528000c01c1d15030005440040040b41c04421107540c542d21800c0e1210100c0550101100c4106120710089109000d0240282200d0b080a8514005502485044c030085c0c000c0100c50380c1c80700f80020025004000 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 900517212 1250 900515962 900515969
    0x40c030b19060504020a0e01050d0f0518120909040308090705040213080c030111091306090614010807020601050a0303080405010e060a0b010f0503150111120a1205010501020f0705040f020405030601 87
    0x800c0c075030108400c5040022100329410003401244103000b840074060b00481c16222194090810a0300e4198540c05030f0003402c001d00902000c0c03400c02c030a010500100e550324002c084000815208031910000e0300c00218002e0001695021102c040410042801012403a030000c0402094840b02511040424240d0b80140d00424281c00588020080e81f402440061031004c02100240107101800511400c60302481e0b02162040b403802440092901442d48418000c0000400070701200d5a148040c803a1940c51091036800320701c1c8200001c5041c0e20100304079068070342c000d110042960035510101c85c1c44400403c11240c9640c0c8030380154a400c4100029849502c8a440c04124060080e00040a4100c2d000c900010b000c410b2081c4661f1113408902c11022a03020300c4d00029030f07001040740914180c240d10420841550000d8411001c1b07602a660118005810000b031100fa40e84d8001280c0c0c80014008144050b005400c0900040c503058101c01d2803404d2084000d4106030301c8800180c01c1002c05e07403 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 900518462 1250 900517212 900517231
    0x10110d0504030c051008011a04080f21040e04031d1e0a0b0a02120a020a080c010c08010f0e15060c0115171204090c12020412060e0f030f03040c030b 65
    0x24100b080026624121002c0c2405583c3e0408a100244006d465204103000e0044003105240c0a40c3c900c0c82031605403401404842c0469440450007000c26440d15203220314911810603040b48050003101400465049800c41101400703241c0c0d403a2400c94911800c007501000d01000d52414904030364401984a5401204030300d100f00c913140c000208074a03c00c075a40203207541042480054030f1990013091000b6006280703600d681d503a003d40070301203040107010100241480c90119000000080542c00303000a0300840e1280002640c0380c01c040c1e851600b103481400c0c200c0e0107030340c0018066000015010f40c0c034000a000a03080002d03a40c0c0d828291040b002c4100303a02c0000c034008005130030f202555010150b5101004d40503101036400c88040600c514040c1e225141d84440d51152014407580c280307030351002b02001c00c5440d11703100c2c070400400c02810700f0152465414224500400306012079042da00360200401180390040b28140290a40c100070410f5480030f8070340c3d1000021400000c2303040c0c030071700d4501d = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 900519712 1250 900518462 900518467
    0x20901050d06170601061b02011107050612010e060d02100e1813020f0402040303080f04050a05030f04060f021218030708010504060509160b16110d0302030c07120f0210110d05 77
    0x110f034682441640070302c08100101660700d010352503600058003455020b10780f00341d01c8048644032600c1d09259500079600200700040685004015100613416640011001841c58490100f048040902080d0103503104020070707107200c82d803030082500c81d00c0395002074203403401046020201ca60b80002160707a0344040d450885020304600e42101902035404080b9001c40c1414116203000f0040800240803404c0052104045414020200003804489510004581d62444014078120180e00705104400102d00065981040140041140c0d81d15580174061039080480c21080d04d130b03481c000c000c03000da0940a008004900c545080c041c03c3d101d14083e03000410381d8204441043e14001ca000d412002404000c20305101359070490045509490303d90151541904050808804c0d000105981583c42505070003010704050700440907004400600041e554802e940301a44803111040c4000100062462800b890040c45d000c4d0b680d90b5015642d00d480105000d5408200f8a0302503803c00110125901 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 900520962 1250 900519712 900519749
    0x503030c0c0d112d0d0f0e0607120c15020c0c0f090420043e030f01030215121509071107031205221e180507031b08010905070c080d020901050d06 64
    0x40344910260315815210b08d07192110607121981c079003003000340020800c6019100c940178000000c40c0721480c4080301004540c2ca200890304903540d0078442006038000d2064021042e05490104030b918441c035044052943c1a4000045854945151603052540266265500e05000c0358159800d04484003140311440c601c400800007800c201c04400356401d0710364040003080402003005240310304483e410b880400d000c00ba02c1d401e2407941d02520300f131780d0030700e0101c0302c10408214a0b48030b41a801940c159903da58540710a40100c0f510303c010002d00c00c00360702c90401000001e00d040000c503040c180b5850020b040c1910804001d02111a44070101203140c0068400c0c84800c03000444184600c0200003030140203423400d64034000c1440191305008a440d550303c005405030740a6000400c071141c04c04d03181458401c50343d0000d813081800b8018244100d1400c03000408441c0513101076100d0a40140c0c24600308402101340f00c0c0690320114250381000001d0040c1200312519000e5880075002c0783c079a0410300c010 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 900522212 1250 900520962 900520967
    0x608030903011b09060e01050715090b52110106090b0d080903011d0f1b010e10170c0c011407050d020f070503030c0c0d112d0d0f 57
    0x503d1400034103104900c0c00e40300e6140d4002d60764204032a103d04105800480217001680c2e1401101d101800c03420014901000321200b650040100740e00c242c031011026100c220741913001c40030001c1c6000078501c0440e113044e500c0040390070802d050109801d403c040982402e912003010144d850b0308101244400d540116280001e0141a01800e1038400401440182200041140500300c00150120380d0010f4205040d48003900702140d0810201d845000800c026040c40f130b543c107080f140100560040c14600c1c0c44c0390a030700c0d040c440710301c0d416505d040d0f400060200300031081e40e44540300d800f400421401d0040b500711003181d0505c42c995089125407140800e0700128295000c0490122076100e50004100d6403c4d00503082c0c80050b40b4541c0d0068540c41c0141c902d20151091244c060190710010042083c0c844440380200364400780b40c0143d85005842000642d803510743c0e03500c0c3c04c0950f00488105100055850740c07000101e1280c00d00354102484008a15080c401141000e04c0020554100540c0064 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 900523462 1250 900522212 900522221
    0x24150a1701080609070603020d1407091a0f0406050c1c05130b0901140c0f1f1b050f0d09140a111903080708130e0105031e0a060e030409060803090301 66
    0x15901003e440d071443c150860310703100c000300d00542080c1540492240c00c60403895002d01004141620443e515041440c0c002d0300585840c41409210100140250851b040480035100080080e080c01402c00d41081c0054500b60480c80c288165489521000501410038018041510b41c45468507a078030005030204010b502d119070007028010404014881840c1d910000b41004502d14441d8903444042214000f410003000d041d880c4158418480b158a611b00d103041980200001c1141c10440503d0701111030300300c3c0c0d0f2180c000f000441c07024401d05030b03044a144003c062030902c200b0000b6101d10b00d070f0b8a06040c05c14201c0c181e60503074000c96400702040400c4480c2c0d4190307002182c1c4401c1000c43d82600000c103590f1400700420060002c11801c0400c000c2c24242c5584140c00803800703540d01d032110003641c0c0896003442680d10030300c24600340c0b8900034100b03500e007005110500c0250040e40a9034817190007510300aa0080020320003008009400d00e001c0c41050080d000210145950b955680b04150035034 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 900524712 1250 900523462 900523469
    0x912030231080f24010b250611030a06050301060f030f0501020922110405180403140c1e070b030403080702070f12060f0524150a1701 59
    0x51040180344180e020506010506071080003480c03034003000d01e0011450280090384550010702c50b906101070f80300004160300e0034070050620803500b800e400e514000b492680a00c1200c511100400034101c0b160b51140c1501001b00002c1f440b501e6800c0c4030307520b0303000703c90200d042e0082e400404010b000d940941406440000c00e0f0480090241c13604080d06803c40004502c0000c05525078969101e04110082d0155000000020803a0b504e9091104012041d0040540b200708a40e1401c9030064002444009940030354030040e240311629011510f05900340600940140c0502540c4030070380b0601b010100082c0600740310314000d04901450b10f03401003d50812541240d20f180c0084030103101221984081c5ca84c042c2e01351601107600e840d42c1105a0074205107030020051034400d08070106110062407080300b042072080a08000e04d10b1030208030001c803881551088900610810010000c982032001296428401011018000440342c0030101c0c0e0341c4050301c68008aa00d0720280c81600c0c54461245006 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 900525962 1250 900524712 900524717
    0x90c1106070801060e1f0e03120c0c01030b12070605370c1406010e1905190f150e0f090f0304060c141509060115140d18060912 56
    0x203051594024000b050140100c004210b03a41e007042900c0d075a500c5c010003004111080000040310700220081207010000c40a90081c490700d1060341c43c0c44015001c0311700580407440500204000c080046002c4e22102201c2d981c01000c2c802e11180c10b0314280301040090a00e03445540d40c6900160b2508810b07000000c0742c101e070050702c80d40c032a0359210103640061045202c1ca8182076003000303803a2801c1426141c0e0828241482410000b0aa00003052655801110401d0f80510784100740c0480c0400d65000b21100c00c48c001600c0340c40b00d0713074034103641141010300c0440300003054036038542c0345000c5007440c0c0e1350000f109160310720140618815425401074216414101a00d00c111045040d207541b031017940b007400100122460f1740c600340910000481b0150310b443c401c2c0c480400b00c4000d030030800082660804070f81d000303c000005080385100b0540b401e1040d541c4a80110309981c2c403502d00e4542203880e25044035a12100141d0f0200e100400d820b081510903c00021140d455042004c01e1180c00c031101c005 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 900527212 1250 900525962 900525973
    0x2a0f19030c0e0a0e060d0c0e0403090e15040f0219030b0f04050705161703040609051e0d05090310090302030c060a061a0a030b030d021f051509130c090c11 68
    0x42540f6650200015983c0c85054850302c0d0320f40c0f10200d11010114039002e042e610000d04c0100742c50206003011801140240c3c0d407100c59540300d24610050396010b40781c603400c900401c01e80800c1c0382410703040710070b96001c4804010f040440c40c100c0010f8000d00326520f4000613a0703c1214544a10707150104412403041680d04000c1031401110140051080c00c1c1d5810344512032800c50801c0003221400c64400c1c0b480c0c1082c8644900b030514042d00a40054101221240903081c0e111401700f003115502000001307038400404081010740c00a550f00e43c400c810700d41d054011125405d1000100c0c2c001d4502184c403c2e4000d546d03800b2440000c504007170780500060f1095040803010850019105050401900214411035950905c49015401025480300443d0580102411203910703940109048401c1c040601419a590100c111b15004071003040b00d100060f81c40c00c00005038141002d491051f806100350200b41c03084e60460700c0e2071110300c00a60000300401d440d0018501d4440d4007007809000203062200034038 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 900528462 1250 900527212 900527237
    0x708030301060c021e0a260c030c01050a02210408060f16050313062c12031303051b060a0e01021809060a0914060906092a0f19030c 58
    0x1048005800b001174481ca400381c0104200c02249030201107403082c000d00130b0030300310341c3da6265003490054500c0908140229940413200407501140203801084002c0c0608206d00d041401580c2c56000110f1070004c61203005410a814841410407208242580200540b0740d4505441d04d4036010000b001c140c201ea1020090008ac0c00114940d18000c0e0b0031420300ca912a6981c0034140800d40c1e080b1310113012a410501c4249213003101c8941103074000018862050408554040c0d02c0d5244880d055242e80100b00f000051900c18a00ca004100c9034860702c0d2040c030b00080a141c8410040c031a404240c01608203c080c13005040340c1e442090002d2465030000e5061507044c50500e6910310441201340d01542c1c2040c00102569103404408003c1e240d100002c000c081c82c100300a03c1440704c1160064001c42800c404a0846d1504849c468414200e40541440800076034528562010b04194800c030300080902540c100d5103650406080c0403006005c28031501c08070024024261005400508203000074031071100b = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 900529712 1250 900528462 900528467
    0x304140a031b2d020102060903250c050d11010206070c050d030e100f0603020f040b06040603020a0e1201091203060f0b0309100e0d12060b04030318090c050903070803030106 76
    0x4003400382020070a240645060800000c18022401c502d00c2000c18552161044086a80f030b410107a8000e03401c848081c1e45d6540b07069540e10615400b403014016030740c6035203482520303100c5061010384240d40182c0f005948101041c0070f5a002c0c80c04071030b80303c0318540e02179007035904022955100010340381541d03401d0039548840d40c07202803003800b00e0b0400d9101c040400503a441080828010254280200410044980c0000052001e408200d1240c141003985014902d0710f4050842440d000400217443e10b840c02c00c00354001d5101c00200400c0c4200c8103085151695074030300440d07407c02c40c207001154081c0703185000082c0841603c07900c005c0c103103089028000581004121010740c1c2400040503a2901e40c8080c442c9001c43c01e070800b400150628140a400480207c0c24400c1c086403501c41e000e89002d810608403e0301e40038015001076202c00d20007040802d2288a4150030240680820b0150a0b1101420010348203c00b003c480441d20000340300c0a14101000468000e01c44032020314255410500d00 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 900530962 1250 900529712 900529727
    0x7061a0609060703020a050706020d0e030106050a17070b210708040819020304030b01030318150203070b0a0b10030c1b0b060d022206180c0c060e031b030304140a03 72
    0x40c42d0180c00082004400c00d8020004815100d4020301192007869540d84025500c10840310b50700d002a1039206d007078040d402e05000702d505840004000c20300540c1040f4190649251898041041e440385000001348449540d000b0801503000c44103801c0c6110070b400040c42c4210001c1c1442c41084800000c01011500a10564020303044080030f5114954141900328954011a00301405000400e00000704046c1c100c2d4440c2d08091052104102940d618240341c41f240d003e0030202d0015810401c450310003d40d031940500d9102d81101360015030f038000c4101140242c0264000c680c0460303036650510009980100c540784100350618003000391852941c2d90410b100601a0449024803403544038801191b840ca920194450301100b0046421000102e62401501e0548600d0102cad06035030001c195000b13100c1c000c40d94407020303036100e540951245954041c002c12801043e070f00180028060050180307604c0855103261141640116220b00b081c2c249100789042540642d195603100ca500c0c100025001103c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 900532212 1250 900530962 900530977
    0xf042003091018030e060318061602010b0a080601030803070c1a01030201180b0f070302010b0910060e010c05060f04020a05060f030609060f1f020a021c14031812190807061a06 77
    0x403880d031030b5200c231004a00020030351010b0340c0f00c0b80599401c002c1c080b0145610741500e20380c0d617070091010011080074000962501d014542c481d80010b070040c404200c1030002150001c07032314a0401c0030070b0265155400012008983d00d100c804091004000303540c1d0103030401c26242d105840b152503c2c1d160203584811441111942d502c003590100d680c2c0d0905000b0340c040411880054060074a0386480c2102c15120251030213a0310102e0150702154003e54814001e040503c0d80c064010405503c074001042411140140101ea0244000d00702054585498000d0905400443d00350b540f01c0c24a002003104d2032000801440c054208004071008c07540d00c060f404c4c6011802c40c0d0030055a9503c00d60100e041010450300a900b2800e02d0151001c00843c1443c903141040c00351040e1106e408060303a04580b03a00c60001e0700f14030900181d40044042c54a07d000e102800d4044089501111800714031481c0c4400c01030040d07071400000315001d81030241034040e800c800b00c00141c01c07084000303c040c005a00b9008246 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 900533462 1250 900532212 900532219
    0x71511091e0409080d0609110301120f020a300b0f04060b150912070e06011404151e08042f030601080f1b0f042003091018030e 56
    0x10103072480d40c18120180803070000684248182c0d07a071410484515400f108800703540c82d03c0e14070005510005442140f070030184c1e00c00160302d56441e240f4243c000100303041041c0c07144c1e25150301950059440503002c0001300550941d0360031005015240072000d141000300500100741e0640808000764484041d6540301c50104035804240e180d41c28110010b1640303128494108501c0b1120008003d070500c098070382580100d4051006030002d8001c652241d500f4441da0300d20350380b0000401e10a40c005c2507826040c2190b540000e0600399550054101503410042440c0494805040803205800c00e905412094205041817080b50030b0980d910341c2142d014030300072449104540844000401d014110f5000388a00504076010703961070381201611045401d045000078801d04182d20381183c0080e04086401c10b0041000044008280501c4040e1480021613032900d0200400f880d8042c040301e0103180500d003000000c10000c40c030000c003881100d40d050501c0c944107260100c050300113036200800b80c4042d05d069 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 900534712 1250 900533462 900533479
    0x1a03030f0a0305130501090813060c020a141206011409010b21131212050108010b0a0306051f030b01050a0f050330040b03043f0e06040b07151109 64
    0x4090800519151084c014020f5080254a1040c07040041c05030503c496001805002c0381d983e400196482421810001c0d00002c00da803040104814115000520301005422101d1205019108a00b0701909030401016940002e04079681170412548150240045142d05031402160442c19001a43d241445c00249030030900000c050b60205030081c03100d04d0340103419841c8500700590140407003042c052001d0307080f403a0200014107014140100140b01001030000030300c0c5030858441c04082c00008000200750080c502d03007020b082c010140070600460007410102340c1035041200b0851201405e80c4206020405100c4c00d00103907502190003110120602140700d1036a580c03041da03003000b1041c44242c0400f10302c042400a52400c2030001544501e1094219000c455020540c03900814024003003600d0a0400c0c8904420b0610030404c00e0414502170b05002a48182c0500000c203a40d01c540c110b800d0201703000c00e1407403c008005480610034000d280060080000f042244030090040d5076078540315007240e = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 900535962 1250 900534712 900534721
    0x90a03060b0307030b01180c0f210b100c1401092012010608030405040b03030703022503051b190e070c0c08010608010606180f0308090102031c1a03030f0a0305 70
    0xc01c40d070f0000b980d00c00c844080b1980d4450604522802d81c0524045141c280f00c200e00c101c034400c3c4280da0040f4026100d0281c0698105e44225400440000046e2010742c0c0d042c440d45507a07550b00c10200e0f40c030301558030b840c0c088240e454244002d10700c0195041041c0e040420020000342ea8004071b001c900e2032400d0381c03404203014070001040e00c407002e00d040c5220351230208042503151012000308281c3c0d801f0748060013280f001109040d528420b01c000640160018031145000c6211405c2c001c00d9446422260141203489445080c10701c1d000400c4110b01e0300c0f00000008040c2003c2441410712019586811010b07480c2c034841c4809000c0c010203800811011615145c1044800903004000c1c20050703000700300c0c0d81e84452015000700814090180031890010440300862079002c9d17820203481c43d40244122151850750380310b4450700100c00b00c0d41507010a000710030100b201e01354540e104a40101005c11410b00b8591182d6020580c41c00c0c0c0750007078204001031030400078400200c1c1d1801c180340c42d0001d41c581d80c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 900537212 1250 900535962 900535969
    0x21804020f2505120a031d0f120f18030703120305040201080f1b090d050609030301031703090d05130e0a0f06062d110706031a0904050d0305150a29090a03060b 70
    0x4604c1a0003442c1683e00f040004031200000c0c0e03c4850802305d0080720003a01c0c02c0989405540140d2044007204901000b0304004590300071040c0d0400c43e00a81120905a180d0b550703d03d0302071000e55a04002907440d170070813081d076038001c2c02160001002e4401442c20b040c00700c2d00070720070f03a022032000d2080070380068a444640c031258407188680350000305460240c03c0580006450358070a104c19540c0c0100c0401c00c4000c220a101124020b840d0040184400c01c0e00010079512500300c0031040802c4ea100c80c200040129040b0080c074400c17041c85000040c0d07210007082d90400c0318900e0300020200031207210b04042c0d007107403103014655440348143d6100300311103002000c84d0344880703030f0074042154043c02d100010015055040110110010a40c409140c10300341c0510115400490f80500180d1001c6c3e080f2850034003940c002c40c0c0006000108083c070300e4107800421120607469000c0319102c50540c1080054078000c100000c51b410410b00f90914202c40030000400e4101c59010180c102c82da6410380c6d03003090b074 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 900538462 1250 900537212 900537221
    0x203060a06030b28080d080906070e01021b01020304030812070f080108070306020f09150703091d070305100e010f030506160c02150d09080a0f0c15021804020f2505120a03 75
    0x3089400c40b1024106d0342801070a100c800e586003240b62081001003008240a00c810320210401079004044191548080d10b480207c0e150700e203415400100400f2000c00c042400408040b40607507110605420300700ca004014a0800e00b2030340400440d080144600c104c007066100890f0340010016803640428000800c60b0f01c5090200c56000c81221540a801560351026103030b600c3c0a87c0714200c01994a00f4581031081111008542000c0d1940005003076901070b84c4050f40207004020420800f81d02c51400760340300351023078101c0c810301c04d400a000c00c200407040041e55400030410031400c000155001e00584445c1c04804003c2c4140d5040c000070100c2410041921100700c1d17101c6081c000d261850034000699442001c03000000b0f225140c0700d05083e4080c0c0e10000f0b5446d03014081800b84c0b40c1c035050b203d000f034110322803a00e442048034000c01a039039203038006800b021009401c0350790355810072030300079030550508840380c112420000b9414000c10300204401c0c500210032031190369141e8412000f24020b1 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 900539568 1106 900538462 900538469
    0x280807020d030e03010c02030d0c0e03071401140a03050a0b01020a03120510080304180b010c080904050c160b150625050a14010203060a06030b28 64
    0x10705051004050745070091511401e0b012540c000030742912000207903800142c1c804220540c40c040c561007070440143c07042c103045440a2501d40440d0b110601e52042d600554401b101400031a409150b80c92099a50345c080ca03a640c0f40c00302c1002c2c00034801a10b80c8002603103400000081c40d40000740302400541c160701c07603100c0b401d040e0302e00d18007030100100240c4c81100c0d1000d000070000e0003040940003030048242001d030904030f440c048008036079500094034100011080080040750b12078080381c04145003a80c0108455a80c40c040c07000920505100c2c2851035a032001d42004e01005840a038010f481c294041c03551600640b04002c940d009504c084c2d4a0340400c858824940313140800000c107070704c3c8108181c0396a00311544914580d510101e498408a075000010401d69140449808014103082e041c2004003004140104449880f860303071254cc82401d004c01c82412080c10038901004 = true := by decide +kernel

theorem cover : BRFrame.Cov 900359712 900539568 := by
  have h0 := BRFrame.cov_init 900359712
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900359712 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900359712 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900359712 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900359712 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900359712 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900359712 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900359712 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900359712 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900359712 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900359712 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900359712 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900359712 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900359712 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900359712 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900359712 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900359712 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900359712 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900359712 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900359712 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900359712 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900359712 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900359712 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900359712 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900359712 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900359712 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900359712 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900359712 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900359712 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900359712 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900359712 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900359712 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900359712 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900359712 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900359712 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900359712 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900359712 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900359712 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900359712 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900359712 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900359712 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900359712 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900359712 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900359712 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900359712 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900359712 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900359712 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900359712 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900359712 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900359712 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900359712 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900359712 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900359712 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900359712 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900359712 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900359712 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900359712 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900359712 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900359712 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900359712 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900359712 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900359712 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900359712 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900359712 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900359712 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900359712 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900359712 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900359712 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900359712 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900359712 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900359712 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900359712 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900359712 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900359712 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900359712 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900359712 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900359712 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900359712 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900359712 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900359712 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900359712 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900359712 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900359712 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900359712 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900359712 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900359712 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900359712 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900359712 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900359712 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900359712 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900359712 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900359712 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900359712 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900359712 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900359712 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900359712 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900359712 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900359712 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900359712 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900359712 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900359712 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900359712 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900359712 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900359712 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900359712 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900359712 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900359712 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900359712 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900359712 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900359712 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900359712 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900359712 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900359712 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900359712 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900359712 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900359712 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900359712 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900359712 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900359712 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900359712 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900359712 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900359712 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900359712 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900359712 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900359712 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900359712 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900359712 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900359712 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900359712 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900359712 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900359712 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900359712 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900359712 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900359712 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900359712 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900359712 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900359712 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900359712 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900359712 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900359712 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900359712 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900359712 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900359712 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900359712 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900359712 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 900359712 ≤ n) (h2 : n < 900539568) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
