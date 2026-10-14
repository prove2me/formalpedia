-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1743
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T04:30:54.314338+00:00
-- url     : https://prove2.me/submissions/c5a54cc7-470a-45c9-a017-adca93c2114a

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 313309352 ≤ n < 313489208 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 313310602 1250 313309352 313309361
    0x31e160b090d020c0f10030905120f09040f0e0c01080c040915090f06051c0204060510051207050a0801140d052a010e1302071401110307030e0d020606040c0210 70
    0x19860503489002c52038503142d01007114286000c02261900809401c001c00a82051910360174403081646a00081040107803c1050314840080c107410701c1d40390400c0c01d40c00b0032950003030104644aa820f000300b014150390203104400d182040030b0041d09051401390015181c0040217010f0f15086602088002080d03a01403048a0041d95440b6441e08a185404da0b405c0c15256030251003224580382c00020030156541040c00c4c96038440640e0300c2d04154045000103001048154402ca410900e0b050000440e41d500000500107003500503031030611511604011500c03800b6030036048021074440c20060103035601c0180390600c400801803050760358200b29690301d42408991010350036082d0350100c442d0000040346001c3c856040080c41d14036600a140030009031071014003555254021341c00142c54040c400484001d400c85010174000740420301c0e00325030105a99108454900009151140d0310030703d0782c40031a400001c4801c2d58000d0aa544030307032003004000c02c000c1039810198860304945103a1001e1034041d = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 313311852 1250 313310602 313310611
    0x40504171204020405090303090709050702071806030605221509020d030906081f050d05030c03070b10050406080a0615051c060f021303110a0302090c03090708031e160b 74
    0x26401c00d03900386031052000b40c845c06401d000707241c1c00c14000c0040c02e29001580108660b00900d000c41d050301d4101007079007498115003106d0040201c5260b120903585483e00800202e074407131401040a0f544030f000030b103014500b01070310500120f88104030002041250080d4031410500240c0007035441941e5001503e02c2505002c1180440da00e42001c01c60a40c00c00241a446813428003500b01c2c0703400d1244200860314907401402d1188074407051704001c0c8601042a83c000212403002ca075592005410000d002210403250b114181c1c164a23030210301402c1c540100f400f2074860300b0040006e04941c1e034840e4040c01e01603000307016492007040c0000b10340e600c64141e0364600646c020480341c096101d0521800fa03400032800c907443c3d10300412185001240800100044a030450822281e201e1a080080e018080c20781c4007a40c040e454a0a11001c842c0d00d00043d401990003c048036021540c1e014616100c0c0202c507112003001011106042c5030f10f1908000305400303150300c1400e80718040e15a460491403001602d = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 313313102 1250 313311852 313311877
    0x91211060c060a1d0d1b06023403081501030b04050115030f0510051c060c0504060f1107050111030c030c010b010f022d1603030e15090901030204050417 67
    0xc00303000d0004100e125800e00306925034140100000070014103655034001350074400c204440c850321900c05682002c48074000940c0b003a070641d9948aa0209d80240300e10000340104801e102c070b0740300325154051580e6440190b40c5500d8031034207070f0380c1d6050610301e404410079018145601c900e4950300c1c65440e0301c40c050282a0f01824005000c0044100400f00c0f2a000b81c0820801d2400c401c0c000c00740c001c48ac40808403041124030001718100d22001048590010000a0049050200d8110300d6900030300540300365038007561101904502c001003101e5580c0e601c880c059841d0080e040074446e652290314a40309044e04481102d141c4200540d110b4991b5102c5641c401d11030359110300c862080e40e030010740a4030000803440100400400d00008002d04c04040d680700d07074a03001240091030010010300804442c2e18980310200c00096a80c2000f9000510a151103440f4100e046004202c0811102c25a0000b00000d80542c0050380ae40d82400020b0201070410b0f1010000000285440c520041c010040000c248 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 313314352 1250 313313102 313313113
    0x30a151b030e010605060f09060a020a05010c020d0f0201050f010e07180920130501030504060b040c0f02010f27020d051e010506060309100b01030b06070602041802030403091211060c 80
    0x10040e90071658a5040584181b0080000c040507a1800080e6078004808403025a540c402c6036200343e240200c1d2100081843d402d084421542940210b80400407a110362180c1000702ca0490f0101d01301c1d54125603031490303484440010310618007441801e0b0b034028000e003020010008644001d00c4c10140c242d206020f51503c810b01058842210034403880c16054a1050380d061034416140b080c060a424041d0a0405546000250601505402000720391201030020040c4103c0c2450081c8000c04807100c10015600340803d0005051103449140040c54108885103507020401a00c1e4259942100e000daa000e0704040414001c903100b44003810100c41e88036040c0ca10640702c03040840c2034a00080000d4480c4009004100010601207450340f00c03030166490010740d82000780c0c01600200803084072150080c0020944104028a5a000788181c80c4000312001c1c1044c0d601c0ca048046e48005c4600800103003226000308002d010780c5052b0b01c4000d2282c0e8803020552609c0c0c0c0400d20b0703a000b1101500d0694800e = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 313315602 1250 313314352 313314371
    0x4080c030c01030b06071e0b0717060307150e0301060b040e0a060b070210080a3b07050f0d0312020a050a111203011202010c0b0f18030405030a151b03 66
    0x402645107062800c1c00d003807040c100c0e15000a0143d000c1c51030702904d90051815007040c0074800c81c610071200381c0e11000076100b50a15a40c0249409a00c2c7e03081c2e281d60f00e103c804104145030000300d4008480c074484001100c00da00103000c03101802c1030f44060303405641710300000c100102c60700c0180c0090444260390701c107103240c10070000701514210ba0140d180c01e4003c11055025071150340305002d40040d0340c10001042e03200d0301c1c01600280410185072100e0f0b001c4070b8291140d00321294000410025400442024540c052007250b15007200b4403071140c1c404070410288400341850962404514045c4c108000240600350444059a01a0b580f40000540005001c2c100302e801c410001c5094000000034014420711900008540c44180900100d01c507910380e001086a215555540c0d6036940608440d105040a003124a00d9142c20b6800240e680a80c0d5000d0300c0444000050f0ba0485000400416000115480d8002046021983c04081c2070b150760340c0f22901c51070205426105401c80d5000644d0861 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 313316852 1250 313315602 313315609
    0x20603011205070b0f040911090a270b0607031b05070e010330030b030703020319120c082a1c08070302040b04030b07020a20090c16060b1504080c 64
    0x184d000302c000a00148401c6800e00b6400058400b500d0445c1d4000801d0708010203c2c0c240c0c0d0149528684c2e01c42c005030800f040410000e070f14146880180c0c40c015180341e44c2d0307061650503690b00e40409900188240041e1010910401c030055066242c00040c0103d07070200c3d100c071030901c2901e4210541404415004208211561b0141d40d020341c42101d4004e05217401c40906943c845020000030105601c1e942c1c0340d180c81e0b4090001c03500660b4018125103c02c3c626907200324200c0d0111340255802d03e00003201300c0300140a000314000d1160300100382c1c0e15081c0c03241c41c600f4801c100c41c10884881c05100569031002041005080c10651440582402c0c100003080010b1640100804550405006002c10002c850001c8103883c1a0380d032215408e030301542d56800407454070b4510040500310091005003200d003138480c0700c588140040b094402c55602d64a4071003100041c45041c0c40e860101c84c41c0792444011036290351061001e02c000400700400402c2c0040c0002458000c3d40003082c203a003002070381448614 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 313318102 1250 313316852 313316863
    0x8041101050a0c0f02062109100204082808040306020c0717030403060e03121911090d060b0114030a0c021b0307181104090207060c0e0f1c020603011205 67
    0x4800340781181c40c100c2005001481a140c800c0c0040010b0300d00440d0000b199502c1066807250224030506c880b50032034a2102030300d08030341603d000405004183c03281100300064000c440c1900d0281c2c1c000d14010102603099101e000310300010340410005da007034007800143c05100420085000703000145e10744000c080413030308014403980070207201001420841011100441aa42240d070008030011b4424444080306082d885100e81082501c1006820045140861240c955101604450811050f0144080d20145110303200d10a80c0c0300c03090b804400c00203a200c1d080740f40140c0701071400b8141c005210400100302d4005650711401143ca07100f27002415035041084c444d1086102803038070361180440021a40f5495203008284502c0019000920407030100e4002280108401e95600d80c0c903652000804001d40100c0d00407a561820300340c8403d115071040e4201d0110784d200819a44950f0000c80c20000303001c200c04001c01c942c020f00001000513a4480c00510b00810407048096985180ca141590620 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 313319352 1250 313318102 313318133
    0x804050f030706080115030b0d030818010507120b0111060a0e0d030908161a07030f05070804050d1b0f0503032a04090c1209061b050c120304210804 65
    0x25400082c0070880c25911102039411100c403900504038607003d1140c00c81c05409850345994020020507159420150f110900c14800c16428800d03441d8810752081d00c030700742c48007504c002002030000c078840d910110541d0b110303468890050400011030f8982d2440303d410410220b4103007441d581c0d01c00740518500028401e840600086150411408034141d803141d005000e4001102500c2903c25408010804208011425161000c5002c1d03114505460010040d01b03000000c04191390401c404604d0060003540340d0703401103500001801440aa8180c01c40c1c46440c080307042ca03040500c0d00080d2000c10b10f98840c1c6078030a405000174541d00d01d881c0803041222540080030000f1102710500324101e804d2441c0948055940b41000820f9070103209404849140030200c070412010300c0c1428000c00c00c0903aa11031011a101c00d03c2d40c290944020105440c1d40c054000304050580211b90f0110240081c1002140d000e88a0f41c0d003141c02c42c0441c02035a564111a14200021803124004d000a0218401c00203d00 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 313320602 1250 313319352 313319359
    0x1060602030a0903080706060807080a12090308160c0b0a0509150909130204140a090c080d020a03030f0603050d0f080112150902180a0b0a080105011a03070504120804050f 75
    0x100100ea40b401081000288805017400c500403c1030401c005254201c2d42c000d024110460b003082d034407071450540300c1c142c1c60300c01c079141d40c1401201d69005024085160840e604400c2850400034072540080a101c00308004480d00c0350b10303010110f07011039250050203e800141c1e4890b501c0b00320000c00c0c088219080c2d40c24030001241800004480e81d00c000396603a01583c5040c0000c1d5003c560310100700034200c6050707039510700c0c036920040050600040d404410164010000f012449a8070040e45841c0d20464445c440183c00104d03808021901a4000451010120340d001074420360341c1d02c0e01070502520718486000100c055100e040782c2c03035001c02d0b024090a411003181a113442e8603030340c0d200c098581021030b41595440340306400540d42c80d01b02c0c0301030000e622492007090f4a00000d0641c000c00c40d085c5002e00c1420507030000300d500101407080070b041c0d8138a81e17543c0308030700303205803030240550001407804040080810011840342448818200d46512800840d80c5032410841040201105081007a00 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 313321852 1250 313320602 313320607
    0x103050901060825051003020d0b010e0328080f030f0916050111010f09080a020f0616030504080d14010e010b0703020601030201031d010e0c0319032a060c0e030106060203 75
    0x1104041081207014103403c00c00084102281000d003c0701e1480e030b2010394098400e1001e00c141b00e030190000c2012407800d0104000c174445840064825070b0810b075000360075520442580052080040316030350241074031180e40501590b0755641203520782c01010f0705c440c9000c0220500503012010440b058101170410302403e4440f5240c1d009081d02c0032644943c504004144545148090080d03000786c0b200c8540074002e2110400c141080901c0e0751007800e10385c00510070912007151030340010803514010300d44090746041041003a0f070210302800b800307041500d035a081080603902c0405c2c10311581d521190500018a26503240c6020084810300c16070000000b46001c110390400254085003440c1920342c2420b0011340117200c1ca6041c0a8840c0c20101e0102540c41c04200409451002441c050042822000c0750300b075400100c040c001c0041c01040c01400305000c0c00c3c0d0f01e074150f031320b8042c1c0302600b036048011800068120b8607800260b40031200c1c120041013400c100c00071a418280540c00140c42a40011b51 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 313323102 1250 313321852 313321859
    0x150307171c1d011206051f02120918060315040b07030612032313030f060c1809020304060b09130c05010807091a0d1e0b0904030905040203070c060c0509010305090106 73
    0x282c400d0400c603241080740400c410205070100da80140d01406014120b0821903003140d0910700980110760369007001d4802d040c014075100192404a581508026011400741c141400c1d402e100f60340041c1c41107501d8060708a42c05510b03110300003114404d0340900c50b100514200340d00003900b210440c2d04101c02d0b18650121400200307070050245011a182d2024000c1701e82c1c1800e90b69844c0f8002c95400010310407a00f9800018000000320310f100b45030007000c00b046051036141050321040001041e581c2e5229030703c041004681031030750180d50b000d40100b07800b050380440d40000440103441250040c2c0300e1400c032900d0805025103c3e0401020707180a0030880400d0a20240c0580401103502c40c89445a50440b241d82d00e0f45403150079924641e040c40c0d428030080d0300302c4010400000c3d00c031543c40d04207443c202c020440740c94240c00c0075000341d8064070f45e00c2c03c00b414182800060341c4018800000d00034a00c11803030000d02c0a125079111004181ea03110b4807500040001070940320064403485450381840c4062 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 313324352 1250 313323102 313323137
    0x70321060b030c09032b0e0a03020307051c0606090501090e010504030e040c0212040609050102160510030b12070801050a180525090204080a060c08040308150307171c 73
    0x140d070450108003c0c00e868440150010340b5082d6100d428105818001d07280030300d040b00040d159414030780140c456203904000441840200c89036032101a41c1a03020300c10400c001e0800150541c1a0001c1110035002e40007141c0f5040c7c10744141d0b0740640c044640c0d4100401c01240944a0b0480e0340c0c14040092195040c00d44000f0480c00c504075460788121703600e01e2100b4040e07000700034030200268000d610648540d658103020304540344034400d003030260061040e0b080e400300c0300b40611010f407040103003040224008800100c0040001c50401500100ea68490490300c074400c0040f03400a0420034000b207420b1030100f141009641030200488400c500c607200880000d94042039904815102041c24180b0040101c80d0080710710050340001c418502c00280031030940000705410f401103000300014041d4920124041703586520840c0e02500060061000c1844007401001c03140407944003c003101c0c446078441040d00c0d8802281036404180754008000c07002c2a111036a0204011141070514801230074031036840 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 313325602 1250 313324352 313324357
    0x3050606071515050409080301090b0303192a05010509011109060304082503080906010605210603100e1b04090b0f0408040e010e0618060105040302060915070321060b 73
    0x74942c4031104030b1903484511450303600030300006000b0306c1140c5403820a08800c0d80300707000f00d9040b1780c10000d02003250706000040f1441e80c1180d00203444070102180048a607640c0d0203000c03103116040004a0a0100ca2244e0b00314000e60082e0300000d100d0030300803800d500315010503031019801d14061013084456569601900c0d4042c0e00000341d5a82ca8641c0e460f500d0a1028800d0200510000740c41c1410a00d0350208840380310701c42d01812a0700c2642c0b5010147c980d800307605e40050000e076072820044020752401c1c02d40c40d08510b002e4202c1c0c501029091100701900d1000080e0b0049a00041d1060f581103407a110407451940280c0782040004442c0c0c0302d0740300507080100800d0001c00d0800c00b04003004030798002c0754010500d1000f446182c0d6154014088070a030705540703e520031507401400103032045450641c1c1e8000c680584074985413a00d10703400d00c6060b80002207950b80c005130039441c01400e0741d100310003428100d22940d10030b1811000c00307402c1ca10200c0680e110940b401e14000042c409840000c04 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 313326852 1250 313325602 313325633
    0x20705101d040c0906030b030a081306020d18050d0507030b15130c090308070c0506030709230f0114070b07050a0f0f05090f1c060b0f01020604110103020304080d020711010305060607 80
    0x21b0106600c1d0f40c40001c603141898445c8020250781002a19040c500f001c12440c8065500d40e900703550310030140d0398003241c029164400043c2c1c40800160200200c2c60031495100c5424492410340301c403142c2d03e0300c80b011a0b80c1c0c200c0704541101c038807150f8141c2c0c918001c030100d06007614502c420800b4494901c0001c002503540d000080000c100000c58405105042000200400300103000955a2a012030001c181800c24400e00700e00c5036102d44e440d043c0e910640f038080ca120001501c0105940c2210b0011140030740d20010300100000104803000c00700d000000018800d8a541e21541d40c0c07003242c81c10042800d000844c1950400a90508400c2280d03484002c48643c02c004a44d03025903c40c007030b0000b0340510210031842103454500ca103a032040150a402000c6102400c035061200c2020030f40040e42c86041c111001010083c0d02d061020041d030080d805140c11a0040c0c54590a143e0494074110881e44030510a644481000c10350b05030a682c54083e081e48010309491050502e500c0e0f960700d00e00842c00d0f09 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 313328102 1250 313326852 313326857
    0x270b04060e0a050a05070510030e06041e0203060108010b0306010b0f1204080418052401081603060509040f0c060f05090d240902040509030703140a020705101d040c0906 74
    0x3084007403204420001001401c3d00201a51804182e91030401d54030619841b07020702070481641c1041d400c0b402072050480c11001c0c0400f0302059034441c0e40d00900c1d0041e0035659002040301c80b1000026132010480c00f406003800c0c8000242c108181720426281c010140c2c00610074400410140190f204d01c0c80c160364a171040b280040da4907888928195443d07014a0304104e0b20044610b07080c0514074042e801c034900a5481da80030a40042d503940c0007203825000000304c2c84c0419241c001190124041010804482c0505d2070700144e4107448800060000138140c0e0295080c009810008003403010281443c0001d192f18148100d8030f82c50790754007500c1070080c02c0b075442c800d49500c0942400e1100701185010540c040c94135a01c109040c4160070001441000403d038002ea1501000400810000084400194054840c00c030358059903488501035038000205041140907000e4001002d44542c3e201414402c000c0d20303000000313145525220101c0701080e50081c455420901102d03105904804200306071466032 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 313329352 1250 313328102 313328111
    0x50f010917190b0a0b040b060403030507080c0a0f0302010c020325050709110c0f120f0c03040905010314060601030c0905100519020a02030706080c040b031e0901270b0406 75
    0x1e9075141c20904a01d00305644190344409000400c025502024442c41491404000e80021082404115407007001c240350440c408100600c04039004402406041e40310b5030f075040ca0009540c00403800c01024010433100c40e10013003261000c03d034080c0252a1550000d1004505001030580c8118514052000420b10000d02c158110b06104051204d00050010010180140740076074500f041240d00c5402d0080540c001c1105542d001040450440007505000790018200b000107413445550b6071111000038042d2104002c0021003c900d401002e0003103000d03203907000002030142d42c00e80c28180700030111410185428180819541c00c4000301041e1041600c140390344003180f810a88a41c4140120b500e1202d2812041c0080107500043c41110390307101f942690200c60761040300361202901a600384204520521080c01000107800c0a0745c1c0c0a01403105036a051004400342c50724880090310140304503510348602d01e8040d44100f500301c107c80510804420b0f1080d06456101c42c0306800350000b00102d0b180d = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 313330602 1250 313329352 313329389
    0x190503090a06090615151101020408060114011106070e01030b04052e0905131205040f090b0409120306050406060e13050405010b0a0b1206010503040503070605060109210507050f0109 80
    0x150300200175541006403144009886d00b80d64800b011200b05000005000092240e400320f4041c0291002c031052200146096400c10f03490b0300030754410f110341340d040061040114001c0841004114002c55403030711101a801c80d9480010141e0750701e503803a01e0046080800b804030302452a0640c0480e50b5007400f5901a025007a504080600042d0b44003521903401d12061180c03c211030180781c41e0852098845a00b03ca0300a141aa42c034000c07845460708041c050744080007240c2c4580c00c44048c1640080c00041c4d00d0300307269078101924812601480c0082c0d5101010b000b582007034420369000d03088070300303040501c015003800095170541c1420784140c40986031004902040001d40041c0c490182c01010303140700c0ca450741e044402c2070b0491550410980803031000b00f0a00d5029008032030055420801651901c0c005464940c040d240140515042104c000c0000032010340c0c00640c00310100c00305145c2000b05000381011464600307190011031080d83e4a000e1120a6a0010100340c111064841a51a001607 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 313331852 1250 313330602 313330613
    0x190e270a03120b0a090e06060a0509011a130b0d0e07260a02090403080a0f060b2b241a040e130f030e0315040b071d031002190503090a0609 61
    0x20f109020354101d900100c005c5404581d54000e5809400c043d0b00725003441d0307584020807120840314826a030300092100014846071252448140c0f1520311410b140c2d180c00011f658200e600141540304520320140441d0041c502c00c4c0c81d000c0c40e241c0120100090004504100c40b4030900c0500b030503c1050112030143d2340355440014410b5404071900101805900d02d454100506200d10484142000b985040842c003081d10f024481c50b03054500200145007031604c9180d464a80c00740d0032018040215085020740e5003842940a540c40c0600c0e41c043e00c650700085041d1018111002c0d8002445d0f02401242042d8540030410030748040340c50104545440c4e888455441c441d819107550044d021a0300f03a00b8603010f0503001103080c3c183e07200580c02c4035800c1200c406107848d050704c141c1d8010f05156014000c94051441902000e4414a1507804144d0fa40c5112000901c0c0524034003a908007a07070049810364003090b0654019890250b03906246245280c0255583d841da4141c0a004144590f510034174014841e = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 313333102 1250 313331852 313331861
    0xd24201b10092f09040302010b09090c031b060306040902120a061a100c030513080f1b060403030903060207080706180506010605070308010311190e270a0312 69
    0xa50324025210341001c800d0201018181c8410143c034407444001615600c00f0300b6007458107809414001040c80c014800c002c01002c0040034000360210b40d00ca21290144e5511035102074024050035004002128603181414100040842610f42204890800320310548405040341d9100000311000a1041030b07510014403400041d510741020392096078000c400b0080c0c25403104003030307403240b098100900000008110301048841d46807000503d407100c0d003800090160014040040c90ba62201c2d10807501e070300704a4a01003190600d501e03140d1150000c003017581c1340070078911244a0290703103080c42c142c00d54401902c80125840010301244d0300285110a004107942035030743c402d9010005208000c0e0380204100d07400c00b41d04050750b03a030280310000a4a10f0046044410203941074071500366a81ca1a100d108c0b000107104007440c0c00000c603101e043d07911040000d110001d810142d19030700d40c50802c01605652400080c21458034202d001214000a1030005080c0c80e00c07540c0f600e00046082c0d501d00a440c05030 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 313334352 1250 313333102 313333147
    0xb101e03230a06050609010e0f03211c090320071a0a021513021201021905040e09030f0f0a0225090f021815090d2420 52
    0x210003440c845505648041c1c61030188810301e00c103002c410703180c00c20071443d407103803900c05800300d038565840324058103146040d145034940040940354031400800c4110b9038084100007081068500140500c0030b80041e009842030541c0189013049084415030b4040c0c540e860395036510524104030a441c07500c0c482c3c108946005082491a241c1055150f4040100756800450221015004001940c1c1e544000681d0051154055550051240c0e180d50240b04826a10028808540d5001c100c0301c1c1c4052000c1d0303080c02102c00651b035a40d54552510102401c0100301a01548144d00b0810101074112500d50540300e49945492045980b0002d841099140008010080507901e074031110303403803400030201c3c03c0340e0444000420a001410074902ea0400b28440c001590640700c042a030411442e0820898a81a28900c0b110a034581912807000031309898410b5130880c0c5102c41030450801c1d40700d01c1042d0858414840a06200c2c5c00c169101d40703088824501c00c144100c2030003280340030070042c0203003007100719 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 313335602 1250 313334352 313334381
    0x1815050c0a052e0c05090d020d0b130b0f070f0503180a080309070614040b1e0403051c03050402030a061107080706060f0501210906060806090705040b101e03 69
    0x440840f000328480c0f5901d0044036020880109040462000c542c0602078018105994aa181c10840000c02c01c0c0c007601a101a6081942703032582c0000070311800c1c001d900600c20084100c1e84030303500d480c14610b003c1d0020b1408400a0044007070210140d00700c0340340501c600f03003410602d0701e0355500c02614020003146c0c29420494800d1203400c01c103019070200203601a05541040e01c880b240c59110580b00142e419032921000b00c0200810402c8450420182ca6508001441c042210401500b42c1007141c0042c0c02c00c0d074058102085152007040f00d4002400504086d007802c4c05140340c1a00003e4654080c00d6014140686800b80e400e0130340c040000310380026500100c4162160402c1c1001e10040c41c09010f0720662510300e49002c0b03915030042c24090f26090f0105c81c0d5007407562150083c00040c04c07903000226202c0d9117609006c540d4000074004280f00b036003003030000c0c40001e1512042200340c80600c1100750080300c22030900e14a455003c0034402080350420b1004504ca0b507a50811001401501c0c4800d00 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 313336852 1250 313335602 313335613
    0x2102010c0809061804060909050c04020a031515081501080a050403140a050c0f210f07020604030602070b0a230c0c010c0903030e180604050916090209011815050c0a05 73
    0x3124400d00110a80c01c04e06445c00c020140d180d00000301101c07406507000e0041e50001c0e2241c1420b10389038008000301d084500d400310760040c001002520f80710710794000c0300c2443c5070300080b901c600e6440481c9a500c11a0710302044504c0e00c8110010700000c2d8054000d10b15151112b0004040c940204041084544000d0b0429035450480d0386c0140980c0000c440c7e400280142c8140c002c900c04002510072800c0300e19003408030009000c10b00d1164030740c0005d04128944005021281c0542c0d0303410083c0006600401c40966500541e00d40203040041c000d06e600c141d9450b0030318041f010b0031112252110580350400d02000740e190003031140000c2c091201001210f600b0007880080050703220b00c0c42000c59100351200403541403420104000034440721103100c103000341507001451510b03084e00010341010b155025220003600030008072060b0741e010b0704040e039480d03000540c103680d959100c0c0d080a4010740761440b108005060807903600007031260207940c01c100700b4045541402ca840a006d401d01c0070380d0050480e803 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 313338102 1250 313336852 313336867
    0xe030c16050906060d061a09040f0b010203030f18030403061d07060909110f130608150310090f05010e0606010219050a0807170a0e1e0901030b0a02130e0103020a2102010c080906 78
    0x1051f81c5c0c0030740e201ca07005a0420400404104070741c01484080c0405030080d50455480306020304045200a000401202c0030255591800d5001d00092000c0d40c014100807c00190300b00858038104c58403050070340710b540301da14108400e075030000696007030343c4500402080c1c04d00c00070204003150060305030102c00b41034002010b280a2800913404021107003140c8440020341d0791003074400040c00300c3c460590b4250b0864021900d0ba01459030280b500d0502c100040c0c1c020007034684546086483e000d010360155804001440030940c4c04015100c1507105210310200c1c0300d203482e6030301e5454240c640303802070400c08081203900c200402d0158260032302c0891081c0342d0b101c0c64070f02001421440e0a4141c14001c4014845407101f0400402a040c41c0c41005401c260311030f440c40e520340e6500d040c0100b0440d2103076400d001020b0340c494081c0c00c01d401810440507044082d411801000703c07960050f401880c4002c0d100f000d0520942c4ea40e524000c0181e0242041c061010007401d05205500c0b80c0649560301100008080 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 313339352 1250 313338102 313338149
    0xc0623010f0602010b1c1527051603020625051902090c030903031303030e030403031e0203040303020622120f171308030a0e010e030c16050906060d06 66
    0x20707401c66a031a402072015110803410f100000300c00d91030815406944007503440c08101c000034246d00f00c0490030000a60500d00c0e140e001401c206107002c60740c8490010f0700f00c500b407200810682c440c91000181010800380b0b182d00003a01c40c41032880280d001c00503030003143d007030000c405130040c0d00b03a0700007003034800d440036401d00840504110101240302d03042120104200b61000c4095070b00c51406500214070716220b601c06062019490320040b020143c840001d010100c900b440a44011440307603c0d061541c00c011422410700381c000594640c01c5500034070041010a034006449500404980f800d034495180e41d0300701031035207034a4280207480003c0100c45110941d61082c00410b600311030390340354541c031540d8490303501c00d0360f10640d00c94444200c000c0300d11000c288090001c540010490000103a0240807240803429034000d40d540762240c0d000810442c11620007071140e600c0c031030100c0310b403072808034100400911280006000702e0300520f4003152040703080150340d04c0f1401070604000380b196140542040e8 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 313340602 1250 313339352 313339379
    0x23060a050a03240207021309020a0302060409020a0e12250509070e1e031b01050d09051f0501121403070c080c0a0609030b18150901050f160c062301 65
    0x10b05010400080391140b10b0000c0c4d100343d802c03003540100032000c4203100707080c500081c080a11060703070300003a80c400000050f541c7d44000d00082000d90405611170701e4041000c1d2003010b2007081c05010b0b101d842c00c0001c0a11001c201000e10301583c41d189449408210303040786d00203455401c20381e0042810410700c81480c1e042182c00748040011038040a04001060200c4034603908c0c07400c03d54140c1d00c0820400c2c4411003141000d40b8015043c50420300b403000c4009040c042d52182401503680c2e40102e02010800c00c501e210b50602100b8402040c002c95141c195000200c10700c110028005070b01000710600030350700610883d0780654000d4002c2c56030307646942d6900d45915130008100d2103598001130024680340240360f00011260480b040d1245640d5802104034010044588a10540500c010300ee11542c0c0d4256407038003800ea040c000092500d420342d0340380401302018060900000701d2002c030403601a8801d030342d10385003a030080e404611500c0780003c0711000b019259582e000f294444001089d075902e1840c1 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 313341852 1250 313340602 313340633
    0x9020f03060f030c01140a02030d02130503071a0f0702210106060e03010c12020c0708030c061005040b030c0d0c1208070506070305090d1b0b011404050105030123060a050a03 76
    0x64824105002504141d90751204c0728409021a0b6107481494a4026800103402c1c51202401642d02d00715101201908030390001d40d034555491000002408942001c00c4004040c12800c125100d0b296114040840e89020f0a0740c8004401c5000514404649410000080103041440c00324031a55420184601803c56401400c0000f6a0b06102400c40e20b41400f1302001804a61507850720b1109011940c80a940240b0842ca600e11a800c000600148104000c0c905034400c103001e0206810054000808550360ba403145100300d0034140c1080d00780d54003150030b40c0802011542d8600c507140b039142c40380d00e15180341c3c011100000e14a403000c061050840040405134131940680e031712680c4102d4150100e5109440105581d0b01c00e21940301410301940c01c0f5113140062240004890720b0175500d190040600f40c000700000c40c174000f02002507040ca402450b024007402c500921100101d08805c4003212044200340201407100030100e806c41d1900310215014250160506006946900f02071821410410 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 313343102 1250 313341852 313341859
    0x100c0c1101230304060b010e0a05241902060901020a0f03050a14091e15010303050a0201110a0c0629010302162102060f060109030f03121a010f0905090a1509020f0306 73
    0x100c1b14850b600c11340e403061740c030403008004010b2913003400140b240c8200d2042c80c444040040240f0880c0103c444405094020309a51a0084040c50300c1e0009082c040c0151001030076a0040c010020f0311508903501d901c3c03107984c0380380c00141645e510b041c560203020b00c00c00428a46030700b0000d00c440c2803000f06d1803208040b81c103030100301c0d907442c0355000c990346007410002c0705200914000144002880f0700b000300302030b91180c0f00100303504468401948903940202c40e50008200c1c1440c6040c10410103010700c1030b01506190688800c3e07d125400c0c07100101c0400007040c1019400520035070070340200079401216075000220395405015188100d5840408001124058481c40000038841001d184840c0d1246506135a403286040c81c598900586d03040c0020120f00b8804442050107452000f84262014100803410500745120340070300142010715203440300f40410a0445051180351181c0700d100303070450458080000d142084171400c00b40e10039290022003015000080c1c1084030142c0340c0207036001d10703002c9 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 313344352 1250 313343102 313343111
    0x1150506030f0c091207060f090b0304031d12070f06030b030604080f0307031b023708071106030a0e190b0402010804021909050405100c0c110123030406 67
    0x220104040d9010840d401e00101e89020000f50280b01000c001d04602200606400041e42c59524070900380641c40d0000d41c0083c100c044850040e0381e10146a00c0184902071505156051a032070081c00011101a00340780d50500c4625000586c803506511900c0d404284281d50655803507031040041c4c01400c1c441c4000007402c01d0411541450040303112401654820324282c070b0030144a203195000d40004180a050650f221091007000980001c046058490f99001d0148170340c02440186c4408a461140c0001e480c84030301100c45211014070440d421130704118035940311580d62a11141e9184840c42aa8200001005020601e40150000c4104200c00e00a480704200801213907608810003040c0501094a004042000f5500411030746403c60300181a5100c1c9916402803507490203020380c07240402c540da034400c02080c004240256081d900c4085401d100b00254400014113100041d14003902c400c0c100e103c640e070380d41c1c0201c501144419007840d0314030303400410007103000d100c0d0011a015201039040 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 313345602 1250 313344352 313344359
    0x12090824100807120c0b1605100c1b08041d0115020c0609090a0603060e030a09120201020a141510080d0201090c140609091812091503090a02120115 65
    0x45031407078030584400400a05a103440c0814003240314541d03d04c15078816018100200e02142c00138020002c1c0721003c0420064600d00745026840c1081d01e40ca1038000301d15000c1842c0e03c107580001c1403004403689103807080521034241084000352090303030b20000d007420000000002c401058060346048031510303d64440c3c03008251006a07110380303085104592001041100000e1441c0070f2414a4211500c034000042240e200c0c1d07510720441d554200912103541c80400c03105c0e1855404069540500288043e08013528490b42c0081c0d51001d0050000b048071640c0d864260001e4802c00015042d4200740c42c0350251340c204904800a0385006000d0580e071401028038000c000e60050041c550300c01d902440e191070f4141b528000d04000290040d00d50391140d01000a00f065599580302036000300391065450701945504403685181054021282000d2082400f0444042d595108804180900000800e0f501d0b503440c41078606002c44040000e510401780719041004100550014211900c00c030b1280b00c0550300d = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 313346852 1250 313345602 313345621
    0xf010204030c05060f091002060a1508030d0905030d05010618150c060f23010e06010f0f05031b07030206040b1f18060302151201150c12090824 63
    0x40e400040c1005500c5141001030f400c10303c0041154480350000340381415410400940403803551413811006030f00032010b2244d00002c51164192007401d82c004ae154480ca4020015100e02a807000c2c1c800d0569920055010721100707004850740c41c01d00040401c11580c440f18050f28154141c0030a083d503600c1c0d50404203c2a20013034130285400c045032200c0410311990f80d1408007070200602c0700f011650303d404407481e44190080450081034507100040c2000d605150b1859625203006040d2810840020a4108815008400c1140e102d0461804954a0f9560702521100760b20600c1071444a050000c0e4490038540d02040050240c2d01c690110030f50b070f80710220702046d03090800d03580b100c00348482e0204005403013a503004030058811519000c07400582e2900081c85802035844001d0b0310b10000503085440101c0700d1041e40c098801e1000d80c1100e1502c10b03000a0400c28606801007a0040984911100034000c040354002015010215441504111625640440706107800800e850b2800f001c12111207 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 313348102 1250 313346852 313346857
    0x30605060f0d02090601050d0e0c041506120207080f0c0d090806090c090405070e0106050d05010603060b070602030a060b0a0207050301060e0129070f03050408060f060a091a030f0a03020f0102 84
    0x200090101e00020b00036001c00111401c007a0426040c45030811802d002c0c51028020000c001c03203802c1c090201003070031b0810701064903000d1101000c0088040020302c0882c0c0c000c602d4420100c00c00400507182d101500c0c100403a0310845100d074929490214244a0f4032000241800020301c15a60324080d403070fa0740d481c00d0350f20b42040d54004401d4000c0c1440d041c003814012100f80d40580103004541c00c40303075140c41910142c9001c3e00600d00080c000248141319800364000c1a004050524041020034640300b05070a5070701461200800947e000400701e480c071481a00003601030500404825030b0340861040180d0364000074803c6600070750800000251451408101a040324078180282d0101c80c420002110300040441810800b80c80c01d008641c00f240060311000d01d01c502c40e4550079038807420800103501c3d2810040800350f40c03e5580f4104030700354030341c00da48038200c070305100c404502c00000034907400c03008102d84955501440b5090b2511002032001440740040ca0190b02034030050381034100510700382d1 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 313349352 1250 313348102 313348129
    0x80c0d2316153e010b0d03050a1d0a0b0f07060f05060a08030702060a110a05060f04230c060f040e0a0b04060e07050304110d050102030a05070f030b0108040b0c040312020703060506 79
    0x30290f0841201c00341c000c00b58803618203590000010311100c21000207124246000303010f0340042d07400300700c0d92000d541103504c843c0545483c842241c641004800082e046145038000c4106c1d03200d000c998034901d0159001920f00c8594040000d101501811400030001c01e4111440c604c0340000c071900058400d03000c82294045900074050b0352402450800039108040200003410052052080b0440030440034400c00e4015194a107043c00d880c106414071800c0401d400d4032895501d03400030345425242c50002520080040b0644086841c2c1502c06800c02070380c01607a01ca50034921040041007008a195800300b440e00034100c0e4104a1281c48403166202201d0445100021510030004640410420b0451440403100100f811302200d607981c0d00c4a09a1704142c43e016a11602e41090040860700040810449005071504001015080000030440030000d080a404900048003048200010b50211000342d500019201c0d014190000c00a41c2d500240c442654810b2402000c5003031407501d0070a04004 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 313350602 1250 313349352 313349417
    0xc01050405210318120c031c110a0c03020c03010c0e1801030305030a09170708070201080108160306050c1e03070f0c110105030702010902030610080c0d231615 70
    0x440d6251450105100f1381c94030800000d115140051030407145010040c100010b00d54003842d11995107961001c5180145034062800b1400d00c8190020341e030140703043d694500d403140b0300000e08608604040c3c3c104940400707501c0c1c00d9400c2071507007146030b90445242d080d500e0095401ca00440b4510f5540d40d4005000c0c040100000c0c0100701151800301c050300050240c0f4061700191851161500c4100100c0e4840d22044842c1c520100c1c80d041950303013180c5810300510003407007c0e129500849003400040c40d81404001d0403242e5072004100e182d03180c202500c8584c1e43c40a44083d5441c90504800312980007141c0318000100d04800503082103103e5401501c0c0154032808110948511900558064200500b81c0c0119035a40c000790002d0717a0100175046c0201140e0488840181c184080542040340c44818540214509880c80c0300090720601400c001c5190f11138040c0c0c042400d080c0b007d003880c10140c0100f040b24490800803c3d80d242ca07000094804103245c82e007003104a000d00d2400551007440542c40036 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 313351852 1250 313350602 313350607
    0x30f050c1309142d100306050a09082205060a111b060d02090402090d060c120e0303070e12070902091c11060a12051e0603060f0103030e13020c0105040521 68
    0x1013580320886140c500f1045540014111001d011898004043c2142d040386840040401001801010310a040d0084052001480810038a0b1541a01da1061118081d20340f510780c108091409100d95092019010091495545980c405001031003100c1c2e040001215001c0c0c81002d9144a003582d4240c588010301611060400d5190403192000b50088500c0b10381180c1c0030040440165600c6440800706403050000203825440b24800400140c89a440d041540380703802d500306000e403000000e40b584a600e0b031808015141040300401c645c10705900d161507252041041c040752194040c1c01070304d610f002c2543c004990700740024000d24880c001090241c840341c14000c14810b203081c108020040302526051100850b14455a100100d0744101c1e4072009464020039507040c46501c0007155a0048002c500030141ea04150f0418258001c06210007000d0214184055070582c4036503080003210001518215181c40e402e1800c14007a1400725401c4900e8003902042041d110201c1513405810250180c00f00e0 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 313353102 1250 313351852 313351861
    0x201271206020316232503180f03200a080a0f0501051e2e09051603050f010e07030f0c020c0a050108090c04020306040906060807030c080105160f030f050c130914 71
    0x24410303131041c016580c0c440450004451007140c144000b06c400341c442e6542d0040000070340c03491061019a03801c02048402c20040800c0840e10522030350064101c6204014207100800e000240030684a5008000034091003005400b4062084904100180a44001d0155a58452172104001b600700c2e03a00520702441c50100391700394480b110202812844000d8003105191348100b810103030000307610443d48592100100244030180440098103001b5600381070010b801d0090510b485814140225103500105000080d10603101e0342041c10340141c00041040b083d1103084000352201c15810039a409862720010000c1c955200ba46103a125543e402e0151240070441c10410019500c042c0100c2d50103030315000c00d40045401d5209500042010070014070342c2610310310380340411504660011281e40d25140400c800040f59482084102d00146443c0b40270241104c000e40c0103101c0072032079417425883d01e0308110002201200801c1c405240c080009240342e41c3c1c0503181c09442d04d4450b0010030600c0c03e004107 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 313354352 1250 313353102 313353167
    0x306060509071209050109050f10060b0f070201080703110f030103021008090c0d02010504080708030a020609011a1302070c0b090f032109030a080c070f050306040201271206020316 79
    0xd0245210b2000481c0d1201261150b6103060000c408500d010307004602b0910444100e4401c441c000c05e407201c0700904080094050650742c0c0641c8002131305000508001445041c400d0b44002690b540240f0020b454048009484d051a002400101c1c0500707103a5041203581030085000c1881100c041004201262192083c0034141c0c00400c0102e0500106010104c0c44050600a50b000340c81044015521641003080081c0750840c007515044460345820b1540c240b40b010901000411303d0182d070b455280100b01c03001c5031300174805c5890141c81100b40520100310b1190060003422030b824110b40c7c540308420000c0401d078540c140e0001030064440c0035078000c5a01c0d402600a0085220000d0948011034019204c002e8698040c01583c109508032a60034020158031b5090080604026070080c075851805a0010700319500c00c075900b109010103881c0e5000741c0300c149104c540c0038205000448445114500d000c0c8082d40080d94074403a404100d8221038400c0e849080c01d20f129600040b00780560315402c4146 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 313355602 1250 313354352 313354361
    0x5040b130f020903060a09030f090b1905091003050a05060a0e0103021c050604111801320a060206040611090603010b03131208040302060705090a06050c0c1903060605090712 76
    0x3915107540920100103580e9090218a108128000010071040b10b18a0001e00440740d1000a43c14400000b5050040b00300246c142d0316403081c0c4c210348000000301d072641902c0500030a040c0300d0b400b001e4409090f20f132661680000c1e00600300d03121305120035100c4601f0082c3d404183d0064000c103044050041025140074207040d00f00c030180e504603070700212050304c8036410500d040390305550281c081c904030b05050402520711001c81500b01001241c6505095100f0141c01c0d8801e0040c41c0d0340c4101c80c02c5c4444040c1d40691600b050310040c20020782c00c3e41c0f0135004e5103526040701d017a100b1034a4020140481c01c1e01c00e003101d4800b41e0003885103165038203245c0c1d2400281c00c081c0580c0304e03401c541c01c484e9001415086009042044984440116207007a28000307103858001130483c1c0c01c00c481030110304043d4a41103500303410ba5149003400c60712000700c186e0007450104845081540301000300c0140c1c0c02025094800e000342c90080e101070195030b032201c0a0050317084055038054009010701400c13010003d55a0701c0b = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 313356852 1250 313355602 313355621
    0x50906032e0806130c12050c0916020105010b091c110d030e030f0c030c0d061b0f021e030a030905010905070e15040b060f0c031c020403060605040b13 66
    0x40380a00d9000381c40d54907a20400109141c00e4140c540e11050246210820025901036041e00001440000540d521100c1c03407650320412039595103444802081000030300c0301c40d1421001500015036494240d8844030300b100c1600b43c020140d46403600100392210b07200d044441901d0042c00b80100800e25044100040d4070141007910a44035580d00e0101d10341e641d104e02d07040355000313540d50b6014007400c804241c14841c01e1200c0380501c0c3d00042c1101c2e2281c0300801e040302c42c0e580448484021061605219005e40702d04400c0394401a0721170b24003641190800e803030341c1b000e00b40b56003195644048448074410b0310162a195000075407043c4000b150300c600c0394001d810034505c41d000215905145a41c0d180c0b4040c1e540d00591001c0014408100c0034450100c245000c5910449042c06110180c50101384940300300201404070705800107600007551010821218560103005503110010032350042c51000350403500040315440c2c20030038001a186414007684003d104010100280e000645101070020001b144 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 313358102 1250 313356852 313356871
    0x250b030426160b0609070e0d15020d0608160b120622020a0c0201080903070b04060504030c14070e0c09030303070c020a09061e05030f0a120c080a03140703050705090603 74
    0x1200b041040d840d00a401401d0788103003030a01d07040c00d003079042140042004240b41c0c01c0103003c1341c1201301070b601c24119901c0c0c01d40200c4510b0700002c4100c11000070748151800c10b040ca40c100000018001d5000a00f25140e680c00445101c0b841d480704c800c2002c0e44110220311040d40880e40c0030492034582080c00d144421031062202c2014111f800141d0280d800c901150408101d44c0c07840082503582042125038044e6011010314070340805036546013080f04000d003018007a203507694005402c0502a629030340d51250401c1303100740500044a000780d40c2c1d11844c0680b412550000303010843c4101c20100362065100c0c01800f8506580c0c0f18030007229140c4400106a80c4085141000200f011451140301c0240640c1c10380000c1940c5985150100c400b03584c1e01c620300941c08000a130004041c04210401241d80c0701a6058484007683c5080318982d0310300304082c21807040013502c84041038155010000760085a06c6000256581c15015400c440b4116499404110100001c480c2860402d00441d485000719 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 313359352 1250 313358102 313358107
    0xc050a1d04050406020a080c0c030412020a08031c0e0705310e0a1106070f080304060b04050106050712230a11060103060e100209010507080d0e250b030426 68
    0xc0c0024042d0784060b00e0540318a940040c0840e4216402001c0941c042041406240780109001040741c1c2c031b1082d0311074600110700102c1b00310115070702d00944900424142d0201c0c1e407259544200004c0140703203210240d0000c1d18103026040396020210303c02003281c0c0d00400015080f130000360441003010020546025940002c610a83d03104103a100c0d600c0c40220510081c00d50041e40d10f0302c4004800c0000d9030910680d414840d52001414080d00d003c03441c3c0d030052125880c1d854510f010000307404121001503210b414403002180701c80e0311101921200b4042d00045041e88281d241c140d80f4600070904060107408030203c00c2400101c0eaa008025885c014038041c00b8000c68a003095003080000e8004441143d200c05120806081c00c002901c0b80e219480402c51604603042c3c00a0168031075808020406407000c02d40d02107094682d070200fa000310b940400c0d00c20b947e508080d10b1109200203144181c0701c003800d40000c0341c203891420550344229071201210319180350402807000340e003000070001d01503034404 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 313360602 1250 313359352 313359407
    0x1090f0b09040e0a0b01031101090501080f06040b03070f0e06090c0324060403140c030d050c0a02130b0d030327021507110d050109120e10080408090604080606040e010c050a 76
    0x591703200318000d50007105801e00500b00c020004003031720650b80c083c6040110700070038410000390020070b082c0c100348101d800240d2200c8610200341421810342c080c00144007000400a046115141e00521491088850134150360303840c24540080c1c0410f840c1c880c031303401c8034042c1300d403501c2c010403a074007580c80000303048604140d904e5850300d070007280c3c1c200f190b219600070b843d02081380d08040140740080d01150401d1800c000c0e40303440c00c580d95041100043d2103010200c01c541c0045409038000301d50100050000303041003029081c00780c040c00b040f40c44141140007502c10f4000f48400008041d14059009280344145014112004c00b10b0f0440a010344110805140c00c6216503511068481070b1445440041030907135083c00c000c4401c1c59000d00c0e0400780041d0700c54191503560346105480c0045c040e810806155200d6051210846c05003e1806412103000a004510f030700c00000c140d4030425040301c05102c810720004400d400d039000e5001c1880811030901411100c18024014004c4c541ca01d500101602d039907 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 313361852 1250 313360602 313360613
    0x7030209031f0c0203280306090c2607021221010810050604140403110f030406091410050301030b040305070506070e01030507020a080f1305130b01090f0b09040e0a 72
    0x3051409140007031820b04800051071901601040700c41c540091420040c0d00b0b0b10070046548420101c8065081c20352050804074020303032000000d403504202c100a0079804c90006030a50f4140d42c20200c00000c5040c40003550004000001e2080d480760b400b8010240442103500c8054200586401ca0512400008081191a60000c1e8028207040c0b00800d8a0708070740290604032107001d01064050f80c100840d00010744a0060900c1e00550325244c08405507010401d0f19003001c2c100c414600d4980000140011116485104201074594045850441c044803d00b08540310403183d1340c9001244091004001049100c3c0072281d0242c06810240d21f0103085940d1103040440072500d20002c40c14010030034085513030520615600c49142d0006100062a85d101d043c80350041e16003e01040300009141c032002c12000c03078280d00400001c0e01c410404064095014050080901c5450010360415400501003400b00660700803601a00d645a1408500b60300380000f804441c400b5807168460441420f00050 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 313363102 1250 313361852 313361863
    0x1e01110c06010302120601080c0603130219060f020304050a050402090636010c0201080f09010e0604050a030e01020303011d100b030a060e18101823010606050a170703020903 76
    0x40c20395000d0100d0b503045204210980401004000c9551720800051240c6000042c50314041101206c08a44a81d0f81c04020340340e600032624003e4200e00d41c00741d912403400e4499503020645145496000d050018104221790780d0207a4481c095015122400c02c002038181a4001d142545010b04160b14141406080072103c5000d120000d003002c296030142181c0441c0d03103680c000e4480d4246001d90040b502500000d06c1d0003000340c002030343c0c00260004500103070025407000011005900580f0058500343c2030968840030b81c0c25040d4003260b084190304450f90310100c02c881c185c41641881c0e520301028150f070500841c80080003059800c031283d4010904078011000303180b003020405004105607060800071040c002c6d0142540d5042c000c41000e02200440200343d9682d01202d41c03100084201a2101010200401d441d000d0030002a140225002c1e020b00258107400c4030b40300c0002d029107a65040c04580f2751250020580000301e4002105040300c84800c09a17800c00c14915015003440b02d03440009091a = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 313364352 1250 313363102 313363117
    0x5120310030c090902010c0605090102250212010c05030109050408090909160f26010b0907091d06060a0503060d0503190e0d0503030c03040614011401110f1e0111 71
    0x45003458080080100c4041003602030310803003005000c404125030010300025140342e030081000c1e0315840050030a203000d505031000906510307113859601501480421f8607651071070b41a0700a14000c040407401040500400b01030001954a441c603503860281d16030700811000c3c0048550b14400c1107845141e940d242c05107402501000d01800000700c55004010750b4440e2680301c1c5001091980c801c0006405170500704030424448484010404590090a8018041d2040c0c0720303440320120703090100b07003540195050b095580342110b400c000c0800001159071300324211981c41c0c0c0700a040001002c050b10075400345400c514040e0000724040701907980c55045820003d034044110080781d01c0001c855900c1180102140000d40e6800e02c000706944400b03440f480000c141c16800c54000000c28200b0071580e000c3e54086c51625517814881d612602400d610980120440e40007611400e041e8030301500100d10702c1690382080004107801141910042c100500f401e2400c1e800e5541c480b41881981040d50003401e01 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 313365602 1250 313364352 313364371
    0x11b0f0507032108090717030c010207060204081902060a030207061b050a020c1c03050306010c0b0408120a020306090109050c0912030409150602070509060a03050a050a0201031107020d0b04051203 86
    0x224164003d806801840f42c0214020098110140092050081025415911400c8500200d041501d00e0386e450b522501c000c4103800d620001e88041406031990113081561808070030345550407030282141d002035517001030103540a80c040010806060080c0d004021892103220081004401184490303402c4044002c000c0c045000003844000c12a41844105030026040b641075032846150701c3d40d100b82d803c4c082c00090034407a0000110f0011f0303003d102200074495210300c0d00b405600e040d150540c0c40740c028420103a200d444100110314032110500035a07110714005001c000e4260310b40030989018040103840040944e90400c01c001090f00e452100c191a02c4111005660f5a441c042c0d40034211a40708003001014264060148822580854030320f0441380304403809070203500c8600c00500c07004c1d0342d580014414410307045800c08000c001304400d07845c24003d8804010400042c41401e1040c46100c0000b5072240032000c02c0c4000480400750250000c0c0171707500321041c440b00c8041105240c0d0023529503852 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 313366852 1250 313365602 313365623
    0x9020301020d0c030f0606090b0f12041a0618061011030f03060a060f1d0103110a0f12020f090d06020f0a09080705010201060f14030a080d0c080f0105011b0f050703 72
    0x4030350384c050003600035a5100c05420002e49141c03d00007007441c8030501030440c409000090707406400d200e00c020f0310201c00300b071103030108182041d207804441c58041104802e4916002e000051843c9407401c01d00d04841380407128210640c1e2040100300b40c40040c400040c0c2800503015008078000000c002074a59812040e01450303603030400d0030030081d84c5591540300b1010440b0440007400103c1d84090a84010305150300c04105588542c0010317005030101c25604454001301180ca142c20540c8154940d2641881c1e850704400340c0b1040d4000001c2e441070b000c6140241d00d042104180b10f0906101d510b419a009000050504002400b100c0060380311400c240002640000c00b07106400050180c0c0c0d000384003d000030440c0520740504c3c90880107044c070542070211a00324601c25240c800380f060602841d0312030000d540c2d900e680d1400f074001300a94003400b80015500c07000511500103500710207041c0c0e40142c4403000c0c0201c0f01c047d03920721385031050022216000c01e40070b03a03000107108020b1440612310a030344008 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 313368102 1250 313366852 313366871
    0x329071d0301050c090108131221060506041a041205060103050d0e1008090c10020f071a0306040c170709050114030f0f07020a0c18110c1002030a09020301020d 70
    0x66a0340d00021146200ea4034040601030881d2001080b101c121100b828112a16501c3c0100c00b880c4c4c51502101605078403141c40101d43c41c641c8003a002820010200c0c03ca0b01106c0000c10b42011600d1500405401030b070b00b00f0052084d419000810003203000c2c0b40c0c404d18903084d01d0f006131001642a03034508440542c0400014003c202d001d0042903079070300d07191414020165003400041c50740074041c0e00e44030a01580303c01203008814103000a2540300301c0a40801d4044000c050300075554079402c1c241a5407400f1b00301d000310f006004684944c942e04209040f00b070a46d101d0404120085c40503c0d4a9403d000c081c00754020f5189050410611400c2e050321b40509d11858a40054810944280d401e4007a013820010070521000d80c0325442e82104409210394040e130b03107483d02641b400c802a0009031000354040340000710070a00c81720011a88035400d0f000d0000c51a5080410308a00a50112803030541102080d00d001d2600e55010f9940800d00300e40c0420b2800e05078001c2401ca07440801441640c58641c010807 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 313369352 1250 313368102 313368137
    0x51005150706060b1204060b0a050607050c03010507020a080d0507030b03070608010806072105040201112506050c06010e09010219030515030c0109060815030706080f09060c04032907 80
    0x20311010903510315114618032081c1c0c1411001b040145810381e1040c0c00c04030342c0c40e0082c10601428000d00020768404042c03d03e1039841c0350038120540719600b0500040c030110320100e03007003400c90b034080002410550f103048090f002d05402045081090391355001c850b000c1c1d5040040d00024005615108110750610412a06184009100c03e060000d02044240c01d8000d041c83c0350038010304088001403e440d20720049600c0703038040e40e400c4810721070503080f0a038191009101030006aa100091a2001e66846094859003d1400324810a40040c03004001106103d80d0050340a0403c2c0001440e0224001d01034501c80000d041610010356103500300b0030000001c1072403d491407000c43c02050740d50015000240710100c40d010302d008000301d000c080b40442924040c00301402074002d00b40c0c1c00190711902c008054040c1226003820944c110700114226000c045681402000710150051603d401d60729a09403040103201440200b103600000d80c0030b42ea05503800140621115a980310503640c0e0311101 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 313370602 1250 313369352 313369361
    0x2a12070605090615190f0f052d0904140105100e0703060308090f061e070314040819021306060201060f0503071202041806110703080106030509060406051005150706 72
    0x116102c0e80d01210602c90b01a440075000d004c1c5160481c0c260001301030a20548140203010707441070b00b80c9040c40c0710104210b2004c04c013a0b01a60401d44010340c14100d03002e55580110035411151040315100d03002d0800c1824100c902c80ea1082c007444080030300b81038180d41903003128400c583c9a04060020322090120440b506041d98020110345014405c1d1411a1601a194440c0f0380496200d813040c4030b00b0080e5074803000103070f410401c050386071140f81c8014005640b00b030754041c0070202e0000c0d00d40100c08681401034010340d401d5605503030003032021070550396183c4207200030b00e40282d1f40100c08070f02440d40e16165024144c081d000301c0d0b002150086c07803d46400760b0b01c4004d0704111710940220707000780001140d88608000443e01200d020404c054400b6403040038008014001d0581030526040e12000c2c6402c030010141c2900c00d036125030140e13903900c0049080b503d0035682c080d210b4221102240100d80705400c42030304000c0070008509043e59403000141102054240c1c0842d501d40171541400380a0a40714 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 313371852 1250 313370602 313370611
    0x170c0a120f02060f24120a0308070804120e0d080a03090b07030911060904110403050703022704150b0a0305070306050106080c0f0d11070605090d0207050102032a12070605 75
    0x3401941400354400d08407660003400d103501004403062540c501c0d01000200d072200f040c041c25a0003800311b50281140c03940100e410076404180b17000081440c80317209602e081c1c07090f50811180150038018120840300b903081008200d83c80060f20031400c000c112148010030301c3d844140c40c001010100c07442c0c50700110400804000906245c0003c20001c02d10321503041c0c100d41c130110380455613843d06030b00290050490308031013001102c020802000304000094240c003600e008580c5001740880314120042d802c0c5c1c0c4440c20b0b04000001c4400300e03000581c40e02080705910f02d1820003094121145020a411200685c0150380d158080b140810030300c91035120321805030829240c80200d0b80303080041740c8541d00c91042e100740c5d58080050000f00c00405c075804440c2c14031142c201c1a6075801c0509182c2c001d000301b901e5100c0f0310300540b12100324043c0005040c104540042c1c010318201100500c2c030362810030840410203034880c0200713012140d505041c0984c0e184805403e4001c1d13160105821f1000441b4001070 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 313373102 1250 313371852 313371857
    0x6061203090d0204051009050c0d06090204060c0305072409031b030e090907091107060b10090603020f0409060603052202030705060315030601030501020406030e0712170c0a120f 78
    0x5020054894030445219503405490104194a1ba07049651080030b185c3d00c18500a490700b014040022803c4009203840c10303c00e002440910303210051a803c1b4466889140c000ca030003a0711810000303004601500c00103004a41c0b8111681c0360041c0300f00b90510341c01c0040d0001c0c0d40c5074802c0c1c0c200f54000c40e04115020700c199039220394604070742d00581408104c004442c41000340e00300048a0741d00800c50740c00a02090303c01408001d004000e140115040388004840329070806c800380b20b45051401900d40803103010b56400200515014040d0020750001000310210b160030000400d401101d405400b00815080c2d80024603807814a910311000500d0383c410300e0384172400c40403060242c0e034002409421f4405c116101d6940307840b0300c144c41c02800d6040140d0b68050060600000c00d12006501400031604aa2024480c170140200e415442e150b441c020040050b03200704012010520f80b003407100341007407400303c114609081d60854902d40324070710204a4000da102c68000d142c2950014581d0301250460 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 313374352 1250 313373102 313373107
    0x909050c07030806150c010c09062606120a20030a0305040513090f1104060902091e0103020403080f040306061d070c0507050a0909061104031509060f0e06061203 71
    0x80a034462880740900c09010001600003003140341d80d0f040c20300c0e100710040c100355558502d500e807100c40c041c1101080800c0451100c0d480001e03000d000d0030801c0800501c040e46120759214010a0040040010f085160428144240f840312048100f211041607405460944e050b465101112a03c103030807041c0d264001d804c5292840700198201c016141612402c443e4440e58030b101a601c1b0b40180343c00f580140001050043c40782c144040000d200f001c504040d5024442036458610340700a0748603040ca40c0c0c0d0403280468800009000359801150300200526001d482e040c1d5986444100303800011003c800b18000003070030010407047d80309240040003400c900e02c0100d05031088540c044200100a00c2c180403200528904100083c0300200103440c0081071581b443e9120150440148a1a00c003100c0952510702d07083c0c1c034030740e031942a42d0403a0751041050501651204441d800b40084020484801d600c44102840d0301103540692440c920200008001a241090400104420f122050b485d260000c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 313375602 1250 313374352 313374361
    0x50304170a1505041104020409020304230c0f18070503160801140f13051509060307050d03210501060c0308060108062107090c03050907060504050102150c0c0d0906090905 75
    0x190340c89021094050b900000d190f642c500f0a200503914002042d6481840001c011403241d10545c080c0d401540500000b0030010410361060100118800000c9170707035030082285001d90724044020b0065110701414000c00000302c05410082c1050503a180f4020480110400c400702c1096188210681040e160203411035251000c00e8640428029039640191022100e1031403d44038200d4803c42e0f0070a1903001c00440c81c009622842c03902408000358842c0030083c012a149240008881c03044e0794000340122060303174050b60282c54444030030511119940c07140500d80b0503a040ba120310b500801583e21800030340216880c0041403d10700600c9941440004030500009072150401c0091350240c20340700030040b4403024021807800c50382d0f43c424180c3c1801c104800e144d080d4150070240c060090300041312102c85e250303c400c1c0c4940c041c0d40503c5006a000410710640aa080c0c110a0b4014a0881100e1b28041d80d0150030790810300b403290404042184072404202050340169050010000503808002a081 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 313376852 1250 313375602 313375613
    0x604120c0804090509010e060f0105040b041b080405071502030901030c05031314010603020a170c1f18030821010f08030403060b010e090f04061802240f07050304170a 73
    0x19a006255400d513803900029038081c02503210343d081c170100104507041490882c10603040520300740110ba000d10308107502e21805003080e001d01070481c1e0441c1e032103460300740460070b00300c0b000300008000396401d20803400009002c100b95502040c64003010390182d0b6030399045a00140654891130300c000d04100003041080404403c00b020040d80f00c1d413141c010303030448018821035405000507800103503024404032000100c1d010881c0d040d040b404401c10039510310b4601d0300d0070085180f0b01061000804081d1410046a0500c01c24804002c0341661903625a03440e00c940710f007400d58101c412007002c0101d40c2c1490145003900700c00101e0040034110172804100341825061500c0e4001c07848001c003134948170300201800d07a0003195050b902c140d000c0c0c582c505625000848400450080c1d0f0281c0c1c07980e16020b0030b0032400c501940300211070741e0054001004c01446071203400d81c880130500041000e03002402805c0c00319210302c1c014003115009100941d1958105074410810101d2980d114200394400356034200004d9 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 313378102 1250 313376852 313376857
    0x10506011d12030c0708060604060e01061d0a090c0503091b0315040c0801050705190206270c0312070302060f2e080328080c03150103110307020604120c08 68
    0x1405568420841009444983c510301500b040c0d00028040c0305004078001030000b500f0303441004102c4040c0710480c0d50f003401f014070303113402c0c001c81c4000340d81c4104c03005403d040000c21140000740948038821890369012040111100268150002003000090000b01c440821500400b40200b804001480c01031200180c3d40b00384500491072010311050004050000a1003500000c040b500001d02c518681020020000d0340042644407146000d118481035040c40001d9140c41151414600c01104150210440050400f401d075a4114454000303806640d0320709006901000c1d03000d522944d190105841c001e420944010720340d2180280d82c204103d816260203d580140002d552000552503a940801c00380c0c0c2c5c0000d80081c0d5483c800000c500748102c010034000c0901740010b021000d03107030b121060101c84141040c0c0380000c400005002180b68003030b92410901480405040028510318a4014580aa0011030f8041c0c05078000c1400c1001f400179410013983e104489103003131400180e5a03901c504490 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 313379352 1250 313378102 313378157
    0xf03061501020c122119050714010f1b0201050405030d0510080d0f03050a09020307031b09050c070507060f08070305060d080c0f100c0504090506011b05060103020301050601 76
    0x51403900c4006030740d00030b0201c09019070018128000111a0f41034045ea140003050241c400c0000040c00001106201810740d0f911450803140c400c1200c0304540115025000030005403107104000d561000d21410074414041550b0601002040301444640410340c1c010301000f50f002036905000402000900200840740000746070540000d680c3c4801c000d04107101041c2d0009081c2c0d1083e0401902d8403900b004540d1859a031643c0d00303004940c1c0b00f480c5001502c10042c0000d40641c400d00007800040e00b51607050300515104500c102c10700d40c2e02c3e41c0032415a030091b6202a4140780000c1c5e0801440002c1c81010050680760801c4041d51582c1c0034018550304008180350101542c0e04082480e60b60341a007581141c942100041e0349030840400419140d0385681c1000c0039a200c0ca149500141c51217010f022142c5407213407291414079103002c0f03140003e000005d0161b41080000801c12003002003200781c4081340d90088008103003079819031040c10700711030005d000c40307043c408242c168140d03042812400c25482d = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 313380602 1250 313379352 313379371
    0x7030e0d0e0d1a0901090510140a09080f0f0c0d0e1806061611040b1f11012703030b1503040213090206030a0b15040f0b0307140a090509060f0306 64
    0xc2c210b09060520250b03403c0c4421000d507004680901001190540086240e1b6001d1020307206c1844040c030390319044807001c207180307419141c9280010394907448a500000803d4010b03080503240c00c043c040401410f50002a041846000101d00507551000c1008651801589810020301e19450400061040106510794a4400455030700040060b101c1d1415244a02e080f51208055a0498946099012a40c6004500039071410320a58905c3c60410800317401e141d83d07060019072041d44100304a40600401002800310b42d200c1c80c4050b0f0f6602d401132101c2950200d42d01d40090b00da480c0c80c000b82235400e90540c1c0f521801c08600840031038542c40c030489401c10381c1140c0341c0e42000b4020320002e02410310100061344c80721000c800c209544045400214040307908850b11351034104200ea0f00003040c05540940c0381e142034100c030f051006000c5000210b801240c0c50a0003900c12103004487d00c8194450810440019030141040005003000c0000360340100b42142e00f55044085400865515000140744000 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 313381852 1250 313380602 313380619
    0xf010b03071707080106030c1d01140f0d0506010e10080303091b010e09090f01230103022701150f020a0510021608031e070f021903031e0507030e0d0e 66
    0x205010001c43c402400200000d200140e0340c1d04015007041854441c0f082320390304d011003d8800c2d0000d400d826069403031210310030100601c40410321111000010083d82c1005100d101d80d000316004120690080c940410600c0c001c0c54405030400d04d51901f0b60116059074824818040c88960201c0c2c50361811460080442c8116a0800100e0b002c1844110441e00507006005000101c140403a014400c50440e4009008410071070040111030080c44000b107001705103500041c030051030090010603400b202039080314104207082c40003015104080e801000c070340550070310b10340d010742c1c010404040501c514000740c59203100c242c840c582c0b1090115005035400d80d0008001c900d5109103040080074940150501d501c034a02480c02049540c4610301c12000c030644131001840a500c240190035500e4050b40c041c0100e03d0307180d030704008005100c4100304c0c00d040e240c40d000b40c840e6805100380108400d52810201d000d090102003d800c48801020780c03450742c0c002c10b440350340c43c0d0707003045034200d142000791003009 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 313383102 1250 313381852 313381889
    0xb0304031215171f0b03010e10051b03010501051207022e15030807030804030516060b0f0406061b050c0402070503031b041404020904060807080a050f010b0307 70
    0x360790101540001d900540b80451908181c0d150110600980302c085100d1002c40e044065600e07941c42c0300c80b180d8000d410190541c07841044480e040080d030b00a0260020400b1000c95800c541414161b1010f41c1035550307100708100c070502940815041d16240d141c101481c55040c1400217203680708800040c1c1030b2004040200c1e01841c0b0801c560010380141c52002042c40c244103440351954843c00d02c05e03079822401d00040b89254142a00084101caa0000704103282c0001d0b80e50a0382c0c80b01e0010b0007a400c5c84014400001100f00001c001000c4e2845490000f80d03080403c0c04015201d4170000010307001b00e250100600125030002c03100083c404080754024008940c03440d00c2c07894840e050584c1c40c2c1080c00032075854100640000034500030032541c0c002c031000c202d81c00d44040c0c150140c0d100d00002040c2180f0303500600d0a00c0d0303004000c6e117040030344003041c41901c032a6080d19254207584820702e503a00404070602480424071a041124112100901150783c14400181d0f40c2d00d00750080a6020014104a1 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 313384352 1250 313383102 313383107
    0xa050c0a2f0627010606020705190e0c040612050702030d09020d050a03020102120114031011130612110c070b0906040e010f03140105090a06020309150f0a06050108010b040b030403 79
    0x1c0d8900302908048545038504600c84020109a600304403441d00032800201d10a110180030382001d07251a83c0c0146281441c19081020741a100c64000c11018545800420080000304049100700c0343c00c00b907280d81e10300e00f0340018410a03449020b000f00c603291200744120694080201c0e00950040003010a804134140005a410402044018000d00c02d03a9859401c254064010307103601103d40201c00c0709a030380c83d10010554182e00740c606602d134000c0c0035002407603050b65010312408440030039020b040140700303248806d100c0c03c03e80080012a00380440012509000d0052224034103800c00e20314204a1103448543d0740c1d5125004062008402050150503519402c042c0c40041c14201040740c982d50b5500d2440301c0c4a441400155000018516504500541405242d010720000e10003400e14802c80c0d1242c4c0001e41000d0f0130440240070344110760740481045806540180552000d03c002428201c02d201700b1a125588914140144030004010340c10007802543e007218005601c00d0340d03039030b42c500c2d08 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 313385602 1250 313384352 313384427
    0x31d01151701020f0d06050316030b0106140d240f2303011e060501020d08070f0804031806121a010503040602030c071a1803040b090607080d140a050c0a 67
    0xc0382c03001800445c0001100080f50400b40843e2010b0b01910520175000c0c0d4942c41e01401c50002800c11400000100040d900c2844d151a6804001d402c150400c240c202d0594240c400800400c0d03044002c040c0d2426003107aa00780000c0c01444010003000310700e490185203004c05078230b4506104841800c50222140c51b2000e402100d1605500058030040494120390301c3c0050841e4041d903130051254a41072111140941c4400d4000c3c001ca440301d400d160301c44001181c0e01d1000038801c50402c0b44040d5100740c1c2c0c4004401d400043c00160326000d1031142480d81e0101105c450b288100e03003c062078a440c12160340c000d030889802c01d411401c050f80d60340e20541a040ca80c8038000000b0400000c0001403a8080205d8950a0007030440000380000d015000266039981d0256020303503103810501300450050341c80c0500052502600c214207050400a010055004544170350301c51107088400b1504000310002d40340714a5902000c0288041c0c10500103020041144412148002c0b001e018940800b0810307190a15 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 313386852 1250 313385602 313385617
    0x602031e04140f030324130e210901081303110d030f0b0915060a0c080a0903020109090e0606060c2b020f0109020603062b03031d0115170102 62
    0x202811800c1c81c0c41c1403082c40800029a14041c0141140c88586080120889006410710b440f003543c07001040c60405580d030381d642071207a88003004182a44030002035000358646808410040c200a4554401d018160750f8180540800301d00704200440060fa007011346542c000c40420f41c400700c803a4092030141c440c8161504032a4040c402c5501003683c90744e250300700c0405940881000d000400c1c1c3c20050204100e8280e422032449401c480c107400281c10610050403145400e89800c2d041e40c13200752985045a4000010000003d035a100144155600008001c000f452100c00c20083c040c10b810707059032100000303890309102d03020000301c3c00e51294082141a500318214081022072903c41c68041500d00360b40354400000d07000d0400402240d40c0b041c407c002d15950060f0001c0e2560b580d01c8104038401d032040c1ccc1225103001e409080410046d20440c0011000c40c4241c4000038202e204601060003001543c0800b46e032a81010400429500c0d80029201126500c2d140310380f280402030030803400385c0105803 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 313388102 1250 313386852 313386901
    0x3120c031e0403021005070b160210060e0601260c070303060305030a02100608070302060d05060103140708060922060e0102040b0a0513050603010b0a0809281a060d060203 75
    0x1100744400c00d81c45001802264800c4440150b82d11303064806603203034000d850f0050400e200c0c0500080710f103000200c02c0c03d0050514815183d1744c1d40d00c00b2600044941d240c00003c900b024883c100185543c0041c00c80b95000a0711003205c0d201115090011103500004151002d0040080307041c0d01058000d4018001855204c405d80752201d20151000395548584000718032524104400091040350110b40701c01600d40150940780b4002045841a01400c0080c207500c0c100f42c0e0b00e03003100f0b400c021004005400f41c0d5031079031014050b090a41c100040300c2c03000380c14080e1702c1540126800c3c540c03500d02c20900724958004000300d28000317851203180c0207008031340c880550014000b41d4010401d52240c000c001c0880030340f003003200300e40d250f1090240500090140c400c00302003c00086400a01a129455104000788200d179092805042c51b9030180201040311180204040c2c50002002030601000841c080c5a40c422a90391a00d5000661041c0302c1c02405007640c0c0c0c0c0000442c000c400c15600100140e074928 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 313389352 1250 313388102 313388137
    0x90e030714030a0305010b0a0905150d0207050d1d0109030318030b09010b0301060f0602060c16060207060b030f16060c05102c0a15020a030207050109061b020601030203120c03 77
    0x303800c6612a07003d03641002c0001d16000000c540300d044070058801c034540d107940c1c8541c181c0c10102440f540e0645a01201e00056041c0002c1c040900d03540001c00c0480e1080001c2c1c0a844040c80b00a803c7c3c01c100ca40500c2d0402181400656503680001000c0c1101d4251500900c1c1c4031080c8028000c20009410260030f10100004000c00c0c0c0700305401c682012641a00200085a900c004086101c5954002c42c40141c1050011801e6181094040e05101020103118080b8054640c2e40c5002c036030000404039003041d12002580c0701c0d49003d201ca654060b0001c009060784001c000c0c28a84100740034003900d0140086451910240101005409004071100c0401c00c00003290005104103840c03018200385281024a201055010f800716425a50983c07005c44908141c400343c0c400c03400303134000d03040300300400d035080c0469030100e070003401885101801071a0000b07081600c0c041400007640040214400d5510082c0100010b1310300240f44490340741901e80031600c40c0d104031800342c1944038250070f400904121 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 313390602 1250 313389352 313389383
    0x910050612150a0305011a01020604051c050f040303030f0b10020a0201080907120b060a0f12020d021206040b01090609022503031121070c030c140309041a03010b0303030402030601090e0307 83
    0x55002407003a0740e290007c0000801840d004907581d000807100106a500440300e21180002c1040700c0f1003583c9898208030b801c2800c1542154255081035000340c3c0029210290003408550b14420a2803045d026a2400034003541d044001e0740c8c1b1800c1c04002030411040b100050010300041c031159000e4003001003030030545852810032448001d002e440840c81440080d03000940304043c4501c16086a0808403901c200e42c20310707000c0080040c803070340003030b030300309102c10504950000180302c0c103072040340300f58944c4c06a54100304041d0103c0e405c030b400c0540b20710720422203c2c00d840740b029825030807580c0c200850305c003401162604034080d102d820461100010701040300441058120070310f0f550744000e40c140005650310268200c400401a00c0080c0108221030001c0000c22070400625003000c41800c101c0b4130f030200e418003060444ea01d45d0403500d032440007084460000d290030300409840d03030011401103045003491b400107505c1b18410300c11f8810569442000f500054002d1058541461f00101c80c0203080c2038 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 313391852 1250 313390602 313390613
    0x646030506100809061b120f04050106080705060706050406020f0f0a080a09030e010f0e0603090714041a1215040818010c08040b090a03050706020703020910050612150a03 75
    0x82698114814400724482c801c1052160b901d50344030b122510010b2126440d8006e424071048903d90030441d003420200095000001c2d03c0088900814a03030154010700d1a0130708285003194a9900701005982105100b01728903542c0c3c400f55040720307402c0180041c241d1181d01d4084000c0c403e14615403030354800420000444992200a49541e00441d118186240d45080d031140485989800040100348a01c01094071548034000b124680b0066040403583c491403400003031115001210182001ea01c01385c014441219480ca40c4d0840b024150b505225a10b44407040035140d8144503046400b544903035140c158030000400004c40702c0c0ea088104c1c18001e0415003800125544160b031202c240140080c42d0000a5100d00880d001d0070b03402c801481d0a0900b0050540500e40c001580b21341d12100008000c40415000d00040c80108102d400030542d05180d0310600c2003a5000270145201d0040c40c542c100560b84a0008445044052013025022a0781c2c0c503140e01d9500c1030340c080c520341013048400003200f0002d = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 313393102 1250 313391852 313391861
    0x15060d2c01020a0507030c080909090304080f070b07030e180c03060f0f01021015031502130605031003030e0604090504051f0911120715031a064603 65
    0x10354054420310109034140603400d0b8400c80c61880d000800402081001c24403980f00350030114460b0030f6031031a107403c0d0030004140c0380703050301c0c0d01314140c0000508100c00e80d01044601c0c5e800d8450000b0b04203040c0b07404034038000742c020428090f0502c0040c0e04034888176511122a43e8512401400400d241d00704042243c40036001128228090a10080402d10394a4401211580e420059005110300d064031041036001c0d11300901840348241c000c4a0202c00202184280021000311980068450000108104104580d40e10070020b10001300207220b498803550400c40c09032a00b60a0100002034810701080301c1d88910ba1200241c54900001d20080001c049142400020326562011801f00c0600d000d4045440c107030320040081403042040c0805040003412844c52a880708190b400581c1d0315103c29055003410300741da0b00069910041001c4030f0b000c000d1415044071081d5441c0c0d0034025500c0d03079501020780d11480a42e481070201c1e122842258103074032006500c2c4214030104500210594081e0180 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 313394352 1250 313393102 313393151
    0x80304060906030b1c020f060a020a150b150c2b0e030102090d1103120f0a0212030402012f1204030203061f170f030a110c100815060d 59
    0x3481c540000400600c28040c5030003240008041110a103552820102d00d0901000c5c01ca03048100704c0b69150181d40d4a2000e00303080e02c041e030040c00440c3d07071524040280340808850718072401c2c581070400c40b290301c03012100740b04030150880107a5160f03414403102c0c0c030f40860021a003c80441306110748240b0040d480c00722680034031948841c180c03540301100301401d0f401207615070b640150020302c010020032070f041904444c046014045d5296412403800039142030b88101450318000d0000221042c036540c2c1003210b81d43c83c08109a60034190f04146e40001e1009035900ca4103004800c4661030140024019400e00c520403c1550484103e8401c1c00512140b54202c0d01c010ba1080c000c940c002202c0d800f900c41c201102104041d2900121814881c928128a010003544952413142002091151a0400c01422007203c142c4401091751510415286041c400d040018000c2d181500141c296039040030b21180c00c203065480201c0701d07180c3c41000c110140102c500200146042060002d500100c0c000150b412 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 313395602 1250 313394352 313394357
    0x303110c1e1306080c040b12060f1f08060a0c031b110d03020414060f0d0203010b030f070f0f031a0310050a0b2e030207020d030807110c090606030c0403050708030406 73
    0xe41100c0410b80858803a03224806180e044980c1c0303841c141c03910740d010b91032040d00286420801481218224609541165a0b1141a00040030711800010380301e408034900e025000800c202c28206a00e007034991b24041d01039020161600795886070607000e074105080d800715058400141003026200100040201860203102c1d0140c044103940403440381c02194103551480b06000d0b0119241002d00100c2d90060f85d400b0b032010070a011071110100c89000070f40c02403812151490f203a0409a0300030018620151404c1d041c000c1c0240d24001284e046005804044007170b090028242200000d840300301d1412455440c0e1500a0048421503040150702c05801614031000c100680080401440b00d10781c0d410414410240325514404000d000490340c0c0009a4120315015090610a0b800701e4011800c44c0300c102c0205109500300111903a000b200882c201c2d07840300090060101c2a000314a440c040501010b0017000700000240c00400c0c01d07000c4030004c540c440122845030355240440e0782c0f03d801178003a6200 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 313396852 1250 313395602 313395619
    0x7050606101407021207050d0f02130621060204170102030f15150d150303021b01140a030e0c0a03050a050c01030c0906030b030a080408030a08090a0308010303110c1e 73
    0x2612406100d500842c1125007545440600c0d003c00c01e0351000ca02039856507114000c0c01048a450b080600c01c0c00e02e20494200c3d1075540035104000c8064460b021840095103812000c2000403451911809020606178160804036401c0c06c0c894060700c03540c0c01200c5080400740981e10002e005500840c801c141d00c040710a460348608400b8035989480300c1d51a41e000c45440c0c140780007090302e007004000340f440d04e03800000d0303010440b103045a00c040c040d417042d405a045404001c9280342844040e80d20042e0902c2d14401769038450102102c40d014511084041540e19070344a071030401d0412030700d20414030040c048070050b07a6a144c415a6000d0804085803035001d108100c0140d0750280c012400107041c2615080744c1c0720305209080f8018080700d2015640362040040050100e0203440003403014100041c0615034990801102411a10005d000c840a5610158002000c00e0340031a4060640c0d034545003d9144844c003449440c40d0005000c02150300040c005090b106094a00d09c42c8468a40240c40e00760 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 313398102 1250 313396852 313396879
    0xc10120f02090303120901090f150b03210d0207080d05011802070308070804020123130803160303020304020a150905010305180c0f06120c03040302071208090405190207050606 77
    0x42a402400c2d2101c1c1c01d03500c24000c0d8110511072020340c035801043d81c00006841e004544902496a03000b0a0644d205840441d407200c044105000348204048103600a000d030051411101520030002040180c040c3e90101d502c2c403880300c49404680c0c0c0141c1105c0e00c5621001c40000090081c41c003807180022491108480c02c02c00482d45c002c0d1280d403505a03c0d0001c032560364000544401600410490402400070000840c00740d805000d42442d9003007040031910303221402180450241190400d00c843c0d4003e00404090a55810140b00220f51502e005a1039866500c081030f22902941c00081d20082c035a140c07807904a40c030000303020444009980074040341c3c6818101c4803905400102581454024110740300c445c0c1455100b0340c908260151515160400d0b85503040066481600d0000e18503800000f84030134550304002c41c2e40030b01003401100c0d548440e40e60700e018084c030403100d00b07a001da516400001c40f81c1d5080b2004182c840009242595221454070301541c0b10701003111a94841c1c5101e07002e81 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 313399352 1250 313398102 313398131
    0x1309060815060f0d020907030b010e0312030c1333090302030d031d03070c0e16080a05091e060703060b0406020c010309150e0d0f180302010e01020c1012 67
    0xc000160034141140664942c0c0b02803100c20f0940054a5030080e030302c1d99000300103031a110109480391806076000500243d00e140018542c02c00c0110280c4240d00c0490703044400e4912a04403130300801d2a00525680e42c501a110b042d501842d64401c0344542c40d42010700101d00841450748000d40086140400000c141076401d403100c01c42d03030202a4040d449254040b0006000ea8002d2030400c2c600101c21405041c8070b00094550350084d50110b031041514041040740320a00d11401e900144484180c800c09400440010040d440042234040391640b01c1c2c0100d0f60030f01082c000106140c04441a021010701c01040c45940d0380340035941d040009140000000340200c085003510240d858030b50242210501c0c1500440c050446d45005540110b880000390000c0f01d071906c40e4841c03580e210300140907250740d111005412802100b01c10001c6c1320384c00d07071485150041048060166942420709488540c006c0d40101c1c0340051820716550451500d4100003040c03900b000030240718400034201030041001d0307907581 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 313400602 1250 313399352 313399363
    0x3010e1005060f0906070c050a0b07060e01091a0c0405040c0503070e0102011401050103090c09063002090402092806210503030604050c07050d05031005091b030901020f13090608 78
    0x14200c0c3c07903020300140509180110040c130900c1e003d00011004241c464000441d14050703503012000c9140c0028040007000380900480b42c11b04c0241c0c0c0204849041a00d0341d4030340060001003031000100300d10004d60501c890348299000313850301400412500741da480d40035240c0c1c2d10944600b4003040c03802442048540c81406100070040b04d1f84030000299180c0310056000e00b4030143c04450000608202059580192090000511484000600d5142038071140d00505201c1d98800500074851103c04015844061307415070002e5041d1050f84055848001d00111340030501c804081c01e440210301c1d41110b00007a0042c80036203c00944da50724010b8221643d105078400c0c0c08000788240c10038000550350b45010790003181c1c800b8005403003a00d84203a9607144e0b82000921940d081c04038801000340003021040c0b8501801030a0b05940221b15030178100240b1a4080e1410300c07050300c01000000159003c4020b40540e00420303c1449510349640901014001c50041401101c246615040c0005401500003c8 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 313401852 1250 313400602 313400617
    0x524160903060c030204090906021201060c1101080c09090709060906180e0601020f06040309090506040207050a02100e0307061e050a0f0e0612010306140c091318020603010e100506 79
    0x1550980c0341d2039580c8810191071200e142c0c00506501380300c002150350075402008d0400e8032990005a586c1c2c002c103c200d88600c3d042e0407160401011205840000714030b0014400241e0090800341d4094be00d50710080d80c10704c910441d0b9500101d5460501c0b0702c858007ca00078040e2017454840801c200d0f09e900084500c1011034080f01144259060100090618104410341006040c41600d81801c4000b6100d40b92500c01d4030100d000482815003040f090b0824455a81c010300b0440c3d00b0b40c80c0c1003841e12038543d6607038121b0019100d050071030101070409004a000498081c80a000e40e0241556007101422a1102c504502d00d11111170111a00300303072182044440326002c83c1c6551003c4565011708a6002002150f059006981045001310030b405c05008030340214410400801c9030414034900c18085540641552000341041c007103400d2583e200300740d101111070b04480006144071140c0e40d0108000e1184c002035080b0300004000b0450080310f06003540b041c14010000c12020790f60310700f804400d10460750b = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 313403102 1250 313401852 313401857
    0x51215220f0246090f0f0b04230310090b090601080a08070f05030d051608010302010f030f020702150306190e040b0a0e01050c0406030c050906030604020a0c052416 72
    0x3400c11242d00000c2030710214001e0000d03a419850485220060425040e403c03180c020400d0f00d102000382c42c3c112071000010f44084144460301c9840c010440c0c2c154011401920081844000c10294000b100c82119044035801070171110101891074a00740144070010050340c01003507040008407210000180c841c12980301e00c0061000c2078050310740d0341298200c540c046032000761010741c8502180c8100040d14462082400024540c02c049050504003904194610280318101004001607a040b10000806080c0c07414017191502d041300140b0000d200d03403d00250320520010403242d102c0c4540340a10301c00d41064902494400000042c906032070914410f0622210601b0005400a0711ba060410b42000a0101c08295810380d06891400e6400c104c903042d6410401160030090107030715015204034a5800e0070014500301110300840e90521005121600840d000101d8544052040300c810121503040f40070340e0f0b1054090712454595100c402e14022440360710301d0125540000b030ba0741d840c02000454 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 313404352 1250 313403102 313403137
    0x9030c180f0c07060207060501050a081501060e1c0c0509060a080304270507020606100306060206011703040302100e04050622330e0a050403051215220f02 68
    0xd8404421036140204810042d020501c8040d0003c0d44a00240c40300c1807150201051540c104805e000b100903050b07200001c1da07400121244c01c840f1001902a0648103e445e207000514001004038241401c04a418450b80840b48040741c00d00054148001c152402210301c400c03552640420811200c20701d00542e1a960010081040300c04c0741032014040c0d81100706400940102c406e04640110f40c01104c0490141e00810708002e440d24003a001c909641d569401c08105241c1402030096440d48140641c1110700e030014245200c8280030400c0c5d600456000300792034080c14510000034100c03800c4071280c90246043c800400d5052414002540c40303c4646810718900d42da8104945c000307454144c1c0b4121020140e1400790f4800228a4100041032182c460303181c0b12030386000790900202d440108064945490724082c480025405011903a40403100b40995820780c488500303640f58405070142c1c20781c0c04100d07401d0620303407060400709881c60280801c0e0100003c001401030700c400d91094402219044614 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 313405602 1250 313404352 313404361
    0x14070516090903121802090f0406050630030d020c0a031728140a0b030c040e0304290a110114061c03020106081e070b13150302160809030c18 62
    0x2983e024100b21107120340c90071719400c1c80d60041109040d00744d60342c1120a441000b00401e01502d40190382d0004010b898194204001c9020860801d0108030307051590f41c4071080890300440c0810548120411070a000c41d9210182601d49648002d5148103c0c0410412500c1a403000703196050790313104841c00c518002421454100070b04609400e001c1401d000341d610070402100d4010701210078454241d4040005a841d03105040520b042c0c0740c2c20040e44034500b04850b0080701d80c0c0200c152009c031240040580d41c42d0b904a0100f2005103800000c0d090038000204281c0c2510b64411080c10543c1c1030b83703000304200f40d85610110300008084580d0f07904145001d016410030607900302d000d03982034000d20000840e02c2d283d4602c1414591054a00c0c0248203412482000b4060184101002000307003a180a00d0300d400002414907084251146031401400c0c00358504140d4041d80403148041d10388039540c41d100d1800d1078481c2c042d070820f00b0007500134403e0700d103509a01c3c02c000b031103d00f02600840a00015a0305d = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 313406852 1250 313405602 313405637
    0x2003120406111c0f12090501151a07110103150306050903040f0608060d14011107110a050105041409100302061606061a0405060a0314040c08060c070209130314070516090903 76
    0x112403001002d6655541c6c070140820800e01c074106450020741640b004803031402c610000007042040304220b60720410024180007a021111810200f1400c2c00c0110320f0f4090880e07159285819a44083c0045041200f0049400c2010008005071140c14080050243c0c40d56400c440e8004200c2d1302e90b41100100310880081141001240c200017070074170010540380c5000713107140d00d55002030504551040740c00c17101091380d00d88025040013400080ca001403c1034900311800c182e20702c500324018000c006c4e03800031030000d6082e25854006543c01505c081e0703803290940c98017040078804034400d8407914a002030200c5c002d81c60300514421003c22600c005e05203801d01d002c200803075100c040b0100c01e160351a2a400101004034940d148528000c5104800280c0703041019824000c0040c50314850401c00c00113540144e44520385180c20400030241700400c200c01d8070341510507254013980c0000c1d81c0004500141009800186c8064400680011508065031a54010103540190500a01040040400c0490180b = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 313408102 1250 313406852 313406867
    0x1606020d0c140f010b1513090e03070807030804060b031c030f02040f060c050c060403080d020307020a05011b03230f0c09040f0b030d0c2003120406111c0f 68
    0x5000c0c00340c0000c0300c0110207442d8649281848088504d9440b200a07072090b1418480d036990300441d0301092898542c0a16002c020007190b401a046002c0e0380b5426060440010000d4618159004c03a8503541c1d8040c2d4280500b42c030f41d0880341100c500303042000a200e10309011520158102c20703039004da080c0a040000070f5003c0d259000c1c020601c150f0034400014000c0e80a00045c0040c07a950329100801051408c2540c20010781024a40c040c0700104070400029804004403003c2d00c0700c0002c01038998807090000ca0070090100c0014000b907003004480603005400305002041003c11742c03020450704040d80042504034540c400040c801441420000d4180d440800030154800300d91840c1c01d292600301000a0101c0f11203107080c204182c2d48080303e0303003582000c10003001032443c5820440150103541ea0b440c0440022205c1d1079106111000c5942c4494404000d4018400143d46169807260f488180c01019282c0c0c020700c2104c6032040b00c024171030300010780200007034100941d40c886007030f41e04c0d5040544045 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 313409352 1250 313408102 313408127
    0x80a050a091203110c011407141206060c01021c0f0b04050c090d0c081606030e031606110f0d02120105010f0f031503140c0901060201290f211606020d 66
    0x41340e0401050785041d20030710805200c5141c080280409041809004081c86284900d41d060b540007081014440b044a0740c055601040031541c01340c0c0e420144e410a8064051000880c0068010b824038940714591a0400740140c043c208040085000e14003c0006440d01a160702c00f400000304040400b5040c400b00310074200703005141d10756003165a042c0080c174140350454034100307640811030180120780e4103020300304512107640015800e00c00075040c8485e50b07080c03000b00106490356402c00303c07604280c08010394940d0481c1400e05601c1d90544007456004e076100c551020302812040002280030360050000c07242050483d51213544441c0b400c0c0065006103660100940100d4800000200107075100341020130b1011501c02500383c11b65140244400c400060b00080c096904040c010708034007115044079400c0c40c00003050351400d036410902040080030b16070309160304250b102421040510300c409003010b0f0b0041400480b8600c030400300010441c010a401524010780102d4461181140700342c41002c0320 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 313410602 1250 313409352 313409381
    0x7022a0901180603140102070c0e0903030a091707110a090501060c0f0201140f0a020d0503130b2203020303100b120105041a120c01120608060c0307031506080a050a091203 75
    0x1c030f9450382c0f16107aa01c04450103040c0107a400241030310400442404900042c111803210030220300b065400036071a80001808107000c955100035413010310452826110408070b5030b0180b42e58036106403d115211000703030b00ba400c0c043d480c17007a000a8500d00078482c44ac101d03541a0340d0100140d00641d1003c0d192250304000fa0b0401c4080b01c40c049450340b215000701842611101d0f003542c0c4090708038010741425034000320348041c410184100310340d8601161b402244903070b20040400e8540c0da08008542d08680d010a00720100170589840001c241d000001580a20460800c81c08419582c4015188034411044040400381102004205500741a04010408000c005c40030140b15480b1000c900c0b10000e10307144c2c180d070b6800941c0c090b00e9940c0203d0399a84c0300c00c503400103000c0c0c40d003000651640c5440c0540000842c1c00000300081c0300d00c0c882d502030054080700c3c0715400c0c0c0c19a600c0f42d00a22810003540e144414074075040100f82100708621403a4009603010b0340c64141741072080c03015401044201c206015 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 313411852 1250 313410602 313410611
    0xf0d05010f0f0209040f0c0f03020c0115090204080f06100315091b0603141608071e0905010801080102070f03180f030c0305010e03070515060607080307022a090118 72
    0x901604600034102c80d040382190040c0c0f240c03070180400040d0f50300c05028404044c40c000340c00c081d140c1d0200000c41000c045090250b51003a540403464018451901446501481d0030804a81a1156002081140c481030304460718031284150365925400191041c40e41c03a000d8a008000085010501c50510340c884080018600019100e00381d5890710165400d140da0341160040c0b1045070184249043d0188000c0c0302d0710645001019100a003640d100d2400a202040000400442c41340f00d849c109641c1910711044c0e02040c3c0e000c05402c51005002d15400f240d070600c00440c0d800e80520a8840701e40d00f111441123203202d1038070255030382e41800241b91000307004c07900080b07890101118070000071840350f0b4100c5910740c6503050082c21a502000c8464203a08104010408a074000403408400b0050752201401071f00c174a0009035841c801c100c0c008023400c0022080141550300403c1d84444c008085021810800d40201c4c82a140e5154145a561002408005100804500d070900404001902c070009 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 313413102 1250 313411852 313411871
    0x306270625050904020c0d0210090b06090406061a0a1704030c11011115040c0b12072d021f050118090c0b0412140c0d0605040c1e0e150f0d0501 63
    0x4017643e1004a911420780d1100006544044e13041041c9005e510904a00f0040d01501d0f40d01c0308007240300982014800e1001d5000316043c42444d5016400070b2061004c0911000c15103a01c0c4d5a03203401c08103017100803e2520100c81385c0c100b08002014440e40d81a56800c48445a540d06d000085021070b50190400183c6003001c07145070000c00c01c500300541004207146044c503062a0410200f040c50b00420030080040c040041c60b51004c804c0207401066500702842c03a4254510504c28000c0c41201e080d43c460b1070b1003051450140c0100d140c580440c0303112404418000750602c00e00c21360f070382881a8034021505842081c0d26191a50215001c2c522a0312083c1c43c59650320301d440705a402c1908a0a003854005610504000c940b8002055007040c81000d401e00e05402000543d088520707a6024100b5a15940017070200714002103448040c2100c3c0d039800c651261b030b010940003040f245000300c0d140721510101154000001807128800b401008080010060b0b4010034000e010b40440012109992142e0b12007 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 313414352 1250 313413102 313413109
    0x91802060d09052d0708030408031b210301060f2a0317041b090b011d131103091e07060516150510091e0b0a030203062706250509 57
    0x203000d165041001104c050a80001160030281c81e54400d1a09074000c20040140850100540c0c41c0c3c7c02c40f501400301c40904040c0c80d40c2c00c116191342194491580003501c1107401000002941c143c840365641c012800182001c00d950300008003803012000061482c908402c00342c0003100640d500c0c0f09242c441d10010104801c1a6803030010f41d41200d0240e05220054110700c4004003038001491020b10030b22400001200107030402d100382c0380a46031850b20203c4c1101c0c540326042ca001401105240030070103c03a031461410001e4106a44d402824000c0c101c0c2c02640190344094150004113080140001d58078007407065505078028000c140d180403041540c5400b2501c01e4840c3c10f80a0b05808010410b0f103030401c8031a40800300364100622181ca0710401c911903081d40c80b120040030301c6000c80042d408110100041c0410460341c0000e6040c481d80f020850f126201c034411740400d00010300200084410300605588800d8111403d030809040000d1890500b45040303003209103001c8900380781d46007162200c0031 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 313415602 1250 313414352 313414393
    0xc01110c010b030c03030f030403052b15060c0503090d05190506010e070801080c0d140a0309030209060913110a031a0601270302040207020315040c091802060d0905 72
    0x4032219955804544610341000c1c80300c908402c0003280039502e0081e0b144035003051400080c0000c0c0c10041c004c80c11000f48848c0d041160004944203100d41c050704942040b81d40645030415508810106181e00010468007511400d000650300802850a110b03161040c441408042d400a407414411203910809403851000342d0352030140188040d001e10340c1000014004804060160000c200e031000041081040119061107405412201624000100c0c184001034101a24030f1840c0b0740961180d403004c16030000061000c403407096400e034a5980d55a401c1000211080f1080c2514030441407181e0002001102810312286004149031215926500e44400030744402141e0410181040d061003d20b40e0000e100340b06081070700401c00000040541141c1c1c021380c061100034000d0350085555070071036800f401076010100b001040300d4142d240508201020034640e104002900d031a04020b200e030300c0501c041c420340c459009880f1a00d0a001d9040020041284a1050b2882e000c3e280b0a4030301e040c0140c04 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 313416852 1250 313415602 313415617
    0xc050d0b06070b01030c0614090f040510090e07060924050d141e09010b101101020706020d0504120c0206040314030c0604200301150501030c11071d0a140c0c0111 71
    0x1c86e103480c02d0501c094810002800f40035207801040c4048000c3d55140c0086074485642924082800d48840b1482803102c005500011001402c02181d2000c01c43c000414004440c4550f0f00d40c204141d032408200c800000460411684181140e2088907041c05000100311078492242c0019400c415000040c00409003900d0101492004581404c03040d82941d030328a4004201d100200422040750000400b0040314a21010a02000c0210294101c1003907040d61b4405400142c290743c0c600305214000020f01c2d086808407010301d42010001040340c80b9000c0f50a84503406000c05140c00d007503807101a44081011200140c40c8020481200e40c554240310b1140114410078184201c40740104500240d8240d07002c03203601030780c074000044460a4070510074008545081c00c1c002592900d40100702c480031a500008403091143c0e046c00207521400310188003050b03884010700c440c070b40c8075440b4000a0315900c00c42810301c03010b62404501500c40b070380d0080c00e880035030a0000504c000000c0c8022030380e070030000 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 313418102 1250 313416852 313416863
    0x605120c0306120d0816110606010e030a0605151c1a1b0c280302071505090d03090e07030b1f090503010c051c06030b040821130606090c050d0b06070b0103 68
    0x510003000395092a00c0a40901411f10b5010700f0107814580341c1e1450018082d0b41000b448900000107a18144466580b42c1e4121405100c00d1400c0c00c0e5603001c880d01c403613400d4000c00300600d05d086412150780a1903082e40c2d0200c1825440c42d210300b001d690741c9902501c02c00c0d10040333040b0080b8040384030030000c1c400801e00802806603510a540c00c41c0499198040c0c17081140101c01c283d00c0002da02003101800d4510001405082030003580d0101c030140500761a050b0449403140f4003005068210480e02c00302c0d6200b400080d401d580f40706040b8107544031030a0b40c07900b002c80c08418440c0050040100d40c4403006519014120300e0303481d0300007401d5904a980350004140300080c2c200c1d9a0010b4007000900d003002910a00082e440e5030b40321550b010740140050311b818004540303510f29004216010020201003074882204e130801c1340c080c41c0000548001201c0c1185040760000320a28980580a801c40301034651608045840690750050508009025032210003001050009014030b0405030180d4004d6 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 313419352 1250 313418102 313418117
    0x50904020309160f050127050604120506240f010201091e0c080706350f07021902010206010902071a070201230c0316050714010509070605120c0306120d 67
    0x5041100c070240f40303030402a4403103101c100501059130000e414601e10190741c60100d01c0424102000f001103011a005150320030f00c0003e0000d0403400c408200f195081c02242511a1601c501140c1c1941c150131701c0c07150540c004003d02c462904d18014000d030014070410b00021651110681c0c0700c020584046a094080d07004d6103042d10705000001c24a8805412000018100720b418684040d0851407400200d209074a20301120360766950440c080e03c518050340804500550419000c5c0700d030265000c0311800018884c810500342c075013007031464881c205901a0081d0010340d0a0212001c0a0b6119501c1543c00d55103081c02504c0305203001069501c40c41c002d600020b030440d8642240c02e4059102030303411a800c0f1302c0f8000d205c0d0b885624003c0720381000ba091041851015251000c0c2d50500440c64090040688040201c15030a0103400035403189070808141c0790f9058407903e0507a21070007034246042084141c580019a051003450041d50000700080c6001d001b07a20b04c4945600d050441401c403c00905113 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 313420602 1250 313419352 313419373
    0x10b0306040627151119120e0109020a0504020c0a0b0408070212060903160611031306060b040602100c021204150813020f040515060f04080607020a020a031101050904020309 76
    0x90032034500c3d600d50030040e010600141d455001c401345400c103603a40e803560ba40303107040742002e24003044400300d8080c1c0050f408000003500700a4001070034031240c0250380d1b042203404040c106043c0305104d503003940140005050f604200611009400540e5200c0c95486100c000c1000300300d100640c28404c81c403641d0001c0c1d4038003d52061006d18000c415481e4101d85c0404c090295450020080e108405041ca940c11222202410002c0241c140c641c040d40c5030403400400d1005c035000e84070350503603414005d01090241941ea4169108503114501c10b5400507041000420540490b030340108503019154030480d01c0c0c0c0e407081081080c0580c03050707000405441228010124481c0c003e400b80798054140804442c4011007500419944421031203294070543e035810004203940000a50070100c8440a0701040d15080d41000800403644940611289442010001010b00f0302c00280520040ea014010115480c510b030f2300d44800c0114218614140141480f4603980703600c4510203103202d41c1c1c401c0010600e96a2 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 313421852 1250 313420602 313420631
    0xe060f0303130b160c33020a0201110a23060604150e1009060602030a0e0406060507020607051005070804120c03091a07050d020303071710030b09010b03060406 70
    0x462840d00a4109000c0b40460b000c0b90840101118550780c030240d50b601070950811032610500d1343c02040304c0c4207688041056400742001c107958042084421300a82004400502511a00701c500b50050388010092401548501c0c0d900201048040032645010800c1d541c42844c1004440ca10880c80c00c1d0900d106c01b80101000303440c1d04000d041d82c0820028105001c1000306000368000d4503440e02000c1e000c40d5111400b012500c00501d02080f0030400940c58100094030390b8003d090100c0092045007500c2c9451500d80f24070812901c460315030324078108059003804043d412414060b1254003a100c5092006556402001d1040d002c69a0f0451149000c5c6014006000300c915601d007042448400c00e00002d800040304015164420380341c030036103560314880724420320513254003d285006440c0d5440703050b50000082d50040b0810b460300a56090b0072001030540303500c2184c0000806242c01000c20100385044251900086690000325050307002d480400d00e02242914102d41d2a961504507980407072 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 313423102 1250 313421852 313421869
    0xd0506070f170f101a0a050f1303080c0d02010605030d110708060f0a0e0607080606090f0604120b010b03090d120f090c05030d050c06060427050609010b041e0c030f060e06 75
    0x1e8811400651255102c0d2421090142c003d007002446000150082c04114050a271204000d1492410f028540c0b00d00d482c003415006400d41110b50b01c1844a024043c50042c0200f0701911030280c0149500c1500702402c88034509159040c507054019103e01055900c0c09006280c07080d1200b80004031942480c07000c940403034241450a05980e005501404145a4448035007034021004071860340e20b850340c0c0c000040307950f0014645180d03c6030000900003030610301034100142584c024800c0f2500e80c5c0c2c0e035034406510b03444101d9000000360881c07460304c40b003139020740c51240d0801d0080300f0020340c04410040b413904540c0f081c10241c941c811440c0003040585006c124021643c40c403450010305282402190b540e803050003404180c0b241d6201c44000d500491220030341c403407480b560780c4202195500c42c10850344584080e40d81244650030103d007401030742058018a56040140e150f450700d00d421502622000b000544188020513403226442107442c1e0841c005c1001800c078034103000380542070506c101300c0d040 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 313424352 1250 313423102 313423109
    0x6060307060e0d031101062102030c01020d08010905040611040909060b011d1e0303030f070905010801030201320f090f04050405060103030c080d050f150d0506070f170f10 75
    0x410580002d003110346442c11551801ca6050a10a00f17840103820003e01410141e005035000d0f1184291070403a5202400448000b02d0003641581d4014464400485c0c84a014035590408502d5036001041030441e40e1740030b644d120780201e90005010110780f000100d25800340c0d200748443c5440d400c18005200340c0744103612008000b401c00340b4202c0f0140020031038144e948240980300da0380c1c5c800e6000b8032103c03002102d0701000380182a00d640e49002a050030074014207444520002d0424040410b080d402404400d05a0b60142c407031080503940303c2007000703940c4503a8003164200c0c01d10340006440034070240041e104020045507010384412082c01480b0700b82041011491040d4285014040450400304039181500c0c1c1510b4241464800381c100000540305c0c912218420501d001c0400c0341405940101034081c80039011790b13505000700c2c1d408000303a1010b04d03003003c0c05682141c0c01051445000d003030860034402c0d481c2000840c003081c242040c1c032034810071078140030710006000402c01c0d840b1541c014000036 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 313425602 1250 313424352 313424357
    0x60c0f150702100c09090b040e03042d08100b031501060302220b07060b03070b0408030901081e1f030503030c0301050909070e0402040203040204020903010207060b0f24090619020606030706 83
    0x201d80c0c113910000c00c00b050a2080c2107030b6903903480807900746480b59000910341070560401c40303544a40d00d07050300343e021b10380d00d0b5000039186c0c06210310051070140004c110100c80c2d00c0c1c8003c020b624004a1040010101a01c041e58103101c0c0210b00391610aa898201c0e0007841162030058231611035200314094010185001111202d806005002c624084802d95200d90303005200051b9010ba81c0010907c1d15900380c004c11081540844c0000e050f14002000b424020001c0c0d950750101d85030062034000564640c440d840c0d030343c808400040e42c043c2c14020b2000e008411400c080c0c5d4859965240c4605692095401181a00300080103000340c2c180848080e8000c0c401c0001058034501d4100c070280010320251000b0302c9150004089000e541d80c0c1e4041d00c1c20b40350010000c640d5240145000c100a0202110b03041c00384504205401040c40c18184801014030948039052000030b110201c0c06169004c0361031150300003028840340001c0c004c42d03000031005a07203a03001013603a411710004040c03500f99a940100c04 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 313426852 1250 313425602 313425611
    0x6170f0d0903030903150b03101e020708031503070504020f04031202070e070503060103110406030504020f060f0702010e120a0c0311040c0905010305060a080105070e19080a02060c0f15070210 84
    0x9903c441040c1c02c03281c100800d001a004020901b0b0003400880580c0303541032052520709000543c2d01e5210030603603101d400003003a40d401c00c81000b0007030f0f00522a010744011010300c002000210703080102c1c000304000074151200c1640b41e40006080f030308860540c0b803040c4008501442004041c00d01d40b0030843d26800281003191804082d18004240101000c04100c40030021600c00c1c1d0098201d1080151007100c2540c60317548a4000a006240860f0281e01c103803480c5809500c10f050000171076a019150300c1510340b07014510740064858a10016103180c20800c11300400a00c140140b055203203552040b010000110310303600300459814030700c0b4803e03407180e8600414407030020f03001021b02044a90a00b000708031541c5e0800000d50aa00981c45a201c9500308810840750507403222005884c418202c402201e880350b4521a01c00311241400355020300c0d80070a030304002515240d0040d15410034494101c2d0160b1000a140302c8c2012a0210080f44900341da409000c4010340502039642000400c0c0340420 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 313428102 1250 313426852 313426859
    0x9091703040b180703021f030f0b0102072706080313080d09120f020901030305030108070605090f09100906081c0e0306040b060d0c0e160809030a05090406170f0d09 72
    0x854440e01622075208942c600c01e030250f9804040c44400d0080d80c0003808400382d0401c80c8203200c600c60030914a100020301d8070100c0c500c08140c92164041c0144180d006042c064184400010364070300c1400c1c40070190b4060300c45000d8282c41c9009400103402d40070081d40d1144505201c400c030304a11900103c0d810340000d02160010307907110711248100c501603801c0181c0b69a5600300a02501c401d02c2c0041d400605800000c8107058000c8025412510301c81d040322903c3c1d54507001100c075402424002a4000e04400c205111440d26800c06900013108088801016603115050b10886d0130300d600a107000d8100c1840e02e11150b048450f04e001c0c1103100c0c200480b0444481c800039840d210010001040c020800f0007041a81d1038080315060701540c09052820300742d40742e0400440d22801101c0407500d05424100c03500c0740324401e021480c05480010011414110342502c244d940750841c9100a410540d03500000031505c183c62445810013000078007402c40f0340e45070038005040170011107444050010000080 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 313429352 1250 313428102 313428113
    0x2060108060f0f180f01050f0c040609150302040506040305011517030a0c0809180115050f0a11010915090201200705062505030318060105100c030903020303040909170304 75
    0x301d0780f040860319071400c00d80e10000210303120b80341c1070356032981c0e4855601080380a41055110a010f1420900304044564502c1c41c100f00c00d1099006400004529000411003181e00c0c941c40c100e0700c0c0041c2409418261610040342c555001a841550b031a074690002240c03228002104138003070141c85c55180700785002c1daa80c5d06d0762441481411010003860840041c04e0040b0340058803007218004000315121110080450382c1c0300b0082c02829510800301801121440c0a0f40844640a030401041818140c510b1019910a0400d0f5100380c001d549801d0044002140c5554125a40818040018030030343c2c1400010018240098001c44540b00e40819128a40001403802d08488044503100c1d920490115140010303140100e800390482e100114420401c44040040d6205410f507240414000b40d541e04410f03920f0b80203115540c0c00017400b50100391890701c20240d52400034020700300703a1040e9613240e011a2540c0d1241d4010a4804c0d43c84802030200f141c0a000300b4030f00c241141115065003484e4452 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 313430602 1250 313429352 313429381
    0x6050a02070f1e1410060b0a020601052103071220100209010c1407030b100f0b030402040e06090706030c0305090712020310091101030c110d0807021005010b0a0206010806 75
    0x508101d8141440841c82403d4100509003158400c40d1403a2070b00240541d50b55410041001c40c441c94186034020820040c0b500c00d840c00c0001d264001c06c101e901e08002e0006c00381c1a410075070300c24101309044400e003081c00c20003056000c1c400c20a11048201c81e500043c04441d03582a4110340010140c80c000c40b11100281c6882d406c52940001641c42842c10010782e00d02147c28802801c82c00340c0c2945907803080c0042f4002080303d00401403640d0b05d0755030f40a92880c09031280604400c00d0200e120078468003403004017641e0312905c003800c00a855103040b0724242c6800d80031103403a1190750001c4d5040c49541e030f25000310360486000d4102400a420400300c81d640365401409100406008a0301e09000c2d50750800c0010901c00b1802c00411200e651800c10038203d030f001150302ca0109085c4075250603240d1042c40495000d5072a0000b408980e081840308545211002e001101180718021031403000c03a0301485480e000b81840b03242580da5200c20704001c1d04019050380044100d80001041001d400604150b = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 313431852 1250 313430602 313430633
    0x70209060d03020d082701090b0106090308030a020a030b06180a080f0c1e090a020d060e0606090f13061e06092601090b0112020a09020a1403060a120b0406050a0207 72
    0x18041d03016610100100c6c511929101001410840701c8081c400c2e894041d80300c11b400d64004c04550a55a803100c1013a00c4081c064800201030010400002c1c0100b0603543c06064052010b2801042007524940010703125008007009030044603042900305030304d02c0d112000400416619000c0e0442a00d900c95413612820070704007050152030090743c03509102c203030f038403241401110003041c1c00701c0760604205500082d0042c4e4101020796103050000300d0106d18100b042d03071103018020412403601d40c860003403001d1045a003954503000400d6151038109480f40e800748601403c0c80d02820222040c0d50300c40015070301801d501c044280a04000c0034030003d0703226030101006c40900f03c1c03440000e154502105005214071100940f0301026400007040d59410381e03d078a0001802225a900c0240d165040f0100300d2083d0304c01c620218080e541d060900d00541c0000d1036102000522201280340d07948141603220114680803511012640300b00010041c441c4200b64000c1c1516404500b080b02513500d03842002c2d96001d = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 313433102 1250 313431852 313431857
    0x809030f06070509041122230d120e0312070201080a0b0901050108100b0f1803150a18050a030503061f0f050c011508010b0109090b090a02090a0905070203070209060d03020d 76
    0x4000060b003030951040b01c0801c4d82c5947c8403510a44540c110f060b48450501030b01c04850b102e40464595401510100c803104030000740301450314496070740c807150340300c20404180061103902400c0d0b008940e409d000c3c8110004418a00903500c0805200062412000074207040c0c050b85458140b00c019100d20300000d064880038205291240c88000c540c680100555000407050306c030004050380c000810300702034025180d44e0210050009141c0041607180c07025002807420058140000a040601c25007001d9580904a8460061405aa02d600e800e2180350407050300496400418428036050200e8400c06850007104000c0c0a02c034071503001071800b040d82c00803070100000444c804004400130352140c0b20000400c01c0420015546514a5010340702d400380060125484010001e08035000d801002280d0000418151240d52114160340c001c0d041440005d80242240c5c07801b06800342030b80b18032406510aa00255143e84091040110480d0002c00b80b0b4000c80c08404010006a0000344040074000d250 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 313434352 1250 313433102 313433111
    0x402060a0507050a05010b0f1212131701150f060210052e0f080111160507030f0309050405011512090302191b0503010507021209031002070809030f0607050904 70
    0xd003040310540034140700070740640213001ca0641040710540c040c1990711001d960090b00c0200e0081004401d100f0800705024030b0304181030251048010300c0050205012880c0c01c50081501d0b0007840c10030a841c801070f1420fa83d5280356280444500a4aa900400304c0c0e81c2c1d449111f60528000a44604804150840244c2c44038042007200400d2030313001c0b24544281140741d40f40d48200300c01034041d04c281e10034500760103101e040204031541c040c01500e0032400075081040c074040400e074021b005400d0004094070140512a070100025400d0301c0035800b424000d43d80c2d0424107050004100803240d041e804940901d50461606095540000f241c42c1c0d032800400b00000d37402e0b11800c080c0d003040122505080441d81c40c031900010419004060342071890881e451400d00b60f100d50506007220340c107803004d0003d644003d0f0249501030b0071740000c20b8244e80c05010381e14a5982c0900c420240c1e0440030084a0321140070691890904041014051562101c40100404d05021700301918130700c280d6161900650700c4 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 313435602 1250 313434352 313434367
    0x30203100c030617030304031d1503040c0e0108062d04060b0301060b04080d030f050f0402060a03060b0315030c100e0613030f05070503120f1209010921090b12040206 73
    0xb030f5000c20000c0caa902d00001c46120590000d40d01d0744c2c400c5800f18085443e00c02c2d60301107130f24011611410250007400024000f50f4803010305c400c60700006e00450b40e41c00c000c0c1d0302103a440b4814810714005c7c0b0400008000c2c60030006401250b6152240040c240c0041c0103880414414003030b90b0481d04207170091000100d900400012902400543d0411002c80740000303000200765000140003807010041d031b40c080061110320140841a6503007900c4003804046003002081c054544074006010040080c01c001800c10303039070200c0e2002e13900100d5a840043c0400e44100c1e09038203060001903102c510032594880d248050144c003820b075280c42c19090703000c6d541c0400c60302d00600a82d010324001c2c0d0f070803010090440c0507514219a490b20346014180c000c1c003550300b02c84482c01c00c4005444040401d45901d40c20804112403403440030000801540c034540d2110040d40c00304410907607841c01e00d1040e80300c44100805500e80503103000059445a400307200304000c8070310710b580603c00594009604544040d50307082ca = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 313436852 1250 313435602 313435607
    0xa0e0607060b04140a0e030702030309040b0a09110301051018060f030902030601030f0203010e030a39061a100203090402071b120b1510140f0a0522030203100c 70
    0x2d46106803900185410040d84141d065500e11034826120078000b0b0140c2d111000010b9200d0091601c000e41550040c0214585c2d440c050704030040d100381c00b822120900e035403842144140e505003050200f6520000006201034100365005190360764480c181541d501c0b045182c1030240304014032960040141c001d440c0d0a0540c40380c1c0045410075001021103401356180d00700300407602d5920b40b04074031075840e0040200ea41d15021003500e00c0c00416807907880d00d05803e8041009043d4141c0c107512900340c2014416980e03c1005020920903500480340040c1d26a8845843c0414455050085d032294904240d1000c085070f00208413040b1400c191400f5032100542c0c81c04078200c101c45506a02ca1400d4200c0124003104000c040d2031843d40034a8a401c055120346000c8070078010a40c081a80104240c0102d500040c00344010351f585c1654030144a14020a41e480601d090b084080d1010001da00010311000e40e9009800404a00351441e1004080c00d01d503500182d42da00f00d0701000032282d0340380c4000500307160 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 313438102 1250 313436852 313436861
    0x1361a01080f0f1b27090702030d1512050a03031415041a10050a0e01051c05090a05010f06090b06090a1e150e090f0f150613080a0510020a0e060706 65
    0x1315069032500d610b021040f4036120326039810584182e8041140034002482e00080860064545402840c0740c0007100407901c000c1c2c07a00502c0408a12824440011303802905002c09c4007160050001e000704c195a454010b05482040f00c0720f0741000c203c8414007a00c00d000b00c0381104150780490300041c074800440903040440340d40542d007962000c1e800e41240d8099820000802105605555102c00700d15100c0045d2028000c08451610340503030b400307a0000c0f503c260f52000c0d405c01003210403035000e009542e03142400d64280078a840d04c643e07111501041500e4450040d400310804c119201030070450700d8408500b40034014407400c000c50405640315500c44900442c0c12001c0c2c0071800f41c02d2080c100c40703800a400c134250b40504500580d01800010141c0e0403501516004600b10110380c04943c49540204008401c0340c18103651102c0c00f04684650107031b0310b403003036001055030758040e00d0a0100341c100340b0300f0b0903021548076850b0781c0104550300240d036010300e81c18411101156026110b0340c003400d180d001030 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 313439352 1250 313438102 313438141
    0x140a0b03070e0d02040e030909090106150f0c12030b1305130b060a15031a01051e090301020f0c010b09090f030a081e041407080f030301361a01080f0f 66
    0x170345000440015200088014011050b0a40b1105041e0710780361403541c200d620a11400310401c0c50340070f5034100345214007013043c0750030707124035143c1100b622a444900d0103103019002b01c00869540c91450703030941001c111502c5c42070711414040003149403080c190b100da00600e240080c40b01c0694000252070b6914440010090401e50200c00201e494003440034000b008040010b580d400c2440c1c40624641d0311890481c1c060b45251b109143c2c0ba50160a600d42e6542c0004401c1a41035409020318010307100d0718805002140e40000000c61013907086002d22842c13001c0549024403503007002c0c4580070100e03130000071149034004910f8541c417941d03985039501c03a01c041032003d0813400400754824801807040d0320903040000c40d40c07002030390310890751010055a181c100a140b0321180d0402e10041000c0c00e24098110750080c003180540360040068200306000b10403404440760650755414152000740b45140001604090a090460711401d12501c80c11800d00001c006010340401000002c006251004002084 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 313440602 1250 313439352 313439359
    0x10605221413060f0b060d110c0a030c060507020613080f0f180f1906081503070305030a030f02041805060118090903140f030f040311070e01140a0b03070e0d02 70
    0x282c100702c00e9030711001c0c003a0034003959014145200010b4400b524800c2e0b130314404000340341a00d00001485040007516503210720280c0070005008440d02c210043c0200c1c42064882e49e1541301d801c4d071519121040741c202520441c00c6500c0b1004100d40c2c0200d4103088a0381d0341d04054003039120040b40349210308922801001080140c0d0100382104a810074644c141c2c003500b4101d46140203240a0028040d012100d40100c1706041002d8000b000b646002e00c5000c1d03000b40b4400d11034403101c01001c0120b86809001e5204507080e5000150344110154188507403103140140000070f40c0761502e010300c20796000100440c0f01448540c1e40c0c010800c50780c01101901d50a001080c90b00c40d5003580e070344804d4020509204c06402003030707640c90b40703403001101403007140d42010200040c242540c840c52801d4041250040040f0700340890700000080aa00c100500c4c0010512008403034115814015000191441046101d01401044906000686003042501c0c1e0100c0e0601c0c0c241000d0120800103100401c0c4034101942 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 313441852 1250 313440602 313440641
    0x50102070c05040b010f0503221a09060c0315041a190501091a070311030417101a01231b0703050d0516080a05071b090e01060522 57
    0x3008a01c500000407602c088404019a4200da40103580c00c1082001d01000a98104000707010039100c00003802d4040140800f4500e18080740d81e0303551040c0c5102d60b5024840c2d9003c8100f10b04140308200c0c040c2d000c10744625250840c00c01c44541e802d280d040d03407101d82c444c40d11401c1d0b08080a001c2c654061007400001c0c2041182000003003050a41a84c034041c050003d2020200869440300d0340030700c80079030583c20011900c0c2421544086405c50103100c01e10001c0c2c0010000041c442e00620385604c40044800080c0c4541d120940b2104200c3c1d43c00d03c0d69024803032101000314106d0380c000026100e02c58140c0c00035a4100000300c1040c034148030f90301030035081c0c40040c3c0402c1c2e06400f00003441c10a40f4801d608407903441c0e55031082640c507070248a60103091a51034000c0100007407044005842c21030030b5030a0083c01c260180c0d075210200c0c2c1e00c2c0b01c400f18181d010000b0810424050340601440e0302e603454000c0250740d040601064500001d5071403020070304400c0a0120356180103600c00064454042c15210 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 313443102 1250 313441852 313441867
    0x20a050d0f09021914091510020601080105070c020315060105040803130e071b080702010309060e0f0c060307092709151401120b0604270605010b030906040816050102 73
    0x61081801c10703401040071946a004c0b15440c0203509066035900c140c509020310704982005600c000040082d0301c00300034a180321115860b0640c0c400d2000d00340d03130040e046960400209030f08450f4010b00000821079001c0340ca02c0941c4010580e1a40c1500300b4841d5070080c2d881c04010b07192031243d07500840c40b91000007188501a01e40d00080001d1710760410715469651502d00381201c812901031624810040c6600d05c4c10000360403031000300580c5106050100d51064141c6440c02140c410301000200ca800079482d00314020001d110111101c04121111402c5042c2100010502190f500440060a2001100c00300c116070b1400c00b212a1b0300e4104080c0b144605178541042002582c1001c4941a81000748608950303d80e8043c441c103a50288860803c10a82900d400745a100042d0500e50000d540c2c072100720342c0c2074800201c0d481d032094404110148040ca8a00754040312030503400440070107414002d0000c916808030728160000e41141d03240351529880606130107034000841c401000f9610014009 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 313444352 1250 313443102 313443131
    0x4021803120d050a061d100e040f0201020c0d0b180708010906060608130210120221010614031611120316030612020a1802090612102403020a050d 64
    0xb44880350090105110940340c01e81e015055890038015011003402500c1c11400c94024206801d82c44120140141400c83c0d65035501d003580780e0280c41c103980310744605c81e0302010755070100501600003030f007a250551910015150309001035006042c90714011101414402002e5040102c5006456000000c00c41d10700301d0b1811000404207803080201003894a00001d800401140d440b80015402038480c48500c400301000310761440c52030200c0c450303081e803d0048043ca050444807000010011580980f85541020b0003d001801002000079841c0c000304100035540f00728080c0e0102e0105035041076074241046906040c24080109002030f801200401000452a000124414040455102042825241e460749400d136030722450040d4000503400030402c003010165290301d0991208032001428170b103d40001a09980c00040c1a40c060f920660602024000d5041407500138070035003003101d01c00c9000541e070b401903140400f0441c00b070640c0420070092141c0544211804c444d441502013051110b0507441 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 313445602 1250 313444352 313444357
    0x40b060f01111e0606010219150207080d05090c040b181302060703022401080318030316110901080a02090112020a0504052a04140d0c1a120705090f0402180312 70
    0x24070003513229413004200c00307500220303c5811180500c3c551420019240e103d15860f04645020b00c590305508100ca000030800d450040c050ba101c403500c0c0880c0c40e060182c022468038403c6110640b00360b14200f0541800e507075000b9020340b41c0b010318411240a941d0b03007566503c20074030a400070350003510004545040550200d00c00a0044004050b0300398940007118003448a8001d005030345895204108655500703482c0802d4448540d4002c049030315044449600c44400d1003114011920185a407109078454981104d15501410444006281c440e4813500013400680e01807207801a03504a4000d10004e64450096140280c04040c1041c480750401c0700302c0d107900308052420181882d42c8201c180d41a015200219801c4544c07105100101020b007908100506030310700d01c112103000030a6000901c1503085403504160301f0f580c046603919644a420301c0700d403012006001d80100001080f00381060b5403400000801400d007500e006849a81c0343c2c0c854101c0c103802d00009580751140d1890f194041401000 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 313446852 1250 313445602 313445653
    0x6091410061208040618090f0e12070206160614040f050f0705010914010201061a130906050603071b051b0415120b0c040b0403081908040b060f0111 65
    0x182081099038815440c4905942c000303005200c0601088200103143c8a05018051100f0f101c0020385160398924140044580d05c1020249198803070354480c581c203038203114401c046101c03064168502001d41e800030b03445110b105801c419405100f071420060113090303070040041e0343c0c001c107010328182418100151100d20202e8102c0f2288244080d40b1903001010908400710303501038440c440e500d070070b2051603842403201c02c10981c1199618880002c3c07404110302d068101090700c0c54016692200201da96000d40c003182c005200d402e00b041030401c40c0d9224042182c3d8864514500b48021950b40400003901000c082800307001e80c81103111031301170003d0182e0042217158040f201008445030b14901840258a58800c1d900c030520b0540d1120041240780001c00d40c08810300100030724183c5c6075052249240c210750401c1c0c800c96000b181d880d03100301509000049260345401e010501d49400e81c1d4124440e1170003850726002e800b00086c004800d90041609031180070807542691701103540d1100c040f64200f000f10 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 313448102 1250 313446852 313446883
    0x204051005090a0315020904060914060603090d0c03170a06050a050301140a0c0c0b041104110316030c110714040b10080c07030c0b04200303040b040e04060914 70
    0xc4a40c0c1466024100700c480030240600b80700c641e01d1440d100d90980c2c05a00e03910341c80c03680c4c080080b2500e580e1148075500180c45240d40004440640040c0c900708560000c000c10b0043d1800c005000c00b1000024081c08d0106861404500115003440d044605044481480f50004804418024141c0c65038201005641081d0b4040c0c071102d039100105403c0c0c550900000e0625140f1318046000401e089d0840c110a00c0340d070a2180a0180e01c0e0384070304003014200c8096170100951400700c0c21074078283c041c1c0c2501160004141d401e5040201d0400d0018401003100707028550744040c51035590313019000f180c0207016040241c07104240d5919004445082d6483c2183c441c6241c80d0814a503032515210701ca002850960310184580d8407120700605550003240203405114082e185800000d4565040c94403c40c4135408201035001e801c8030f4221a031050840c1c85200740c206210520030180d031203007560100d0b80040044d001e55101da082c1140104280300c0c01900c0400806030b200305503200000d544044c10b40c41c8 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 313449352 1250 313448102 313448119
    0x106050306131116020a0e01080307060f020405011e140a020a050c090702120d0e0304060f02100504080f071a09032511040f0b030f010509070806040807030f090b0d020405 75
    0x459460b080710321100c0040d03d00782007400f500400a0944140742480c91010b0402c03c5a103031070310081c20016100360700a282c42e910014081042142e1409180300c02259504194102401c040010b400001a043c0903400c40c4484420381420038030600c01e12200f2114500100d64a18031a0f6000751034144111003903e4078450340701d4403c01801c0c10030200d8468030321072703000d09540302c030444104000303900c582149011103403159410900240240020001407000761155100c542c0002006070809103420344440002c3c2c079100c208000b081740788048444101418170102d84e00c00305403130940d11440b440004070000c544010108100004000010540704156060700b0400c40d0200e9070180500d40c01400052000d1a90b801c14030580c20287c109000c80d4418280200750319800d2000b10b840c5c404d6210004500d81e45074000d01a650400b480750401500519005d00313030b01e00c3c003500d0f40005445045001010000c2184004400c2e03031056035400007170120707881d030319655040703c0707030082c01a40090040340d101d503014 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 313450602 1250 313449352 313449379
    0x1e0114091e10171501060c0c030804090203150607050c010e0612090303010501022503110d02040f0f05130b15010908030c0303040c05040c120c140408150606091f14030106050306 78
    0x3030004101030303418411103c4d0ba0070f00340e00b211080049401203c80c03544803c000b20003d01280003400280902c0700c00140c03039142c103c0510314141207264400703005500030803500020880200c4c8445400e40203007000492111000007094840c42040c0c007601e03404050505100ea8017001200031030485500f41d0071100041d4000701020006607040000209a4100501c200000b800220042900c0f900003413001000c031035190045000d40d042c10800398606a512112800f55001510800e5048141118100400c425903a19443c103280090030304100520803807441d050702e81c070540100c0050441e0350240d035121341c41c00708076554981003a2400c40c0c0c40840603c006c55207083c5803165074898100ea0740c582394040c8040041c40700800d20400350000300110044580144900c0e50700400c010800708008044858246a8040140c04003800e000d101c1d48003041412115074800c250f8031142c9800003411007041c000c40c24181c9003516120070143c00303e10301000004100b6001000340d481407009440d4402c0c028803 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 313451852 1250 313450602 313450649
    0x50d0302030906040b0603031b06070f02030f0703030e07121a0a20030403090b03100807080607050913230a0b030a0804170c0301090b1e0114091e10 65
    0x812100c0d050702c0d0384600001808100c9002045030402005415213107400408901550f6000048861040356032092040c8401030750300c94070700200041c01c0d1002e10f05202c0e5540341c50f50144541c1402804141c0c540c01000004a01031081c1001086503960103030000880d403402c02d80f1030380c1042841131840700d480c0000d01030030080d001e0010742c804194030380c0c44403c1c000c140c1e4400c550006407040d1b0401c8101503000c00c01900040046024112600325402d099152041c890b00d080944e41040269820200a1042d0749811800f540c00c1120100c070700c001c801d520798181c00e008008000c00048900140d0f000e1148981c1c4621005000307150440d400c0c025140c400e800d26544504000d4005c280307900c00c200801c42c07500203e00c55642c6000140c02e44030310750301c0c2c880046d00307441694006030b0307400030070034207000d580300c65101d0540000304842c2c8142c900d07614200c0850340024010400c140039200c171200040f80c0641a500c0301c410b500700d8541f2880e103810540310151941c100c07402030075500242c1c0201c0f6000744e0b2 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 313453102 1250 313451852 313451857
    0xd051e040302190809030706110111270118060c060501080109020f0907030b060409060f120302030d0f020904180201020c011b2607050303071806021b0f060a050403050d0302 76
    0x1e416800030015408290381d40300e0201c1103680d040e11480c0c0113016580195400b80583ca009100310b503202c02d5111003903144907007103500c0340101c0100d8107410448255019016a0307681c040e81902901d95481010f50303401a2007800c9a10524090710a0248004c107000760407050ba1401d15000d5401005140e0b00c4d6a90b0304d0032200d41c000040d600400e1485140c640d850901d60056201040e460017160582c80c01c0c0115140782c1243e0021400207444100501101103090785070401400280c0703600c021601152406034403482802c2c221001c46803a038400086070000c903011641404400f0308100100400340c803c01e80940302c2000120300500400500a0480d849120986040b001d1940505c24071400caa80307100e011300b2003082502c0300101500042c0381918030440504016805240516943d03d0544001050b207201215481c1da040e40120081c0300d5503030b0004400810701505643c191080d0004000225100703814440b10b82c5c884d10016450b1600ca9014000e4000c03248190704840507802c207120700342e050f030 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 313454352 1250 313453102 313453111
    0xc0708101404031209050f030412020f0f150a020c0d050a050606010906201518010509031c051308041d01053a08040f0602060a1103161101020d051e 65
    0xc03c00d00c42c0250499051707004800380c83c440d404807000800341042e032070f056030041d911024140441c00c10000c10f50400016900030400111409103081d1240c50008540c00b0070b0381c034200d4000324040b030311040301c90082003100d074071040007040038143d000c0d2464560b45d14120403104071040d0043d48007069695006800d010156202c50f11103c031015248042000070060a42801c56148a6444e00c1042840b492407170500a0040403400028540d811000e1400c0d02c4025280e071a0640c17082001c01040341c0060307403440550003c0701c00454a500c802b01480c29144d8840000384c540840024000b0788902801040540090032a01c505010fa0342e44080007001e450195514192040500e10000d100400741d8450f410032400c60389403070b881d248030b40700ca03003203500590440484c00d200100d00f4001150100300e1a68444450502030080c2200801c0148079400003815100700341d0003054529030100d005040300c8015103401e400031500e440c04500e806020b0f0105941c110403510380c2d003086d0007514814038900e41c400c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 313455602 1250 313454352 313454357
    0xa11242a0d180215070b010806132910080714030c100909061514190807090506070b01090b010216030209060409081c0e03091e010201020c070810140403 67
    0x1805009048500904900c03082c0b550040080492000140c1d50800e01003501c08819030b8840c0c480d492458814007204e81070308801d1081c1d2200d020401006186c50507541207960040c001c0505680180c1c45640e04991005041d414a15000411860341c00101c90350040b0f448007411120082e03650109606c070015100416038054000400b2400c0c1801d03c0c41c882600c0490b54648901002d030340ea4005000c64000d600001a140035440400510540c401c9201c60f055401d08151807900d2201140b400b281e8500c49038184c00d11549070000780d82140640009001044050811555003841c4d160440c11200300f4000c9450061030286004203d520000310f00c020141d061040944280c196000c000c100080200300300d40c400e444d0000b5000148850b40a020030540050481e02f00d6071120f803c2c1c105540c2250440100c5500901500b400b99a0f46082940d4440201003d0b2921098050040340644928441c40b0001c0c4070701c420003d00c0d0f0200003649e0006064440f81004914403400000d520610b050790040d00 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 313456852 1250 313455602 313455607
    0xb060906010e03030f1b030d0605030d031107110609030f07050307080309090c09041b02030a02060f06181803040f0311030d050d02220803090a0504060b0a11242a 71
    0x17040540607005182c0120300d00907405080200c0011145598403489081043da0386680c4100a6400c08104060200070b050078103014402c00100210607a028890b0060440d000b10034815165858070421a02940009001e9a06c1c070800d86c503120796100d003584103e500a00c201000000c03c101c01005440442000407c00456501d5904031041c032908042d1030b1b2039101d1340d1040e4000c0c04c00d00c4d0203003038a40400140c02031911030b1520788000e0704000c2c004000000024a207400c01c580d0740e94020441c0400b01c0415180c02c1652500307440303400c400b0003840c2d050083d40b100050200b944446440c0407001c6a200c1e00c25804000301601c24161a000329041038070100740d05000305202c15009130043d00d804441300900303000442d04074190051107201d40d80610155000010801e00500700f025010018042c01d90302481f05619220503510a81b0802080f5010810f5405040761801c03020700280400c0344c5100300203080000e05600000c9030440513100b62581800007005c200b40c1c0c0b880c4c203065503890002c0d80700550 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 313458102 1250 313456852 313456867
    0x909170c0c01050c1f050703140405120a0201020f070c0503070816150e030106030c17071202040b220606030c031401141512010f08070e0619120b060906010e0303 71
    0x12416000300c82e4044d420b0050300c40340c800f031030f0f001c9814110300500060049207a0600c4400035088490714426113150460703200c20000071a200203840700c40d08118040540c0d079100d130124100d0080c0503200c5100c41d2114002000e42c2400060945041503078421000e41d1110740e40c03079030110354503d074005d025007200303e0260040044144a810700c02c000011030070505800e00038040003900316641500120307681c22500b0b03410701060701e00000341c80f00c0e0f0f1049001401030b5130412200316907100c0300000c0240702c0e984401c027803216520f64400d40e000d00c428418003000e4075440b9224100c09019a0f00802c000a40f414021984240c4203026540d03850321900c0c1d80c030707500764240030b0f06620f6800c6520000b03030080308440c03d00b480c142c101130007482140841844080694100f004005003991103501c00e84c0e0a500042e4144a1a81d0451100740c2240c01180c600e0000e08042c0c180c201c1d00c01c0203038418482c001c1e4004d120010701801c1c0000a208080880300c030000d956481005440e012001c56020750960300510809 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 313459352 1250 313458102 313458107
    0xe031602060a09031a040309060903050a080a141215040603240b13050f07030203010308040b03100504020309010f0e010e1203090a0221010e03090907030b0406030204060909170c0c01 80
    0x2005070740b20500e42526525100d0b1a000d180c001c0300945002c03a030303001004006c1410f51017100c0c5006006a46000d0311843c0c51a159607668007004e42c4040c1907050b002400783c0c42240180304680b040034860034141d03260324000e9400390096200300c41501c00c05005005c0c0403841c2c40c1c6449244281c036031090aa00002c01521f0424002a40700c0ba90b5820855980b0803654455596270383c0b100045080ca04041400d250095809400e10750180c00c008c14180107000510000d059201070b503065a4241d661540c4995498840c48440176a5603c090b0b007140c800000d001400300706410501c650000007a0900c21241840c002f5822584e045455409940100400c03e00e4903807460011500314180404480350103410360001460b60b484603110500c80c00d801000c01480900a0048035002060503000d1410001e002000c140540c000910101c109640c51686480c55510b030ba000001842d000780c400c001c62510f442100d0020f0042c0001541e0120000d9900b000c250140300c00c44c0d00c1c01400e0b20103400b5a00441005 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 313460602 1250 313459352 313459357
    0x1050a05030901061e03021201090b0609090703060501060806280b071103010509070501020f070312120e010e0d09050603041104050613020313021f0906080c04050d050f010e03160206 80
    0x20a0415504c0c0d1000141000b030f080c005a1402a07121100320380c6600d03502c10801c04100c0d14484a142d039060402d10300100b900b100255503c10816980304906580d40d9450504000c1030703410007455680303058004500c885c1e114048502c5140c007030b03c80c04111000d2002910b02d92040c45000d03140301006044c01d110340c0b01e5a0002d0a0703054412540b40b40802103403070000707007564401c803100032842e885107008202541c1e0410203514800785a6000c1c021070b5040d0b440d44080a40100d28820074090029541d001c2400d140c0c2c0840e6602d51180000c00002d07032224083e6880701851807034203000481c81500400d040c94910212402584d00a401110a140c52404d0001a000c001c111035842813030070070030810050742400118851110f00203c0a82000345104005401c407146031105108000d03140036409254019040a0580d162410714540c0e80d960281e5000c0d0920681e00880d4200d400f0011070030800c003001503e400d26601d4100240300c0c85c1d0042c591542d43c1c6c09040c140c000c072141015000409820140b00 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 313461852 1250 313460602 313460611
    0x209041e05011d0114010807030609080c030c071a04061d06070819030f05060112050c09030f070e0903030c1e04051026060303070b101205030301080111070201050a0503 74
    0x22150114603060321901d08444210b007169001e1540d040c0182d072441820300c60070f06a00d4008081101550406d40421350b1034940e4080100a5960340c8403400902c00650265615448400100d03540c44460004480e1204d199124421102d4000802c942c117981c205000d0b1000e2780e403107603a01000344814408401c080d42c04480c3c22074010004100000219500000808203450007010311658a000701c00b004007100c80701100c03c040180750000b88001030313910954128005004100205041d290140c040300301c0e20614000c290b141c8506207645210840c041418404c840b5980c2c050000341d178541022649a1000300e40c0500c0d0b10b0301c1040305914007040600e954450840c01030160307050036100c81c0415104110100c0c8100860342c424041010700d00340b602002c9070302a4141d0b2112841c104100807a50360f015002004107011303c002d00107202c1c240114400c400800280c5054050881035041030b540320b034020b00a4a4155080c00c9480742e4081d4150200d80d0825410707900c3d645072526040b01291076030400380 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 313463102 1250 313461852 313461893
    0xc0d0f0e0102191e03020f0d1e1805060c0a150207020f01210c110c0103060621020904020a110706090b0307080a1e020d0605010305010b12071b030201050403030b0904020904 76
    0x300004011305840d0000200184a40c0040c980408a6210689051381d00403044040221403600c03c5108110700602101c110b00307604080601200c865002040e004964001e00d81100c808039160b0415900040c005d8020b80c0100140f078040b00340341009206a2241d510060f4104050628900c5294420701010801420425216003640c034429844816103d0f201c090340000b50b4800b8411611040074010650f8550003403c0070800755241c00009460450350008013049400c0719004801c80b0980c0340c045404d000401042150f86204c5901c01824802c44074003125400c3c443c1080108825000301517000075109440102c1c0d00f180d5a440080703501ca00300801440d00c464480000011414045400141c40318001c3c00c0540ca506040880104460362940058100f40c00c1c80010007d400c0803004031100403480700b013054103550b074901064880804520344807001900c40009002416410351000740107900c01d69050256400c014100406054140c0c0c001e54002004404200010743c003210300b268411459 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 313464352 1250 313463102 313463123
    0x203120918040b060a081b09060102070b040f0f05150304060209120607020705040f1427100b093114030406020f010b0409170304020a03080c0d0f0e010219 68
    0x1048a2451003016a41164200400403c1c4104c43c902203241c80f001d894404014030318507918805810702c40f10ba1080c5180180003140100311203910910040d409445e1860754195916a0b4007001034242090344101c000102281c600420540303840340310011403030700400099007140c40700d0f111a0001e521124000da40254031525050117400c09001f8103114900b6034024084035481d20080c4001c9c2c419046000800502c0e00200480310344043d40d0490700000d8003c105440843d60301040c8400003d00300350140d0611030094031a0210425800284900302c05559016454450800f5a0140303c8000e0b11420010072500380805404480503801e00c400f401010294125242c1c501101d06541c0190003040060f00140340500b8000001d00503d04500425141085100d4940c2c88449800c1c01c031030300c0030402140c0000898250742d0780c004540055500a800719a403405c40f40d10680d521482c0140e06400302d0b00d44104201994090180c1000055043e005001d00c1c3c031591300c0507080741c3c0c0d0404007103c002d20358 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 313465602 1250 313464352 313464379
    0x50c04030c0e09060f070215090304091d0706081006030207151d010605031b060f0d05010b0d14040b0a15080a05010603021f02030d1e0908180a0302031209 68
    0x2400540c0000c1c01c2c9140d1007505030030022079003801c202004006220080e43c0505224285600152514400801c02e030891a90b4564140490540c400d50b440304078000c0c1410350350880710800326001d914600302c28044030149680c40c802590721440803508000119010401001018002d80080104900c1000003c41082d40310039014221141e8032000000b0b42a070004c0a90301d180300344217030780180c0b204400420403045007186e4000a6803240c001d090041001040b892143c26816041c2d54210060400070702240d81c4901b050741076038001031a1082c4880c02c100782e80c8012016170b05034034080d54004031800318036034420700010082d1551485481502d03010601c0010b001d541801f182039624450340002c20840d156004111000c50030b00c8000c02258203074806c10309681e40000c200c6190903441000801ca46a500c1c24800000e0303034a2200550503418072002c41c04205c040401070900850114481d4885113034042406510301c014080250968048000d80480304030110140400c010003d10361240c2254 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 313466852 1250 313465602 313465613
    0x8070308060a090c1e0c120801050f120304051507060608060f0a020a020c04020a0212041206060f1202040b0d082a030f090904020f0d05061005060702091302150c030d110a0c06050c0403 81
    0x4005007c0b400154408014002c0c0e02d03041c4004420781e4030807140324000301c07444c0c1c0e00c10b501c0744a04d200300c40c451030b04c2070f4654440c2c0c440a0300f5108425000102088445d5640c0c8100c1e8840d4022106101ea01350201300081c00e0750101d2017075400071000c503030083c90001c40a01c1448001d5010010700b100354402d82c2145010585450002c0000d080340d6902154030000e9031a00c1415141399401806662490103028403a03105d29401f424100b07501100c0c00701d00d4008040c007140c0c26200054000d00b82c490002055920a90725011614803412202d540581c1e40d80c41441140c0c9032300841030103580c404000c0080300c04030301d8031194451300f00740028050421031068100160845032003c60468071074100200300300702e500d16108070390b005200540b8194504800d55000400314070000b0116440300c940e07030b0314100c15501c0e0034454160002551482030b07035036200711107c2643c0360031034100c205045003842900410809100251a410042611046141c80c82940c4070301c0600002409801c1081043c4000404502c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 313468102 1250 313466852 313466873
    0x6050f0411090c130602030702130c080c070602040b03180606040b030a06051f230103110304020d0f1709090c07050604031d0612160314070e0d08070308060a090c1e0c 73
    0x106d40045a82e4185c900c14000081d00070b801800800d840d101112581a4000c00b4056104010b08125560f03440689085802406250014035050402208010070305400d12015111403c2c00800c4842607941c000030401034034104029107405411440a01000070170346d410154000c0c036038080c040744a6054402c815121a020341c814400c040c0c07440c00d0781c0b024044440250300d45078400e1074107018140116603106031900c809000203005420042103c020300042d12020008103500c00d01c00e030140b503400038040007190030102900e84551081c0e408104079035007c0084480b050742c041c01902c1c19541c0c5440980307003522000070304000010844011050f070764528005025503500107403840b1841c20841a6a412503645954403001d061410481c07041c1c002003014600d600c60303d1440d00740c01900500020400c15103520304c1c001e1090902242c41c40030150041c10341c1d84940300656850b090b4613a901080010b03100e800701e0940c00302d5045503104401c1031640241443c40c0101d4280216080200eaa9524001 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 313469352 1250 313468102 313468109
    0x5030a0804060906080c03040f050f1006091404120c02120601030f0b071b02130b150a111605010c14030c0606030105010f031a06010309020a0e0406050f0411090c13 72
    0x41400007000d124a9400808041c05040c65190000c80c1d440c0900c00b0003542d220141024002e880003000c8441004000c2103015a0b20709550196042104002a800080e01442c0240c0b0380c000d0402c1c00302c0c40b090300c01c402050b114503044040c0b00c8201c01041001c0c0d0312100904e0059802102108042a01e103200f003106e81d000358890f138034100c600740803801c20b002c171500701a2100e810844400c1c181e40b0080d503003810b4000ca00d03804880000b00160000d80e1140200482006140c02001d482445003c41603400c001e0489801c0e580c03203d904003400c000c00603450b84e074840d000468040d4013400c00d008552061800006503440340340c03094246c103505401545560031840c0f0003421030340241708001481c1000e00071280100310300140b12031428110b07940c0d150122500d29001c2c0c18408132307800065003a807103900851045500588030f0f80b51940c46581d041c00d4003508503000e4449600340700100700c00500300d401c294812074005100005c2e607d00403042014503c0050400542410140440d4003211081010b03030006 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 313470602 1250 313469352 313469363
    0x1c02090115020d031806151a07050d02031c0504030e04021c0605010f0c0809130908030a0b011803140f01181509081b07090c1d04151e05030a 62
    0x20060714000e1501d941c0407070365000c1506107810b0400c00c810000c07200040da50700180c0440e005203641d1003001c030f098565001001c008402d0303a0305107030035801a0081501700e00400558a04032201c18060b81d40c1d200d17003c0c3ca007905001207014880031017050750003950010321910304280e81c5c0c0072900010301a608185803401c40401e0b20348100114500c6481390741d006120170308001d01d4080480d000501142c20f080b602805801c00050844050340d1440d40d4240200e0954034100800314040c20030541c00c1e08121400e0424614080d4541e182c0e60099000d40400f00c4169514142a170455803104d2a840c41d03052100e585100e00319440b040460203006d40303407160388018002c1c55114400e00b480f11010080c2400c50903401d1030041c4810200c1e00210850380c030b1040c805203440301021003804a42c41c1c2a0309a01c9112020700c0d00100c40c0402c1c1d8800084100c06100c1608500500c1108040104590300140b0441611802110400100c041d014540707451100c0e59540740d205030b9880f400b283c1030116034807003104e9 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 313471852 1250 313470602 313470629
    0x209010b12073e011803080a0e150106020616031104170309090405060a0605060906070b090a0503130608090d17060d0204020f1e030108070605030a09080a0306170a03020a021c020901 80
    0x1a002440b0717a5076024030401c0d0103070704010030382c40143c1015009810103c1e11500d95110f4600754004000c0301000700d08000980616603580e04000b91520300650304400c659150030100440700d44a0b01541e0a81280c41080c03e04e00340c600184a0403400b00d0344c010703100354002406113048a50b1880c008a1046001c1c101900c11407800300101d004a802d26041140700e2032060210303100c103403074080a56513000d41c0608030000350340380c1c181118036054400c28014042d11001901c0d11000c00002060340c04c48109441e81c21a50711110390103910b0780c0c2c80810b1480060b0b01e41400c0300240144034603990300310071701a03c01200d8150b02c3d004101070b07a10040d0788508100700010400c0902450030880e410002e948101c850855040001c2c681c0c5940d0b0a02c5440c080220200101c0d441b11381c1903021030b00865000789919a10b2120b0039019000e0301d0644101d1031612442655000306076800301301c82404660503409414176401680c2080a449112407003041d0310284441144010b880d8040b11502074850322907a401d = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 313473102 1250 313471852 313471967
    0x11509080a0515010801150b0a17040c09060b1204060c090803040e06091e010b071109010909030909020a050d020c210d0b06090a05060d150f030209010b1207 69
    0x144094185e0004120340e15000200f01071410408442054a0400d101a40c0c0c070140000210b0741d07500340026665014541505000030020b5101700402143d007c220244003895580030150814000e002e003038503034100c410002400003543c1e50701c803e00c41400f034102000e515440b42e45841c51600150002d0000355017090600410789054041c45e9070040070703121000c40542c0d0400071030014034018032038507048000200d4250200f00c081d00f400c080540b000340c000001c40da03545007108060b010302030098020500064011400d03500f240215446603415407155880e00e44414840c000030360020784170707008900401404018181100c490f01c2e65210040c5200354460174030101003c100c1d0450369009214035020801e200040e00d583c80c006049170750840c2e52070386032100c0c500a50003502400014071038455003c0c0c1c0219001c2ca0700e00c088800e4a0081e610450302e80c1c0c0b614441e502502c2690010109400b5407400282103d10139801502505182c444240210740100c0245a50701d802d0f14000c61012004000403 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 313474352 1250 313473102 313473133
    0x10f080609060105180a06051507150b1c0c090203040303020c10020909010e18012a0302071a0402240406030f0b0121060803040b0a0e0a030803011509080a05 69
    0x40703401c80402406400194580030000c1c0071000c1e02c00d180d400000f000300c0006d501300042d42c00381000740f40140c4174002050035000f0048031070f408848100c40811000c00b40e82103050181c40303412800384019200042c0701040ba5800e004200c4000d108032640c079420301c8086800903c90010314080c0b84692130158031210b500c412941450540704a015140f441030040301640c0c2d8a41c0d0030b00b030440f8084003c82d240c5485040c4038489000c007180c031942540d801c200070010070304c1620540040440c041a0001d00f00c2c10490b1044050703100f5080050720102c0c1c80c00c08514103400c3c11180750740041c4005d28001005800c4082007021810740900251004030115003001020b400d4001c90ba030201171050200b00103041c00001911407100f100354450b00786021481d02c03240d1040d6911480183c03000310100e0b0340b2180d442c0950300b920745c00303101c9290010306550820440303824424200e50a92b07610003603a0741541c2c20002e88252a80414030000204011400000303240401400b000f201140100c02400d440100841c03503 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 313475602 1250 313474352 313474363
    0x109110405010503190303020d06030503120604060609030506040b13050d09053a1e06200f0a050a0216080a05060708090c040f0b191814070c0507030b010f08 69
    0x215000390031506400019290305c0407043c000b20340c142401a290f001d01d003003a400825413a0402849c0344130004040c0c0c640021000401c1c400c120884d014000143c8650040703500d03610910004001d9408400170400103100042055407110343c00e000d10400b00d0464440a10b8680440042d2000c9a004a001c0c0480d007046100307075240c0240100e107040014460b1304030107900408a44078441c0303c42c2c0f0945a000b080301100341c1070300e104000b060607112500d181c1807950081200003201e80300d050b450301920480c42807200940e030b84484022490303828403107180010344042d40440c004404501a8040c0000d4160003802c0f400003410740100104010b40d00f41c1381403803610f4000342100c001e003c0502d040100400d0000b655076211201a0303070201d44c2c00a21110100036040410149921100310701d07041d0902102c1150204c112242840040c1c0300080941101084500c1c5090040340c0703203520000500283d00a07960880900d115500716064540d03a42c4802076150340a0300020902c0d400860f0800c0b050208014 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 313476852 1250 313475602 313475609
    0x501050a0207030905010305060f040c02010f06120809240d0f150e0c0a090e0115140304020f06162f1903020904050312011202040c1b06110705010911040501 69
    0x1400c6242c4603407514060100401482a58100340d2100d00007030990302e4180d007a4082e80c1000e00140001400301d08042d010b841c194031440c480d81e240450000d40c850b00711035a40f078542d40200f1450700d028407010910280c404094141c0400070324402d1100c03a801890070003480e884501c2c1d030303000420605900c880c005036a1144030007450742828060900c05003a030200b1039a002030141c2d01c620364488843c60b042c1d4044030380c0e60241e0345c0e15580b10000200c92100d030204407506202ea41d140743c2d18140a49042c5464002500d01a4002451440210207410310740018000c08001c02e0030820410855135030204014004016041002c40d02d070800c0300a0080c0c0002d402460388101e880d11030056000c4071900061b940361002034824185400800c00b030000c06c0c011908248890850b010156844070340100c107803400034030b08034080c0b480d1602c00c1440030b00c6800303144c0007040d103101d04840c081c050785c40d42c5000d000540c1100300781c1394040211200003402403103114001407044c443e0000305540c55082004585c0160b0 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 313478102 1250 313476852 313476871
    0xf0806060a05010315090b0409020409060b0a1203080f040201030609020703120f0c020a06050406180302061014030d0f091e150305040203030703081b0f0d0b0f0607061109091003050105 81
    0x14808170701780001c0c0d4141c09036107800c080015040c00b82c00000c0c001d0850100081d402c40e140c06d005506010442e0480405000e09546c102e000c07a41d141c61011120404440150005900d00046181c84403504551600540145000301e42161181811422030b40080f80450100d02d01a01d01c0d0382841050240988201d14040100603400e4140c90103521160a5040200071030b95a60000f010000a584072a1b0702e181071140040c0d84049524000c0c0d07540304207407130541c10070070410310003c0ca804890581c5121070714054081c01e813444c02c590701580c10000c00864903050001803000450400145032540c0e009280080100590f1450f000119840114066460081604000810000d44c40001c212110542e01d03192621860766141c424000e4010141c86610f03114100003411103000c04844007138100314a501408001084a010410000160141307101d030700310300d042c0308280100301c907a40320070320602d00c01c920103240038601070008110000445009c6c58002d0006403d10901a09104445c0e0100100 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 313479352 1250 313478102 313478111
    0x1050a05030c041805010c05030106020105060f1c21020a0c05061603140904050103030309060c0c050d030e03040f06030e061023030a05120a17010e1b040f0806060a050103 75
    0xe01180d200d03440b418590b409140c6403420607612100c24241c01c2d040e0b0350840300030840b0f5010108020315076030080c465400190b0070400880e2142c50051545032500400500e8208070801e140c1c1d4440c54451031050558664452100c40c1381c01c444012110204001260b000d40002c540346d01c0c00307541c0084030341c00c40c5000e43d10070f015201c1c2075000c202d80208100c0d0181030403d00800294042049803054241c41c58225003054000810181c06401041c5014403070001480600d407003c00481c0c170001e24030030141699002c0415104480d0090b44400d040061003010b40340303015201e2120b0070300441a60701c4a00003075070721003030319a1241e001d1100d55080701c00300340b4080a0500e42040d040e841e02c80780d0036506400214508a18003a070702040100740b069440000da45444800d0903070039035250800c10040d80441c20041a0130b40740c0310007030070140c166410400c4006150b100c4600c10302d101450f804903140801e400700400301d140450902c4103401069210f00521305031414009100040041d50310031414141403 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 313480602 1250 313479352 313479359
    0x6030c06141804110f0409020a120b09072f030a03060b040e150406030506070903050d02030a1704050703050601031412070305070f260909090f1c02030909090d0801050a 74
    0x8580d04441100b100b21000300f070794241586403001c9403107004045081d5100c00280040c0102a5070040c103400e405944a1014002e20602c00c0020750320440442544a50740000050101707014100081504103804024584d500d203481402d00b04440d41051100546e00100e030700d01c0d0990785409940c003e44801c0384030030b090601d03240d0607044c041c0b0041d01c0c5403061144540090070545440d44050011500030b82107803039508100d0b501403c0040075001c01d07180c6024203050244014000400c448480c0215075135010781c01031415191919a1000d0030440343da0080c407400102249040041e280654087c3d10f00d10980c20030b10081d649408610840040000340030b02007040429040420768070515002180342c0301200c0d007072410001d80142c00d0040d620103104801e40911012202c4080c2c0110b031019100c1c0755054070742c0440c42d56201c02512100c0c54903030104214035444100c1114010301d6440d10b00489040c103820200040e07d0a070f04407201c0061341d10130501e40c0ba07110b42c0500e60a0041c08140c4000040504 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 313481852 1250 313480602 313480627
    0xd0c0507120614010b0c15070e09040227100905040f1b09020313050f011116300e100f180512070f0b191209020406030c0614 55
    0x2031807140d1411060304101c1e00342881a1500895040510000075102c55038540010480540002005d0342603446103a010b5602e00c0d91000b1100d00494440d180d10005c20b49400030001103c000602c2240c05c580032400900d4091000000081c00c06440c017407200103868040d1105007000b01c613600404c101230600c070070b0002142d03403c05407038134564025201043c100304d096140406140c0b26032000c410030344000200f0101014500300138048038400c5d000d48004c42c50910405090351640301c44546580000c11011810004504076040800e100c2c07000d000c00401079103400c501c3d80400c1060500300700c11a542c22030301a54024034840c904801191056100404203000030301c1e885c0c0003c030300c000340440c9180e160403c084041c0f01c4801007800502c030152809101d41915107844191140700b41c050200140418030440748000c0d1030b6501070484010354086034085040b6074110190750900c1005a580b28400c0c0580c0303a900031180a18042c5083c00039071450584000c005290004001003080028400c60007800e0 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 313483102 1250 313481852 313481863
    0x9070504051c0f0209090c0904050c1503090601051212070303020318011e02030a06080a14010513030e0415030f0b0108060603030c031e1201170d0518010f11120c0d0c05 74
    0xf40c0595005c140d0340e4404c0411460705a41a0078240d102e00300c00200020000009501200c0ca10141d41440400d90181d1100c481e500041c1d072190076a400400040c0b11a0800b91901c4004440000440e004200c6c81c03000c41c00141e10040095001a80010030045024020069a04002513500080090032907c440c5050400801c0070b407013480c81e40020200300001c0723035600a02c02800c240c0007a548102c400c0e28003403000f100d5100d80d0b030015508100004140f03002c00c03580b4140036174050301e55480000000e810040141a80760400c1500d0481c0240400450b030000d0f540300d03019200d00c044003400e505041005260002c010403103840703913108102d80000080c010040c0c591a05007a0b1302c084242042c014280194011004200150040400001681c020340d0b010a40e00040020036240414074220040b00e00d446101152b40e00c50b18a0316800c011355208406201080072a032405044a52814880c581444990080700324100c60225038072010900920010341280502e003000c603d202416610a40c9030b0 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 313484352 1250 313483102 313483133
    0x4050f010c0218060f0a1d07032708120108030a08010b0301050109121502070305120601020c0a180b1e0411131701090b0f010608091203060d06020909070504051c 71
    0x80180030042041ca80b12030f0110403c9203030081c0000e1510b0344801c1d12419503c80030200c501f603140014081125a8009c1c4290b995880719004a01c550710080083c424540c007140000302c41a001c10070048000025000b030250203080340703402555895001183c002d0494030b060308401c68085040004205603030b041140c003030807070340c504180001a010318180201d44c1101140381c0421980005a000c082581c414018607101418241c0c2c601c41d600d4040c012a80c603200c2e56100760b0885030300c010a02c1500e410810f1070300c1960740d602c004600301002c7c201089021010060100f14141c100c0911141c0b0324040c081d132281c040d1031146403800c00480c440140f4000e0324a100e0907000360704200784552031200a41100d980140c1042e214119424181612015101c091107000d000860080c04501c00b100b010135400440440e8084290854580c03100700310680c968078800302c3c0c6c810ba080014821030340300d81000b10301c5880d01d5140c0c02d413210701d04018441210380207051150203210550003540042c0d80391800c01c00c034 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 313485602 1250 313484352 313484389
    0x140601031b1e051314030622020402070501092a0b0313060903020a060e0c090c030603060103033209091e0c0717031501030e0a210212040b04050f010c02 67
    0x408182e07501c1540d5074450042e5141c000101100c002c50520000030400000c0d100036000c54a05945044a910b44200800e511541d0503d03c50110030243c60203401800307e40b400b440000590185070342d20780e05500c060302c3c00c2d0340507400c49540804040c00032494072030003004802d04240c0785247c0402c4490300004440310050070155202440c4050510810004014950240040045062550885640d40d00e03c0308210301c00e0031010300040310080214203580c010840a0001c006990031aa01610100070104800400c1d0808001008040c1000e0120281c00c07000d1490507039544414409101c0011002802e003034180c41c00c151410300082002c0e881960081c84c142c1c25075290310141c5800b124017404441016400c42001c000e0000010a03241c4400e0400000d03203040203601043d2880a44800c40001d01405061318808802427482005442100709401d81c41950b28611140714081425082600b10030600e190100b07051015007040b40d65285407400909101d2042c80707007030b40043d80c4d950f980111140b0 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 313486852 1250 313485602 313485647
    0x607030612030e060a02031e0903071406091201110d06080105070c020d08090103090812090105220b04020f060412030f0305102309072106050901030201140409140601031b 75
    0x245403082c0306030742c5c0000703d1007402314049a440148000302d8004c0705c0c03503501c640100c1c0000074a403044c510103030341401c0c4041e000a080200c0d490030480000050601c9103019520380020f171902d044564002e0400004400300059604d0070300901e28215580200b1400034001100859000b5030f503600650402240d0240b00c0d03035940c08031607004a024209148008001000100f0018103d5014440c000e100d00d402c032008000315510110703c15090034030b020703203003807038850102e03203280801c920341e030455805400500180300401064000c90170743e034040c1d841260a01340070680340d030416a0040c50301c051240c0701c2c42e050006041c40c004480950381e031441050300368111030300d420400f020000d03013900103014003c14001c8940b80006000d00a110080145030003003c4c0599502210519841ba2500b43c45019062040390380c00c50340195280b040003280020142e03018040050140c3c00340c00362001c1e441a5a40351112802d0060014060b03030802840e2000000c0b90124030841284c0c444502034086e80d05001c0c004 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 313488102 1250 313486852 313486867
    0xd021f0b0d12230f27060406081501020703021509030c0604260105070203040909030c0515101d0f18030a03060302010806043b1911240f090603090607030612030e06 72
    0x5203810700d007070781c55001b10b00031600089594100251a2180c0c41030290f0814100301c400c012078403804c80d4040258040b42004903403170450f20500251401c1c0002500721216103200400240d100d4210b41d01459188074014240d42c0040781d407032805815000210b00a11290600074000394503409135000380c100362952010700e001410300c00c1e082005c5068000c0c003511428450544000d01c040e100b100c2d420180142041d00286114a52480325071110012203004c4050b02c40f5441403204000290200c00b00c0440d0300c055041c040014801048855070588000400c10325500c00500064002496207210318580211840000d0010480704081c01c602c510785c41d02d0b003c4200400c4072004100b80d00c1d01c044e200d5a400b1500b10f140703a41e102160503008480e40c08051888800700311219100090392940180c1d0041041591a1030070045d12034030684694050410102c603000c02c000e41c10407116025544c1c009024418520741510501c0041c00d180715802e2900304c040c0d2005840010440a10f42c0140340009004 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 313489208 1106 313488102 313488157
    0x4180507050114071b031b0303080609060d0213110a030b0a0b0a050a030c050d020315040e1c0e191203020d021f0b0d12230f 55
    0x1880d1900039a15000ba501c010041100f04800c3c040f03006c40003c2800c0c20983c54820281c444070007003803a41c200100a003002400d2540291903402c18013100f612040711107082103405589480200f001e0816040050017540542410004007080000a20794550421051190129222414103403151b04407913080c865081a81c011408c10864410310070302a0300b249183c004942499410310700e05034088001e992040f2030b440561026800e0700917440c900351041c50201005000180002091800704500d441c03420281c010a00100070741e20081580c0f8a028001c80450440c101981c030f9a43e10b0040701030403140316048000d030141030710f0346001510000b607038040031361540149a8860801441c1000610035440440d030000c000f8004940840c51110300150680c1a0399160030443c42030042c43c4604801c0140c030761706490000c00c203081003008034109403509000452040c83c0520b00c2503001 = true := by decide +kernel

theorem cover : BRFrame.Cov 313309352 313489208 := by
  have h0 := BRFrame.cov_init 313309352
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313309352 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313309352 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313309352 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313309352 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313309352 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313309352 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313309352 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313309352 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313309352 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313309352 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313309352 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313309352 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313309352 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313309352 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313309352 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313309352 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313309352 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313309352 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313309352 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313309352 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313309352 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313309352 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313309352 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313309352 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313309352 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313309352 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313309352 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313309352 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313309352 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313309352 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313309352 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313309352 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313309352 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313309352 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313309352 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313309352 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313309352 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313309352 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313309352 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313309352 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313309352 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313309352 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313309352 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313309352 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313309352 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313309352 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313309352 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313309352 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313309352 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313309352 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313309352 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313309352 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313309352 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313309352 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313309352 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313309352 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313309352 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313309352 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313309352 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313309352 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313309352 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313309352 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313309352 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313309352 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313309352 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313309352 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313309352 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313309352 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313309352 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313309352 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313309352 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313309352 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313309352 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313309352 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313309352 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313309352 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313309352 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313309352 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313309352 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313309352 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313309352 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313309352 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313309352 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313309352 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313309352 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313309352 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313309352 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313309352 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313309352 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313309352 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313309352 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313309352 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313309352 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313309352 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313309352 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313309352 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313309352 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313309352 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313309352 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313309352 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313309352 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313309352 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313309352 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313309352 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313309352 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313309352 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313309352 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313309352 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313309352 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313309352 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313309352 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313309352 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313309352 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313309352 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313309352 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313309352 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313309352 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313309352 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313309352 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313309352 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313309352 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313309352 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313309352 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313309352 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313309352 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313309352 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313309352 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313309352 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313309352 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313309352 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313309352 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313309352 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313309352 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313309352 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313309352 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313309352 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313309352 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313309352 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313309352 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313309352 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313309352 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313309352 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313309352 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313309352 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 313309352 ≤ n) (h2 : n < 313489208) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
