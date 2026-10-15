-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4150
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:43:17.488996+00:00
-- url     : https://prove2.me/submissions/f20f8460-d56f-478a-bc80-ee884ac6ad2a

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 746223021 ≤ n < 746402877 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 746224271 1250 746223021 746223031
    0xd0501090606080402010903110a050402120106090f03150c0c020d0507030b060d080f0d06030f081c050c190504051c021e03030703050906131e08012309011b08010e 72
    0x61482c0404c40141e034410503107026030390301c200460411550400030a1048130250840d40e0000d20014081d090707080a018850304890301039807910403041d2600d09842d00403109100007451402c1070846845082d4407a04201c03148100ca18180364161210340000d00c100034142d0301500c0f240c000b03d50520601c6542c0000f59030090301600c009040d180143e4400084d4421414550490700c40803136040444880c03134012000550700421103054001c054200700b02070740d0201d2150117550021070040c000780b00d804e0103414481e01c40d02c400c2c1e904080304207510410710002e9032005010050104400b0a4035540c118202e03a00c000c0f2807a2001d1040301d14418000805200d03041800c64400c8454511b40c156800805c0f6012140d01d80f52070358480340040302044040c0501c4da2180316601c0c43c800d001c10482045c041d030144000d9006a03031552183d44003c0542240d26010390f05650710002c43d8003002003860300d511282c0046071500001b83e11a21101c8501400c1460746d040b500144000d0010021560921a000d03000 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 746225521 1250 746224271 746224277
    0x3010e15012f0a050a080406030501090605152101120605060f0a1203020109080f03220203100908070f060209090901060f030f230f1009020a09021308030d0501090606 73
    0x50310070200c8041038802c034411420800e64008181c5101d50070074000f103800103520000710348804515141c0303907816030482c0c06a20002403800d00005918103160003480d007140c101400a440408541444161039842041609a040010f00705203460405840c01c440c000c101c5444050000e00c070350320740941640c202802051241c0130700301100c0c040ba51900b002e44102c030800e0a01c01140f0050b403405901421000c0c82c050140351002c507940303170302851550013588141c080700b11042c1100c1407180613050811881c03201942584c0324215003000b10740c150b4400c041260040409a04040d0035949098500808041c1254180d402203000600390800050240e048000c12000b132000c5400c1c07050003181c1c1690762201a20b5070807500c1c508001d010442d0905034048803417259404000031040c0b20551744144aa0040c0c00e030340300d4007081c11007000c51441604541540108209502c910344241c50001e504041102c03103155004007000100180700704001e000d66150b04034040740543c074102119040301d05940c0100d041c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 746226771 1250 746225521 746225537
    0x1b18060815091c0914030a0302060c030703060b0c150f041a0403110109030207080f070503032703060f0a0b0a030f200a06030510120213020f09040203010e1501 70
    0x1218004903800ca0704048210002695a81e0152420324001c904800d5184426401036110b49255102c000501540c82401103ca10032000d00f05155540c00c0600000d00180c0100740032802c10401d0100458102c0760506d008106242c03a900c0700301c05940862141c66055014864032241602c14820050f4001d03008040d481442c030f00380c1c07a43d903040d9685018091000d903900b0002030425016200c03482911200380d000300b00300412490f0207075440b091806642e4551144080c142d40584c3e000902c0c400b6187c0141c007550609030040713800c45c04900e00c0307010b0b03605109444100403426202046071a10900e40e55070b1600c0c050400e03e1a210403185600103490080180c8181071002c1009400e203400c045510646441034051010001c02c40c0480391032903141c0c0074408000020355240e05400c054000c08900e8280c03500f02d40e4806d076106941c425008025004440106c40408001a5501904410b00941d025034601014080020104e034400d0300210800402c1405118442c000900400d85211303081c00c0c035400c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 746228021 1250 746226771 746226779
    0x2406020c0a06031e0c180b090f0a0602150414010507120c0503010e01030b4b01050a030b0a0e030d1406180a0b1c03031b0807080406050901091b1806 65
    0x250142c0307058405108503486175104a03055110721001030518410a02c0301690030b44854004c2c2c0c3da035100d8071a4038031072040d1418008244c0b4145014a045071201c0c5c00070008194001300c001000180240103407249868808a80c5c080309003801183d110301119a184244003003110344d00700886010131003c000300700c0f0910042c40800e000903040b50540390072800d4401c6960714038220800744010400800741c2e00341c2c103a1082d0b00089917140402e011184541d480c00b417445003241840e400840c240301c2c180d031100466904202080f212040160041e002e1840440c04404001c81d1718995031020004601150f90307011030100000e482010650070030411030b09086132003100b0580141c40203001e401c00540c5540c40307494041d00d598045884c141c050401140c071170302c20a1410060020400d00d402c1340c110000b80706081034000e102d0b01441d031050b41c1036100c80681d0b440c3c5031204030040100404a1361590b5a90701c00e00c001c104a0803c40401b9840e5000314500c490506e010040741595a005c83c180ba90300709a8140 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 746229271 1250 746228021 746228051
    0x1e02061b12010501032c160803030402150a180b030f0919080f0d14040b1006021c0e03250902070819090b0408150c090105030a2406020c0a0603 63
    0x60440d00e003440c02040742240c84002099946d130080143c1c0b81c00c144d080750040e039100c001c0307880441801100b14010a0903a03641515440e44001c84000350301140c0580c0c50805003690f40041c0804c2103d500d80380c0c0c0030981c0c05102d440042a6a00101000200030003080300c0a0a041c0407645d01c0350012014003140d040444000158100102e0020112600801c62403103601c490b00070341d07201d07a5240205001c0988580c402c46800311007680e05480e80b40061000601c034180c112483c00445003181d00500000b081155402e422000d90110001048201c0c074204440303660400444c03400c12207101b07205c1046040b441c0440f2640b22242e102c4102140107001d500c01084c0d400f004d0740c8114507858850b001c0030034001d41c1154200d00344e03048080303043c101040c0469070082c0007404814942078030358200c0c066118075105045a01510045500150003040000d05841346d941010b035421859031140ca005000c01c0348945480101074000c007006a0009407045614608403400000401d110b05007006001d504031000 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 746230521 1250 746229271 746229307
    0x309110a03120e1f08190c0c03050f040f09150623032205150f10140d02030d02030d140702061f0308040e161103191e02061b 55
    0x414000a10202c0c1c000e038650361351400701444800044141c2c100b4101010300b0103402901c17141c42440d0303008040145014644251550504541c07a8888078824a83d401c5400c0d0348000c40a401c4100c09000c000340c0c0070007214024021380780112b400b065a6030400c0d000000032100364000000c0000310008405001702c0a242c0304210400040429620342c0c1d03141c1043c40c82c1f0741000318060384c0080100c0790001d008000c82c502050909510b0104c21644905003181070707803201543c40320400150501d08002c58480c51402d50a01c04001d05242802c1c81c068001908090400803002e000d40c100040300c001c18801841342a180e005054031040040c00d001c1c1c4002d617074a40c014416000385002c14140102c8100000c0d42500459100c040d0a51b159100c50052609050561704140a89010b40c2c0e1034411030f008000e20300d0b403820007600840c00c01800f103400380e00400041106d0030a02c0000c0c01c40f2a054051000a2043d000301e5800800317850521811022106042582c070b1300d4803400502c5905030144041d520 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 746231771 1250 746230521 746230553
    0x70c091a0901210203061602060a0b1e1810082a011817030406030515010f1d0409060b090f0c030412050f0a030f05010816090515100309110a03 63
    0x31009405030030003101002018122406076240c441c040400c09484407c40440c02c0200d000c2c1d0a41d01d4039200c420340102074411442000307502c0071011240340300c010756a840b240b01410f030060401d4a040380420001c82012800e030380d11201281d8000052003200c03c100328800c0051000314406102c801448071303d01c01e042d51380e42101c0c1048400100c92040d000c040e24102c010341200164100005a0051a0341d580d81c03051244001190074100014006448003100c00700c4010180c40710b04140383c1424044070119602a00a080307908204071250003522180f0403e400c061040c03c00080d030150a40c00c02440840040100d80014400300401c80b60350800b0041c2ca401c075502c00c840f00040b80110000752001d0003072900800c0802c00115603010b89507895005409044042001000580d1b01c528456840d00c90b104000011440c0038101000049076a44c0004e900007119101c01038583c068500040248140f6aa07650010740c6500400c014440040e011501000c02150780ccd125a44c50341d078035201d002ea19185 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 746233021 1250 746231771 746231789
    0x906020c040209220b030c01031a0114040b04180f11070b07050d022214060a050c0f0f03070501050c03040b19090503031303020f010207110d03030b0402070c091a0901 73
    0x180b0408113031200c04a000c5041a2842080d10103180011307014010401071103c03c0c0f092141c02d10b144c0103940244900c401c100d410f00a48050310610000554038400b80f01c80e102a044d10801c80042c01361103001c085e1011340341c21801d40c000d8800c1d84200c0403d54955070544545140307001e0190030004141d10031145000d03440350307528406549100c0d0940b400e0094800f1504d0803400050405da04d403071882e02c100001a454440c0007000750301c402440c100c03245a0308103a03422103400c10140c0140340c014005400110000e03800c46007024a500c0142d1f041076001a1110b600b9840442d81c501009002c1c041c176584030100e500e146041d03242c251207444114501a14826001c8031343c6040388603d84858206101d0550828100c903980d04100d03100c1e000c00e02030243e0607001800b500c1d10800c40010103000b11081940c10152035452116414104003002203150012024595a280012507a0321a0f00140c21018020441c80012500d01907248095480c82d11002c1d40001070662441101e558180016042d00c01d050 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 746234271 1250 746233021 746233027
    0x1b06090303180f0303120c02060103050309040e070f09090b090a020303040303080c073e0d020906061b0601050a060e01120f0605060705061b0a14031b0a0f0e010906020c0402 76
    0x203104554020700c2d50412449058000404424150003444103442481d02c0300013080045900b00301262500700c01e01009181d80c10030003c1c8102031609030491440d8000e8401a10700050b940c04486d44c1480c0141c0c09070201a848000a03c1846601c02400d988180f181014101080595000984900c2103000c020f0510024001140c20302200c10262150340390310603050712080300080d600702d4030703005082c684003113003950000c0044018013031101e8104140b4010385001580a5950b0070081a090b00600d815081501407012000808041d40304140c2200403030040c00c0710394140002e00400102d01d81100c814000c03042031204442c1d03482107c45032105240c1000240102c0c81c1e1111401905250b48205d9000781d02240c103500b801008200ad030700841500007044502004403c0c1c4403402c1c019903e001010408030b60800f41c070200070100542e8401d007102d00c0101000300d0920049007540001c164100003030441003201a5498110b8107600340c400c0c003400c04416080c41e1a00c000d503120100007060340116004 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 746235521 1250 746234271 746234297
    0x141c0509210702150c0f07080d0311160203011806060f1d1605271e180c13120b010b2a01090c120303140f07050a0c0606080a1b06090303 60
    0x540583c0d02d02000002a0b804540c800d90186031f40700f8a40c05043d90900499551202040c003038450205d007120845c2c3d440c4e082c02500000d980b50000841000d9800d9522070446103a000d411000d1074208520408000900905010010340284440d410946540445e05654a607022600d0320f2154000c0c018030961a80080d6820121080c0c003c8d52004003807103901c1441c010018003076003041d0348440f00c01c0d2950920000ca030700610500350492801c40e0b82165221b408003015940c11226903034400d0661450f140b914082050701d100c0c0e881c4e07035803003606060700d40a80d4400b000403582285006040a080791030819844101a40105010a0010441c0f00740b008480f11303050000e40181401a030020f9000c111555500c881a1049140c0101180020701e04414482c407e00071042d69405903004100d104055604e00b50143d44035442100600c0500400f4400c140010f2100d000f010b010344511405490b903c0050b2802126001051944048184614805119035035205518070116a09450400715038411307 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 746236771 1250 746235521 746235559
    0x70c021c0503030109020a031a061e130b040501030b030c090637050108091c030b0123250209070e010903060501090218040b010e01141c0509210702 65
    0x152440003070a5001c04000020704035610740c017500d8006059142404818006103019924841e034820b04c90740040b0a024509066442150404405a0720003c0704d142c4038031107150306001a100c0c1d00ca001d80c1a400102400296894090100c80341010380007043c034400200001180c2d03c20050105015455040e880ca2410504550008a000c000048040140100300e00d418a6007098015203000c0342c074000102d0003482c0c00080000c1c400d09902c07512115842190012005440301003115410000303a8800c24010842c0c4840038243c0c064410101c40e55805500e41c150440d100303e0400c0350b414420b65040c1b60150320303139102060b880341852420480b20151100143d5140e034050f04080c2c1842d280900200c1d03552656401420044400e0100c180101c40d00380c00c000031349a00b84009400034100054141c025402500009000350f100802e050909100c40d04075140145042c109000954580c800c1c0510184244021403d903003a041001003241e40f9240540c60a10039000700a00900d4220901c05186007 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 746238021 1250 746236771 746236819
    0x316020f0609130c030b01050a05070b0711010c030f0c090503060a0b03031312020102070906180506010210180b0a09030203040308210f06040c08010f050d0503090a06090e0a05070c02 80
    0x3030024001490464121000f00052128224441c0070a1800c80c0d07403070280d030145042d24040c51013a03442510b400328a81c1c0d546c4841c080075100c07009120740694190041282800756044c400c03043e0b540020300714804140c0905546401e15101c09100d08500240aa07131404503001d40d2004400c017004c66a9000d0320003080c554845c0c4070b018650300c0300140c1d011401800070381c001b07241c0b98001d0b82210b03845030722100c0aa01f160a54403031203990040c0001d00c03d40e41c0c80c0b541c10960340944140190f4225030000d000b50002d840184821901500c0e400003120200440303c110340f80c22401b2104204079180d072a1f980650baa00c5035010180013118041804100d200111240b00085290046482c080d401e0503008441140e40981e04103118a04082d40142110b1191043c00e040361340040032211480d18017801c2c0714101000d04400c0d102da00041000c50680e0705c070104513000420791907480d207000901d0050340311501e0401401c42c0c43c8042c00c200903c030390198040303030780c9a20783d8045403c1d003075005c2c1525800f00303886 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 746239271 1250 746238021 746238037
    0x160807060203040c0905060303030f0a05040312020c030405041d031210051906020c1806010c03020724021b030d080a02090a0801020d0e0a0b0f0c0d06120c080316020f06 74
    0x20780000100030801c04082220b0b01154030f91481442951a03032002c0507160300040391120b40600820000941c104200d4128640082c0030342001207450250f80c94800c1a80d00244c0f2001080d40001820801e83c00c0c00d2181d0010120800310306026803042c4c510040e120702c0740226402241c21448003243c50b420000b6003042c01032000808243e60b00c145903103e429048050301c03d240140c05003290f4040c0d14100044408003442d415242c20300700313982d45070043da1750240d1404142e003144956140030616001441c012021980f03c07071450090b0034420380c0000d14103580041e60309582861344416054903240060780e005000e02a0400d0411a81e441c2040f01c02402610b02469011144003c00552120190300410ba20f12140d54144041a20030084507903e4510f94001006180001c0004003640006500d0541040039240c40a240c68480c280c083c06031466074201c004108030200aa90401207418002402002018041c5040c01001c500c0f1400f841c200840182c00b82d100c1180112055891200f116520 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 746240521 1250 746239271 746239283
    0xf060305070212040306060e130f081812060405060c070b162601030c17060a020a05070f2f10031d1b09090a020d080d110f03090c04020c03160807 64
    0x1302c0ea03a09010380502428859a030402c0301e00b2006c0381801c6046c1508840d0942c100c82e0400781a145940d403000c081d0700091042e01810102c4540748025170703400c910390001611060042540f0b08080c14a10f007010000303042c4c240c07601c004000307400010f4007000340a6032000140c0074804440440e80030079a414082c8441c1284000102160000d00400507011581680e0107400c2000f48251201c42d405180c540c0000101044da000000141185085800410307041c100d91420504000e0300340e5944650141d10102111400442048062501142c02149412080d04c0001c1102d811020f00420010380d0bc1a94040070540c80c0e0311002a139000d201003c800d181680012110641c0100f04074003504481e0310181803054042d480810500000090200b0070075400903c4086600496998080564001007038601350b80d40710042c4040e01004000900021020301000d079541b49481a443d5080c610a6131016208a10501c00341510100001c1510440d40019041038201c00307440c00e00e00510f0261140007052 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 746241771 1250 746240521 746240527
    0x1b060207050102030f010f0b07020607020a0801060602060702010c1d0108090f100e1c0516050a06021b0f011515050c030a05090a060801140d0201030b101d01090f060305070212 77
    0x308007055009510400b1640c1030615141d80b9110300c401015040d00c40c505000c1420300c020800351a01c1e8000740070940c40106082a01d907036a403440c40c29215598000340140c3c01150401402c99028056049504107520701861a031000d101c29481c01d209601815041105420028030404803c1002c02003030810242101c503005141401c060180c007000e81003a04600500c00320b4984000070015076840045192206802c080d801c8805291000d4540e4090f9000e11070468080c02003409480140380b680341300c013622800e00b0440c8039018a820b0b6803a810820300e030b140c440d41070030780e0304542008001e4810203000c50001522610f400c586038021754205011500000954040d2550464020b101c0c1c1c95069640c102c404e541c070030040d18030318801d1141e08005004039040c05c01c14076100d0700b07202e0018814100000c4e400495004298030f00c5004c00c490001c40d10034a4a58042d0010b60140382d00707841e091034101c0c0007030304041901c00b510b402c51080105160301d540c00b00e80c0351030003403042d0102c5400b06030035252 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 746243021 1250 746241771 746241773
    0x70507150e0103060f0614040e0702010209040b09090607050c03040321090e09030a030c17040c050901090e330403180902030603030909070201111303060b060a0207061b060207 77
    0x440d0021044160001c1203022030349031440e50081c0150070885d911801d4005d06549084030540f80c40d059403a40350b144060070480411644980c00364035004201302d900058451841109000450b40c0310341c0701c1b52240104400300980c840780010794680c0018541b03007040d1550103200c5490700d5409503800042c0b01600d0003401d481804a2014104940c80c070039507510260300e030341c0c4441154803901943e00700c0041d00700300034032241113010340c114000707407505483c0c518048030f50410700341c2d01c4140640d4106c030705104600c401c11003407409421300350142404a0040080c4204945002d640d40f104a07901204c01d80d41410800c1c0d1200c804e00c1c0141184030404810040c1e181c6840c008008178401000c81c907113814001004590240c1c20320036a4443c800180007540f4048002c420041c2c0113400a000404540d20703402d440c4600e60111000e00301c00c2c405000150b01807415441c0040548150341329450040f00288110000e03643d002680c50700b00e444906000c0e500240d1100000d11841d8562000382c80d8500000d0440 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 746244271 1250 746243021 746243039
    0x302062205100201200909040f150203090d030c050a090e181510061403010b070c0f0b1b030f0f070f06090b010321020d1407060f06050a090504051903020102070507 72
    0x641410208401c9245c2c40e4a440340700d020307004003480903410008141c0010006041200d0781006103001e24100c211084d42401660706a80c0200e880c1102d0350041460b04030317025054051800c3c03071840e5041c41c40c20b14906000017014403c1520072035800352580004583c08401684903c20941140781c10364036044d00309101170300b80c00b80035107000c0050f069504c0f00240181c41104000035016000b2203e81c61130b440c0404c0500c094000540988a6946c0608002003000c01c200c1e0040082c40c035000000d40f50064060300d0000d813064030095142d650410003815901c580740c4d000f02d0b54400c1c25071190ba52686010b0030b2410040b041c040005003001c1c501401401802030307480d0041e0481b032040c82205103e100601f02d14030014000d1079101d01507402600340c481c0603402004031040e1241c40078a13260a005413a1104029550740300c0141e41200d039121001d000504054a01c000549499003080c009030800e070361040e41d1101490303203100f4101002000700c41014402e40440303028640110841d051240c95940003 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 746245521 1250 746244271 746244281
    0x302100f020c03070804051f020d0509120d090518060f011107091802150c0a02040209031f050114030d09120f0b10080d0311041703040308030106050903160302062205100201 76
    0xe28030820194a00b03d00b05d0480d83e48044070b00b0002c0d80544882240c08405582fa600245001940000b0803000f0840c1c0701300402c0070034601701542e520000d50a242900b8458440110561240d0b403c521500f0080c1c2e5482d01d07116406100340030328015681c0f0350103107482401e140e81900103c00703ca08060114026841459000348818000c458100b0206031480310051244500702e8441000c0d0001c1c203101d000361810750302504000002805071468613815010707502d01440d0f0503946d2007400e60794230014440619802480c825105040d8020700050029800140940b142485940802c1007035a00e602d0030404078548005c126a070002081d8400d05004072540c2260f00e076401003400910440003200b407103030320a000e0b0703014162800a01615242c14283c58280e1005c628150200c03600c4100000000180880002c50007010199152502c9034903140400d41000c45107010015207940418052025036a460122614001e6404000007007685d000da84020038525075202640c844507580f04410802d03019089 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 746246771 1250 746245521 746245529
    0x5041215020c070803030a0612050d110c120f060702060402091609050d030c060b0102120f0309011d07080f07050a061116060c02090604050f060918010f1a09040302100f020c03070804 80
    0x34414227480e00d01c4001000c004000181140d400000d000304194042c1c64004092a1080c2c00e0702c0c11034054402280d000802071704200c50720340c48000c1c00c1c55100720520120740c11079510700c00341580b402d042d0005206000c01034000c10340340c9038244001a0b02d42c01854a880242806054546010094280509111204c600070703907a042c100040f4507559072001c100000320740460346140d4141104014054003d403c010000400356580c0c505036a408145504c203070114800100040c011642000c200354105007020300e0000283d441104144a07641d14a804041550ad00340791049101c07092146091030100340403a5041351030300445000c03030340030b61262142100314020b540344005515003d09010448504841c3e521703842007000c01189151524000064001c9884140b81401d2881c0d10400c5007111000d036101c2000702d0b0358185030407404141c48065180100115044581c0740303069140a03403503e41085101007455a1b40512085840155040d621948510b004490f1901694500b0720f1080e803141c02 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 746248021 1250 746246771 746246791
    0x70506070e060307030c03020c010f091e02030d08090c090c0c16030804060f0909020c0303060a0e0f011a040306060803090a0f03030915140c0703020f0105041215020c07080303 77
    0x285a05018100d07015484201400051075a41c0d0b44004a00801083c18001c08140d0200800c41f0254400d009014503103490b103500040c16500c600d0081a108c0d00000c20441d00e40c090040000035a40104042c0b481d6485414030007040e070b03100010707a8201840711101690060881c801e21980c91111006011034081c0007040300c005801075443e4408204851000518440c002c201c02e000d410300c10591f505124000d410106c80441e145c51108059802c06a40c0b4401e0b540040304000300b074a410384124004080044c1c000b1780d5424032084002d40180140a60075031f4120b400031a201c00d200038012a00156046130040001030b48071100c4036100e500c0225550f02c40c0b500a10302107448900c000d0804200c95041c0c5805e4003080c40d188061500c1c0c1441e80403002440115450050a085100018405503844401511189095104108240403114642410000d050200b400810588081868001d80000440598142086c81c10f0064464400b02c11502d010300d040014180c080040075501900c22a1 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 746249271 1250 746248021 746248033
    0x13030b0a090b10080a06091a010303170709060e090402150f04080105011509090b03070513020d06090219050f0c0d2a0b0105120c0a0609030308010b0702030a020121110705 75
    0x14400c81400110f60150a403a6007250800800240725030303011036081840f86184090304003040d032018041da03001744c0c000c0c0d010600b04200080510030781030359554032109506003103524504114004045456040004d0702412140003c2019540c4207404074100300c07a030690a40e03442c450112005e1044d007182c8600304c8907600300780c00442c58542140100c42d01c200b283d902e0a8035107103040301e06405041e550342000e0305030080b03101c0486c542d226880e0600c180c0c0d25500001d40d82c1d032010301c0403008440b919030005412900c1804401c0170016641034000c038204507450565194154403401c0c540600c54103690102c2172180e001d905611a401095104035803801a80030748401001030901c006402e0744120041070f0a0305040144140c1ca001c80e000e010301c0c034400302120a075540c1c04000c500304511903005000401c0b4045010410107501038015405000004095400c200d401c0d1701090b550503254500905004004010765120040810f0400e4103c1980000340050240c2c03012000840d4401c51095075140200 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 746250521 1250 746249271 746249281
    0xf060b030c220605090f030a03081f1d0f060d0c0b0a0210020c1c02060412031a03010c0306080c0f092811072001140d0617010507030b0907020a0813030b0a090b 70
    0x104401e42340513056200c1e915250713100d0308481c0e5003440380040b003102d10300c0901c00454a403440041402d020314000102d11031905002d100c21159120007811503100c1c0c41502002e00c00070341003010080403a041411a21340b907400c1c0c0401a4208811a040810424408541402c0c1648006085400c0950600c2c100d03042c0041003000300e0f160300c01190701074000c0722100030f140000c51181d40500c0b1080a000b120042403641700300000d09540104d10701c400000e0329060305000318481808150b00401d411110380b104110120003280e403122006208118406103881c01d0b40c209110141300102d032110030601000b14044041c600480c5820100040c3c411860f616000108a40b80d104840501c0c04143c6544a40e020002c003008400c1d40900d20130402a81c4502001841074416100c0050440c103d000209092600040081c02c980c202d00b00f0074422007480f030500c1009600031580c00e803410b81021201d0b0780c1d84121003080c0c00307501081e80010a51420442008000300190340502c0c40e452007803001e2007890700c60b = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 746251771 1250 746250521 746250523
    0x20a0810060e090601090314060906060d03120b0103110d0221040b1503030d090302240103080a0c06092109050a1406030406060e01080609010f060b030c220605090f03 73
    0x350003140080354044600c8521071a1045815610150502d44049269240c0d07450a076041800b9034041c0c060fa20a87c144a0840001e108595109a00b03a907a40d40700c404540700103100c000c0001c0b02450b000d03584c608490060344130740c12180d42e46640c00901c541e2001c80118100007540b00c00424903980b0741c8104a0001c600d410080c140c05181c02a0000401d61100c805a07000003401150696151001300700010102003a40503981c1c1039030098010b842d05600800c0c2c0501304180e10f0a0144010220b40300500018101005850300c840191a08290302031141c58607000a02c1c9184c006030090000c144440414041d403c0074040b01843c41c2c0c0e0300e1027004d54920910112882c507004820714041c9c000d1004180e4140000034650060090901003007aa6440d846100b5030310b004e0300071800541003030f41080b9180e40e09000b161014414000c00300031003450300c0c007210360034007007d800106410340003d1400398034115024100d00902c0046010281299102d6004c0c140364800f1180601078480d0709409001490 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 746253021 1250 746251771 746251801
    0x8060103140708120708090301090c090c0806120703030c03020708030310090e0c010f14130f030b130f0f031107060806030f0303040506040b040f05010e010f0f0c0f110106051201020a08 81
    0x1084d00e5a01d040c00425a90100b1035000b202d2091740543d6030784441ca010842001c0382100910301500001241d48100e10b000b44511401803555000d91070107080400d422100140080480b505450102a54001d9180403800d00503035601c01309041c8804810f01c018101c8810101089030080c000400c5034002020f0301907140c03550368010f140807900e0a8611040e107030203142400070920206800e5840c1c10f41d2854000001800b0307401c92103004102442c103208000c1a0b240c1241c01900b20541c1c00304200c4a669401c0d028294807500401174041901c1c1c2c0d4003050301542540b68004140c0d030546240c0358944900504010003151120722a1140710107400705a4808000c980c001d540100190003290b459864cc80e144410160003144d11030340410032030300416030a1203090040c1c84403c0c00455014203590080058600b00d90b580d600051070100300f024a0f41d0020342400c043c0d140c0c3d040c41484000e01d090154010308440d4440b90704900141055034014406600038008401d4680b103c1d82140c07615180281126 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 746254271 1250 746253021 746253043
    0x81305011716050d0902040204030c0e0c03240d060f140a020f0f160813060320120613110301081002040f30080706050106030b061c0608060103140708 66
    0x41e51000c0d10b410540c41000286810440c4544c0032509520680c0030808aa0044d0f006507900c00709414140134890490300015004100310340002e041d81007039849142c0000307160010654111503004a80c0d81c0f070f114044c4e0380c4252504582e00304101c50250303140c4805040c84c3c0c00c10340d00c4c00000c00009141c1e92403610a840e41c4682c02c007003503030030101c10b544808200c1c0d00440244c0b4031201307040e5011000448074001050300c081c80300000740b202482c00c100a420b0362111442d46180d660642c140d81403c44001056500040c0008512451a1a50004980101880b002d03591449060120780400d0000040003141208c03025400c0301d025407003101803a012401203016003d85241208001c018420306500e4091240300c1c600c8440800b5081d0480581755540700390001c4616020220311b0300c0501045110307440c01404a0f040610030301e078123100003600902c01d0001e21900d16860080d011420b15490f440300000e04103010459685d940c41c0e040581459203030300c2c0da04c1d4251151010104010402040c1d5440c50 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 746255521 1250 746254271 746254291
    0x12050a0b032a0126161d220603050f150a090b0117100507030605270c0c0a020a0306050f1503030912010b04060b13080105010e0604180813050117 64
    0x44030300c003401160884c402d014040c0009448118004040903400c501c40e00032081c4030341042d2102e00046002d00109030600586503181141d4042c00b00c55191078900e640b401d10103d180b01d2a20682862100050a041d04080c001e4810784c8110903401c0340000c4d0000d003000320291340700d41f01d0340d60000c25001d0b074001d808000c2403607401c10b0040101c0c84007000d8090111f80030707030f080d83d80d400c00d80303100c003c12140300325072410000751144005c000d18142034140d81d0005600700b20755200300042400d03080c20050701034070b0841c580d600059a034003941d905004070941c20354003c088050a581da410400d000c2d290590b00311a161800d41c0108604041c0c5502c01400024054040c5043c40502404c01040c18402c0d00c10000759500c50401404036070f43c51240802a08400203100d803211001183d807112511035400007080d50b80f61200610103900d100c2c5083c4d0303100d02c1c00c46000c1526110789030144240fa8100c10000c0c420000030a14200018240061005840c0280c1c2c40b0314010300341d200c84d0890448203440000341 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 746256771 1250 746255521 746255593
    0x20c040b1005070f0f030905090a1b08090703020604140405011707030201050706020405040903020703230a020f1503040b0103200f0d051212010806090f0d0f12050a0b03 74
    0x660b4040d5010b001c6103802500030000c0754049441c0c0c905094601c0c2001c034005005a2420700c62460320a510365001454000100031018001444401c291080600607061140010000f90594402c00007040519805480350307031181d6881031000280c20035400b0b00c0b0b1045041c48004222a1610300e07503480e203841a64000c1412a146800540f200d0b8444102502e40c00d03001c12000c125920fa9005100040e40300c0e5008201039855410b00106094240024840280d058241c0901e507000025030900036540450304801d11292600001d01c0c280503003180b0740600c40d0040208024031104918240c100d1303000703041030a0103828504070118104112514994000c10881d5461054201f41c108143c103107100360116800386422082d0040503400948070303600c21203948401401145001d00642c1d400c005010000c05001c240c40f0001c945900c00400c245082140030f05c8940344a41c4540c092082c0841c49031010000c03801c20b03042100183c1800d0700654040d01c1744281a842c080d80c042e100c82c0082d1124405055 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 746258021 1250 746256771 746256799
    0x8010b0303040e0c040306061202010e01030e12031806010602060a060e0c0a0507020307050406090c0315060f0c2406090c080609011205010e010c020c10090518090109060e0d020c040b 80
    0x143c440044c061400d808414030011002407910700c10040a0030350035a1120f020501440010300c0305404079030b154101410411070045034030000a030101c1a007540000543c6983e00c00d0804400c9a1814035400c0b5248a02400040e01a401141a03030241c83c80380313402d0050a40b151801e4000500a84480100000801515540030700c50000b910a41c0e05c0102603c2d40503980d40300290030303100c3d00c2e008128503070b665441032500d554045c450038540e0064108600e940764600314000c1d0004154400b0343c01405000c441c008100640c00754041c020b1b508503600203c68031000b600d60301c0102102e005940081d441c0014040d041405070034003c0c46107000804902d826800d000e40210160780e00d00003161950740320751456030b5000003801101d0410300d80340c1c02001c2c45d44a0404202049000040700006d03c620385000b80550f407144044640f103008003040b21902603d4000980b801400b2100003e00440e11740300740440305000c04603009504007081d80c02c95500c8a826020001103031580c036400c0780e12008603a000c075 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 746259271 1250 746258021 746258039
    0x5060c030408090405090d2705360109051e01030615030b150a0609080d03020a20060103060501090e03090d0203030f040b09040507050a020d0c1e150608010b030304 72
    0x560240c403440303229041124060114050322000e9801d9051b6401079804912003035800f01ea0800241030142e0782c0650304007600c600103543c003404d000e00c42c025500c009494400d00c1044140c000d115520004004048001d0f0310383c0c01c007007942030180758071980c1407070081601e0355101a411080007021010041469107180d0b00c00c80204480c000303400e80c071071002c00c0000204c1c80e611699072040603031481040c0c80044040c00c1203034540081d003145e4103003d542070003840061000100c0d013900c00712074200140d80f013002c00e42c155500510b0b0450f41800141300740040200038000300e0014100e030310803101805540d80395403102c0c0941340c00900b82002a40240500d24192800c030f80c541c040b060000e0706a03483c001c4036004c0c0070150351160b007150a00800018404805052a00c40c0560003246442c10074201501308a0003505c4550315090401040024600042480890850840d034a540d12000826010f020718003440c0003a04078803903204852a050300010110f0040c096240d0600c4010080c0d8038043c01c04081d0 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 746260521 1250 746259271 746259277
    0x40501050a0941030c011407080a02180a0303020a03020705010206070f2001020a050a1103091f0e03031b060903070c21051b03100b09060d0203010e011803080903030405060c 76
    0x1502881c001000003410000d0490f025002c50042c20099560340740801324481c20b440c610746503450010520b104001d249030303009a03515000080b8840140c6d80740304201c9940812803510341d0640d8001e203020030000405400081000c100d62081d029609072075690401603844540807101800031a0a41040064a81c030500d507a2940608a500e05201c039002036034581c0c00c9030044003c41003c280300141004c0090b82003000e8a0b400140c1100451074100100081162140c50041007640e08001c40c40e12070141d0700602c1a540d111038041c044a072130b11030800c1444280800900556007074007681c404600d40c0c041c04011105415048901f101e0391900e4042102d9070b01c12841541d00c2284580ba40c0040002d900b403042c2c40c90551048001900c440110f001c040c01c06d1059511009003500e0000e1190031a11503007501c90b800a42200c0010001d0701c02e001090242c080b050324004a5480d003070074451402451089100303036034001c0d5560303c02555510080f0340c1d00e1000380e8000e0200c1e40454000b544407140704000f = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 746261771 1250 746260521 746260583
    0x3070c0c15030e0f031b0a1208041a070e0607140105073b0111070b0304050703030e010302160212010f0908070c12051009141006060206130209060f060906030708040501050a09 77
    0x11180c142e0901d484150705944540b60882c0018000400d000074408902c043d1000307080c106958509a060174cc1020704800b141544203030241201103054010710041e51002c840800a46000f40918a0182c0c4014400540070b001d0721150700c5041d0a003546014031800c46035a030020305903541c0860740c407a401074500800c4403403d40030501c00d03110042158502000518080c43c443d10061401a083d4a03001c0d2030400c0c0b00e01d81170b0402d84140280300e00c800181464890440d0180c600c06640008407481c980503052820040706501e00301b0b944181001141d0000300309071070048021701c003500d41f074043e140480c64403c08058502e03800129400e078800e070554007103680c45201d0400c0261060b4a840d025050034103e01d585a05165507400801c54150103001e1264440c50003084251030620581c00115407100c0030304294007910300044060581d840724030450740452002801c503500d91030b101e20b000303185482c101d600311665400c001c0854014240c50250201c0158000a9002083e0319102001d09051007044 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 746263021 1250 746261771 746261773
    0x16110102040b091e060c011509181407050a03030c1109191505040c0c02010305060126060402041703031005090c070206210a0e060609010308040b03070c0c15030e0f031b 74
    0x4c6104603030b6020024140d00c91070380c00104100c1005c40070030050f440c0035030080c040d0b40e0400241a035000f50440d0108410399200c2d5101e10841082c001040c5409080c0d0801e03508504c45500110a06030031030104121148070300f0b511750500400006005040e1025a0039040200800178500d00059098024201007203c440c1e502e58a19076a900003025180c0341085007000c01c00c43c88120007956814010554032800a0030201000300d00114801c120041c02064400c03a075100c40085110340d525501101e008103484890740024038400200c903a00da90040e01e02801c00c4045440c00503e6085c0107903c94455140c02c19142d051121540a1100c2c0d50300a4403200944491b91003100590344861100c1c0d40140e030800400506a641c420046190803406418188034002100040001610040031141501c1d40b448005460b40ca81083c1900d144141040042540c1c0e80d804d00441d0f02861850780000d000e19a6030244208900c080e14103440c1d4031004014a07031900b0400100026402c40b00102280c0b0304000 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 746264271 1250 746263021 746263069
    0x10f0b190215070306090507210c09050d121706060f03040206070b01031101030605040e032a0d0f03050c130b090a08010e0c0114192616110102040b09 66
    0x2c1c000000e074140c101c803d600442c1e17540c2014821281c181c41445d0f441003581c20900d80388441c40c0c806490f03520074030707007606d019a0b00c400100710814480e40d0040b00070030003d015090320044500c0d00c4c20034518112006000142c289072101401d00c6141025405070320301502d103601c0c0c101d10248000090741300801c22f80e002001006003000283c900c581d241c0c004c60180a1040302c004005000500b07980007984a90300c628107240c085000c8800c08411200308456402011040f11004201c00001c03020302c00e500c01090182000300400290840d040f103213504034540d0200504e94411079984018090b040d290107940303030703030200034010810200020602200d000b130100b60215a00c40701c19003542c1003c404852650011000d903500c42d42c1040101044c02060000d650030050540b0020050a6480081c40e08202c0e01510344070300014011a503d02c801c071826520312107803408000342c001100c0340003004400503410311640640e210043c803d45003601c800c07005080ca840c0e41142003101d5144c0300010650751000394 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 746265521 1250 746264271 746264293
    0x90203030d091b270b0d152909090118050607020106170619020f1305191a07031b11010e010503220203010b030601030c090509010c050301091802040507020312010f0b1902 75
    0x1e0348000b82001d201f14109106018a007078103d0a86000010030051003c2d01114801858100410031055001c2515514400d550300c0c00e40311302401c41443d108581d42800180d9106110005c84ca15100701810b4000340a056510301030b2200e1001d651614490f160032150104000c84658001340703030158010340d0017504101c420203025007154001d0000c10302520034002e0030030050402444040403103c00e01d40440c092441e20703641850200305100342c02684031000928008060140d01e0240161201c81040684503c603031506100100180c00c4050200c1d00f40d2a80e20501c0d8414004c1724801c5281d211135403069001140c3e4603080540d030711001ca91654036a00398016a0302c0c204031150095001d041807030002171030300c1c90b5401100c60190644090341d040000660410381c00c401181c0c1101c2010070000750b80c07200b0450318540d90810003030081d48035007854180720002c4e034000090110310f1821800c0d0038260341c3c1c1e000c45101c0344c03506100320810340320280720034184040410305070600504d041c0103613040e006c1c1c0 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 746266771 1250 746265521 746265529
    0xc08030108070305060906040f17040f12060b10020d030b0f04090606170114010501051c0c02030c01270b09030d021614010903020a060e01090203030d091b270b 70
    0x98001074a02d60140508105004040004030b400100b0a0301828560410792107403a03126422480c05400c4002d9190000c4581520404075801018140ba500ca0760a03150f41c0800d80c1c181d0400020b80d180b0703060120b420568504107256048001d03242c0c00070100303140100700a802811782613074020b602002c00825014580ca682c0a1620f0061062500051403400c12818044480400f42040c6003a032504911400d4070215201e07240c103584007400d10685552444190304001d90030915246074141c01d05d1800d07212142c00002500c100e8000344000d104038a09a441ca40100710b000c1c0c07981c100099183c6008021070700484c543c42e04580200b0559142c00c410114601c280d074420864010404540d126001c02d200a0f40d091660b00c890302c100a000720002d40d02c000350364026842029009640d106111700070b002095110742403007940901a43d444845240303200000302809030055070741c41c05903108110110f41071502041502d00c091060a85014a81840b20080702000307609004295580001c45566413 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 746268021 1250 746266771 746266777
    0x70c110402210a0c110a11041d0606042f030402031c11070e2a09030f011a090c160507030204090f020109090b06040923071d09070c030309030c08 64
    0x8280158011410200210801c980690482e13008102c00d100d10202e0020011a6401e01c56402c2000e0401c400e00040004008008015200306a16640c01e1020141a40490780c1441608c0443c1e003004962200400d0144100c1031403075510f07819030300480ca0428404040091600140041d0490b4041244c60341c003c07a049905403042c00104424041c9418407020401400000d040c0c0310810850500b00015103002281540e046140007010348105001c80f9034620080d00c01044004045030444080c088216009104507260b480c600718402101403881c0c1082d6444502410640c42c1952074860074007840380c01e890500030103c466000310780c80003015903100e0082c0d520007805030310300912448542c8009041a14507501106516081c100124010303070f80c10b400e41d030866200e41004039034110400601d20004001c42400c0441c42000400d012005502804856006030f10021480415a500040103c40002190342100048800303c2900000f0700c42d4000003201d43c481d003040c0303004210b03c0c1d440c280160 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 746269271 1250 746268021 746268067
    0x50c07120c140d020f0d030210050c04091a1f0309050d030b09090606091504020d0609090507061103030705210c0a1211092202070609060b0603070c110402 68
    0x48028802408007802e50700c41c01c04010403c9a01140124095001c10754000d00244030701d1160100200751070905009020201c0e1614040504110030303d02000e40d01040c0d0040c0c0101c42d0320710f180c005144209411034142c61213121004088180c0c070b00d11040314042c0000044400000c2588402e200400a0410019007a01e100103840102d5030842c2c00052148154006003191129480364041c04110b84030307113800640155075031085404001280011401901c108494000501d07c2c00c000082c4c0010142d03c92644c02d84079100b40d4406036960711045540c000c02c0c8a40741034a400c00c02c08282c01c18040d1006048408148062411103107034151803800c00c0740d085406420440d400143c90700e010398482140012413a100310100009825011b0340c04032800345500e4940200d20328144201100180210724065103c541e00943d62244035150a002030140c03444102c1e49142000c101f01d08a240050a81e8881c0380550f445255120b0b864680401c044540d5031910f400075400c0140308010001d640841ea802 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 746270521 1250 746269271 746269283
    0xb01090b0d0605011b150c020307020a0311010212040b0901050a0905031917040803091509190303021203010806040f0204020d24060e01080c03060a0e070c03110d09030201050c0712 79
    0xb146424000740000180110418045004102407000941c803916055005c101071403001407a00000d01060380380d4800e004003c0d43c0320700658000002c1184141105910071300030fa082c2c401c00400721910b82d1083c021070082241c1e40105003d01009540b0501c0a4500c4070000d140243c0381c1a81c90000c2810b04100c066440d0115104111010074044807864250042411010942c50203241000d195200d00038010980c3c8124207044c980e205644401094130320b141001400614a9140c1440206124910380f00032800b500410107000003061000c02502d04865040300902051b0342d9a1b91452401003c5100c100e03807003035080c0300891204c141c0388038801307101409240348507055a80e4105200b200c1d181d640810200501c00e802540140d81c0405000c2e00030a51600d0a03469480c1c0d940060511126a08000840d42400f0200211640e0125142c03284a000303456007041c40c012085107230f448148014200d00894900d035030400042d44a02c00500d149803000c0c2c2540d040e5900c6440f10f14409039042416520 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 746271771 1250 746270521 746270531
    0xc0201140403050d14040b040603021317030715090c0303110717010b010930060f021809150a17161203091203080a09050c0d0b10080604150b01090b0d 66
    0x41a001700801040c0e4640040b414200762824100d14954401c03801407404054010480c0350003036014512100252418a031540141607045d83d007655240c10264040d01c901402c0c04603000008158810700c180310390004954601e9500b5070302c00780c810b080b101288d24000d106440c00001c0340351481c0c00a40304071110ba4004103140042100041408105820422802a400e80488808041007803644c1c68174183c204040303102c002c0b03414054014200c00d9241c1c00720500020755480074500171002c4a0000104540c00501c40c4c464040c01e1001408038080e154005071050b409000080e032684038801c01d00c00040484011881c1c441e880d65210041e584160307012490705030a9010940c0151515001d000038170810400840f060301d0040800801078044400107590f041d9401c12300405005040f100b0710080c007a0b50328003040d4a050143c282d0100c801607200a0400c00215000340089902c81c0034903000080c00740c00088850003070000f84908540f042c1403000c861000966000030802800102d0503605002070 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 746273021 1250 746271771 746271793
    0x150602070501022d19320606010e0f04090c0906170a24090b0a0e0d08060f0a0807031b05060a02151518092b0c020114040305 55
    0x4642400340d0489415900008400c44000082c0d000854459101501103100f02d00000c240c00d0502c4c22055041401c1144a0350b11020300102d580c1110341d0070890561204445506501c0840f1498078020500d0550005408181258403800c0042c10055000706800c4908040c8800a000c890b070401e42100c4402890000704400d49051082c40001d1070004074042c0c901841c10261a1108a8420000c0659211241070202c0d00700e14201c107660a003061800f000044c43d5818074128448080f5071350000207040418260401d40082982040c03000302c0e40354072001d601d82004002c001a06010800d8000c81103030400038141e4020415070004500810350560112750100400000c02c0880e00b2990088901f000401902980041d04011f9103801c040c0321038458992403604a88642040d814035407183c0703041e1800381032100300418203009080b0101180c0900c0a10303443d654a408241c0940345150340c050300c07040302075806450b140c031089105140001c10702640c0080a5115000740c0c0041c1c0380381c2e1140b81403003 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 746274271 1250 746273021 746273023
    0x619080a0b09011a0706060e07050712020c01120b0607060203241903200402041d011505120408121003021e0a0920221205060610050c01150602 63
    0x81501600b92040c003501e60402030400d00503400d800000600e014009040418441a680702c407001e0421401c0c50b51440c02d2002000b4100d801240701a07511860b49c82e44008050f0001501100c0f20906031503490900d4041c28240c1c008103400c050840d04240c0401c403d000240c2c151000718800d4510880110309100320180819010300200c42c4940111100d481c1c122522100005000c00c070303a0b20402c001d444141c155042151180d960326981d4106001043c00319a01e200d51505c5070740c810048510b042070b603985807100818990381507109000f04208004414017103954061055000740a4030b0007503c0c0204280080180440c2103450340da001c00340010a000310314103d402c1c03880024680305411220030f6460005070011000388940404959143c060652856000300c4501c6598407007000300e42c4444035020340c200c01e01b41d150b8202071201e6100d140810340c2c030000c00000c90301a8201e07000301210303500e54043c040d0760750b1211402004d01205000d0520088400d004040410200007a10f0b46001d241031406 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 746275521 1250 746274271 746274281
    0x50a030c0c0801111603030e1b131811180705190201020c0c100c02030a080d0612050a120306030209180d0e09040f240e0d0c03020c0904020619080a 65
    0x12030301e643d05040f02c1c02079130140c40e4103503443c61850024032501c5450074501640103142101d542c4a150081d080120f0403140d581c11400b1001009840038070282c2c0e241512036080356418031558025483e01c21042c0085008900114170b01107024000100301400d50401c100501012144180040c20008245410081c08400c2c400c019800d4002507083c1400c1e014215296413a514049019903000285a400107204d1a0188111038028041e20602c44060a000e00701b40e000a212190060070305c0c00015270310301c08c00e640c40c6e0340d26040000750881c14002e030350381c25258154940c603070105a100c050100c05644c425110502440450141103890100c103c0c0d0f4a0806c2d0382280c3c070a0600ca5a40f90442c00c0c0d840e030342e020a610603800380242059000d1451300496050f1248001190241000090089000313181d00003880e4088500c12111138403e03114046440b100c15120040058200c283c12000504041c68a150418801840305060684c0d01d89500d8058501c10802c01c0005c0820b020300400c49024451 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 746276771 1250 746275521 746275529
    0x1106270334151e180213110a11150105181b0a0e091005060f0903010f0c021608060601090b03060f1e090a05060a0b181305090f070810090609050a030c0c 67
    0x105120704000c100c04d04800080b803100c081e004220920444800791080d0b44002205904820940d84407802000014220200b010782010310b407040d04a100400c00186100c641242c400800354052101c0803095103040440140009921028514950202105a038050400f10310b141e51004041c0d590748081026008002d414041c0d0b10720403c4062000ea01c03400d040b00d4201d481c44104036618800000400c0c014400b801100641900e8003d085240a502048600100e525018200d01182c6c48000f8661141c8043d203401d0701190800404200a003c0c80c00516800500102070340d00031070001012804d001c003650a420212140e403c1d0f461b00a1414044154020000c42c108000314501b02c008200d0074101d601880501c2140800e200c014010a03103940d0f01d061401030031031001501e101190303001800050701c850000380203c03d49024111000103c0c1c10071500d05400800100b07141c05100c1008000480c016600d940d00c5441d0480814070811403c44064425514059100207508043c040e462842e00 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 746278021 1250 746276771 746276831
    0x40f0e1603110a1b02060403060501030506100510032c07060f1b0b041e05010507090e15011b06020f0d05100b0d0b01110627033415 58
    0x40c852500c040b01c103040c1d40e10a961804c0003101007500d0012411140300c0400000e500c00000240482048030f141c001504076485001103913030303984445403e03403845401c2d80105034000380304038030b200300051094100440c3c01607003144408514582c840004c502003c41d6491410f0303584051800c01c146d42e8030400c04030a680c640c0c501000725008600301c1c101202d45c3c000c1e001c0c00c0444d010010406001e0118000d0013125855040c18098501c1c2d03241c414042d11f81210070001050a4841c0040c4081d100c041491141c3c4080b40310f0013074010b007800107440002200380541940f030300740604140001d120b407000345009801007184035200c40540012a099071070040c6500c00c0020080410480d185c840f20584504061000003c12528107200048896903040004140c1d10702c01d10060240d1100500e84010b4200d131441d00001440c03c5000146680c1c3c429040e441c030844980d240d146070704200b04080f00416800a88581300d819000da01d8920300c0602030128011b05d56500c02ca0364181d0207180d100c4000764070840c1 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 746279271 1250 746278021 746278031
    0x60f090f070b030a1104050d15050106030b01081602010b130f050601020a030c030324060c0b0a0506030a030309020d06020c0d230a08061809030a0e06040b0f0f040f0e1603 75
    0xc240c1207980005050b40d13241e113464252049140b61008169805000098406916800c050030916105a039034096074101c94039010000c65101c0c442c5c0100603428506071a10f0000e5241c4144100036410044000d1085543e544603030740b807d1340c07086500c058400c0c00c0d000c0460240c401202c3d04003202c1010702401d040d940001c2c0b202c400a41c00101484e03910b230301800c00240c459082d903500b146036511a03d03040780841c007041d80490110b800c07001003605103019041501041e6030322046007045440954109a041d4440d0382c07040002842a0000f04000d480a402524981100d40d1800144c1e0845035601d8000c0c0c000740e640046032a4059250a0f41042d2402403a5900381e00b0085084c49101e80e004074010000d1000003d6a40d4480d5525031041d9141910b0358a114170346000303656240d4000c0b000b0040051034841200849190a505440580710862a00b03440c203641a0051107139503004001085000900b40b00024500e044401c0c0000104a040340b900305614201c0101085a0509a07800040c03620300 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 746280521 1250 746279271 746279279
    0x518010e0601152a1220120a020102040e0f0f090c01081b07050625140901030207020117010324140f101a091c0809090a0b03060f090f07 60
    0x4880c580e1401d0105041c40c0c0d618107803a150700c00009000c80e40d050520a00311842004110103000000d264140c90361b640c21783c07014200c00ea41035200030007104400a0340070085951107290010014041c1200c140001454603941e41d03054420000e0854008401c64103030404c001d418004002d0040d44a01803a01411100206500180040d0380c05040540d02d640030200d01d0588101d80022a0300d0150030908461442c9400c00380804000d1001031103040600d000c50304c6603015400b07504201114003100c008203040806040046009401c0010140d0421802c600c070302e0211070b4030340c00e06400b940c01901c80b00d1a2903900c03c84441e00b102c00382010100ac1d031503c0e850400c0b40140034481da4102216807004c200940340c0403ea0030364180c05400c01c1030039440c2040892403080400000300030307010050365150003c400391240d121106641440c045c0030700404010040a1b490078070039160b4450018800003a4144406012924010080340d0300c991224040041c8510400b04008403000f0740d00100c02004c1ca1814 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 746281771 1250 746280521 746280539
    0x72c01030b040204060e0405072603030a05060301111801020d110a0f060b1e0a0b12070804031e020d080603061311040216120306091407050a120518010e0601 69
    0x1440040d00c2848407030045000c40d0b84a4011400405140c480394195090a081c0603807500803a205944032140020520304a42840c412610140c54816001c1d500319600c03c24080080c0900800856265581d8001482e000003600b01905085008542030402c0380304480000e40340c86400c0c0c0d00b00061040d9000301c3d0145440000b0006081640301c244c84040445038600b400242a05940056204000c0b1880e04000305540c42c10300f607030b01d004580302d030082651100130080740c4c41101071402d03026900c00d00103076000b4016650260800e1003450001620342020120300342d50086c08103a540160050b401c4110001c5e4001119500710070101c004e002c003400c040c181c030b0000200130640241025105072411040346d84550569031114082600001c83c1041c0d4501018418400009040403c1ca80140401c2d0101541305010080003041d0a00707225440f01798081e15183c2191180404000341c08800051144141c0640c90040c181242c0d05414031039288031090960740740e8103800070705922400040040f141 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 746283021 1250 746281771 746281859
    0x3051b030a0f020d1104020301120218040c1a0f0307051b070509060f010e06190f0c051b210106080d03020705060f0408040e0c0702040f1e0203070306080a0507 70
    0xe0b04135030300402c2100c640361030081c4000c0c1030f6040e0303400781c808000000c001f145080d000c0001842202d110488152032403d071000c0b01002d540181800b13202803010b000b00b05c03104500c201c526400111141c144803070384d138032445a0380c82213805000160002c0f4500008580c01b09420400324462405400501d06110100e400400001c124520500395001c04980a9000e490891000440905001d0b41e50401840444c1821100420040040c2e40099500f00c19441410381944269008025040c00803049425041100b04a000070780e20000d5005500b001c2400e101d58106085009e8002040d590b2401c0e510904160310000c904060500412103500086c501064a6034000c0140114851980b1241071010050055400110343d0020b070005000052145001a0140d5072084800380182001211101e050702e180041240034090b09003d45116000789402940c1e21084030326000600503925010720f850310703481d03400030b56590300014003c2c0701c8820144806404009440658114a444201c803406908 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 746284271 1250 746283021 746283023
    0x28170c0d05090f0d0b04050d17011404140406050f01081b040509070b0304060519060b090411090d03050306040501060503010b0403060e01020712031b02010605010f0e0a030c03051b030a0f 82
    0x8002440d029035640390100d0305034840c8060950f860344c2c0b01d6481c140c90400300a64050350513200350034500e1405c5120700f03007144032603011019100a907442c0540074540403c40611056102e03441c0d91071405054030944160307106034054040414039007000541e0300410101070300b003507040307401802e8000e103100c02c1444507402c00302040d00e0003d55581ca4503401800c00002da001800d10074000403e010510005410190041540a81105201a008640808403031091107008180301041c0241d00691800d680180100122004541d2502c0180d42c0090000a82a10124080740c801300c08d110943c1000d2003654090001380c10aa07145504000c1c0b00100c60003a840020a00e0b80c8034610b41684000a4040d03a02a6522174512030342e403103042034090081d000c441c041a09500280102526140c03050140c4421148103840700d0000000303105044903040000c041e61074020030720100000020f9000344501004600a0001d08810104002d0840407403a031b04601d944280e0205d08448049003907141414107071 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 746285521 1250 746284271 746284277
    0x30f02161a1f05120a02041113050a230a0302061c0f0e190302030403061103041109071d12151f0602060a0c02190606140913080c28170c0d 61
    0xc85134500702d03031400c004132030300035001410600460f5100d607100d4003514044d8008510110a81d80f600203204480c06544100e800d09032126107000350b800040c0b0015950307441d000d803078152403985940108403d9882180f801d080407800041c4020a20400c0c401c400072603140032810303ca00c03103841c100e1a030354040e43c02c00c0003841412141c000007010700800440b401550b1100b024807000a1106104d034058008560a5030b5002d11012011403900e00082454030071591034444085100fa8220424003603041812501e030821f010000c1445c1052040007800c920380c408069a040c149070400b01c40311410702d120600e094606551609214882d0046000d135071100d4010000a081d0041510891070041c0b01c411140c507850029210005008440d0030543c00c0d580c44101c0d40707040c1410b41041c040d80d4031003140d109214202c140303200d00009070180c00928030040a001200c0a001440300401030710800d00c0e407100901500740c2c00b140f0400022000003407401c2040c0b2042400e1110049115444407080324600d010 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 746286771 1250 746285521 746285539
    0x20312270619020f060a14070201050f010b0307050d02030112060b0901080c09040f0b070e09160221130b1c0216030e03160905010e0f040f03030f02161a1f05 69
    0x850b40c420003955000e8200760049954500f00f0340c0c1801e00a0440400504584406400040403070340140240750051484c0c420250143e8600019a040743d04060180e00801904010000c2c180459002950103046000110b03440701045103805021600b203c21143d00485201c00100b0030600c000c11041c010f0740f01136412000715503551601a8110240910080c020501c0c070301401942a070200e030203070040b07100351203400050300c3d542400c10b480060341a100d0b00580c0300c021054203194401d40e410303034030b0044002c4480c1091482c9030345106802a036080701c28000000f05016002420820301c50b6154544008110310345810740284041400060401030241302e014456003402d520100316508072034502d08402d207003454840c3c110101400b003e1291401501401e40445c03e925043e0318075902550744180c11078030b000300d02c0d5010b501400101400050075503081c04804030391101110340080c40c80c0310b0b03542c030b40c0c0d8076036000012004c286018110340c802c00d10b08210b8185041d0000c00134070980b0402c4600c000 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 746288021 1250 746286771 746286817
    0x1506040e0a0b060a081b16020607052b02013204020f0a1d1e1f0e0411010f0801031e050109021002010b0315070206070f05070203122706 60
    0x2400810700001d070410f40001e40c003607201d80c1c0810664003610070703007110041d1311501c40307035004590103512400360503055020352038401071a20b10024020700b8402c1003a10300c0040030140604a0345070700d01c101890580b180350380d40103259080c400c6084002400911240950010385943d503403a0070340001303600300c0000102050075541d400b60144004800100301c1490303030b519600300060102d035055490010701c1500012031800030116503401005002c5066981c0c09aa0300410034480711905040402c0086075404041881d0f00b82a80d01d600c0b40f40200d006c07007015522280010036040c6035030202400c1203450300050000441000845900c1032541070b01e403e4042260034090700600c00c10400940c04181090056007207601074000c0c005c42c140c100c1c280c407031615011a003021094004c942d044010382003100060310301d034002c28020400020614180341001840c1c2e006c03a103442004110301182c41d101042d04241c15a090701f040b0f29228540726200c0c1070541c00004501c0c14002c0da01d00c41600c1010780c403401 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 746289271 1250 746288021 746288041
    0xc030708090c040504030513050603130b0612010c051209150109020a0203041e0906050d1104020307030b2205010801150909051f0501030b010b0304030e0f010e12030306091506040e 79
    0x180b01c0100400030040c0d401d01e40313400f400d240d02c07e4144450746003103450001903500e4200203030303803040e001070b503c1000503100c5d0340e1021003c0c1401440954403149088045078903940074030484901e4102c0d92120f0307594080041c20f02607115001007d400704c1d81c1c045a1814040360100e00307040d04542c0300440141c0c4030651804140d0450096810000c084112440440c07150f0a07080c010078202c88080d0010071501e516031041c001d00801c0d02c000a003418800901c5100142815402035a0111705860002a8101208005120b401443e030464680b041c10500c03845c0540b10030f100d100c0c01021080000c0114454400c0310800c008140d1041551980e40e0f090004c06101c4103200407298000c3c811000c1040b56a1074620340014031080c08141d42c4048000c0c00480c01050b81e000710307402540c254072022200759181d0204441070310168007690400808128081c520f03107808070644044410200030b15103e00d0300a06008103000010031603000700c6002c1e6000c0425480319011a020380c0c0780402d41c9446a61403030421 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 746290521 1250 746289271 746289283
    0x123030d0f090803280221090a120609030806030106120b0c0405030304170d0801060e04020307030f18260a050d0e1504062306010f0c0501020d0603120203030c03070809 74
    0xd110f050000003580d600101c0c10042d04a0001400045150140c81c2448220b9079003c00d0070b41b0030241045200c88101050550025041070900242900325941d142d1411016003e20004c04455035615150084105500045447da000900341c0c02002100e00d008001c015180450320007902000415001c034940c10200c0044030003070f10004e0200c0b55110313901d040c109850440e11003281040d01428907089a10352144140c50b0484019135141a050041e805c00c01000703510140c003460515a0703a25000c060000d89015102106a54004000c070240d11030905005800410740e442c050b040b94080983c0e0401d40c04020381344c0910007031038400d44400f8542c048800500e180104100f42d80f00b014010910850040c1a0522491180398103000c00450401c418401841441d0381c411000100000292070754420a00c854050084c0c1c58078518118154441c41d08aa0001e6814138040d84c68400510920502004200c50b1285c244021071079460311000d1381c2c1880c000600b002e001c0010800102d10241c40400034 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 746291771 1250 746290521 746290529
    0x108060f0415081608070609090e0f0d051902071a03040f0516062c040e1e010209010906050c0703030807171f050406050a0302190e0109050123030d0f09 67
    0x100c1582c41e1140009aa10910b000d00c1c15950a11050049200035001c5990412501161074190545062046120140011070348186140c842d0031000d01003000700304001d5080007000d44070305544c0d03002034501e24561800c000100040d0f50280408100386850341c450951050b2440c1480c0341c070b075229442c1103030782d16405000260191040304e84141d03100403c2040107040f5071041c6c031030384600381e40300d480d62259a11480140011460240c13840c210381c141070308901c07940211481515403400003103180ea0b04900d0400c91002042e07502240080880d42c200b0b81c050301030642414824101780450904a54909450000404010707441c00403901142c0100045038044405110b601c0007481c140c40440421360b113181000c4a94501100000f03020300706403081c00e06680d0060580c5600504503024000440c215014100c030401a4040c00101c3c21507648402e40a000c2404011905524211290071051204050303022101c015403051201b950340004c25009201060516840341e00703440d04155150003d50b40 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 746293021 1250 746291771 746291801
    0x2070606030503120910060503060604050a0e1204050f030109150c0210051e0c040620030f1b0c061623030307030603021503090c090c04150306230108060f04 69
    0x10701907034080c010040d0f140c803a505c60000c07108084c05922003103081d40c030140300b03150309030300058013080080c20150032482d400405e44001242c01040340801034a4600c0300e40c3c1841c02c0d0500130a041c481450324255010314000e0445c000e024580706a21030701d000a0b5451054070000d55104400d8030001c0c024400c01c080080170b40d104011a10341190949804514421a510351050700000501e41c00c0c590700c142d9064580d83e541c0c0c240000140024411b07078250b60380d4503080b9803005211b110f09440d403203001840250704107984100c10100400070203140c0b050840710288200418002410407120285210b50b03501d820000704400440311503040c10005105010003c2c2c03030b000000410400c1038058000c101102d100345c3c1c0700244480352040000c2c45000648451a840e049007212000503c1c0055440342c11000c941491850039a980c030118021051072404200400e41300e00080045004813500b41710b202ca1b807485000c1445000c440024205440102079900c00c0d8a8407003102d02603250381d40030307850b400c030481 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 746294271 1250 746293021 746293027
    0x2011805032505060d0603110a030b160905030607050c120703050708090d0209090105070e0f0f24030430020c011b080f0403051e0a080a14030f01090f020a0c0602070606030503 77
    0x24244e4040c6c00e00780429148603544801c2a04242070000740202201e801c400020081e0301c841080d1900000c0105c3c1c07400800c50703c0400414141d6080c406940140c00c252182036481c0c0c2c0304040c503800d0080c01001c0000e402c20078441100800d82000454031015406005961b850000c0800142c0c814084000690454400d900300051588154009400f0309026100c03541249414010404202501d011040d0804005501d803507c2d81840c80a51200030303440d000e01c0600c02172290f00100c1a07082110240c1c2d50b803921000003001e003110710110300712a140030164803c028010900295495141aa0140c100110110050903010607002103251140c2e001030816521a996484902d041c1c025010540d85809007000c42c3d143c4c42c0d0850f690501e8941800d02408079440d035a25030340f5150304444400800d0040700340720340031422003810041d48507850424269440d54105000c0604481444882c42500751040020081043d000142109010390060740580d540c101450f00c040607100710b0380004d0942c8004 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 746295521 1250 746294271 746294287
    0x40b031609022b1401123c03021b090103031710050d0302010603050601090e19030e090a05190c02100203130b0c0a0e040204030b011e170a0201180503250506 69
    0x650030460003e0b107022040120b6903280e051b1050002c260002c01002e11820300208070044000e00c2c1082281400c41000d1483d22000245c0f400041c540343c4002c80041c0c2101c1e103050100d0b401150560708401040d164580c566045175006072201601c061004104500e11000a0210000001c5a00900030103000281c1041704d51130003901820090108507443e001c0c820011404020303911520710480143e000500d003a03030028034030f82440c58070010b01b81c0400040782a104010740311004007074007608084130000b1b210b01d4006030080c4454542000f4004060901503174840c0694000781d011110762300c143d40165240c079400c0d07003c1080c813607940c0b0051002c00340030100a2400b0550000d4500c1d46920340380e40d1032491014003008102c1c45a4040100342c4030f40076006010302591a19564074080c406282c540603c0d4462080c903415022012005416500605442c421075a20085e443c403040011140403c40310700307020009440f0340b140b05d551100f03a1155503072600c5101d00f50700303000014000035000316910040 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 746296771 1250 746295521 746295607
    0x30506060f13030c0f140409230309041b03140c0a1d03100501060809030403020604060e0415081b030102160f03050708030108062d070809010b03070b0702040b03160902 74
    0x20340c80707148042a03076031b01c1c000403134103003406501801a0322480701100000e101e0001e00c0000030131401c80c400d500c02401055541d844034401c0084000000d103160201d0f0002103130003010340b80b15102c440c40c500302c40d40034005650720310002d0b100454018107205c100e40c0f4500c00c04540d0191045402035051040140c02c100165495200c0b5040e1081d80d6071301e100075624800349569a208a100083d00490204020400701d44250035401041c80010000328001c000132800200284840d0001010764003c030009450350091103a884114100070b800940c201038109000408803408200c000d40300b000c0c03d00b000000c25200da811101e103281c2c0302098a40300d503112004680c1e5000102d601d40050420044120074443c4068003c1004812760302e0062001d83c2e40310300803124000c0141c0715000a64a43c21000c155039420300c581e50103007030781d10034003130b22901180104800d8500003502c030380c0a0741000d075101c1c0d218042ca00c4400d05541c4040030150b60380b40100700c1c203c0780e8030081481c6c1a42219406400d44a024 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 746298021 1250 746296771 746296799
    0x21c03092718050d02062404060b0c01241a0304140f150c0f0a0c03031512060b06030f0112020a1a090301110c070513090605190c030506060f13030c 65
    0x200072000c031344416510301c10a03130f80c695055039101ca032201f84212015100400c21805002018064000320341c8540e00c45020003150450305280311145d440708006450341280c84043c2409400e14551040028030b801c141d8406141d44403c11030b2120b200000150034402843c3c4e49034107071400c01040750015020b550b442d580f00c0161182e100c42c00380700f002c00714041c0c01d1144241c90040c1c01039922685000c05801055034451400c0200b24241500c0e44510305004107040c0082d402001c140800d04013040d4075140080c2290300404e13003540320300420b10601c42c1e10340d0550151410b40700c0f400d80c29440d86020f4000503036580a00e600903450b07140020300c4084004000c8002d001c01200c168000d0040c1e4000d0880700410b03000300705509083d94408007007003160b80303044406a10002110780000810000079140c6c0010b0391401c60308002854080000036080d0b02e20340c4510807901d600d03032508002e503042a100189031441a0010a1010040403a8000e280281300c41c01c00021903022030514851580e402013201002 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 746299271 1250 746298021 746298023
    0x70b0403020f0c0a09050423010b03010b03030a020a030804060b03060a020a0e0d0b16091508040203150c04030f08130602100b01020c211018021c03092718 68
    0x80103034034a84001d0000001e046943d604020001d6401509180711000284070090094402d030550418880c6912a11303201c4940d4040300f0000031400100d8441418251242d15000078042c0c0d2081010042c81540401c4504545074185030120070740d221b5090803006805151041641801040180460311b002a030003040c201000303840d00c0342d06009610401201d02c18450300a041e04007400002500c0c640d11a07105010605c45041411000d900c1d074094501c0303101011a002c0100c3d0f421405d000640c40c0411182d1007200c00311240c01002e1400c3c00350290140507a1100510641d04202c989040100f010141c80c084d100c641c09185a090741c8120095032000520500b0300a94a0f2840c40c0072294400714001070a01d002a05000307024500b09903140c4bd02003110030000282c000c0080c1283d9040c00c90240100c000a402e41030030035034105c0d004100e80d070381d082c06000c83c1d030380c0711b11a2620019410a54010440b2412740c0d84588181107100b02207428042c0f0400c1d540720600e090b82c4c4456807000f521500c0542 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 746300521 1250 746299271 746299273
    0x8060103051312080c130305061005060f160311010510090b0303120f0a0605030d020d020d110d031505060403060618200a0c1212050a1e02071106070b040302 69
    0x182c9a041140d02c1c012210301d000b801c01ca00d001d000c1d6988500901400d500902202c0e001c9203803101142c0418180001707500102c1e650303000310742449091810440703503602811007105c0d100e207072010007210303140d09101b807400200c00824030031407400900d400307540305900351561b00000313104038079288000b08003548403406046106440c14400c0900e50500106455407000864918840c0da00c40c000c030a100100000c203100c079400e44407031011505440034405c019498429800400a2900c46c0101031309100309040c0700c0b0100410004c003e51404000180314113140c403503090009115000302003003102410f080d0412a0005070014000041256a80c400402c40300982e0048000801e546042d90030b0b00c0485c8040c60049040c01c0310000500c41d0b040082001c00300d141000c0884d0394465448550030307482528210003062454490105100482c040d00342d2060807d10104104002d800c00b0003a2aa1030144400019a010030440708100024000d61840391000b41308944030800c0b441c0894032694116422001 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 746301771 1250 746300521 746300531
    0x5130b33031b030a020105130305030c0706020606190302060901090f14190803030c0c07031205031e0403021e0f06011403070602030306060f0901120903030605030d1701151e08060103 80
    0x81120b0144a06106800080250003011004d400450b5a60040c1101d219600d0310070a0010005104000070110b6400341d9010304601d40c60808042d0500c04000c24032806000c80c540300d98180d008000c1c01400b5a13604454507611b9081440040300d540d14550840300c04182610004104044082c07403028002000b240d180b01030351003d40c1c0c0d22000100c1c0d440f83c403880d80c0c400d00100b0607070503000b0090400e01c04254122901241e0b00d885940c20212420f4001010600000501c111490080548092001d10055045050400350350003560340306024041c03840b0f04c03900322440d0a211800d2141031428040101100c00755610f4404100b59190313114070b45803092140460020790302d4004001c0d039104800080c03000d400c0c1141c0c1c5035072201550002e48164108a0746800b00d1001d100103200b03160340756009560018802d81031105042c601300c0c20301e16410611890050b20041031017080c55503415194204507000d202003803810289c6420107195210300000200c56410000396038810380c0c0c02d100f124241e07010700c0 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 746303021 1250 746301771 746301793
    0x207111e101106130510060e0a06051905011115250206090a02010c080f03150909070b16020103060506160c0608130210120f0203040209070305130b3303 67
    0x8070b0b024205150041d580041000030407240701c1181d60b11040c4c0c000c03403c0c3d61a541e03000b01503804032074054201480c040c40103428170021089510030000580b0313007130700c0c600c61103a044102414029100d100d07590421034489113038005400d040c06029000d202841403080e450070488080c80000110084c1da80c00c1d0110a007204000d42d10001e2000c0c01500000041d051024040c0c004403054070502c9400d0b03c0124040012a03680e0f000200110300c035050014682421350300b00e60400c10a003401402015950b40005001c0c2711000a1504450702054038184502000c211480181c020703140b40e9000c03da0000c0003080070400481070324041c0301072600c20640080030548454040e109450156030209079031070301c01442c1006061201d0300301341d91100d41c1410303114002d4a0700f00030180c481100702901d400c1d4020090108504141050700d0304600b1509090041d841e05214071000800345000280104080d4004140100b0103c0840b0103404d00141640d082e10302440389060788124040d1515000740303d00030040c8 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 746304271 1250 746303021 746303027
    0x4240e12240115110102040e0c0a02011b1407020a0308040e0711010501030c170c091305070f0308030f0406020c0a080702011b2604051f080a05090604060207111e10 72
    0x281a81e0786014056000d21046808032105041151385161540d402c2001280700201c5a4003e4400c61020352555038802d10888002d0a4555440e140e82425010109990036183c010200011414620040390380320100f5000040d0300c640550b0000e00803450008020803a64001402c09204404a46403400a01a0404014201d40342480b01400c1c4011070740047c4017181c15540c01004020b100012a024000350000140c08614103907820040c0b1620b444408041101c144815002401324080c44205589103440d440e071548002095000201644000101040101d50565808003040c0080310109070750307490303e9040303179000003810f80c01300d038002c2440010003003140d459008050703100b100c61a0306402ca9818083c3e501101100c081121424000031805440301001114060341ca8240a070940c0780d0400041c00d091000f03004203207418144000c100d0740c401c0c0012030030b0b005a4400340c01a035440300e504000071800c0c2e414119036844450016810303c1480302054150b00801c003120760b02500c0044180c19 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 746305521 1250 746304271 746304343
    0x81b060105151c060b030106030e03041401180e04060b0913030c0b10031e0b07050c0c0d030c021905011103130311150406031a010504240e12 62
    0xa81c000a500d11041c1d14800350009020b050500280300642d030f40800754507609860342c1750000e800106012004101190f03040c003901030000c0855020794035003400c0c0001206101d0818425505100c1c004265580d250b200c4404c8500800002e040015141800e00c2d00c1d0000d03204170781c2120320405100c8046039044820f110300c1c071980c541c142c9481d500c0740d00c59646c0c0d008c013100040c182d05507080340307040010114111660640e1200c00c031040320000300d12517140040303a040c0050211010403005110258591300001524800c4045c116924444881a40750483e180f03045050001c3d04240321141c500480b8010a08050903503100740ca135040325140001c1501e56138001c0c48031020070f00c00140d80c01c0002c030340383c10321203800030101074038001c510080c500124026a110751f000d82b0020b40d031102d0b03880301e030f1009606010000c9001d2030030780e01d014a000d246e03052504406018001142600104004440c0582c2c02144001c4018016040111000d07071010748418184815461071001c03a03880f81c1b10f0720200f82d60 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 746306771 1250 746305521 746305529
    0x907060f050a210e2512080304030311190507030201050a0b130b03010f15090c0c0c06210c020304180603020d0b1b04030b04050c030105072712081b0601 67
    0x40d0030b43c603149800400044000940c11100302e15030300c45900d401c0381c41c280b000849416404166050f003a90814200c0c005910580c40b410071818105095000180140d00700c90b081074243c6804590320040c08502900d501c1844004001c140c1441040c0780300540100142c02002e0103a0003c102d1a07445080c224261034a2180b031a90040e05071900e503810020a80c007106c07090a001c2c00010700d50007080144000c071450460b01c44c02d5254640c000b0020702c070b110300540440c4039181ca8140e9400c0400da41d404410402c1e0b010321002e00c121b8102d600d24001c80502080c0080a400405002b80080c0c0580a51a03500602500300e05940c1d17a107814011030180e02491003103136401360405200034010b8403219015580501481c4410800601d54a42c1c8034540b005000a5405088540300b81c0c1171a1a09a00c0d05150700700590081c0d0403c2e0800135840d030088a01d01c68030001b6180c0c01030f1130b00180c4402c02480e0003900324002c90f55400d0302950034000064041d05400541102003e4030005c0701e90072980d40c10003481 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 746308021 1250 746306771 746306777
    0x50c10090f150b1302070c050306040803010f0b04060e040f0b0a1e1a09060a0207090e010c0809061006030b06040506030c0c06070203040f0302010309020a0e0a09050c0604030f140f060907060f050a 86
    0x21350150440d01c25401050300c540610f02c00501c2d19101d00000b0b0600d80c06071802c0d10b01020100042c024a810f07038406100030f00a2102d55840d00b0703d44200074001c800d0070030215120340d55440b1640c814070250340298244100c0180403a4445894076285d46404075452402e000354519400007007511264825a080e803101241707510307420a08407404020310340c0c0c0030100103411030045010000c1c15030440d01502071911001e01c004110700100c00c9005100c1070000389049100d038031410a106d00000741007a00b800b954610b00d804179aa42110021480c0c41c4031359484181c0003100041040407042d0707440c01500c4801c091005642080d21071810883e624003981c01080040205010308100660080d071115415a20180c03400102941c0d1f841841a840c500311350b9401c070361f0740703680d0303030a0422509001c40f80741b48a0440703100303080904585540c80a1740ba8908000d1055450901680c0030f00010007845507405400821901a8030b0295034058a600061040c18040341c00d0340d44c5030b0305450181040d514000c000307503 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 746309271 1250 746308021 746308039
    0x20d020a0209042d030212090904300504140f03030f13150509101b060e0f0105071106010f06050a030b18010b1c020405010c0201050c10090f150b 64
    0x240030800e0445010b0700444e6100502e100b5980b42241c1d00c034000003a080c1100c0c2400001c00f05050103400c085955110702c850480412440d0525507079070f00c050340c0054100c1103410070200e1181035100c0c1d80150944d404010a2492245020168001c00800580c1d94456258400e400300b08240110100c0081440e86d05402c240650b44034920907001400e9030010800d5001d0005a580300001d00d01d0810b000000002039000540d44054141020b44021043e52071034004100c2c4849031000c620190040802050a903d500c0c03511041c0b14100412100d410005000f002503040c00c440c00303844a11401c189c99001c1c0109400011800a21502d0078200e500030b48545240c1180c03950308400402030742484980c00540d0301c5c58448034010070f990840c040d210100905a851080c0041d12890940078000c804540d0b00400041c4620f903440a20222403e0342801c1c03071903d1b440c0087c515030810f11602219200f25103041c04d9141403058407191501418014029400b041640e14904015542240c000c42d801c030203e4 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 746310521 1250 746309271 746309273
    0x40b09041202010b060d0c030e0708120a0203071b050a090c0c0f1a040c050f063a0207050723090f090a080301231831031e020d020a 58
    0x1400c1040004624400091308800440008001e03030400c0072030060b03d9594101070300d001905407103860070103030505000b09081e5192100c65983c0e61140d1030580c180340004120700c09494003c205840d01c00780d01c0b616402e103185806d00001c10300f50075840f802d4424103000d00d0001e20000b0b41e00c42c83c2d520006607500c65008040c0c9803140c00d138840d21103604481e403030b911000080900b0103070240a80540d10424030034501618050800120922100c4d50034422340040000105c20301c206440340000100c424070f01002007000021120340404411000440d941c0005a0b02c0e080050114541c001d650f69900d81c00050180c0140c0c04500c102101a415082800b160224100c07402407083ca647c000e500c18100da000100d29130b50f00300c040e00b0070b0b0300115205490f0222012540d002c10052108420280c5400450b03504910104084080180102d448000704030885561040480303030021001d5030f5040031034048060f80c54010103a101501940c00c80311107400c0380c10b5004c0d20105217810112156402450b29445ca = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 746311771 1250 746310521 746310533
    0x31509070903020d0f02040501083c0a06091203060e07030504050f030c0c091e070e0a030804120b090706020706032307050a030e031c0e010608030f0c010b040b0904 72
    0x80035004105200210703400100599a900207180502d11501200d00445918410b1000b40c48041c2c20685030380c3c0041c1c4500d4610b82000b1105148000025041903040f500300840300001e410580401c0c140d40140c8004005210850300a140304c90f12039210b066900102c0802101181c01c50b008801e5032103201c8011a218070b201790051034201d40a0025149142180414035103144c1c444108403115800246804000e403400c4d030280c690080340e55002035808000c0341c00c2600d03a284010070780414801e030b203000f880c02034035100313184400b035640100b070b29980f03035220100c9111140c21500200d601d017000900143d40b8070404691349003115102c0e001890828140201503001d004010782560b201d404103460340c0703640c2c0320001d510390007071029448003983e62505e0b250007820b5030695010480345500c1000303070003c01d660324588840d9000300068006601500755030550701401e4a41d028605610001c1051801418404028158000414000c10600c41c40005200c261600311042a82c0180400005400304507 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 746313021 1250 746311771 746311789
    0x1081e06271f0f0504090615140102060901140f070207050a0320030c091506070c0b03091e061b0706150815010e13080d0f1a0d12120e1e01060b0315 65
    0x44955004038000194519440800d141c0da40609880c07007498600d27481c0d9507010301c0400c0c1c200820f0f02c02480413140500d2000c0160b44040c0c01a81a007000740c0c00030301c07103610a1044c20040c0200400741c4824075a03030304107025060318504041110180702410041280b5001034a00c141e040050500001942c445c4c2911014240880100d1b8205604100318000035030082400d00103003c1d0803c0917912070505c404002d1808008803000070081c0040404048000800210a544510314050441d84200039101600c0d60307001b004001090107090982107040a441c3c40c00000c19600c0420495510121011720824640f03800e115803000c2c00b84140105031109a24200d0420a602480c1050b01d06400305801c03008440d03d500c1044800756803160310700000b101801c1c4401452800b1200000c0c0110941c50705066605400000014040c011010f208840040e4100014500c600070554401000b140d103600c2032013809100703a041a500e420b60110320400070380c0549014030750041044251442d08801d00442c05 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 746314271 1250 746313021 746313023
    0xf150403080f040608281e2412050316061b09031b0b1c021b0709050c0c030a080402010e030d05070c17120c03130b090f01081e06271f0f050409 63
    0x407c04900320a04101e070b800f0704a400b102400054200b054500c0710044103583d40d81103c004080340700b04503404107500105444042d41c0c1d0700c0d10405850680d03d0b10074020003911031b8051800d000e10519a00c081c1d001850f036002c9034011106802e922151440c2e000120070f0500880300c4949080c800f400c0a80b6213030864005000341e11500618202a40c41004c582140d0703100b412000d548018010303c000400360203641d40243c220f07103600f401c080071b940c5100e469001300c01540303040103141c80018041d60302c117000f509000d500242c2920600d4800c0315004100768070051050754100b1500100042c489a0903111a41c0300404001400400b160440d28a00c1c542c41000300043c24401400a081d904250300c1510008002c071840140c0d8405829003440010402c00c402a41401119001c00c1407060b01c08038558140c0481c0c00800d940c81d555940007990f03070325101d402c9140b158070f00c0421040c2450381000160040e040e0003001c900840f403070030742010051590300541035200d2901c481006141015005035a5503 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 746315521 1250 746314271 746314301
    0x3180303070515070306090b0108010b220b0903060f0411061303060c0c030e100206061c05010c0e130504030c030c06390504050f150403080f04060828 66
    0x80c20710b440d003d18140d0550380101060015000348840c02d600342c80351200411b11154144030780748051001a01a41c2c05108021560b280001c0b1581020000c0003170b06a50218614400500e64641800c08160340107956041e000e407181c4008600851440c040d400c1c0314030b510502803515294100c080c440c02d50481d07484001081c00c1ca40300400018010b0003080c4000095a40d400d5080065042c018020700103151003e0050b90580380341c2c101258007013905588520150380d854100c0f980b030b40c404851844a820050450b5182983c00004164800c1d0b040300c40200c02c40303e031400c1c0c0740d18110040444500b55402404200010300b81e100080c002c9611020706402800300040700c14003075440d509504a0745603d0200380d80e80346044030800128695410b00741d40790b072800d20301705402c01001c04c84098000e003041e8802e01c60016a90b0202400d00700f02e5007c1e6500c50b50759604c80303280d25001001138001c0d00520300894407003030014004201c8041c04a07840a00320320008404160b2005620090000c88150102 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 746316771 1250 746315521 746315527
    0x20d02120f0d02061b120106080c1c0b040e06190c050c060415050a0b031225060501030c060f05070605060a12030c1e0314160605010305010e0c040c0203180303 70
    0x8040c028488900380c42c04680150103d8a8888202e07074030072110110100825105000c40c58019000381c1d405410f4404605106282e07445507040c0c9642e50141162040c0c44a03180d05117581020300c02d811a200117241941e0601403594401c0100e80c4510080310550b001d90b007062440804000780e034000740451806400d020740341011000002c0e040110403103050717030b56604080c454040d110b091300c2480c1d4440c209000c10000072600f4000030b5228051b644800d200c00001054000d020340403800040c610b5101100030940c1e011691030321002810003444281c0c0c0c12059280009103945c050541100c58442c00d503141440c1000359510000180310290040707402c403010380030200e000d01c014650300c1519400b03500d03054006e03821803501e0540c8080202200560782d0f0303030b400d02c800065000b94505a581c00c0412500e6114626040026040c081c0284060411400c103000041440b0065000b4000ca00c00348040d10320304000d0a0512040e20500c03008840103034001c214071b2070b2402504d1074400700c0d210000c054034a = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 746318021 1250 746316771 746316793
    0x1002010c0c080a031b1e05040f1e09020c1b030102070f020d050a050118051c020d1d060415022103010b0a090b03040b09060115050a030e16060801140a03020d0212 71
    0x8040d07403802000030082000b034214218654080c1c406200000d203503181c0380d440d213414048081c062004034841c00d0110099880d00600301c03840a015400034200bc0d1404549582201d11802d60301c881d0403591800d45004d85080303014504041c02201d51440d0000d080340c0c4003400942c02c0c4498404004816502e0b801807450722000118207000d00f40105944005e080411f47c000d0030400d051a00b43c407401004600b14501903109103401046020303812285003041c0103003401c00078100408040d00c001c4158050340c00640400c1c09000c0d070006d41c0e0700703030703900ea0880365003402006a00310b201c002c1030801004421300740700411441100c00010001c2c21203901d0480701142d600c00c03180082e81c0080d0740490320460364400f0400160800c02c00c0f1801050304502001010203128800b40c203c0c420351501004054884a10714a01101044090b500700240c040c40b81d000c940d5a2802000039400307000d491481c444a0108401c1440c08080c150140c81e0000e040b1241b0b03031030366400c222100c1d1010703c2d910b0300c07800343c4400f0b08 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 746319271 1250 746318021 746318051
    0x190c12140f09040b10090f1715041406190507020309031b040b03010513060516051617030708040c0f2403140108060a0c030911120705060f091002010c0c080a03 70
    0x112000341741d162001d42030f050035010f0015064603008004442d5000d0044610004000b801c03000d01c60304e4040c40f685907200e5041010b103142440f600b40c0c000d031003450180918070b0517007107c00b1100400d05104111980380e11404903141d100d001c0e0080d505500101010034018103403980d10341603042c02400000c1d22540c00001c1380c00d4030803c540c007100c140c1c1c2180c3d00d88248800c0d401840d41c4016842140600c070281040040c005005030540d000e641c10b6034000080c1000b8040700440301c000801c2004070b4507443d041c01c00510354942201d040711b042040c401d00050305e000118011090b0340d500240748110070558070f4000300c50309402c0c1e41a400c064548140c2c02c205402d038552079010741040c0b8050116403410707090b104140c0341081c46040c1050b00d41000e2001140c6d145410340600102110030303200d440c00012482d40ba10081b40c004036445140041e149001c191320328014803100c80c003903074900c008810a80c4141c0c201d0346a200043c0128a10a82d910005045a0300400058490b401d00142c9026400241 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 746320521 1250 746319271 746319289
    0x8151002101406030705010e10110a08030a0b01031a0105161e1407050603100e100302130222050121060b0706141302030705040b01020102190c12140f09040b 69
    0x124804100b0400d004107070030305201c1003024120130700344501c03c480706c400869103522443d20f46008005001d4013134a07901070107201408855400c184860345a0810080c4940102401030807540030030301c3c00201d07a00244000808850000d0144c4803203090044440c0200710b000c0c2004030031038014180050b00c1071282c81d04200b5404060140758000401c46d41c5c6071900b0328108291f00301030b104090900800080300e01c84032070b840640b200790074004480d80b9450400c0181c40c1d01500000e41c80b940e441c0c4c01d1040201d0b01d501034140222155800c0442c030324a0041c094404007180610380c0001d0642d13907a1420b90b0b401038425038000508002c0081e0996580c40011076580240808441603a03c40101c03944c41c240703411442d900028100440076107021540e0029075242c680d032040d41d00450301c56540c80442ea00030350503691044ca10741ca81054001216000031308889442f00c0848080072003c40b4405218440c15240c08080e003101710043c42e1a44a148102c2650417404010382c1c000e03222105070130b41d5201d050740c1c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 746321771 1250 746320521 746320541
    0x3120f090302090f0f0a0212150d0507170115140904020d050604030831020907090519030507060f020703030e060f120907080a3c0c0509070815100210 66
    0x108050b4145085005d0200402030001d4804500501500100001d80d0701c02c10b80000021601018030380c00035000c03030050b0b5403501c4007030040c2c02101c100051107151155122852070f0980700030010348201c0a44600070304254040c20482c1710008090036503d09103000c5072034025000601d030010180d006e58481d490103500b204c044001540c13034014850002803600340e0703014004060f90325110a45800c0d06130389240800c154040e02c030f00c005d00302040f10a40100151806450f001d001d032259002580ba884500703402c944811502d911aa41002501034490707000713040c001c1200e5014202c1d035071070b40d18200e420010349c0d08070713903402001000400d020f404a500107041480e082d02c400303d0585081301110b0b04011641d4080f031465001070080000152501a030030b841c002c0080150b5458100f940340c0038400d04040000341307424040c10b100402c00c0c814040302a80840d0300440394860700e035072030200c125241c040c195921590001640d507825803c1c90001c441c1c4c40d51079000e10403a0a445801d80c10074058503106a0 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 746323021 1250 746321771 746321791
    0x304030609020306150303030f07110d03060e0705210c090d0620090a030b0a0902150310050d080d0504031e0f0908030c190819080105090a0603120f09030209 69
    0x1004208500f03042c00380c50b031303c0784040300725648180780b0901003038903480300a2002540010250019480c01c0c090306800040040388004c5413100e601d108005801000030340606d50410784ad01002405551240045880d258426a402c1c0070f61000242c000724403031005402c0c01c221400c02d01202045485140ca15103000e0300898002c07030440400c50006462843c450f8105075902c01c00c2090500c1a1a14500701003101e030b003d06042016540d1119203401480c4c0c0500080d449081454031440b040d1001c03000c0c60080d0b00e452210300001d9960410014198142040245204001d0160310750130324182c0c3c441a4890b003e030802d88000003031840400e81c3d2800c404d10141c08a030811035883ca0113a0700c000400c0161514200a614050100c01116580e8080145884c50241424070280c204400982528110800a40050207502c07241c4809044000240109030094a04400007480d0a600d40075400489800c404100303154501c2040032640080320040513000c1c400e69410000c010784441801070b100e40d544003 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 746324271 1250 746323021 746323031
    0x30a0605040f09020f01050c19030c1a101a09130f110306061603090305070815070f0f0f09051f030c020d1b0f21020d0903050703020f0d0503040306 65
    0x300820040341e40c00d4410159291420701190016140e91288100300c0d002420103580391494400c0035460100061180c0c1d0300c0103500a488003c01d9000310b01301d00d0541c03203020660101909200f4802c10b64400300c40c90700d0030341c170807a6040244400d0551030130707981144407036094a803c050801003a45d0801c10451003070074641d02d061003035950400d44a060180903411040343e103182400c030000350ba140201d80708054510443e230749450806003d040814011540482581d10031a9103028132500d44c1040403009008001000c006040719120345142400c82201386c80d41c8048103610b020440f2105075035030500d400c0c4a960500800c00c1e07a162034510030707131050301c1103481c104c0110024002e003542c2c400005e24081d58440c04c41c0309411a04072035503441071920841d154048028a0903c080701c3c588110700074011070340410042ca8013092400611140c003009800320b1340c0d00d03601218200c2c1c0c80d01240c4806450341d0014142800180740400c0f44c2c40121f00018607803810943c0903100c1c4d504650287c0d000b29102d550321 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 746325521 1250 746324271 746324279
    0xc0f010507020d081609171014010b1801020c120106080d050418180f0506040c0512070e060d0c0605041a0406080408070501061e1703030c07120e06030a06 68
    0x340106030348808184042c00d0071090344000600034010280c0f0980c0340d6240340424140036489800d0300381c0200b030b265051b400d009402c404884d0301c07010b00440d01780da490b0400048541c8103500711841d904032501014a01c1c0b80214041d0042d08207000000c00904500580d0f9142410f62b030f03070308050b422840c40303080000703005490282e180e440d10500072962824804144010020521056841815000c05400c08203841d00550400b8100740d411540c02408032589a00000510100003a042d00c1148581c0a100790b02da22a001c0090503c4404c005084940c01990240040740001da44550080c002030031031742121115544040b0142c0140d004100000c0000c14104400311103031606210b4042c0c159002480c2c1070401000030800c110040014002402c0010140c00b0000258007890040c01c0340300206500c0741013011080e4401d0031621906801c4002c29591a038a141c020041301d00070202d0718280d030301e44041d50b0740300380000c04203030150003e01494041104550700ca120045124620009001070942c1c20 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 746326771 1250 746325521 746325523
    0x201110111131e120209220c08101e090f140610090603020906060a050910030e010c050301080601050d030c05121e160627061a030604030e040903050f0c0f 68
    0x60b802ea11044041041c1c02080391280008101d03204c1c60301650008030355a0340321401030704818080d40c0c2d582c04820081c084014802c6040d02007003a12001c0007078404280c01c0e00019426a00d00104109014050b2061103441d0419030b4441c0c0c01161240b410355031051107940b500c2040d109800c2c0c2c580d20700d41000040180306000e4480c0040903125405041040e2800c5402040e0051030080a03280a4880060302611003800750003030301c004000c000c0107204e003200e00010050240c2680c0711241490340c24403504c2e2500600480549040e507003003200070041a880c105c01c001001201482c10f0303080c40102c43d0254042401405510950b060552070303555035011901ca81d00e0805110a502c00b440c000920101c0c0018041ea00500b920766000700001c100004031030310803080240c00082030011902d8060f008010030045070030485240401c44401a88003500006050701e4004c102c0b030040005e400101d6608603850f180d40200c103902c0c082d240c0316042c0304a807070010b807003603100210350111580b0142c0e804840c490 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 746328021 1250 746326771 746326799
    0x90b0c071e032a181113052b17090a03050f1e19140703050a02090a020a0906030903020a0609030507050f011b110a06051801050601050313020111011113 67
    0x3210f10702ea8a0020388048a400303031055203018500c0400282c031407261404940d42c02c60310104400d0340107907954000c1040048402c3e21544200e6004045001301001000d8562140301100a4002c0b80020801c0c40e035070300c45a2141c20011881d070b843d40b044c04a02416210038441c44040c5205d04010172130000c002041900d8406660008601ca40b908500c2860310304000c02e0800407005415a0b00100242a02d081903a083c00003070f903000540301d0300100100380000020300590060080c0c0c1d46107c0364403640160380581c49418514008102c0e942010071120f886948110b07105030103403042e05c401c0c007460350b1040c0035110360b0030060380040d90106050050000c180001d010700c3c4900c80082061200400c1641c085518022240060041000b60b840040e2014481c001605901c46401c011501c1d0451010301d112032251a804165032038000012100d5010300c04490040c0f038003559445130352545500440307120101c01c05800d0345540f41c940340300302d02d040d94016010000d007842c060107040e8207050003891303100 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 746329271 1250 746328021 746328053
    0x6031a090106050f060a030c0c0203060c1206181603020c0703080405100810050d06020d110a020d0c02210a0204110306010e01020705181803040b040509090d090b0c071e03 75
    0x131304e444420709041d07643c80101e50b00c1c0d101e541000b08a6a440c20410f4400c0d508255001e50075025210802009040030001007084141c00d04800000f910768006014613403201e408800780c91091000418900005002040aa421989000b5250201009060303045c088a58000c5850382c501040c18091458925100a0030408a142c01405440c2c80203114050213150b22401c0d02882d0584003a106000c010340494081c000082d4080c08500035400c05002c01e03601810806005010b03e0440341c1003144103518811107150020400b03041222030403111031110032410f81000e5540b207982007081c01610b07503000c0c0915620001c00e5042e16403500c14005080342c036151143c1411500450404c2c0718903a03e02c1c90702e00c1e10300145501f64040350350303540304208030490032021040280300219000519506601c0100280d802c00d0b10401403940f9610545903882c801144400003144215806002c044423040c040c10b0301030303110300c104d437541d0f55110303c5aa0f00420070305083c0042c1c4048072091040c8045008485058 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 746330521 1250 746329271 746329279
    0x6030b040b010e1503130206030907060e03120307080c070b040605010f15051b1e07150e21031c0608010c09060804030807020c280803041a0d06031a09010605 69
    0x510364a0f4005032a000207401300b0800c040d4041701003140300d46900c09034505198090700042e5030f4100380c1503807692254144241c80c00100c000701300000501307000c1824100044029152415034a416400380c900c20b100038030341c07840d040c0309005000128841751401409140a0040050b295041549040401507283c0004588041c6601c0400b00e1030380c00303800c40b508034141a55038048444903d4407581000040c1c04000840b2041c042e84210b0480302180c00c10841c0e040000c2d55400d900710b181c058079111580c0751219031285000181540c1d020b03030f4066031742035030b00d412040c0e902e401c1c000302200780300708034015511110954a503814000907809115540c1401460b040400c2d140f442c0013001000323034400410013410080c036031020030000c0b4000c11000c0042d000c01054106405013694000c080720602041e003c003403600c1003500007071141001c400c5030300740c1d86001707030740034450004038802c10701355001220242c5400d41d5a000000820400c0d840e00304001a510039007007041c2000c02405082da0300980006120b = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 746331771 1250 746330521 746330537
    0x706020f1906020405030327010201091e060905101d030403122102041410090503070b0705160f1701050606030604050a021b250e04230706030b040b01 66
    0x42800014410610700d0020740e4071518480189003410182c016503020700d4041c80046502c55625803189800c4102441a240c40d0b540c498004d0012804c1c1d400d0018068203d440781c120504e440390501c0380b2204202d000d14000304200350556101842d200c600040042403503520081c01c032440354501e094a9a942240c0c0003142800d0842d1203e00d80c405003c038036601484412041070040e04d1140001a4011031265400c41d1203e503600c01e09542a0304200c50144500e88421160405034001c280c0441aa08003070700501842c0d04005880750715070321043c010b0b139191155881c18100c038601152440094662130400030b0446280c035481c0030302040c0c40280701400342d0400e4100411521403c0c00e8a900200894010503144c55640300c2600034880e09482d0b100200d00202d1400d621840054808408102d03441c7c43c0b10410502110610fa4007294000e011512049001060104142c04140749048190f03000700181000080d00701c2c0d240031303070552240000c40e86a81e0926240d14140c8074500c2d08a2080c280390036 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 746333021 1250 746331771 746331793
    0xa260702100e0c0420070506010501030b12150702190c08070f120219030f0606030b09030702011d01111009051009050309130f09150b041104060e011b0311070602 71
    0x103201c680362550300340160758070412030b41780d018610003005102e0552245140d882c46c1508140d0749400007409002e002c81c1c14000c108d00c442c1400b10009440312690006000b20842d0280000f11210020380341100718443c102c0520701040c1046001807c00f4451780000c6281c0e0f28288555080038090f5200a4000302442c5081000540346402c0d20451541290740a5200d02d0402035403400d18480e800250001920a1074041009800d0740301c0347c16a0b0203001c0e500107945c0d50110300d81d034900c2940402400110b4000d8070f909010a03c424110504605060120b0300c0a0500e50710341c50001c200b64480b6803207031502948014080103109800c001384100c002800340b200623131911556442034129040c0240201c15001503504002e601002440c0a04542070002150600700071048511a03056407002c00e103849140340051509205000110654810f05801e00380342c04000c3d903840311030b0301d500c1c0e042c400c0864603104040f100580c1081014429156201040150115149004e019400903815544050b203400 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 746334271 1250 746333021 746333023
    0x1104090f0b100312020d140c0705010815060a020a11040902060910170a091b031124281103180102030f0c01020316230a260702100e 58
    0x40219074100e40d20300c5540d10760035007151140e062540090110750108407510f2100780d0104206101000641e25004e146401600f0040c151180000d026441e606c0110200450350107401c1c0503501c0b80561450800c40c54502c00422069030000040b500142c1080c029a81044507078035a41705c3c4030109130b60402c400049030380402c01c0381c423135601a40e00c41c5d5001c00101c0809031040c1c010a09210600250039464180104040060000142e0888500da44030102801000c2151000c904403900101d149451601e0f107820f20214042e14214421004403e000820f0551494802031414900c00c10107d21144c5407003c0082c80540700c400710b9010070001201086070408000141c4214500ae028003005400c000c100603451881810300305c000266022641410408041d40075510813031005042c0902d802410000301e8810405080c0c04510040c10039014000c00c40100180140071002d00f000c45c84e00404050307000c0d59000d02075140090b42001402c000c01194107200d01c0310b0035001e01700b05122124010904c2 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 746335521 1250 746334271 746334293
    0x70c0e04060b04111c0b0d060c051303030c0b1501020627070b1b030a090e04021c0f110d020f09070507140312010518040609080c031204110409 63
    0x80558a1400108007407080c903600881210344000c00400c00840b0003441070205801c0340110842d964456002e9440d0314078280200c00020340000c0202c51001ca03956601303002007015103003100811500b403006281c990f8007100201e0246010b6280d045280d54180303410044448010b00c040c00550001c501d0b44080e903000074900f5000800c104940b0440c2d05c10f8802902106514800c801c61442106070001d04111042d00074041600c03000c000c06007003040390005a55a201d24803c6100160141804016050140020503009840146120014800104490510b58030b050301640c84901044800382042802072003000340d100250760b05441c20384190009003904c01035540d0903005d0348554000a00c003a02c2001243c0006501c1815040c207601c8088107a507903900003c0400000d05080e80c004a441e01d0010781c04881401c021940964030f40d01c83d80c4400203002c80c01c10444400105004d03038a0310602c240b014004060742d0400d0381c0000e14003420449624481182c800d4000c901d44003111010030860420 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 746336771 1250 746335521 746335529
    0x1e0a020303042402070b061903020a03060207061407030f140601230702120f010501050f1e012109030e0f03191a0a060303080718151b08091203070c 65
    0x1040c000240c404440c99010f10102c00c00760500341c80000da070000c00c0f542001080c040c000a40752108901c902d4080707803103544903500003c0d52000f2207640410000c0c01603001000c1682c841d0701e02040907400708051001c00038040d03c1c40b001180d200d40d01c0a00d4032046116100310b05c860101360701c18505040d400a4400070480c07000c22486101c0e04803080719945403c04a4540c25409400607003080d01d210761068031070500d0704000c034540d401d01f00002080d207401130700900351040040900a80712000c0c601b001c0001c40d410310242c11f200a004030101400d000350100c1c2d402c80c00108020640b07a50514000384184000a04640300745242d02c0c131800c040c1c070005150381041c2c0e07911000c01503010b51800c242c00445610000603515008860802c049103541d90400b8085074865210004c00d915003170070076503200f440d411005500c2a410282000042c0c0812407075101c000d017030300b08001c81c000b220041140b4040040420340340b040c00003520311040c0c1050003000300f401844002450a106496640d001c0e0384d029445 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 746338021 1250 746336771 746336783
    0xc1706160f020a0c09020c060106050c0309041805060a0509010c03021309050424140105031506040c110105092508100b01110109031d01051602090a1506051e0a02030304 74
    0x1825440c018001c100401a0603001100a0101583d511903503011f5485440c448119000d5071000040703060043d01900c05440c0d40001071410308600301d0601009090106c010b0420051003110340b00458070503c00940181d048090224085ca0302c03d115500f91810b5554003010180304024400c403001d030381e20041c1305491018001042c1a112420304602000003078022085415a010b00d06031100200d41c1308680780c1c808a110034206a80e50f9041613150005200c10b41103807161000003c03039030b20b81a4132404503038045060100e000400c040e00c003403c6510071200d00703084d6400a07105000d001040c000782c40c40b10200500c041c4c02c40c0d0801040f140c5411000812034407217902e401d1116816030061400740c40200307452700200010441070400030b10b42c460b1403105210f03130381c07442c040b2109951090040750382c0301c00030340828500d070a4030b50300780716040304001e0841f403980750354040d4041d51a5046c1e107203000504255440586075654080c4d4025940c480e0104e140e40994104245001d25402005030380d40103070482 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 746339271 1250 746338021 746338037
    0x712020105030f07020c06160b010f0b1e1902030c010b0906130c03021b06240604030b2e170601180203060a090612031b03080412050d090c170616 64
    0x210a0b49403900c84103100d0760000d800306800242303040c8610f07105802400b621005500343d03038840500344281650302404402c450704004002400705440c412801d4407903101e0115103001c0100400d041000e041c0420384006810001c0c2071018420240110b5481900441d1941c065044c054005110b036600003080c1c0300d09070740328000202c6542c00395041d180c1c440ea02400302e088a441d006c49039070300c841c81100c40010b2001e1001c81d180c07401d840d030301e00c2401182c005000b1500d450b00396155280504001416240100384c1c0e042d48100310030700410750000034450303441c0c410801420f04011110301701000e0704064680c0c0c86840100085420f408070821070034030311140143c0c0c980729103010a104050b180c000f00c0c1c40d1405c0001c0020002048085005458040d86c2d902d916481007030b1116280c2e110703511000e400070f41c000000c40c3c04202001c81c00070500d40c076418400c1c64412043d08440c1036601e01802a00d94412159040204401c0030340c0b0030152120b1a009400e0500c4d00e01382070310501801103100f10400c4413007 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 746340521 1250 746339271 746339281
    0x516020c10090302130c080f0106050a0e0310020d2003040201050315011b050f0c0301110a050a12090803070809030a080408030a060b040e0106091505030601030f02090907020d020712020105030f 85
    0x800b440005140c01500b200c207404c48035600f04d4064140010040c0000c0c0607203000400076224000910705803101656158680310785040101d4011040700c034a02d40c54000c090541c600c20b4071620040406500d40040860006190240600800b0b02c0e00040c106404040041100603070b4481c084a6121607a0071002c642d042000e00101c904480503129110015642c0202c1c01c14040002140160200600c04a9001059820034542a6924400c10400d609428010ba28503103000344081d144440701c0c0c1c68030040d0300d01c6015680080e41d030419404d90b14500c000092088840d03004652950120a00e4021441c162107841c3c010301d50900240080c061001c0440820720035512358010a000303010361540031f602e658940c032005078644000c0c030401001c500745410008600c1240c0c808901107101e241c40762802c65031100010f40181c60b01082e6a9881ca500708445140b17a514142c0c0c46005140319401402c0180608801918001e41a0031228070a04007001600060f82d001040300e0703214154101100640d251 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 746341771 1250 746340521 746340527
    0x80a050609061e0714030a0504021f053a02030403020106050a08030d0b0310151404050f150a1a0d05102907050109080721121a0a06120516020c10 64
    0x5d4601c425004001041c0485100c85800450080f8000c5600f060190740400a54000005031821400030903800d20581c0c0c4203100070f0f108030444040d190000e42e080d11381e01944255041c03590a03154030460303001c014001815424800c0001500e81035403801d40040c01c2030541d0340d90f8002e13041c603442615228413006600d5141400300303140d20740261106008d00082610207241d407145600901584081075817002005140c030f4042c642c06800d91000c0e13103607151030b030820710f001040b0798011654000c000000d0000c3c400d1003803140c038451075158410035502c41a0700d030740c50000d0765806404d0312081003060b8800e0000300d41c400540d070700c40c40080007a03420001d103a400c400c000b030043c183d01800c55403070880c03440b05206002c801000d0b00e034450000103981080c80c1c000c0118051980e9058000202d002188001c0c1d80416400003403031541406007400c00b810001c001560b41c2c1816008140010725905001169140b80c1c003601d900b04084820340d0030300c000b2829009544aaa800003940700d40d0503801d441041c140 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 746343021 1250 746341771 746341787
    0x3100806010501121808040902040303030e03091c030c080a0806130b03070b07030903050d030e1212070e01031508010e0c1206040b0402150412110306090705010f030204050406080a050609061e07 85
    0x64003044a50301c0e50740e2505100022b4000703100c1035000c40d040012104220b207001c4110390300b540008100c0044140524111201100101e0044041c410008008004101a00003900691000341d66805081c900f480520038190342c11001d011000e4141403079903280b5a0081008002e4403007802440380c81e06101d0800b00c0355450ba650028059005a400e0b803001c00342c0c903400103544070055600700c6001140d0100503403580e01c5160035445598030300d180401c02092203003442c82803490052601085001c4480342c8050780c400d25a0029500d0382d0356414201d03e90405100001c001c0200312484503c10401080311900c448006000500c550040e500080071507880f1203c5d07644086610403070685039512000c01c40440f4102400070307251000081501c4250785400108144a20442c6018004e6a464031005403055a4084208001e25409002c08211a200d9120341401090120001c01c0480340d1410800d0a02070041d01091150b0440320070440001c0003500112120091503000c58a590707140f00e000c54000d8 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 746344271 1250 746343021 746343023
    0xf031112070b0402090f0c03150111011a1c08041206141f0f06050706090602041a0403060c050c12070515010311090105030102090d0b040c0f0803031008060105011218 73
    0x12401191107001d101500c448240b150b842545c070306200e902c1c2c441c43d04004520454808421407420400200d544ca0346420005821106050249084210141050940d038040080b11809028084000f9452812080e482103600c041d44402010502c951603030262807040703004020111541c0640003007009540d600c0700750003541c20b00101b0554200b00601a00e01ca54080d10f0600c0115070803008114403050011000c1200c2c907540f185031401400395030b084060a48500165100c4d85d00b408005100b000081130040f00703290405006683d50304520b42441110004181c0c541040428400c2c001806c10000d005030081d01000c1100d0344410701c40c43c2442c0b801156800440d500c8104800000c200440000c0000c1541003c17503510a080e81c0307482c1850700700e008809140394001000044000454a24150350b80c0117070141c00b8000306e0680750410700c0c03082c00ca2a03001e010715503c00410046103c400a05900c00342c50504098006540350400003403100f60b42c1585d05410555134000c0010401440e004001c1d81 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 746345521 1250 746344271 746344303
    0x110304060c0212011517150403031a12010b01030e010c0c0308090109120504051309080405150c0a1112010b01050904111606020a18051305281a010c0f0311 68
    0x40d032010406144d501607a03100e40088048030011000562802180346e8040d00041f5200d40f0319540c56440c1103000d0f09007456030f54102425014400c40b1610b41c03a5040303940500903030000c254800488001411920480c1400c1c0050b45482d4900c00341c942d0040e815000c1d01c4c0c2600d002107854841004803401001c00817001080100d0083c00d51071030030380000141c012514115a840f5400c0ba901301006c042c0c3c1c082060042100a0400061103245050b101021440c0054000f560802562040591070038440c814151150707070394610702128515200140d0040f28040f64000e0049041300400a4810b0040042d10b0340301e03680b94280304105a014601303807404294051500c03110140c0c03074208030000303520902840e40011800071054079118819805102180d00181809010040c0102c074100149006003241c081d01c0c000c2c0028860000403406001c0000340e8210b00003e00e40c41c0508070408108aa0407003e0601140e4007089001c2140d40b82c040c00c145802d400c10740410440c81c0c015600b8031103417011840e50 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 746346771 1250 746345521 746345531
    0x70201230c061503150105040c0306050a0f1a04030b0105012d12380a0e0406020c0601092c0c0d03030e060f1003030f02030d1b0807110304060c021201 66
    0x15a4006440c0d80144010810f079840d0312030030420303d500e0f10412003205c11000c00185c010841420705500c071000a0410f85070000e443e940b64000120940f0099001c54825084008140492030744600300e4a404914000d4003490a80b56640b0440b03400e03014407909041c402001c6414450902d140c505800c180400031000c6901c40030704a015151005201c0360300e00540c0350503522000d44c0141d00c4801c0064000310420840890116500300c0524030001c075242e00003114650000706403130200f032041e0240388a0400981c80c1d03044000b0140c60008141d1003400d496050200b1407480651030403d4407281c8400348001100d40c080c808440d494036600401d120b4004040744102e03424154540e0101460310014001c0d20210f40700c003004207442c080d00b03850552011800c41c1c1d003040064003520a04440003c1e0307005030781c2441148001e0000700d034015800b50440c5102822041402903010240c0360f8411024240001c0d20b0300790340d07511552030003140260814856a420306000755a50303101d2100c01103100d40005d01c1 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 746348021 1250 746346771 746346787
    0x211f02040b0406080f091603080f07050111030405010f06181d0601181a0a0608070207050a03111002060c0d0207020a0905070201090203150f0c0d09021f0e0f030307020123 75
    0xc9131401701e41034106030003000041001c0010209041080c4031b2040c031120381c9a411034071a08181d90090420f40d0101c201040110000b0320280526092040200202910b0349083d00b401401e454405905d44010340c42c0010a1103100344002d030b00d00519a080c0d600084090740b00b00244000081c0303800c4c5076050302c155000002d020300f15840c07469555400302030901040a40701c40d0604110000880d07254058040081806110310503e801c0ea03201c2081c3c8122940340f82e1701c0010400b20360301600b09444508001d455041e45017043c000389078000340725200800076880c1c0521190790b036001d54049040820b80004000056640d130a0041015210101c01041641031442002c2d0082c658140e00302d0190251049400603001c0400000344a4050481580301c2c50707890880c007101c0c0ea40b0880e03040d50050b81d22410280562281003c640d070300c0003860140c035901285400c010f400a442c0c849198800e0300400503030912a10702109540c4100d50a00f0665000030348114146d1121004004d069058000804c80407 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 746349271 1250 746348021 746348027
    0xc0a021002090103290109050a0b04030305090a0909050a0614090607030b060f120109050c070f060504031e112a101b0b01060305071704110310020c0606211f02040b0406 74
    0x307100d80b142600d42480c11583d071402c6c040560341c0ac0c07090038002d1034140000c00110b07009000070800540d006150b241081d850ba04081d003150184a8140c0d480d0b8454003085080203040c0c42441c00241c2d0b200051585447c044558903034911005040c1c0b0f0030180c444580c01c84580340d64040e50440c1c022444840c3c0c448922801640c5104002d1055509181c05e080105404403215070860701c505410018080581c4030b5a01c414004e000060422410030500003404c404040c01c4000c0141001c0c125900c0800462809407a81e01d852200c1c21a00c030001c02e6500091400702c204800f81243c0d03079082d51407441200d885101600d5202c92440d80b005125841a0300750f041200c034001c054143c075001d80b420802526109c408444800603191458880c07041000864086181d40e0200c92060000404a99012410181d45c1f802d03a000a40080c0741e0354400d0090000e81d1600b01c1c407550307200441c0207000c0d080c145030500031a994401d48141100502c0149002158800d480c4c040750060f040700003105980e5580c4980003 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 746350521 1250 746349271 746349341
    0x304112e0e0f0402030c0a051303140c0906120a0201180902040803040801110a080414070302031006140603130803150303130e070314012c010603060303080c0a021002090103 76
    0x40c1d072240e0036508034015503162501c00d5a000d090400340060030300010500c10386082c1c0c40010003107010400441c000000500c8101c2081840c0440d1000e8290660340c881400114503028060901c80c580b85140b88d503c00c100014400007103502480c0c440c0b020100070801160301d0095403c2070210390f0000502088000000000380112580f030402000440d1004110b141c4c5402045054000915110081004a803c40021710b450103a220191a030040d138170740c00a4034003c10400801c15079500d5000401041641c00bd6514240300c06a6500e450b51411066408802a90030300042c44201c011000c1900080140b501100c8140040c0c12290385d0008128182002d611503c03844258031450300010305403501c40d00500903030400824101c1c01503420200004d01340c00c080b640f075002240c00c0c10000100742071607040c542e00070b20032910001106815402c00034100d4400a01d5220128000c10075055034030f03400034040300e00e420000001600d501301c1c0d0f00101c0c06003240c0b10100030712903480300c0041071414400c80c2d0 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 746351771 1250 746350521 746350547
    0x40606020f070b09030307081b01060915050d15180f08031012020f01080c0d09060e0f03070c062a05010c090815150f030601030807030f050304112e 65
    0x12107150668031100c280f00b40c4030f442c60844e0103070001c1c00903a000524100152880c9c0b507000c1010180b1486014205084035400d901c132050b917544071550603a0509141e14000040d00042d142890080319503142c9109040c0305050400e80359542c2c1c5a10142c00c000754203600304441d400040340000180034104115990004c2d5400c0078000801100044d8103021151a90002c41c1e015105070044140140159083c0380004c01012511004018210103012584549050310b40708070030004031400408141443c201144000c0066584100001804100c40301400e00032514180b0b820840c11414000040203a201010907002e10100040440c04100c0c064000c00b0403000b10f65242d80307502c2e0740d94664580c0c852884105504209412001c2021142802017054241707001420001100e10403c011914000090b0f2042d0303005030f0003003401410564400001a040ba0280c5402070543c18a6160090110500e440c1544561404d03400e89020300d4450340f1001c000c800322488100750011a03103001c1c0c0f07000b00401e8 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 746353021 1250 746351771 746351773
    0x210809030f030c06250c150609020a0903120201061a0309010216030f03050708280b0d0317010506121303020f0f2b08160908010501030c030b0a14060618040606020f 72
    0x3030503001807540c0340c5c0c1200c406038455440980c2d1441c00d40300c409911407000280700c00b094a4a0011078034500700e000603c100007030b547d40c00b01420701d0360a1801e02804401040000c690600d1f000b001100903030302103a0440c805400c1c1540c0d5a1b12030000a40c0240300360306000c400650410601c9080c142c004101d001d5030b1403651400c0c0280d541c0c00d402254a00720807148400d516002d0580110304400d40140305485e508408800180707101c81c10001032070317407810b510110700107088541181c10f8140d003214102d005180684596050103400406000086001410055032210261845081c0343c402c014469001c04150150750003803450040f00c1d0303180e90860030241c100703600c42c0311902d0302050305981c24505a90740c0d41c0e4541541d251201e9401d14000c6605450341048124407010604603002c1c40307914004c502c180c05103188289140303026610580b0044c01d40031070314602104402c000902507032655005000302c07400e550701d80704000c00b440420000250705030018948500850f80a8001910211180c0900 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 746354271 1250 746353021 746353051
    0x15090509072705060a0507050a020a0803041d07021f0b09042609060d11040e070f0e011b030e011403040b01080f03041a0706020f0307020d09210809030f030c06 70
    0x159030307080300350442c4601c91304000d00300400c4000710b2042000e012141e1289040d5211003105400080c006a07072500402c11681000800304000d45c0041510006281b100580710410300d441c030703030103904c5031149051041102146801d9042c84443c6501c804180c8000500c020018106410a99484d003145603005071030100c1040c00188660860040ea003900600800d43c031324214001003103c0240c0074200191204600a12000c04e1440d281032007079200386513a80d20710600754000440185010440035409050250081c0d981c2c00724170038000300164031038142c00d02d1840c06a13000c00485d40c42d416019010401400032050008010003c0c80850403105d41350308680034410980105926481248181410340d21130900c10042d04035904085d00c00d0b540110340040c00c04041c00803105150b44121488401608021845003030180c00401600150492a141c159940f0807080c0c000c1c400508104090480c030008112581d403a501082400f00d041c1801017940d0300c0702d00c807101e65680c80d50306aa6041c4420303c41 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 746355521 1250 746354271 746354327
    0x30804350f060c0421020a0e0a050f07050721050408030a090e2809060b0a14031002042312010c081b0708090d0501090b16200303011509050907 63
    0xa503040c0c40036a000c003000d50280301c055840017109071200d1002242c00c01d40701e40001480030190700300c00744100030310f000c045182c1c601290b1015030140c004062100b40801030080303202140c801454102c04400a203508041490a2201525036028980c840d1003180300c000b444103c410391147c94201150000d0340280c82a8440e0310850030391640300c1d000815100018040007102e42c0080d007003c000d0341d0141c1e400140c210344600118141d03906580100c0e8520f00251210b00c0d0b075040401420813920501e480c110708103410301e40d0b44010344100200340300301f44103080424407003595660b050240000d01034008008650719140d020382280000c5540c40c04803100c1544126800007000c0850310559801440f803490090306804200007841c450700d040e030725590703106010b03000a0750001c4114019001104c02c0c41014080050080000440c0218240707000c40a039814000d5100000a5034103548680103130511042e40312030b007198031070507030752145601a500c60300b03020141d41c01880485240c003009183d411500c0c0d05c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 746356771 1250 746355521 746355541
    0x30050303160822080d1112270d0f05090604090b1201020901121d01090803011403030403020a0303260c090f09130b100504110a0f09030804350f06 64
    0x5035882c43c603110450040e0041c00601c10300c1c01072400e010090030026920180001c210342d107070080b600100083d100b04003409003060302d5041002480c03102d081084010103003400c0b0240c5429151001005000001c02603402160044d0295607801101400868465545102d11005081103201503406401411000c41c91200e041c000ca44c20300c54184c5461024452a0748a24001c00c4900d540550b810200444400e4030032082c00303044900780c010a107098495040000c0c0c010403040d8103003100e10071b0380100b0041006850f0100200100c9416080c4003c0824405040c4080d611000107580480c40b0103a040081300c0051030b001c0e02c240c0f80140c40c0344405118031014400c00c0001036442021618000700d080000a1780c42101c150b00540c5404542035050766203011405544522156009000300800c10000a1b5030205071a841da1219180c440011459503d481100d0711460040c1407981c0c50f02035000c0240d49815102e42c0058210812981080f10101105034071040220508142c5004d52804102d41441e = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 746358021 1250 746356771 746356801
    0xb0105070302060c03130618061d1e0102070b040507061e02100509010e07080a1103060f040602130e010806040512040b1c0b1005120a0501300503031608 67
    0xd41030b002014030791242c040f038010940008100c2405000b0398000240024001d008010510001244514004c2c401e0314004003655140981d0580e214101c144070f4402c500001000740c0c80c140c4c110200700003001c0101c03041c2c1c007900c10b019024003054800403e020802c000040c0c0d82084411665640b102c40e40c03400d507480300036000d0b510b040c00141e02200390743c400c16400e07600180d00481c401d40002444210344031482d04210240e80640019009100c81400317004e0b4654006e0103030f2200300d010306002d18040c2e0f580a55000042c201405055021900c180e0300c004c0e07484010054586044031892641e07407409240d55408084a04076030b28000c2424100c40c0d800ca12080d1030644042d080181d0411030314038202070700c510034003000f4035100fa00d40848805907140c440d03242c5029422642d5460380d5071140412000c0d00907024000007101c0746400010072840b41d40c1d03e0081500514980703100c01c409145214401904010000130300350f0f00000040c052040d820303031144200c01010352140a840d0f5911003088c4484070b = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 746359271 1250 746358021 746358023
    0x14070f1a09010c172701060f081c020a031211270f0a14061905030103120c030c0215070b0c090a0501180504110d0c02011401090b01270308030a0f0b010507 68
    0x810384004035a0482e0f0003941000a043e1848a0003039005508250b175081d81d80584c403501c000c81c20b0f09000e20032404184104107112504080800361032a100070000d64920001b840a8208100640c2c1400c640080350404090076030101801611741c002410890601d07401c4080c1c03022a2409030000008504240a803229a0b070402401d00241c20301c0c0c4941628142103201503154000c0701003041c00800890ae09070142c10a82c1a46d43c0c9890791304500d40030701000050034081c010700100200700700010340e00c04a00c0c4002541a80d200c6840114060900c409004981000340113200040401181108910281044001c11100742d0183c90341c0b64015500040080c5030374032034414064080c885410160440c0409140510609140440c5003001a086600c6000c2d0100141d4440001d9940d07400145051405040340341010405403407034400207070501c0e64407031005500d00704d900d514401c0740c040c0710345c200011a00483d20300c1e0b580c81c000c404400107203500044a0f168030b00d00040518a035100f94103440c1c1c21 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 746360521 1250 746359271 746359307
    0x11b0e0d0201080901090606230108220f020612040303050610091707150c2609010e060423090c0c0d030203060f210f01020a14070f1a09010c 62
    0x540e5400450340042c000b00102002e64840a6083c0042c40c5446258010458400c1c20501c0064841442031805800640c19040141392000d2008200303407508001100c00c084000a9550352091414038000104684041d41c03007803002c50540c83c1c0c0c0e00c0a800f0b19204620960b01001165035420410000d103603440b00600c00104a81c00c148544603a500384901480b408000710344c0443e80c2c03802c03000142d410300c14244000408003004081004840c4d00d17403110008181000c99020070400c05064050f01800c0143da040007880c0307500c52265140c0364110342c0507100106400d1503140404181d03007603085560181d41d0244c10b83d840000d5002c990203041e0360905400001800d030148043c0c1c2d040740030303401c042c1604d03911004c0340114034500e94a031300c65541501107100812901c0841001003034185401800c1d048407a9004020141d200c5601800d0010082100c8002c240c03074400508007080880104000245440c0c407d41900b015400700b178025074031800c01c0d14024020798949c81c03000c40b083d0030140322111170 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 746361771 1250 746360521 746360539
    0x71a0702070302100302030916141c050303010314010513021503040c030501061e08060601050906030a0f09031d0909030d02180405101809081804200a0e0303040e0114030304080f011b0e 81
    0x35494000080e1103072f0292410941960002030f201d0a04541c402c0e84100c441c1c2c030b150703042c4c1c1403944020b018141e440404000d08a0448441e5004183c2146032003808114404001000804100640d88110091500400208002030b116481c02c011410402c0382c80003034040e013180c00900c0500c0064000c0c030030320060795400e0034074000f0001e0081c0c54101070b003a111120340340d0148240e00d4400d03125100706a40070750f0b07529003480661060343c01c1d20a078281c0d40900607140d0740100030913a0310000071189a98024480142d40358524100c1c41250601c003c2e10f2a801400c05050050541c0141c4029040d6050b4040701003580042c6150241199800c090003030154101380700d4540382d5051461091a0014080d0000c203480c0402d6105024407a0004580c55804a001c070f0a40b21040d40302c0030710a002c0f030090b00114605420510094500141440707210640510303400c1c210300d40c2d02c041c401c0e0b42c000e102800449840c0d0551418581c0640100c80b201620b101038007540305d41c824030034900c280390b03540041c010340d41d = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 746363021 1250 746361771 746361809
    0xd120519051023090f07091511010e15070f080c0706090812010e0c160209071416050c010e0d0b101206060f0b071a0702070302100302030916 62
    0x2000d00030003003520001d200c2d801c02c0054034605080440b0707a406410056051805181810081e00c100043c00d52030782c80c60303030724200498076820081c444240e51250204c681a403d8400040b00d4400d005102c0020950925424000e21000011100071080e607003c500d4a083e40c640100b241c4081d044480c000005141c02c001c1412008480c0041581d80c0c000c82000ca035485407900c800400e54010358940607400c40d40740c01080030304640461281c1081284004130f141c24006410103000e050000b0020b44102000c00102d02460b026484090b01c21100c440060f8540c440300000c0121400d00f2a41500d05009550901941d98498208001503500041c0301081202441c0c07180b9841c110000d00c2001915091240841d044113440710700d405281c4032f8100821a64245003280e800c2d221540d2004005800038441c190004410645402c900d142406d0348003219a95003000300d241145582c4060b40081110010080203607040d002144144040422540c6070940701000d20454050340c428414240c01c1040041 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 746364271 1250 746363021 746363071
    0x1e030102041d1e130f06020318070906080a02061b01050c0a021c0f080a0b0a082a061209120f030708060d02010f0f1206090b0108130c060c05030d0e0d1205 68
    0x4410036028145180003085c2c01e80d02c1c00100da005580a400b0003081096030f8103c0c1104210290190080e13803011301c103d5160100890380d60b90b2040009208020100300d0f8040e414a460003030741e241009400034007003030400300507410040d031041140c1001070140c00c000e81566802031111860040b000c4d03844480300c00201d0740444440300c0203040e094032143c54024441e0b0642e03601c2d04003009480e4040140c0513203c192078071501c940c0822002404441d140403d20030302c81da01c10b030603500810352000011500f6500d80400c07a061443c15040c61038114000b21740d01460982520142d8881e800e261117a50080d1100000c124500c961740000a001a0601c3c0f44854480e01c9201000c0c0c20078901c3c10103207003040b06a0140000e495258021113883c942ea1078a803425581d01190060304040e80c00d0818092400c29200c4910000d8103004035000c3c81131810030282044000c0003100d0150120075400c01c100e40307030302200640384ca20700610301c0d0000d40c00da12600d0304e81d9802e129583c05041032441d403a00d125174424440c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 746365521 1250 746364271 746364301
    0x405040f0207050f0610061107060c03170106120c031e0f0b0303190f0c080405091b070b0f0703020c1908040b12010e01061d1e030102041d1e 62
    0x16241c0a1000900207001003291180c100282e074054411440c02d01c060172094083c0c3d5000d40200100030b030405504040200f51754050740c11601e1705020040441c241a0b55441500d070182c50b041102a00029940348d00c0300f6000c07010b58490506100c0700c0c0412000300c007620405414110a2070403040e1503818002c01e60f10a0401c088018408940d5009480010341950410100f2520300d0041c086441c11042d032041201d50096401c0c1031121648a0310780f94000c46010b04d0007007030b00a09480c1d02103002c0d46120f2003900f660070b5548201030781c0c880540c5058040c44e8029100a4012000d0a004c914041c0c024001c6d240c4003140c10000b042c25603100d031444a4240d940c0c034010380700104100808900c1d41c51000082000c3d050001d20340c1a1540745c40c031794a204c160141d202c0310800c441c0c039026420b4120ba4400c4100e5101d8211000060f24015840c0c0d2260400004600d6038107610000d00050710b00091118410ba048510210b81495900c40302810030f250019128000741503010b0300010034130840c442c10 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 746366771 1250 746365521 746365541
    0xd1103090c12010e010609140901061214031b03211308071a0708011d0103030503070e031006080d020c040e0d0f12021b1c1e0e0a0f18060b040504 64
    0x1180c8508003040f03131070840d903c45d0401c88040c0c4c0c42d85800c4d069402801c08081d00407610800030884c1618007645440903180c44800203082c210700032214140420704005980c00340041501c0c3c4001c8551101540b90f8a07845410104003104002124005001885410500c601c03110b0605402c15140c6036034050341a03005100403511645807074400c55011500c1c400300791050140351500070f1154102850f00004011161584050707e28000040c0002580701040e290005114182400f06c100e5000010f810044104100388a00c2d00c2c0840c002260200042d03c40e5032014207400707940c0300201c104280000d54191b00a025500d9120f582c4e0380f03180c50321880544a02d00450b10300b006070124081c02d60414ce91140e04000ba00c1d011182c801803082d4414007078076070320111040900c03000f2000c1d144003800c02885d42944200e0301d2040d0421225441c0501c1c900010444000e0020a4441d150551101c141e1503d000394095520348a500004500c810720bd9003094442c0e003032009060034640020000a030000001c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 746368021 1250 746366771 746366773
    0x21f0207141801120b0109050411040b1809160602070308040b030603031c06060801060521060a0e1602061308030c0a0c0b04110118030c05090903041a0d1103090c12 72
    0x1d000b041c10001451018003819038541c504071200814103080e0b460303440607008103250900e80340034030000842503d00241e58101c246c40105003584510b0005100e03030080155290340b050700e1700c10441c0088000c218100c0c80b07520605641a219100d19040341d650500d40801061401c1c00c120030b000c0d44070346d5400343d680250000e003181d1038500ba80044c2c406101042c015901700035150704080c01100c2d001070301180506034502c3c01c0743c2003040b035502c0118611b0058042e10094440724000c0345564603030780301e440c001d018859100180b50034042a150701410140480c07030300500800d0007203140410100b5102c01d026420410450458407280b92040541c0c1c4548801d4081c40740034004900050300e551201c034030072800f0300300c44500c40c0460f40c009031010b0515164011043e940b09070a0002800e0800b0b100d0a03078409840071030b0a5030702e070144a80b43d88610303040309150400f5003c0b03001070541c5500c02082032003000d10052004840c061903404550005403000055070304040515025410811101c11080d85544 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 746369271 1250 746368021 746368039
    0x9060115080a0923011a0103020a0519110a111c0f03110715050703020106060315090b040207020607120f08010609120f29150607170408150103021f020714 68
    0xc050b0030f065500713a50031060980d4461168038041c80d00005810b0a0346003e080c158a03160010400a100e4440c1100c4052210350051000000701d100f80d00389102844074200300d40b002801c0c0e0030007038241465242e9051291070300702210ba541c03400d0b2840300501c5a5101880e0800b11444d5035040e00da601c40390b00c1040061180b0b031000204032002c0c82d9410016900390310b4696980d030346410000c0c2903c0f801d40111040c5410949110301d0811001135a104445440d48001148164640090064890711001a62120005c1504824483d43d492a213001c0130441d103c2c4800a110f003c0c0c00d640450091080c00042202c0c0c00d01041401d80322409920707824480d807203041e582c00c144d03a50442e441b502c044102c0d030b040c0700d5450b104c2c60031445825825080182d03403c8003081c3c00d2125001941c2407081d008004c2000451a4101301107031140016039014240030300c2540c8220143c4110780d004c405003440187e11030001c1442c0008140c070042e00d03080d528092a030150860030300b00080b5820f46101c0e560941d4101d405c0c1 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 746370521 1250 746369271 746369303
    0x1406031503030f0a02011406030c01050903160f05010809060f13031e08010f1e120c0f0608160c0309060806030a0606090b030d09080c041503050f0609060115080a09 72
    0x20b00c0140303410403054100035120201c2c100b000b030864516441843e99804854140f10880c0d900041c003281400007464a203030f440042d000800d040901c20000000e5203400076102040c110383c0c28000b84180d4801380e031030301c0156482c000300f1940d0740fa05950540711f442180e4040360803c0b00035440703a28002d0082c20b00d40070700009881900d040392100100c050010f10890014043c3c0301060207890000c041c90020061200100b4134808980b0b0494441c000d00743d4100307400c1c4030410414400ca10b00074011b021141664540d959405454500e040310744001c080c6052101d001224000c0144102c510b07011b64a0b4490641000816940307404050040d0b54540b081c1c0cae130020000b07980b40c0940d1014003026440841d015141005145c64030048500440c00d1088a40040c042a040025168020402290702240f21180861018065100c1d50400b50582c081e00c520100407240015480c7e004041070821103001e0781e03807074115035201c0000c01d0660340003c400c540400c0d48a07800d600709040e0f0b03034000e441610f10f100b40 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 746371771 1250 746370521 746370523
    0x50f030402061327151a0c1f0204031101050c0c0f0f04090f0b070302041d060d062409060807090f1b0c0303050f0c0d0914061e0604061406031503 64
    0x8024503560b4019515005100c050000380100d50704010000e030f41c44851400e00f000c034040c00c421824080e81d001d1000c034041d0800c04003000150f10340c01d0031a0780c01848c001070311391900195129010580e42c143c00c0710030042041d4410b00c111001154000060141424084200220b01300380520700c5034000000100400300c0d9456204184009224080004184205151103d00c0c601c0091040c018984148010000c802d040b42e442440075140000301549a42c0c2e100c00211556041c40c03024088a2400350420042e4825010a545c0301c0c455158140b07030540d0714050b6100b40d070542d0040390901d801c107003420400da20650700015000100381101103101c0d5840001409019211401c0c4400126103c00c51070506405118481d045000107500705840c0c13074280c51070081031194505004071b150b03486d1042c0040c00200601003030f030282d0b01c1040c0c80340c50520302859000e00107609048800481d070744011038034900e0144580b04c121960300320b160316446900010413100d80c10051241740103d040c902e501d015990 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 746373021 1250 746371771 746371799
    0x10f050a0e0411160201020c18011217030709210305220315020301171501030807051f0f0606052d0408070b07031e08010b1b070b04080c01050f0304020613 68
    0x31602c43da81c4d8040150000920380180106030038042c1c0c003100386c4200299445080340f81501d94075201408166140d240100d030107240b90302d48596160780130051151140d400303910201220000c0c4801d80424507811008400d60003d00c100401281c01088442100b0159251443e480c00310080c0c40a40d8958a4555170007400d001140ba03007146600100500106801c00c03058180d2580c044001c0511a0380f001e40703450750050600000d00380181c00700e280820072004212207a03200d010500290072910881002401800c54a019030b40540d04042000c18468811001c1d942c4110490b141500750501041d00f05882c1503124801d18402d140802000c91000d408210000050210380301301c594450300b41c21f0080203885c1070f9007102c040c400390344401c0c220103a0040110f0b040d2582c44031410380e01d207481c02c04100d00c0c00c40e5542200070350007800c0001400c2d1010f8800b60040b070707004005a0b00001c0e009401140c4e0b5110302850455030100030702c0440c0c0541002c4010700701254012040b0031005466400010400d1 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 746374271 1250 746373021 746373037
    0x1008070902120f0103110906061c06080601051822050718050c03041a0606041e050420190c0b0406051f1809050106030c0e15010f050a0e0411 62
    0x140d00007070000041c0040c0440550f114a0b1540003510359415503940b0000d6030508140c5034400c0003035101184040d17a03208100d0350106241c0d00890001e08407480500054001440b074192503003e00400090a800c0c01100c080b009800c00c0a0307645995109110051001c0c4002d080041c4803050209400c001442001030034041c00340d401c000301c840c94000441c1c0094801c000e1a5402118040c001d103c00254035075020094400000c9884910795036040108155009503481810a020107a80310207101ea50380603a1002c4c1d607410356081c00131000c100e07201d0700a0318900f03004840400d800c21907541990ba551035008103c4020b440c08520403102130b26240342648003036a050f00d402e5929810310025056981541c02002c984c7c44201c1726a514269485800b0802001000707211616a51504100a000c1d8411005198414000a2240e031514039502d00c80b2000c813042452a00e45444491043d80a512507440f00c1c40e09a5030f0f18540f99a885046031180c0110860640064a50704200c00603481c0c00040d101c24 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 746375521 1250 746374271 746374289
    0xf0e06092817120603010603031b0f0b1303080603010606080115050408070b04170d08070c05100e01090309080708070501030903020102130b180114070f050708160314031c05100807 79
    0x40c3c030310741038000081a0f010380124400ea00d03000003000080c0d0418070300b244410200c0f0034000d00d0562400c044195400b086c5004101c0080807041004010202d001130341024001d0340c484442d41d07a00300030b2508852490042c800410300d0324004000405000d40c800303581c5401480d0880c1055a20030106240444036040443d50020206d0188111900a455203070420b021000402ca11206182e01074020300000d400364041042d20020728060060800400d030701c90b442c80900300a8a1034010042d4001c02406404400040901d1800100c84400098000035200e448014018040c0340900650081c0140c0d001201555020b101519400c2714800180300142180c8103160741c0d032034910031401d40603034a5400d03940c1030101610542e506003600c0f03000d81d6000755100d80348044d0400b45090092030b06050b0b502c00c045510078082190000480e03031f0215030849104041d244151400711300e103581c89000e408495021044c8812010500d000107401440d00061601c41c0b11000340d89402c1c0c030b01c1c1404e226801c604c400c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 746376771 1250 746375521 746375527
    0x50910050403080711160b03100305160609050d1e02131508060a0c02061b042303011103092505060a020618010507171009050a0f0e06092817 62
    0x103180c0150800d840f5503085c0740545030115401048010144d10360280313040280c008000200d14680845150b006180c0000480e00a41c54140c809450925140190750020780454000a141c1c2488021081c65640c480003d076000140407100c00c051940390007007aa4000d0000046413501c1901d8030030224070000c00c00d82040800c0c10502000e150000c0a0444000d01c0e180c54480030f8542c0c1d000c20900e42084050300300e69803254144545804602413070300400c5080d0060301c40c1c2c035030300b07200761041d07000400040d0001d0055000340d640c0c0385a00c4c081102c50013680d0700041c65526404c042c040c0080c0c203400000c244145529104c40100d01c031500000015400b5034055030600c840c0b9585101c105186604c010003e0185252a15004203a459407180c0c1c40340b01c054a81c081003400c0b00c512081405404040c504003c0b03440c1c282c219101600d2040e80c200389807494180024515000402d07031910590f1101d008040c0703485440d03015030f1500b09855103295200102e041c3d0f03c000070100340c0c00b607820b011072015142d1 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 746378021 1250 746376771 746376781
    0x1203030c0f0e01050306061e04030c0b0a09030b100f0626130b0403030b0306040c0303080f06010e0f01200a020307060801080d1b0f060507171905091005040308 70
    0x8111500d03040814280900c0126080d205648410900040c240c01c1c42e0040e100d4680b400450224064a50222140c0c0301c500c50f0510710301000805403048a004007090305515580d03210b050441d02c5410054000580791710f00500c0400c200480c0283c0282c005940107011a5640035841d200114903000b2400051016862801c84541d15200000c180c144940c1e100c03c60400d1f9900b440c510b40c030200e0003400c2001150004080c1800383d40f1040034200e024064540714070b41442c04010b0000240000c0f030101e400c10021411307000405009900c0f92006031510142d8825020802001024540510b4100448007100d044128a000000828894807030000e0003031804a204050405403c1c0c1c04c020104000240100b1920500089c4d81004180c1420485100321401280f0440b001c088a40500702e0a0402120001c1014990183c0e101d200b540d520b001101c500901880980141540d4040804400145840d0011050350106030090503a404803860403a100c03000030300340c0d9070484040c0c02240e00301081113 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 746379271 1250 746378021 746378027
    0x3070908060c09010309031b2303030f061507020d0c17030c0c010e01201e010218040510051e03010b0603060d1412180f03010c050f070c0f1203 63
    0x26140c040081c000614140c480d055007402100c04150400d612045200141400b0700100d081540b04010f0120444281d4100203c900d00488000707011140c040124005111000c07003501d02a183c40b00204241e6150305003002406883c4409100705150200101d0300183c2e03408003030051007403054122581d020700e0008070414201100a50880075001085103542c01500460038a071074807424281001c075840d071200101c8005000941c0204203061120070120210000201c02c03056698030300112107007501000116085c1d004820324218a141c0170a024445403419402507584180c105080041003551180050900002d410003030300990034400107110b1909081c001c00d4100c0c0e4003561181d2940c10088081803450803901c8000c0e080383c0e00000e810111010070701c0030f2000d0b0859010841d0f00ca9110842140040741d09080f883d00c89e40100740303810140c1c1010b0040d0346014402c0d07152075003011610341071480340b80c1c40079004403040c4c081000302150320490524004003402031000c40310000b00b8103140c09 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 746380521 1250 746379271 746379287
    0x2a080601140f01020a03120603020a0303031406011803081c0c180801151202031e010b1f080408031302030a03030605090a050105030d05070201030906140702100c020601140105090a08030307 83
    0xa24000c2d0302454915050382d80000d2241d0b07a941d40761900070079035040081140028226071300002d500902092000040c0741e8950800000c80e006c403410041c280e03c0341e80041d108607052151074500c2840014007000401c0c1001c000d4440c039048010707100704030085143d426048030613a03542040821950022556581c21464514014003c40402007104d03070154094500c03003002c1071280e1000030018172029000c42d18107002c01c0c2d2403150080b0302c02c021500e8a078241070181600c0e01529010ba4900c81c800000d650946088000c000810340354981c0946858035140e055510091020381c010703d900202000580f410400740d01510b00a070b40004099050508204030410b02500740c4071294101350051102c0c1e500030481680400090514580d0f075029840160007034941d081c40a080d01c0d10702400c1104403626426814481d400c41d9081e503610b8000c8079100c41c103c030324181c01900181d00c160010702410900ca611040d14250504050b414440c2400002e605110366400400700382c4c0000c4148081039400c1681 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 746381771 1250 746380521 746380559
    0x3010e03120117030f09010c0b0403092909100908070623130e06030c061b011b08011215150503161a07020103060b0a0c03080f070c2a080601 62
    0x1c0b80d6440f40300e4100d0150740303009000f102c54101d1000540410030b0307030143c0f4441d2981c0b640001c034803840d41703060f0401400840b1241724000d11011041da449036002c2d90b0020001c020754100340e20314100040b12060100311080c007010394080c44607100020035200010090ba600410306540d54a615100704000d200748030384044490012a40144400c02c1d00d941c5003102902591546c1c0340c410501c3c0d0340d0100103441d15030000d400e26001040024044045c140008102180070041c00003032086021038207903c142880e0b00c50300400003494010051210380e14194aa500103809a010300504903401c2101c07008546001040030103980096a0400150405115001e008072541e56204241c0d0702d80801c0c9800a5140c8008a48424000440c5011a80280d01030301c00340c00003004143e100c0c0552000640030700c035611000e80200b82c20000059118041c030b1a501e100f0811513641d2060002265280d40540c2511403094001c61032240c02404102c0851500100900383c20004080d50b51400c00c080120201d41c2c80 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 746383021 1250 746381771 746381789
    0x50717010b030f360111040e1b09060f2706341203240b0c0a0605090a1b0b030f0705251109040c170a0203010e031201 52
    0x1080402000800c0d03a40c8a8103c40c81c01c0701d581c1d6010b482c40f00c104007a01c012909981200c0716580440e8200c01440e01e15501d144c000c0001c40c1d4000401e6510f4060b40c441c2c0b43c0746103600000150000a08500740b070a6007103d82e281c9040c011b50000051280e04821141070311028041900030000b15020243c41400060004600e02180038001007071a5205100000c2802550303000705040c2c07600c1140c800c00680902103d0030280c581c091515001c001400120040040d0404804d0482c10440e40d108044000301315501c2e01065242c206284995080032000464901407030410703c003c0b51481c0549445039940d000600251095032518400319103140b00d10f0b680783c0013202400d100e0f002c8090700f00c9404c4542c80443c0806999845000c4915105080b6150740d02424060f10820320f4200112405545208156844002d0b8581d820311103034000403103001d0280d00414000304002c8c0c0120340442d0b034920309002030701e040b01119000302e802c2d10b03825800d001c1e107070b4000030301d14100380c20700c191550240c800d000c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 746384271 1250 746383021 746383067
    0x1d070c03050a0315170708150108190206120f0115050c0604170c010212070f02011b05030c0d02070b09010c0f0906080a0e0d031e140c0706060b04090507 67
    0xd24000c0c032034064410301409056072503102040c0c0c038001c1082c2400403d1141c80c2c04201424070504561076039044e2244400c0d0f1b104403220040000c441c410040d043e01d11850040c550308840d8100280d0380c0008000c10f0780c100030704004000082000c840c0180c8101c0400b030340030306036500d8441c54019214400407200d04110043c00341854a040c00302d4856042904141d00300d50074035420b0280b59180c07060310301c100c140d0741c07000880c3d62811150031407891003010b56403a40e444200b500700040e4203a40e01c044103040816141500340b04541e000b00040c50304110000625824000780990510890b030000901741c424000d10010010084000d0280c040710440e5072606005027041004007a20008039405601c0c1880010720005102d540294084046a14040c00b00d890030900700401500501318404a05074842030300503118510451405104040d42c1d071582d4812841c1d1700d90f4444c81480e000b002c000c07500107484500008840c80c110740500f01802140d8000070f000c1c00e001002400e090500e02680401c00c11034 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 746385521 1250 746384271 746384273
    0xe090406060302010e030703170c0c030a060608010606050901081603020f1b010b0114030103080c190605040c0e07090b03100f03080414090f04060519060b0a08092803050d061d070c 79
    0x10500c81e04016249c1210791180ca07011002c0703091a8640c50120b07010701c66043d50b40148145900204119601c210007042501d480303001c21900c52060740342c030502082001c0b01142e03000203802010b85017000549801800c0004881c00e13042c4550145050a00e02101c201c503000c2400c50030700c1030b111051000d00740a50518540c10b40ba1509020520003c2c00c030810100d01e58a040703a00f03108001401d4002c0710401c42e803000529201e4014078040d281611400414003022480c9030901520034090482520781d526110b1415a0f01d2195030300c001c0946401c5c0401040000d800e004021007840958420401d040e140e42c10241c02c100c03007683d031108203441800700b8014030035164403030b01280750019004000400c4690b12400e403c900180c0440000c0a0140b902d14001551100072001c0c00204400d90354000e078640300c0c007011a03500c64802c2a500c0d00c688501140200c10042c20f070541986c64401e0030500d0510403940c0e050300440d4059441800112101c044040d00b0742818501d60345c0c0704550b0b0900040d44912 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 746386771 1250 746385521 746385533
    0x8030a080a021303021c0602040909030305062220070305030610090e0703180c060908011a150c0a0b0a0911040207030905060f40080a120e090406060302010e030703 72
    0x42c6104c0a4024150500c0c071001c28800005202c62081e0000001d555130356540340e11800404034202d08ae0f00091030100403610070725101e450045219100c080d0340028500141042c801040b1004c0e9644900d4003000312001e2809070f647c0a08100c031701940782c0640300e01c0c2c0702c81408550703600c0507024420010011000d00c031940b507800200390041c44500e0300250130207031580705070145080f07180702402c043c284010000e2465440310081c400c0d1080b4400074880c500c0e000c100310954803280c4100c20750140a002d08010305040c00c2001d08918100c5004583c5116401e850b107923125401a00d00000c641c0d2141002000c2c42080890b4540c05101903404624282c41e0380c4006082c40c0c120f0041c42d103c1c1c07000041c1e0400c01d0190f00300792070440003001001124154200b1400c84a14004040d07246010300e405e8010b003210b0714000d4003804480260001c0c04c81c103070695441400c40c0030841e688605000943c844013207503454040c85248901d00c81e01c0001951415400003600002941032054440e500800043c400100d03 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 746388021 1250 746386771 746386807
    0x6090c0d020a0302040518190e120906301003050d03090501020d0609050402090105040c1d21060f090c0a05040b040615091a270d080408030a080a02 65
    0xa4031000041c0c980ca26041c04501903c01c036403010b544400c641d1203441d070424044881c60300030818404500c042c40c21403811401580c00103441014160031409040c2c00d070201407030082c488000020882c44c07a0040b003801c4d2000c01809041802e1012080c400c2640c0c641c044034000c42e80040741021303045401881c66070743d155184120040b8404040d01ca220803805c00000350180c410310000e0100c103202103611001410010700b01100c081c2c0c4200582e100000395820f0a02c80e44504852940ea0798443c54104007100c2c2ca8803560480068111038290503040b0714202071502904581e004001070007003420400c00081d00d1000240034080240c04ca5512110282c3e9a1307030078242210350603034004c03c20005820004004100a50200c01890440c1a03001d01e0542d2024814094840000c000007038890341c008020100d0241141d1107003918007408a1406404104d0001061408014005c9601c4d500640e10300699800a50241d04507a001041240700e00740c2000300d450340140308803400c604007004000000c140784 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 746389271 1250 746388021 746388037
    0xb180c1c0210020a080c010209040f11030c072a080d18061b0519150e070302060f19031a04090210030c02030d090807030905060703120506010e030609031206090c 71
    0xc0340c4000d0758002c500900100f0407041d00015210788a00500c00114041d501208a980c031592908901114500c1d1510601001d501541d0010b8219942c200311201c45500c4540107860011a0420003080c03820041c1007292007010781030410700587d251070420351411744400e100a09019210340420308854290070a101241d600d40380c01c4604500c0c500c44091125860780c2c000d043e42c0a018251426203040b0540c000005105030f5034036100103a88114074048800584010301c180c0c024150820140c03605001425500301c0b503902c034514060942c5808140da144140903100803035114014550140b030005070700c05290f481074805020070081c81d40040e004401d41034818041c16030310f0500400051080080d110244003040c0204981c0055090103501c50b00001c0307046000a402c1c500104242c1000c0b0141d81c8884c0e41915400c0c4500e014800180103010010000e44c100560305c0090805c0d41d508108040c0100d80c104041c0d0780c0c50301018050841031a00411250013625000103000c804814442251604 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 746390521 1250 746389271 746389279
    0xb090f121507030207050615030706110318040608011b03051b0702150909130203120c031b1011030405060106020724020705090a1a220b0a030b180c1c02 67
    0x50b0780d40e40d0040e0000e0056803400703013161040e0000c01c103452000c0310b02c03500e000000b00c0c103c4680c19a603803001c40f02140e1018002481d500284242d030301c0300309400d03414451840014008a204c0d5243d407141400c40d0030344c40700d40c0c0c02e4400788151150143d40501c10560010448004001d041070109031540707251284c1c24009024603284113180110510b80c00503116283d200070001461401d1400010302c00c0c480343e0106901c2400340000b080c0d00700003001c04503007084601001030f50400c1181d01200d1001404030040321030a0254500c1010040d10500c03c800d0086c010a0000c2d0300c03810182862071070000d050304420159404050244091000702d0003440304115035020999005003e03c00881c1041c14a40c0300c4c54220b180c18081c0708005486401c203008030100800e242d060383c240c070070070051482400c2d001100d040c0030348403200780ca042d206c0d0004100044050510101d80b96a507032151a48101255202c014440000304180d21341414807000c1c40c200c0040711804807501c3c00d048030642c958002d000003841 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 746391771 1250 746390521 746390563
    0xc15051e1602210d020a050f070f0e0402030f0715090504020705070b1c05070e01020c01030902010e010c051c020c030d0212091c0b071115010f060305090f070b090f12 73
    0x100c0d41d1a14046442e0300c03140035913801c0c01c180c0c0006540c50400307807400c8416000c0e80782003a84903074000030b005040351050296642000d184c6980d00d40782132005041642c050080031502c1c1c0601008210950040250b030b58880c0141c80001001801c4a0700d54001510460041041c500400c80c009039001c00d031001e80650740d5541449500c481234000c8290201c3c002a8180010800c01036082444c103040c1c00c0702a02940c81403040300d801182114070744200240481d00c0d1070300d2502c10354130030100d42ca4110300c2101140c044250804c1181104103600754000f00690006d1000c00d4079040c10301a2000403002c41c002042900d806030030100e8036000f00408a0b0180102c880340b00120b28003c42d9081c1d020340c000240030b49509154100502d112030640103000c0307a12900d8422301c0801c01d9002d00754125070005d012140180d080030b204802030000986201d40c00d21482244142a62041c8034200081c100d40d80701d60b07501e9903140c0511110b45003d80b03600e0f20864501810f4805810082210700300030252501d03d90f0 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 746393021 1250 746391771 746391799
    0x1205271b0120010e011e0e100c020a050105040804030606060503015301061d1306140106091a0c100506011803140c030a020105070f0c15051e1602 64
    0x2080c0d20440d0b480352925070030a2210710100c0c90641c410000c2407040e0440103003190b05030404406480001c0403850312503002c075000701e42c03d8086600c005920049481a110035003196200c850039200c054800740ca09400c001010010840c10348660402012036040c030505661420841107000460002c102c0a101c00c2000d280c2c507a0320700001c3e40e64030b8590a0b01c0c1e051580c40d0030444185c0d00f54201c0c031144104d600e0010081851500300324400c60b160840e0640400c01d40c3c81c3c00d8403206180044030b0485410f40c441300e040619240365040140a06020b80e51460300c03500e044858101400d0b0084a1040742c101000520b0f0620030100da41081c1080e0060003040315100d034001241c0708800448203005030110000003108000c5a4400454148015422213041001c0f172420551070b6904400003c0c0400c208002d82000103140f1021240c1c041d0290251515480c3d444030489030f00c401e140c06a0000940000b1808030380c1d0b00c5a440440d10906024285090101031a42807400c0f003040c05020303104041c8642050 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 746394271 1250 746393021 746393057
    0x7020109090203010608041a19022514070e070806010f090e180106150c02090a0603081306110a080a1d03010212070f140d0207031205271b01 62
    0x80010000860704554079a505d040040030810142c40c102c42d00c5c840808078080803103032548080c1c054050340e1601141da400c08040f00c0001d510465a0803000b03c22054112245041c1000203503a840c01085a02d840c1e1800301442400c1c800c540d006082f00d0303017402d018005583e43c81044c055100e00d0a0130300911300400b40030140d031140526885030b19607002250821044580324005454412038980007401002c1c0c854103490400ca00c500d00e0350001038403043c9580d025180000390389030000c0d040c1c1000035806840e0344980c2001e912044803550f12007140c240402c0b54540c0440031a00d010441c10107800107046c15070f01e280e031912600002d038040112001d141483c9840b007100d861070b800d800600841d40e070300380814a04e4604804940c008045602c0704c107c114814000d45002c1a44c0d00d044901030303e05085605840001e421050007981001505500c0ca03540e00064807507940141040d0504611020f115550038600c20104185207102d50010340e001201c4400d0b000d1119002002400e0001d07aa620034400c013 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 746395521 1250 746394271 746394287
    0xc0c030414190311010924050a111005060f0301380d0515061f080c07020409050f06070c0804170c0a06050a030b040c02061f0b120108060f100308070201 67
    0x34552580b400108001c140c10700c02038000401e8a03010003c613682c0584050007581e010505060340b0240101d012607600c034000a0002c918941031040d0443c041c000102d14010000c10104865583c40007403040500d40403080902c115421002030000a41641071411540c4650300f004464000c284c80401703c011140b485c0440660300034202d5000403d507400c00e9039981440706080542c0203a8800424801d0030304024203010070303903036003540307081c541000e00c0c1101c2c0b45100400d00f003450301051050100585c1d0354012200c142d40a0001000d64690000c1d03030a00300383d4060484030901ca42e06c00c802c40060948002d42c0d040382d00c441c2d0702440081c0300d014040d0a1180c030401c0ca07640180f10007004201c894120004d0044003003240da003045840080d4040c00700316880940e0010160340013400003601002da003510846401d1980845d80c07105643d504554074981c00c910102e50350030490310010321140b042000a035a0150410140309045d0604040c0c04415204500001d003c01000050900541e4005e040f0 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 746396771 1250 746395521 746395549
    0x307030305100815191503170f0c1501050105040f0302041e0207151401030c03060e0c1c02150f07080a020f030703030603030f11060705161a0105090c0c030414 70
    0x640e507001c09038200f06213082030308603900000720b1034002c2c0c8407940c0c071100d11440d55000c4000c00740040260550f114880c440303400e1a04985011410003450b0403007030203100500b51180182c801810102000c12a440074820141c10507410014180001c10081850700864401c036034042c3c400003200003410300b0605014010013a050340f110300000e041c0c006c100800082c0c04202c9415841008400300d0321902c807d6010080c88082e255070410325041c000300750942e10000c00088410304880341c8000c0e1102052440d00143c40c10015404041000d5055052404510068020048007241340120010520301c40e0b02030054083c10200c40410201d40362402084421a90301d040000ca944508045c640200901918002200003414012200c0b00c80703801041010704407074080000c0c0c203072a52000000c440c160405074003440c821310003461545c04030f50342e454101446030a407441042d01c0c0d810300042c86074014001e48084c04e8a801042040c0c0c520030080152425101c03103070303038080b5001041e00c005240300c400c902c4 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 746398021 1250 746396771 746396773
    0x2a0503240703020d09170c151e0a14010f0801061406040927150e031602010f020c15030a060501020706090e040606030501050906011401030e070e071709030306011803020303070303051008 82
    0x106c400f0070700b080740a41014540901250051801c403807180c2c03c1010265240031230b9884444020040c140b040f40012341c49000d403140003500204076030b07030401850801c1c0e0100300384215807103080c0f20410081c003c2c0000b0304a00c01c0607a00c8440c07060040b8480d4807644c800d141c00e1a542d03100200c0c03031900502952980080c000d403040c40b07600403820100d60344203881c01616459850103840301e000780c0e008400e0781d05103025948150345c5030304550015107250081e800103000b10301441c168014a550741081c00300c5e912680c85000e039100e01e89030340c0b0b0008988154010505542c0b1902041202c1d9a002c4007640503184d21900c2c040783c940362460608050010303504002d11035402c1404100c1000d00000350323281282d03440c9011030300c403d00c810010b608a52540510b043c580d017003e1814040c04040481c500c0d08110700e0700e0011050910400301001c851410b4980200c02d40000040c05038540e44929511803200032010480100383c42c42d070006e9503a00c00c800000b000d0545460000d441c00701100c03581360051040360 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 746399271 1250 746398021 746398043
    0xc2a03020106050a032f0105090405100911120105091003110d060903020c0307301506060801030b1e06120f0610091406060906072a0503240703020d09 66
    0x1207070203c407281c000c07105400030641900243c901030721506c0c411600c603032068440b2450701c4810400e210151000a210f0350081000c00000103001c80b1a22515204600303000700f880d2200704011165034070100690046210b403440200388418007107004034041c11688e00c80800d0003505000c41c081605010a000040c0100307160810f07440c145900402d640500d0b0100310103550b0805d0301c03003001e08a00e0310b410300b00000300c6d09040c460101e001000510a564103016040c2d000ba06d00f0506100e40c10f540d99a040b4200140d20350b80100104002c0082d0baa40100c0303150040e04100b500450401402c150003003080d41f044084196004c03042d08140040c0d007804d141001543c40c0781c544480a00c03040085445030400351840c003038100300c1440510110500036000102143d107440580802c00040c1d40004c40d080c0c90229040c090503100c8080301c4088012195800e4402c2c10080c0303810b08040c20101e01000214185035001d40c47d4180700e400030701d11907114441d4140161540d101c2002d582c0140301540000b0300f002918 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 746400521 1250 746399271 746399273
    0x30b0d031d04090512070c0b04120c0b030708150f0a150207080102251a0f0609090a0c06080720010b0a1a2505100e010c2a03020106050a03 61
    0x4007140300c0d580c01c00a000500790380500000d100803980e1a04015206400803c0354664101c00799008000da1405142080c040d1500d4901c022400d40c01680215000c450341e9404100304400314480704000e0160b18030050440c5000390000d0245400141000807842d6490402c05150703030f866032800861240546103092482c2c80d00d03070518845e086404c0e4080507102e0000000350701c4005000f1689440701d4107022072440d48a0088110800640c01412a480d814200015031801c45035003180f40308440b03004404500341050400e200280c40b000d8032092007500840e13080404910a81c42c01d40c200d411a01e04981c0c580d4403c0c00c100c40700080d00c9030300d2204046180108002d440c05411640450004840420105690b01d0b580301c1250310510316070300c00c00010f0041400da560301380110a02c20004481a944c1d0709907513a21a4101300e401200350008075a912070000c5054005d10513100e0702c81c000e0401009280725904050390079841c200d440103040041c44090b0007014800c0d000b0704000c10000d003110750f4594076 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 746401771 1250 746400521 746400527
    0xf0f08040206072a26100e0f0a050105060108060f0f01080714040801090c0f060807030908040b03010b0d0609021312060b0d0302150718050d06090813050f0a06080f07030b0d03 77
    0x29403080180c1d400d04064000c0c4204d5843c1c100d1717a011441c2500a02d0021681c428103405000d081c507102c400d40c001c83c03400071610391041c040752030b1841c4107500006183c40c0100015101140281245010310001c8528668a8840240c624034605c000d0030000b06a680c0c104084414040303c0081a81414007c1000110032005400400145100e0142c1c010030342d443c0c008e2170001042a10136500002c20341c9000c100c045009900c4501401c1c014140300740786c035441e0030000302c6903030080c2d010138491240011810f99801807407207001c0103050504019490404203440c02020440503000d04d06046802c1d83c90b0608015a5500c1401303038103406030202c40d94030642d003401b80d119061101c60007100014170000071a00761003810b00c0e00384040c507c0c40b240b4516040800780a800c2c0d00d000030403a0301c5540c400c2d00d94045082032010340151918048041c210b00c3c05c25040c8226104010407a070301503001c4100601400f0b40060b281c5500154507010310501e03030344130b08045019000c040d281c241c01c00c1114a00c034080c158 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 746402877 1106 746401771 746401853
    0x11706010519030b01031101030c0c030e041e1424090f071701080706030e010510030b100b0d0b18040302100e1e0c010f0f0804020607 59
    0x902c0b0341c4d40e40f9008000b80c02c1940c02c5425131000d21402e603854043d4044840551403d0f00c0a154660f4002e0417a0044000b80c40c406e50701c807241b80c504404080410041000c40f25024861003912044035600e08009454243d950402210040c1040e20580c020071140c000107071040310b95a4460140d40140300c00540a4070030094640c01005a202165100c10301902121000c1c000940c90020b000e42101c2c0d8400126044c2d90500d8100550082001041c2089a030040046115a5541412860b03000780039009190781da0380200d02c1030403620031030384410b0b10b040d42a01c81020740280b00c1d10003d07030180210b40c001c0041e4031103440140c00401c030b0703001080c02c25090001c0301e000c6c0c2e50280c0c4a1030458804c0802c0800c0342d1102034082c42540c1e0051001040074011300f007020b240d80f45c1490017072903000c00a101a0003000006049030801c0120681c83c039400c800078902d1003041e017407540340658500d = true := by decide +kernel

theorem cover : BRFrame.Cov 746223021 746402877 := by
  have h0 := BRFrame.cov_init 746223021
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746223021 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746223021 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746223021 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746223021 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746223021 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746223021 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746223021 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746223021 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746223021 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746223021 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746223021 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746223021 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746223021 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746223021 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746223021 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746223021 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746223021 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746223021 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746223021 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746223021 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746223021 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746223021 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746223021 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746223021 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746223021 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746223021 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746223021 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746223021 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746223021 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746223021 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746223021 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746223021 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746223021 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746223021 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746223021 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746223021 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746223021 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746223021 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746223021 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746223021 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746223021 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746223021 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746223021 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746223021 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746223021 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746223021 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746223021 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746223021 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746223021 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746223021 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746223021 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746223021 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746223021 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746223021 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746223021 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746223021 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746223021 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746223021 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746223021 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746223021 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746223021 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746223021 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746223021 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746223021 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746223021 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746223021 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746223021 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746223021 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746223021 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746223021 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746223021 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746223021 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746223021 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746223021 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746223021 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746223021 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746223021 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746223021 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746223021 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746223021 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746223021 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746223021 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746223021 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746223021 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746223021 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746223021 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746223021 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746223021 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746223021 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746223021 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746223021 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746223021 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746223021 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746223021 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746223021 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746223021 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746223021 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746223021 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746223021 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746223021 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746223021 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746223021 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746223021 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746223021 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746223021 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746223021 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746223021 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746223021 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746223021 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746223021 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746223021 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746223021 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746223021 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746223021 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746223021 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746223021 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746223021 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746223021 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746223021 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746223021 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746223021 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746223021 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746223021 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746223021 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746223021 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746223021 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746223021 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746223021 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746223021 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746223021 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746223021 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746223021 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746223021 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746223021 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746223021 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746223021 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746223021 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746223021 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746223021 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746223021 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746223021 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746223021 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746223021 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746223021 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 746223021 ≤ n) (h2 : n < 746402877) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
