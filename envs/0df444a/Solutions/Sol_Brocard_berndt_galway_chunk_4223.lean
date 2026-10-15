-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4223
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:55:15.486753+00:00
-- url     : https://prove2.me/submissions/c1e18100-796b-4274-8f08-4997566e4bc6

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 759352517 ≤ n < 759532374 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 759353767 1250 759352517 759352541
    0xb0609090c040f0608010311010903030e0907140f0c0f0a1707080d020c0102090a05040b220213170f06040b220506130605010f03030824041a0f090907060c0501 70
    0x903ca6a54140c010540202800b050b9403020070707540081710542c080c010010440345d01d6200c690340d84801104102140c8001000c0c001030111712080544010b0190300204120414812500d8848141104691814500740495560341c2d00511140011900b500c1c082c04000c02d03060342c40c41c1d881d403c5160a072850b010f10810503203801d002181101e403c00040d001b92940c0c01007030303549401c00303581d407410802554a04c6010a400540b1085800f1a0047c60700c0d2040050381d054102500d02620440c4402c2c0c14140c40e0f0101650700514400c6500888042c030000c0b0490394800f00074822410f1a486020300680094004170460000c03580c0f4a1301c899520001000d4a42c2000a45944d8035120751044010100f5850846802d441c0800100b404511a80d070a030030741e43c040c2d54450b46035035000354404003140309005d4480382c9510705256584940e00d600400043d00e861000049400107043c052040b20204803841d07a00c43c0700742004011a0080000c2c43c94100c4102d40b80001c241c000358101207005022100c10f81d = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 759355017 1250 759353767 759353789
    0x71110020a051c090227092e0e12130f0612021b0703140706020f1b12030316030e011e0f0b040624110c0405040c1d06130b0609090c04 59
    0x16421a0001d06c1400e050900d0303122105102c1c0c2c1d81c41a078552118000d03480200b20420308260501108415861031189003480340700004d1000441d1001440c00140c0506060005400202c92020000c1c030081800140a641c010b0300303d090410380080c0c1300943c6200c51000080c0d0104081d000c03800411041480024828255080d903512403d04c082805458280312409200304040011124400504100d14244000c050903103804e59007820004010340c1100c00703078030884614601405440a0000314040d002c0c00d4070700c4880302107500026003174410203c00b00c3c2507130b4942060480304040120000c00c0d225103041001528502022000300100080e076403d0b03070081c0c0750080218040303140f604040f1000c68130740402982c0603400c0d14126403842d2280c1440c0051b400c0710510003114149904002e40051180c00c0813035038a42c40780700110300394000d442e01821a01441c4180121418058035940c10741748260028040942542c020900f903224100764603001d40100d03800141c0290484040e607000d403c6408213 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 759356267 1250 759355017 759355039
    0x70303021b07060207150203090909031e090307151b0302100603150506090402060f0c071503090303051b07110a1e080c0f090112030c020405071110020a051c0902 71
    0x140355a202d2842c09288050700c900d50010880c42c14548401a10301005d03030056142c585904184098210050308241c01c0b840184030b50041d4000440d84242408800d03504941c03030f403090300101480c0032000e0b441400590f1014482c140d406034011380105c201611040311070802405807800300d141c450300c55021024070307240882c04010040c0c4001855000520440b081c0000e45a1004000018905030f400a43c40f0604216215011440740098007650000c1401c1e90340b221b50710703840e400040d0b00e04050000000d555a070000304050305485280d811130206404110608100809000c891082800c094450452000030700040e40c0c8102c0b040f8064a08418104c050b0b000f420b90804043c1402c1c06809040d00801c922550a42410580305800060080008003164a001c807110700c854142c0700c00760104250046c05101688950080b00d0081c000f0359555080d8101e101031180c00c10b13200c0b145140000f40100903988450b60b00100360340b41c0c490301000e02c43d4036242840b2000010441c20100035085682601e03 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 759357517 1250 759356267 759356317
    0xe0f0d0b070e180f040213020702130501030b150102030d18121106090d020a08030901090605040c1409040c030210120f050105011101020c071e050d061b0503091207030302 75
    0x540e180b40c0400d03110074001e00d0340110101e100020484000d035400080000003005440c208520b0031940042d844014a0620b2a40109030a1038900ba80b1014568441004000b00f103403000c1440d501407100c2d010b82e1000d06032000001d440c2d228141040b01e4050700da415440c5031803413604801002651016541c0c100c0c035038401c00a0030005a05000d1030981c0941c40c0046c004210104510001200075400382c51000340030340c0c41d41090740005d031483c001c0350368520386540014400c3c0304050096004100f900000343c5041e240e0001d604106004602810780c54084c0310005401042c0c510903258100c42a4240e4031a2a8003120500c0294054408032414140840d1640c061940168180d40007a601c100180808500d0310703090344100e1142c42015030203010100040141d00e2281840c42a5164102e42c810313540c0c00000f418400c420b601640c166941d40800c1c01c4c1f170404041200520802070606505601d080c1e11040d8503903515801c201210000043c070079082600ca5412651502c2120044c50000e2010380 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 759358767 1250 759357517 759357527
    0xf210b041514040b0a060c17040b1602101b025103040218180a050102041412071208090901081e1204170109050322150e0f0d0b07 57
    0x20951038043e51802c07000340e00c00d041c00710700003003544e40d651540709820034580d4800c0260151129021041e030002e020110700c1d074510100030f203020505540c03601486003080c010441040c500b9501c2105201c0c03a5402c00255031034207130724866202d404032411604164503202e606480035081107012040c42401c544d01c3c040b80c455240c0c0114426081c407016103410107400c031980c400e2005590295000a109110922942c0d101743c100758014060f041e03203400013004d840a81d00c0c1400400007100c099401007400d2160400b010f42e1406d0100e01250000c8803101d4102d0f000d41c071000c8900816441c0c400444003002070140360002c40e00031840140c5100155a0740343c602e1929182c01610504402c42031890841006e8800500003400ea8148030f40d072484d151501c070300d1481c5010a4410400a0354861020b0401710f03a00340301901c1246c0301e41289900030035840f0512070f00d21b03200c1d4000f0074103151000944d02007030b41c0c1712580e40b01c5600c05807003103580c045640380020500042900c0080c4400c08402c100104c039a400 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 759360017 1250 759358767 759358799
    0x9061211120109031205060a121101030e03193507091e0503060f0c0d0b0a0b030a0b010801060314060f040b1302041802070b160c050f0d0f210b0415 65
    0x20305c8040085803a0742042024022051080c0d100d813185000d01c02000c43c0c410052202000414100083d0200c90a4031072810340c0c00c40c0342c0401c00c1e10040032859906542000d21035120002541c44051254602c0380e41140f10f102601008c1500410500040ca01038041c1c00e4403405400352022038601d4485861282071460b2160080c0e0380a80203210100e0341c809000441c55004410780106141000d900044800c0106070740d242c40341d807101c400b840000c0e8200034480114055006414003140c00c440f0b850024050b03240681c440d0003054074064803107400c01c01c0c2c80510345e0046000c8035484024054840050007400744503086660000c00709050030a644680c0e4000c0040760080c000200904030006200022406042da0241500503140001900404e0420020410307600700c1c1054121280d440c0c48052400951a5101e881584010b40c040403142e00b0140a9000040038a003d4400000009141100f0342c2c440c01c0011280d40c6907110b90010b50b8550304907605442e290601503c0c0d50b60f484407a16001010 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 759361267 1250 759360017 759360047
    0x9020403021503100b180d14010b0907020a0605060a150305011509120605220309030203101e05041112010f0b040c1b0c03120f090906121112010903 65
    0x1d03440c004910b0b8425034065074030580721040161107040c0f81c81c8050302503902a030f030107580e1000034980d01000e0703603920360b5180e090070f0050f112034015290500c591802c4a1f0132880030703446030011008201000d136000441405040d880680421281c8807078000c00c1202e201c0d0381002203100c00c0c8050110071a545503200c141211a64442d071406040b40400a548582c11801542e08031080086550082080760b0030064000c0c0d40da0080501c084020f001408040100c84000c8000400c2d00d0001c2041d0b1408028002c6400450b4000b0484500da5247c1205004642080c610840d506c3c0c10010b0180028041a410003075805070a450980d032000c850340d0300806440c14203a585902d441038546072070a2a200700ea400c900d403911400d60840080700c14480c84a0807072000c65000400d2040400010407030b40d00d0005182c0280c1304e60000c800040000f0f4a202c22075000082041e1620a0820007a0008100041d070f090700441900f20040c00e150201d1140086103444588644c01c1100e000c0c10540c3c8030304503003c0404 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 759362517 1250 759361267 759361279
    0x18020d0f29040c0b04050303040501030504080f070f17030c04090b0f0a14240406051b120c010b0102010b100f05040812071a0106020604020405061f030c02250b0c070f0902040302 78
    0x40c498500c28130501035802499050352003800140215402130740500d81150040306c841d82081c000746101000c90344079200448400c19844040d108024403003444420f10007941d5203540c110314120700c6101c0c050090b4840c0c41e81140d1150541078494889a110441101025104196541d04c502c00818880341000f442e5000e03c074054541e243c0e144a2200d51801013903040d20f0a454075150110459242c0c101d5051800c00a04001c241084020b08000b90721103034045107071040c1c4940019000302d0840e0740882c600b0703045d641002081001c1d9035902209050304981e80c203002c103848141000031943c1d4007594003c0e82c6144540d10040008000c0354001c1c18a0380e108000040d040340e0030090840d074441007841400050780c803c03c003060052810f41c0240c0d901141c050006050303c1c13500341c00040214004600100800d6552840fa000c03981d041c40041d445000c1c09104d0000295050b44c404103111951007070480014010540b00301c02541440401d000b00128003103101c2003038584d88500002e60141c482244140 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 759363767 1250 759362517 759362519
    0x102070e09030403030e1306090b01030b060c1002180603090c121204090c0309020d0b01050901080c01020a0b04020d02190618080c0f0102030d0c03090618020d0f29040c 74
    0x40c2099842481810030002641c00c02d465139405441c003003561040c1a9000200350044401c208031842a400109000040030616a02460000d0221004400802d000d504104840c50441c60b000030082c0442e84104001a40c504001a0610204010320045a8008000001c0c0180b410001418810015040f90116088040005803179595900840c050329048014082048080d1056109840907105ca04020945406035030000c2d041e048aa4804c0340e240ea4010018000781c03e01c0e26003140580100d20081000b0301c01ca0340041e6680d04010b4005041d03243c120006000c6407035228808141030b80c003601c90340908411450f100c82c120300600500d00000c910a0403174030001410700c25241150b44150107020022114000d10000301c076000c1c2c807603055210030440c801c400c1e8541d215100c0010340076034001480031000d00e055001c1e103490350040a002c90807940710101695038030b401b004a80e43c0c0301c0762484c00710000b031800755070854407240c9001d01080c0f5500c1d07500304100501d110610075845540031800036 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 759365017 1250 759363767 759363779
    0x7120e01050415020310062f060702010b0a061b0804030203010608100e0106060f320403020a0b040305120c120703050c0d090b03010504020705010e030f1201060309110607060e010504030905010207 86
    0xb800300700c80500101502ca0800c00c81a4000d070a0009040c2001c90220300c900d0020782152245a40a4141841327a0f200c0c03010043c0a81d03080c80707040c0909408070741125015140c104002c040b04001400c01460b903002003104801c106035801264015680034000380a01030b0360300c20241c3c640d0f924400c1c0754980c4c3d09103400d1400e1603006208a60503170301aa162000f0183d06d0104c102c920040380079803e41c1143c019060840c00045c80d2250305058110007944640d9642103106100c14030b10715034800d441008042c003052000480116002e00360810b03c1508540301e8010ba80e6140c40d02915903003108104000103400b000b4150b000d001045004c0c140411520f142041001c2200d2480f102d100745518868148010b1005140a070014406a805a0b0020402d60810302c0d0792400e580c0010034010100400080d4040c3c00d00c6103505050040c01c25080400842a5944604000c0701c010409644140300001d800750410010758009102100058020800f070301e0580748c060b02180f16406024050b00c5440c100180c0 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 759366267 1250 759365017 759365021
    0x6030b011d0103030e120a0b060a0911040501030e0304170d0e1215060d140f060106020d020c0103020702150706060314010221100b0a0206100e130b07120e01050415 72
    0xc1e000d0060300040640e103551001c4441401c03112001c1d1307110500e4901ca8400340760030401d120078036001d1000040c05080050400544070055409801340ca4207044404445a0743c410680d0304640c42824081742d0700040c903540c0c0e8154483c82d0800c5d0600c4070142104107180301c00040c008030041054880d2180c50807514108a106505002543c0d11903005900c40c11a9040d40c14070142c02101c003818031850390b000c0d80c0c0c038003660920030350020b00c40c1c1e4050810039072a5102008584d0042c81140050403400400400003034030794005c150218107142d00043c007a401c6445850340c2d03030100420240307810b46421903072520780302030700c540d10084c0e030800040c1582d5282d00f003044c0300300c40740650580c2d0f608800c183c00c0c840c01c15003050002c1c10206000b17111000051064540e500078411400240d010304005e18202d000e400150045400400f0841484002c200910420001d40034041c0c0e0080c400340110743d43c01c03c0444036100c5000b020540d0300d040410a41c160f580c1500018001c80c0b2424807241052508030054003 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 759367517 1250 759366267 759366299
    0x61e0109060e040f0201030204080a050c040f020306031507140d020307030c0e06070213090503030c0d060f060503060405040629092a030a090b0c180d02152b06030b01 73
    0x316501c50380c0c00f08000600e5950b120040c00e1041c1005414195181261f50404020b01002d5a01d0380250480f590245040d100362003298180e90360071421400d05c0400b0955640f8070a000852904010022514090040100c8140d080b1409030190b40d400520460001a40042c1c8034140464100100c2d038038414090b450041039000003900c100d0900c00141c03b0070100e241514401481c290386c55180310082481840111b205501000c00c1e07075641d20380c2c0b040c964103e5086611112664241070400d00c1410391000489070000000c032008074a903181c50803c24014003aa84801411261003465800a0041c0610068500320226000b40e460742e00c0c2081100d0b584141c00f03204011683e142240381580b40c4440240da0420070700f490010f1511110f83e500314020710b054a00768801000800d541069441c1080c03001e00d200d070191080d50341050141e02040c0394000d1000c003012124804140b1040b506003004174081d01c008074a01882460280080700c60050805d0f00040d51030508000002c40d000f00500051a = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 759368767 1250 759367517 759367529
    0xd0903020d0c21030b180106260112110d0c080d05040e06120a17070b070e010c0b131506060e0102071505090604031b0806090a03050d0c02030c061e010906 68
    0x70014043c2c4181d42407034082c0a10454052607a66030704203d05480e005501c42800c40a50322910703540d410040d0280c41a07000280c150071410540060740a55000b1214560440c2e040f4018030062a4061506c0e07040c2d42c0e01e440e0b800c0e80180e088010441481621410381080f03803003803801d0344c40d2540c0842c812140e40c0704500a8805007690307400801d529040c208491350001d8490802d5840e452500c1da14800d01d100c080401003d048808150f000070310140700c4521707030445038074103140c0b250820803400a0191410071401614000c003190002e42c1c0390302c0c2161200e0360544d0003181a0042c5101ca8106001014140500800140e00c0081c691a81d40000360800c2a64100700b100e480030402c144c1c00f115641d0004050b5500884c00b448000001600410044010310354a21440400750030200319030300c4c0190082c000346d02ca50290001c9030110fa04402100e031100744a6070042050a0501ca0603440c501c2000c003503100c1c91140e14100901155441c028400080da000b5544c50280d030b0f6644260107640e01c038020310b = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 759370017 1250 759368767 759368783
    0x140d03090b0a03091506090c090503060a0e211329070809060301080d03050a021608030604020c0f1606140d02030702010b03030d0e0124050d1104020d0903020d0c 71
    0x50200c000080081c0c0000b01d818980461404142e03030300d22143d50b00c01e0350044021625503c080c00842094002d25460a280d4940b4a02d007a180c60b0000380e981602415901c201d070307600c0e0b035000c00515061281060302441e542040d0940e814094150300590f0040c0da852100d4500070502041c040102006100442c1003a031131030701444c0c2898598565544642821159400c1c100b141c1c40007030300e900c40914024440c21020b070207604800c090140640b00c0090515810510421a81103031740313058000401c0d603d4000070029120f86d107500219000b0300c00c6980c050b000b4400e6502c20b8070300020014006200424079400603951310340d61303102035400c410840b4001840241c01c1c00354500328000c070f44c00717164064064030001c82c41d1180100440e00b1603200e81020b10300d01e0f8076005440706044090042980020100c002400c03680c0309542031407200300301c50040380d120b0a036444042c018004412a486003540b4000e0046544202c0003182c10b00404020710f040f400360003000c04806103580241040a01c2e560000f4071 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 759371267 1250 759370017 759370019
    0x903050715090b0411100f02120903151005030d05270103091202160f0b1602010909110301031e0b01440c0d05151b0d06140d0309 57
    0x150240d140452403010310320702e035149005030116110061060007039000e00700c042003401001c41440414a001e40300c0c201403000c41d4400c50780c101d900040c0c034070b5060300c00e09203162202c44010005c1c0c2008038242d0080c0701d205000003400703640158425080d00704c031030841c01c4a1603540301c0b2106403564050000d40c0076441785099400340d801e60090070030802449052400280c0c48905656405404072013800840040e4420460040e04151000b2420050200b4100003042c107407a1404510951085205103000b5a82c094408011039002c1c1158201a2440d4041841401404140442c86400901c030650711051517854038801a40741401c0068100d8004d42e030030381e50f42c4c00c0880041d8882c5807098050b004c00c1d00c1d03161504003480d9400201130f1100b00044e17401319022074a05c020b0710303040b00c500e00c0d14411324084030160001000010401411032158030055041d90321000b030484a01d100e1a005e040200c03001074003104a07039041e88a6400c3e0303114820304800104025040c0070500d004540d00601107400c1e050 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 759372517 1250 759371267 759371273
    0x7032f07062702040b12120705031611010912020d020d02010908010c030e06090f100b0105130603020a02011a0d0308040203250f090c09090b01031d03071509030507 72
    0x14126607010728004600203a18000c1841d42c0d00030040907500000800e0612011072803d03004007240c154048500010903140084900e84601c10020036111500002505d101005800c0c07003501c0d694040840500d10241141c02c0c440040b2203a660f145001a1603240d02181c0190400f10611410382c0181562800d07440a5092015030000c03080c01342d042c00440a000112140240500c8540c0b0f0038554001c07a9454500034858604500602415219008034456503403404000032010509000c07002c0100d0004e02140c0148c0b5544220022501034116814000c03480c00d404d6001011130040903070007004800c01e112002440b0103c12145954002c0e003030440d00002c24820541036402900050540340141d460030b00721401468040903180c2007111012080103c9491400014024100004180420303686000c0080a801c15401004001c07130b66950501e5450b4400e40c803d410001c21b240c0c240200e80c04c9921b40a03030380d03003000c48119404c60041107101003000107401081102541600c4003828400301e66 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 759373767 1250 759372517 759372611
    0xb01060809150c0d151a0d0e07080c0d030c020a060302040608060910120c05040905060f0702011a010f020f0a0303061503020c1b060c030a090e060904050c01081905010e0703 76
    0x10b03c01685071a910000401c0c0e0300c2940c0e5069080c000810601d90b42c40304146503047c1664840c11400115800c90a010002000c005c5020b1190880807aa144210140351509030f078002c0702c808019400c00c0c690040400c0350754043d8000c000f59005501c40c8c1c1e00550b02e80e0100206024220360b0705101c2a0054420018401307004210350510340f042c280710711081e48a0b0003203802c03681051010340b51544180709000080381e80c80e01d0344d034028009200031300040e41d0810881c48001e240d40403039810043c3d410200020766100744030340201c0c01701c584290b80c810046400c009014107040e001c0d03000c0c900c01034101262450b009108071405003081101908402c24040c000390030680d1403114654008000708004100010203000a28240300a81c80f08030076141000240000f821004104601814070b4109003c0803038400105c4042c449824030f040702c0e85030b46a2010f9100c001c0e445d5210843d07503042c03030700105000448001152043c0803541c0c0400090468510b44009601040210013101c0310300440008410005 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 759375017 1250 759373767 759373781
    0x13031b0c03031404080f010902010f020a03091401030b040504060509160f150504080f01020c1014181606030e0f0d0909200a02100b0f0a050d0c030b01060809150c0d 72
    0x80c0d01c240c2c28140c5d10002c903030901003c4000356002c0e03551031491104641c1c00020030b000440c064802010000e405503000b070224002e50040c0711280401d403080140580c0702e6003040030a841e010b40180500c3c10302d45000005441c0a8401c6049400b46607944c0820501c140310315422500c154841d0304c003145c9880019240e580c0351030040300400038108404a1244000c02280c500c102c800c10006030350b41010304110b4240020016401600d50411a00c08105501d08581c1908203025030302e404103910325482010310300b0a1a00c05441d10300e400900004a06800d50b0014181e000320302c0c00d079101440450105502c1c1c40340342105102123030101c3c0f8140f0184034194010b0b0031102075400394004000407402c8001003900048019001a403001d501c03000d43c08180e02860001480545110303040c00600c200040d00b040140c05510701401c510703c101400d00814048000045401901d0081c00e0350b124440109a034500700d400c41180e100b43e520034003884040c0032000e8802c0e4030b0b03030003651300308202c01251001030140 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 759376267 1250 759375017 759375047
    0x203070b1305070b0715050709050f1923060c070e19050f060f030a0206040b07030c02040f09030809030403031d01050d06080708010b040902060403060504021813031b0c0303 76
    0x40c2100c0800082c40030011a40a8081c11a480742c40710164600b009290606411200289050409100f540c64000c0c030a1400d60b48102d42050880002d00302203103210003010030082034400007010000e004144003c00e000603800441081100501000500c046071140042c141140da014141c200a0b004401c6a841d03040782140d02c40078000a030309420071b419140c068591400c8d01c4c191200b03214007440d202c0e0005454241c25009002d020341c8503000102d0f9030085103c0c9002c0c2c0c4c600040c001080520800c0e01800d0300da8020005c0141c9000b21202d070004100c1c1001c01ca002c00c0703001000c40e502e04000416141141e915584008409110030309107250710110144d8035044c0b0030103002d8504c80c0c2c6400c3c051031014001010040c52103502d018055429145020780c514095031800e011070b0056200c0d40100e4090380d400110105058a4605c0400d0030442000513209410104100b481500322000c10f130b8100071350080c1c0d260216080c0100300940c102c186030900400c142c030700f90030800019028920341c10310540c2c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 759377517 1250 759376267 759376291
    0x606180702030f0a080f011212080a0905120d14011a1b01050a05070e040e0c0409021f0201060303090f0509061207080a080702120d050301172a030606060a0203070b 72
    0xb0b40f460304801e254200050300300229000340304101070000c64805060044c01500480c800406440c0c070340300d144113800c80c04d171400c10182070001414401e45030040c54445a100b41240d2401450380c0007441789400045114110702d081400c0c01201880004116041e16440e041c3c0384a094003d14001c0180d51103c81002c241c1d82c04413034046040d107801e00c1480e1184940680c081010b10701040010301c0101c00301030040c8210324140e50703c0300d9101c00107501c0e040d038035098800041c40d01c590700020314008803d09003200d1001841e0701314904290306402400c1203e10a80b00d113072000384c5031503207441544420302489422005113800900310345414501651148100320a4841c00d94440b00c00d1420b1005082044e02c18010004010007103007081140640c4520103030010345060b03c0c2c454000cc250348010310809224400b07446011035801e4090200c10050740340450340b40541b01d45640c0045001440d00d27017185c481d0280b000041c817103080031000c03a40701490a0f80038519240b12a030700c4861380721000d886a80114 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 759378767 1250 759377517 759377527
    0x503060406090501080610081603061d01060b0406020607021c03021303080a0e0315040b0105010c0311012d050601050f0d14072c0f0405071107090608010c02060618070203 75
    0x1900c0d0300c1504d0203032105001408161501d103a601800c40c54980c01000f8a40c410041d180d01e2001d0607070f4002c2901d52107400414284040b0700d0880c03845882001c914165441d2500018200c402c040041044030455000d69a650ba035441d0b050f41c03145100c110507080d0b00203102c21156020b100358024200015202d41e500e02c010303140e4459409940003d0751540219030071904900c001d1030204508001886140014901c500c0c09a8a81007600030610600b810310400c80000d00816010b4511744416100d05c07002000440741d07003156020902800150004074891403220701800581c240100c0d40f1525041e120a49481c0d440903d094a41d40110360055840340e6404c041000c05002030095070068030250b0b00e21070342e032030480051340da01c0200c001200702910040082800c907844030742c5000c4c0c2c1c0c0303e4200c50000703007aa180c000a548000105041014134002c43e08040f4000d11558000d900352646100200540300c101e040681e035900007a1180c61b84050850842d1104141081c0807a41c04807071841928200 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 759380017 1250 759378767 759378779
    0x1051f08151b0c0d0f0909052514070c030b0903280212030a02070b10030f06091406040b01062a0f0201032706050c0a0f031d121c1b0503060406 63
    0x142403600e6400284504011182c200c0c6c0c440c0c0341c0c0024080001041100d0700b85980071090f6400303c1d184441c03041e0404862803203a140280300250310380000e6040b443c0d980c04646410840403084c0e0104a84090004010501040700001540c0c50390f003100800180150507842500305d01002829101c04602c40c0c21003201d5504040406903001d50030002c005600c0720514648080b440f0802040d51100385400081040400c42c50b40b0041c0c00503400010005003a811802e1040c0f40c0c2006651211807446003409000c200076040407001c0c12645555591445d000c940c0d41c003503025003610b1030b40c42d0043c1c1c0d99021910101c1d016440700c1402d544141000503c084011010800455032034103500c841d00030340c4400c8000e00556000c1d440c1d02c18100070000749001102c6c00068008400e45111108240d980c1c14074a000042c0000c10101c208520001c440d05c0324101d50b0110f66a51002d040b1a821859034480b80d50040307141e015516680302e40724114590700c62545e900700e0340b640004190662060300d9041c00514 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 759381267 1250 759380017 759380023
    0x90d03050f0f060d111809011b02030a0f0507020604120b0f06010233010b0d0b1c081e030a0c0e0f01020c0d0c090911100c020f040905010204030501051f08151b0c 71
    0x300c074049406e1100d610f0035174551400c40e03c007402151601c1070041c41103002c60380c1c04800ca4501c00d02c181441ca09040046000312003502071810001c2d088440001c02040400504003e440103074030441200210b691813031240000c907901a5081405a84125200c1c5900001100f04419000d031107480941008006e1802c0f1000c04801c2e40080d401e0100002c440c01c0088a074042d40c1002e00c0c2c15903001c0c20b10482c1c0404501700700e803015805440000081250502e82d11590304500850950705180340e04d07420712940c40700040926481a5021403652040300c0e500341410703010034582d410160041d00043c0105000d1000d143d89421045424000009010580038480d2040c0044580910007503442e1200c10814130802c18144001c060a00c2150305080006a40f9080c3d041c102c0a4145c4000c500c44000f4034115000e4011750b08001d009500700000c020f1110f11149500b0007801210b890720039083c1d40c4202242d160320401020010b041490300008040c03a55450842d0010845218864a824403111085003 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 759382517 1250 759381267 759381289
    0x507093e0724060e090303040b010b0304050a0b0106050a0306120209160512090d1d13020a05070b1905061206060609010e031005091b010c1401090209090d03050f0f060d11 75
    0x2001c60f0340e0304080c0410704902881c55804404640194a54141601c685071309240500c19030a100f9000000542001010b100316414190301c00013403e05540c44410141c50f5400c00310111000900d86803000505013200c05449100c20340281c50002151145142040110342c16126001808002c014120246950003452481006008060409405001c00061000b2801d80b003407290a211003211b05100d940d458076103d08140203020045e43c4030454007007503501d401070303800180c0002040400c0156040304046580142c01400004100e03a948400800140d03038613011562078954000da00041481c2003080c02008008014104104105040ca002901d80403045658601032600d40c0103119038070004000c01151401708401d00301c3c00c0290f41c00000e205120301403005c1d081203004e404052500400798403014000e1b070040c04000c8945007a8441c207540301c0380800c07001c0000307140600141d802c1444e10b540358060b16110609503903644400080000c0c644680000741e510300324803120340700981c0c0c079440c0c850 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 759383767 1250 759382517 759382583
    0x604060504030b0a0c2012041e0e070504090908040b0711040c030c0f0309080d110c1504020112092a0807050a0e1609030507093e07 58
    0x280d41d5821881d01c1849a500900040403ea05044e4182c203469084240800c6850034840c6d041409101c10059134078119100d01c59640800000402003a03410b141381070640540780c07101c041c5c4e500340d5a9140ca00c20110084134103200280c2d05200a00031898140c105045a80c0104c400c1801c16440300c0100b03919900c60402103440d480724040c01005420140074006d03100407241000c2003522902d9202800d40920b402c0b170ba40c1090b40e00c51854080200703103800d032080c41c00003a100300b083c1e1041031103041d6650702c0342204150500c500e08502c4601114a40e80e85d100e1903041c2e484d80c15000d070320040070300900f04100040b00d200001d1300381c04e4101045149a00222544d8a14030700c010343c54030ba40c1504000054000900851488101340400c2042041058000c4c000b580500005501c4c1007044805900c903400081c050f0080c290001030641395500118045081000d2510000311200200000910040c0f210300c0445003007081160785510707200241202030f00400d6120214204d2200141004a018441c4 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 759385017 1250 759383767 759383777
    0x2812081003060c2105060108061306080a03020304030c0e09031605030c0a111011060f060114070507060e040903020703060e01060f080d020105010501050a090509060d1b06030b0a12060506040b060406 87
    0x4100310144008100720b042c40ca1101700f007181070803000207010481c01810f06001c0e403146035001001c1000b640c09480104a81001c2e220904042c0c90700a450f58054402500c025501e41001b00c0e01080d80c41ea400e0081c240c1d24015403030000002d54400b20b19440c1c00d800d950600090206a80c070300d07418008011118428008000c030011440100020207403280d5003201008000c103c400c080b40000a01d02e40c201c4a112007121f21b542e1041c00403103c4441403136030808050004581401080000104402501d040d5140c3c030f000924404180070881381441405030059021102c1000850703050351010b18482400c800120782e841d101d181140c0f80c0701196002d12420360041c1c4400500c1030b820b00c100382c0500001d2804915200110304000c12b140114060184100b5041020030a20b688010b0342000860380105040c84113001e808840035030000780d20446011a0038542841981d20700000e81c0c8041c2e0745010540601518240c60340b90090000924841d041603958880c5032045d5921009040141919513034 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 759386267 1250 759385017 759385037
    0x61e0902030d02010c1b0f020d0605070806120613080f130305060a020906040902090a15021b030607230409090f05210405010e041506022812081003060c 67
    0x185840c02a09488103411645014170402280d035108400042c001c264148200d2995804d08000d51404103440000354810181541102007081d0758001e18400d01440e1250242c580d256000d203d503100c1440035446454001100055400e411042c44030155030140d40300f14248a42c0145052070f907840543c0907000d10755501002c00030030804101c0680d000020140950510785258042a070074041e80c01032020107030b000314200c0c0203902c4040100b00104408401c0603040310130148042e449441259105031208004034000d803007401c0c0010340500800840d86d406039060301080b48864890b01001080744144d904000c0065140c1e00be0085602d0b48d80290102c0100032083c0c03600354903200c0d4003114964000000009041101950302c240c504880080c20b000c003519907a800080d0040000d650380c111002e90844011a200e9070028000c07122101442c806000075880040421815016202c020640d079900350302c400041c1c4c4204100740d08002031801000c007003901c0e80c1e20102914600c0601070002038004072 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 759387517 1250 759386267 759386269
    0x3030f110607020709051503030304170c0d050712020c090c07171201060807020f0a02013209010f0509062b0f0b040b0f01080103062007060c0e06040e13061e0902 71
    0x406c50360000c04500c1443d0700500c034040440c0e26404024000740062805d480c20380c140c17a40c800100c4000040e00010b44e95036916482028086411108040d035a101c0c6444004203407500011711070401d900c00404021099460104007000c90b844048111903017490060344001982920014242a080f070f0740e0079000030342c10f2600040100380020700c94000c560001c50b00d40010700b00400d0144070701c1c1c6c082c641086406400315050720150040003490410041c110481d098405407180131340030b030800036130b03482c032458800420481c0e260055140e21580107030200421080d24604198210305501412609160500d5141c941e00449414280e058400c41e1100d84082d058a040e101d020812030046070301060f0b2040300030009041500c1404014882d940d00d80160340035000000940c800c0507009020503680b04e42c80d18100014014582d0048046082901c0859051030075600380c2c0c081d10401101e210036035071520412580c01100c210700b520f402342d84860105490740313001c1012410ba003d030764010074030b054144 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 759388767 1250 759387517 759387521
    0x1106160204020d2a080105090a060503030307020a12141603171003060b01090305060f071812020316030519080702120c0901080615010302130f0e0f060a0e0103030f110607020709 78
    0x205004404c80d01241c0d0410441e00100d13514152103042e149a2055559052040700500c210f030003881d410311007c420483e043c0e074006002004640b00d0b0704cc90200c202c1c2c0500541d084030f90740e040b41d0300804091004a900c4030820031a0b01c0603c0c021300c1c103e045200b41c126400007440080e100c50700030304190300c014400d112480c0100000c010007072a00b088510701d1078650325101e03240940b4400d4102c04401c0800c54291050125150007000c8240c0c1841b102e079202031000c009500355204900074050154210007804a04414004580e0400c01a0130303046144100c0392410030b51948101c1c0d071a4014002d500268441c600c0c01c20824582c0d6000b00b0301c403044d1900b0890358020591101520740e0080013001200301d030841c100492f45800303003000f580300e10f84524203020b141c40380e4010305684000e00d1000228014443e007168000d950600c0c1c200d00c1e50321228280520744546000c0c0030b0541c0c9030440100700180c402c0c0c84491100d030301c03444c14019602e80350492501745035050702c18400680c04003400f4020386881d8 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 759390017 1250 759388767 759388811
    0x50f12031003140a0b0c041d011a1303120201090605060d050a0b2d0609060f061e0706050c030f0109090809090703020c0a06020c2a0906151314010c1106160204020d 72
    0x1c000071010b5614080f500b80c0b85600c02b10031481004800710b03144124103c4410141d016603880300d48006140d01c100740080c000d00302070809541860804000c10f1541c1003984c030940e10700d40c0080141c9a1860a5291308101001c00b07001c14075822070f042991148203033440004400350051045550350342c1480d104002007108054800c511400040401070500c2e0340b40001c4407501840704406c0b0142035070328250211a0b00a4000107030096007410100048605100e00451007842106252141ea0740c8407214801224091500140008000c2104405c0b91410340d28050740300025140152505810328807503420407000540840e181da401151a011046090207440460201e00707030010038070101c100080234030890703800380603004400c00c4010980f50345034051900c12001c2903903000c1d65103e01c0c1c240086641c101034031462800c41e021051203803d41d840f07a1165101e00c1e0700181d05540b0460001d04110301940b040a90b420494004100400103817103a001400e030340c3d2003484c400a410090b80f040d496041c921 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 759391267 1250 759390017 759390059
    0x1516080603013309051e090f07091109270601030e06130302010905070e090705040c1d060c01090b0f060a05010f030b06090d050f12031003140a0b0c04 66
    0x4100068114442806003040c240180d082c040380c0a004aa1590040d200142c02c44c440789030604080201c2031920300c00090f030414004101d0b0704c02e55150000d40d078450503458101e01e8140c0207c81c08200002c02078208004690003080220b10b0800381a0001c0c1040e04144c400442095800316207a0f002409291810740c44182030074144040d1503da0800b0382c0fa0321000307000030300c42c04201d913039041454802d5104034621a4040104c031a13041c0c48024400170b0f2241100d00560b5440f13400b83c01310f46414280101003095440351584032140700030382e1044c0b0340151940c48144d000b490602c951795025009002d0074085d0f40c040c048240306410101c00c82e03201d03c40d00070704a034040c1c000301c0401c10084c1d90020354101181c0b4545800200520003200003081481aa840558400c91a01100080c0280402e103552900c50303081c22254540c41d107580c031890600007150417202102c550242000820380b00740c0c80c00a014122400c2d42c100304a140d8440300210415640340b1051040882c00f405030a440318107410401c0d03c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 759392517 1250 759391267 759391271
    0x2010f060b090d0204020c070e040503030a0c05070b04020d02191706011508010b030a020c030711030c19051504080102190f080c0a0c02060d093203040b0a02151608060301 75
    0x78240c0c010402e00c01050f04000c0c0030f943d00041d0390601d14001d10058020f0310310062002082d042600b0241e607a07420075105000d2442c94480c1d40c0b40480d008000302e0b94859445140201103580301e408014442c0c56802c02a038026590303244110503a0342204400011700640c1c450a01c1100720340700e0851400d035050b0414001001d80480308061150400c1d407080c11079a191039487d41c4c3c0d079610041000a0300a0040b0785441e84400714104081101000e0b0314007060304107408a803806103100041160300050404048091440440280254140780201413a619002003050346007a554052190072a40075115600c900c1945600e284205030b0f00c80c189903113548441c40c2801d150305101114482611601540b182804015504e180031501c640302502c280306900d00e0108001c10b4103080200700d008010040010f0000001d80840380729000c181c9181d2001c400c42c0003981005c3c1030401001c6681e1144648cc001c0d07108403075089541c070074061201071203030642800140c401100d6110103007820383c01800d028030a034 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 759393767 1250 759392517 759392527
    0x40c090e0a0c03060b1210140f04150b010c0218012405180d02180f0a020c07170c09040c06140c0303060103240b03010f050102072612040602010f060b 66
    0x18162a010b038081c0ca411200000f502032104002a070440404a900710150050340010182c900403580081202d00081c130312403c10740d5034026007122000f0100c60040800041c8112000e80c030419034005e480e0070b001814103450b0003007141c00186401c2d81c225200f1b60f194075284011720420091103201042c6c011094041c002091010201902d103019444a44009102c5246825519075401d00c80d2031040d07402800c0305a502c001c40f0740c861444442141d03007941c507580f18001328603454030074400c590010542801070a04541000b0703040f47d402c40c5c071031010307003540c400d09c441199103075030703080703007680641c1c821145545841c1c0380007400f412480d01044910b8510905015209a590011080701e0780400300b40380014a40004000c03d9a643d218212494034a401d510300104881e4002402181614032100807140765540c0c620049954003124081d00703842c04110b03042440c5440c4003d0302072000401120944c0d1001c1c8040381001e01c6a08541d2001d00183c0d100c440f0141d0310103061007000058111405420b1801d = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 759395017 1250 759393767 759393773
    0x80f030a030b0f060f0307091410030f0f1119051e030a140109060f1a0406050d09080703030c08090625030209030105070903020a08060601092c040c090e0a 68
    0x240a110030440c249a103581d1410a0b030b96480100321500000101400c1c0c8800011204042a0f0000c941c0701c0013203960352401050b1100c0c542e80125040c1c81c002e014005200084008038050305030394024041664036840400b8104140d401001600086049080e46640038061180301340e0220b94412801c0c008204680411340c07940094403042d00e60301e00f49450f40c5c0e8940c0c0d002800100244803655500a15100020400c2c94403900140308442e051002204403e88401e076410114085600c0b404039040104030030041c060040d0064061000c120a000138035440a488009c180d41c420340302180040c1d542d0641c000e00329089170500d9003117580c0000800c40c603d0304940d103d1030f24a403424184a00c828040d903c80095200781c040b26864070b80035009120b40e04150201030080038184c00100d100d54a07244012500000000d072840c85584160340c3c02d009140340c0090900e103d00141030301a00a00c40c040240c0c0550117180b84540100d115034281d1351090300c0d180c40d01d4110b50b0003060360100b60300996010004 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 759396267 1250 759395017 759395023
    0xe010f05070912080f090616200a2409030501020f03010e0114030a0311072102010f05030708160507020603040c050a09090201120e010b0d1a06010e0112110412050313080f 75
    0x2c0c807012002902d1b51003c0c03080000d43c42e802004a03942c02401c5a00e200d00802100d544070070a105500c44040130f445c02c40000b001040006805102c80c00954124604062101010401071007480d80c03d02d05445912a01c941d400c0e61b02401091442ca640040100549100000348030b006017220169030440708400e90000f611241f1005014040041a80340001510310610520000b05041140e8500185040001601c5041110000d9000c281c0c00c01c1000d00c80341c02642128440c045540d28840c0e41e070754613a04070405a03000500c40040141c10300c540001030b12a8070096001d14080c00105080300e152108216441015400c42c13101a0704240156006076000b1201003e000c541043c04908410050010303801000002c0da07280c1c0c002c0e40d005103001441468000b00103250700701c10102d5a659214001900c2e6020300b0b0090f1030000b151300000c6111030340554072160a41c00112800c900d807581e0f4010035502541c0840068842e50800609140200a1030301880700604480c40a04040095200d120707032 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 759397517 1250 759396267 759396277
    0x1306171308070f0206091e1c030c0b19050a0e0c04020f04050f03030c0717010e01091205131e0e09060f13050307020d0807060c140a030f0e010f0507091208 68
    0x160b6072074407103001d08641e103117803e9500e001c00c05024544a1990118540035903070350400074038010442048124a00303c00a03112808581d01520344203100381890b5150f1100b803000918a40100f0450b200d001c40401a034080d8500402229101080d120303510a01c990a0540d0a24060705c164810040d07800f40c3c02d80c04056404413407003114038000d0181105c0210341944140f040d070400ca8002d14801007056a60259103032016881c0b080200030040075855183c0c02c0711a49800a03182c580d10445503c1c3c42031045008104503103000e800e450800c0d58480c10f42441300718519411040c40d900180512460b40c001d20b4140d4041c0a010003080310741056040c650800f0400b0344440408100c980081d801e210080040341e01d6103501400135101c12410341410711040d0089203040710100d052404d4014102c1c07048200000034010421440e19001d5a44401c1d00100344801d00c00c04940c0c2c465014070412039080c0302d81d5150000d00700b400305107460301c040002c02410441d004180104802c2c0364100220720f440c1c084e25 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 759398767 1250 759397517 759397523
    0x2090a1e1e0509030a12090f0816060c020616090b0a0e120303070c02090108010504110f1504030510060509100b030a1e0606031808160305130617130807 67
    0x503292103085814004440458a100001814a4103100c1c44640000017014203403060703556259a003540011000c1903500b0035101615818136000c0c4100400c00c050700402035600000700711101700005680781016a1000c2d000500960000030030410904d80c903021170407001042d0f04c2d04140e00d50904805244900592a44208201c000c3c1126482611a1005a04c203001c0e0036040380e48074030780000c1c0106080500d10f81240680803c00c00080e00b8041402094000c540c040c40503120021804181f10b4155103403030005902c40f440c40148102c01c0703040401040614005c0300a1b041d9241c4c0e40f070990050300c24581c04a8080e80b6410100201150304164040580b240150420f03031300c0c0c940c08000c402900c400c0c17191641303c0b5075010801082480e10307403104007114096201482040c140d01c2c1c14410300c4801c04000b500c83c11041000340b0300000c501c01c1c0018001e01c20305045051044146056102c245c03560829000304849240c44002080d900c42c0c160383c0502610340c605050348083d0340d055440c0c02028001 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 759400017 1250 759398767 759398771
    0x80a052d09100b01022805030408030c070e010501200316061506090b070807050312071125033c050705060901091806030204020f0a090f08120d020904150302090a1e 72
    0x1b0007410340c0000b110410250000103d1341c8458544409941380d6100d0b20b0244014441c036580011189012098141291016102d10581280c0301c0440709407030b000607010005c940400c001100030012031000100b12a03000380700001d07200c1c0d0518039101e0030740d000390803090510000400400c000300d5404200c1b41e9150344800b015407902d4045c80e08600d58002d010b034a0f41620000380400403015070003110074143c11701c030204440169440300079a04038004400411003001d1454034092010400e000c01e810b14410008481103510f04020b801070000304050880390760300d50b41040000050040070030504001d02000c881051504079900006001a2042d1240c0c1c49814542e0500c21001c90740d99110b0b000035500034200395500c2d01d10002e040c142d41c1c030070b0400f280070030711031030002c0754610001d002201a0b9070728100800d01c080001100440c80c0d04426082854140c0800031444962110302501c0715285a06903584070050079407042015100b801854500407910300681182d20600c028820900541ea031000 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 759401267 1250 759400017 759400063
    0xf06231e07030c020a060c1a07091e090c031d0f06040f061506020f07080304030f0204020903071d0103021215040b07202506080a052d09100b0102 64
    0x820b40b120f40d50391401a40c40b026600700014000c5c2c011030008010740c031856440010b40320b207a100650b0028203440d0000000c602480134048582000850150202881000c1d29507030356070045003040ea08107102d0034001986900364980e10003010b43c0c000c107424410b00d01409600e071a000301c981c0c0da1540108041d02c4005603002180500000b43d02180c0751744196603544154135203c200c003030f41e10b803600708882c4030074403603c5c0340056141030201c1902e003a241c6c803694038190602c09408220194201c1c0700070590501038203100090000500380d07600640c0041c41c140c1142d940c510f0040000c01d80301c0100b0040244c0204411919003403000c480340d540942e0003603a084a0380c40304170301120903610a04039120410700d140c400c101107d500217100202c40d495166202064041c6051000170600700b807042d074000ca44a94085030801146422095100e0710075804940d44c0c04d81d643d120819003407450205a0003c20304400c0c400089401d10009107010b1103640140100001200001d6844202141803091080b050603 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 759402517 1250 759401267 759401273
    0x3021203131e0203210919240801061b0206030c0f0c0106050a060c0b0406200c070e010f121e02060703030203060109091a0f0402130815280203060a0f06231e07 70
    0x11f402070701c0c19080140034500c4000c0516a0207850802c201d000c11f100000003d41180b00309440084a100045070703c00d080c10325401c2c021b0980014011070f811031003c0c40701198030f1000c6c0d006484070301c6070740d400070404130b14020520100318802c1d00181d04005102c29444041482e4041554001e54014400140c10120b041524124182d00b05c140d1107240c4001141000400001440300a64420381121116039a90391404202900644682c3e01c65100401099020919407004440d10b6500c1440c440a0042c45a0010350240d100d050214003203540031090181075603014100704042c03c6e482d0410440a500d0040a20f1f511a0b0320300040e10810750b40081c1100f54696070140c50508801c1420307601c0c407603100da00c55500e4a04050b1300600c0030100c80d0002c0c60b0301c0c003881d03480c00340045010820320849060603004c10195000410164000d180031b480011519031082d6140e0090003079a54683d8800b08200300102c890000c0c4e082448203040070711080940700d056803200e0044449411800c0ea88486034a = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 759403767 1250 759402517 759402559
    0x70f0c020f040c030b0a050d032f0703061d060910020c01020904050103060e1213090507050c0a030203030105040e281a0405010906110703021203131e02032109 70
    0x1542c2c0007414651105141078154002c203205400c1107030540e28041d16102407080601c2008000303000101c14400340040c111001d080c0802c0d012500b01c42e4408445000c10440c0b4048417079000f156459a2210000b492840c200c1480f0801d181c000080c03c0a03041100c4c0c800d0b510181981d12145d042c3c0e0028409680d00c009604840c5403440160040c403c5680d40e007081001000d03c0c003011005401803050950301420203c00310750850702c11900c0754a0326410041d00e039000f003e0060041e002d0110800000010030010001d01500c3391180c3d008584d40d45c1003030244810b0303503886100c0705107540c4221542d2890320481c03105600e04120f4003004400c2c003107260800180800d807401001040111507400d010501030190008108a4060107003030104400591031040f0900c14104051300507001019030f000c0c500e12080c019508501740c002007900c00c0e219500d8401c400507008004d07120202e0000d1380002141001c2c050212134031501c030b20181c3d10701d191407030340765140c4142c203e100d100c0d04e194004104401400 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 759405017 1250 759403767 759403789
    0xa05030f0d080c090a15030506180f040609020d060e16050d1b0b040f0603140f042003100e071d0a090302010f020a05180406060507020d2a0e0c03070f0c02 68
    0x285605c90003070362480e0410010300a4800d080002c0c1c20040021094145600501c1010500110742981540c0e9522a030076039041c040c1084130416154644c071005a03503801003800d5100c1c0525000200085030103d03103860614010ba10b9a60649110301c10805556140d44d5007559030740110414410803d0303141d01400410140e00859259080480c002c140d00c0f0102501105444064404001c01a508030b0b60b044003e804580303413100c1185650002d000200d10241c907141c02c4852340c04010a002c0c0701c100081c00c1103449105801c0351031307548120190481003080701c04001d0070162030350960001c20b01c103105592400181000d000e50788030b00d810740c2014030075400500f1118494a08545540602800400075170000d4040b840c5007400148040c400e1800380709202c120b60060301d87d145030407655800d120528880c070f030080d40d840c103c00d690301d40308041401824400c21403054840c6120f038202000501c9030364000d05038941c00b100500811201c2504007654540c10130b118200b0800120603440015041100 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 759406267 1250 759405017 759405019
    0xb0622030f0503042306161104020c0a06270b101e170f0601060e150a0f0f020c1014070614090d03150b091906020c0a05030f0d080c09 59
    0x5888a107005000d80840584166541c003000c01003000700b601490740318100305e030f83c6180d81700404200190341c00f1502050490000c0c401c41003608186101b400050481c0c05c88540c3c2d1035160041d6401000700141407080c000d140300742c41050000d4021540300d0919448810380018045c0701403402042000340340120340001440070921000703003000c110008080e60701d140d02ca144144007000012010241d4080740c000c1289070304c0d000405050b032a025040350454a00980c075038000e000c1c0000c80301d03419039050003420905c24030745810003c0d040640004243c0c0300346042e503004541004008089550741d140100031460080d1801c4035104c104030b540c0006a1181c110010035052030038400780c4000042e40012480340d40088180c0c0c4d151800900d085d000e440c505840c40c82011500c520601a1139038a002078096100007a18121400150164841c4c0761101c54000d42c1c05640301d4124407003140b9010401d480030b41010382c0601610454494503030382d00c04003107220341c0622000000140040003440151041020 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 759407517 1250 759406267 759406283
    0x1501030b0c0d090c0e0c03040336080c03071208040b1c020a0c051c17090106050303120402090c04031e080d060b092704110409022107050102010b062203 67
    0x43c0c924221002e8009413045100c0e9400c90000207401280c02015603108a07015101ca4040b5942040c0f00c0d141c401070f004240d948050348421b0000b00c036880510100c00f802c0000000c0c0074841d0500300b011319101043d4404a0304c0c04003000316500240c10a000d880c1241c0e21b60100b0740e01c550001c0a80e04036007502203042d80c4440c1c80403503401b001a0b4408200d880c6140100d05a519401003a00340180c117080079818440440c0006c8141c142405055864607441001207000203007071516400064103660180c1c00480008060605100551400e00012030304040d50b526520b1415103140d40c2d41048081c0710819000c111080d08641052156450483e02140d101c0b0108102103600c42d002c448954000700c00c0c1a000344c0020707441603d4441c50045040c000c5407248140d0440b9a00d581e2980341a40000c150305822507120482040182c403160200c00c01d00219070100d08151083c2c03250746250032070380d5004074116810040904540e440c3c540850303005035159102e07028039400140440c0c00e880c060b030341700908003a = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 759408767 1250 759407517 759407531
    0xc0409091208010b0906070b091509060a0f0c080f060111010213030b060f010e2211030403020f0705010e0f030109020303120f01091505011d0d1110021501030b0c0d 72
    0x40034482004020607516181c49065980302c0c14260494041c091426030080810031030640443c0040f080c0c6d80c3c0c01500b02c0c0842c0e54915021030b6113440302000752000303082688103805001262125020b01d900962000070b0401c003511414800401c005c4018001200c00e0020901041440c4d00c218a0400a207501d08000d6594007010210000a14500c1c48240c0710800c003440441e015141c01c001c104500c0d04160744441342071890030100803100100d502107061407801c0210400e2440c41d603010360364810070706000c41500c92600b03050290821400301003541c600d401003982401181e0f00170340380ba4415502660401c400f04050004a80103000d040c0000e0342c54480840c00c1e0300b030684900e8180c1d00c16072001850251a9a90752106406c0e5890546110001a07000c9018415548510b0380415a244994001e1500080402c08614400f800360410b41e80b4020a40c0200440c0c20401d82140403c3c650784001c2c21a01c4a01050080400043c00018101c4141c01c000c80d60441092059034030780a50500200240 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 759410017 1250 759408767 759408773
    0x60e18090f010c050a170903090603180706020c12210c03070203070807060e10050a0507020402091207090c0f020309060903010902060406080406050604020702060d0c030e0f0601170703020a0e0c040909 88
    0x15009030f80d05400098020349010f00d80518000c505e400341b0701f05e0307009608000401c0200500d941008100601d526810510784d000903400b041540000c0820b90003610700c00a64005000c107504001259400c60b174044c05681a10010220107400040124900b030782e102d2652400c1d03541184a0710704060f50502c54141e0120740356801040d050210fa0403030b100d5070b88805814042c4403030001c04512400108078140240201640600020b085484c4000d100629103c2184000356182e4120014446990b00101081c424000710340308030890342d9210b00340010714807208000255a441080318440c0a5031000c0340101c0c03a0780302504040c4071203074010541a101c90b150304005200d220121815201107040c14045221070900d4400c81c0c03416070300900010301d0610058941c1c00034141c14513100e001c042c0e8030002c1c51240700f024882e40c0003e807441d001400865141c101045c0503102410204a01d07a0407699042005a41c0c1b40d060000329000700d103a4500e0340e6129034220ba0640107680c07003e501207042c03a84010130 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 759411267 1250 759410017 759410027
    0x304150201050f06040e07030b0709051c140c28090501230612070e0a0806131b0b0423031204031b06050405190305011505010207060e18090f010c 64
    0x3c60441e2641450380c6941c0d24007000f0503190098501c0140d50002d440c00d102140d43e10f4941c0358070200034104004660758510104d0a0025621102941c19082c4d450f01810041131100141e41d6140000090031410b5519000821090a11003071024900340c3c4140c40208a0403801050010255401c00301300542e512005030b00310414507150000800c504c1095242285041d40503250b0854034080d103450a541c6203130060b10129991040540d125180d003d001510840400c18035104c0c446d07035081c280d00d4804520300401c901c8200e040048103100654018000b0a0040f23090300c2c22541c3d80d100f0381c020400c54440010383e15040012054050242ca04404001b001c03042c020807c40e4410640e40c002106402e061101074620344c050240000e100700b1040040d85400085000740307807006038a8000e443c1c1c1c1ea41d038031421110700b4801c0c0f0b00304a00103001040b4075a01400100001c1c000c900f071003420003966200180c0280205a81d131a04e40d01c203180480d40c3c3e640200f0940c403000b85442c0007040503490110001d40 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 759412517 1250 759411267 759411271
    0x31c09030203070905090304050f180c1305040203010806070c1b08061905090601170f03070c050316080a0308180a0f05010b0604030c0306110909040609020307090b060a11030415020105 81
    0x4001c1c440d03e02e001a10000900c1360174841c5040c0800b07182402d00304800c1042d4120585406c0341d200c10b0300c40c10440d5000c28001014041c000000c000b541d110104d8000580341d81c2c2c0f991122344900e01c140010001e03804082138441d4000030601d045214030035503240c40d0020680d200407158021404200208414a0020b00d29000d004031581c0400842041040507007030780c0c011a0405400d0b08400d004000030901018803210b41d100c068252070200300082c00c4103166822507801502c222101003410001030400344070012401c82d2008450f00054106034000b07507605010640101017110f90400154003210900d8042e0f011020b10054842c00c4070a401d1034000003541d1801541e06529003000042d0700c2c03410004481c2169405401c02d44480d02d540c6441d401480701c1d10100000b0341d0b0070001c5000641c4c62140182c8141d22810000074001480c0c0145890034070242c1040c02818906030b085150b40e642c110a8403550183ca02d80040c0030b05958241c43d0071405030303034400300c1842007003000d404016030103410081c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 759413767 1250 759412517 759412519
    0xb0f070b01090b01080a0203061c05100c03020306130b24160f05010b010206070e1e0a030305041e18020a0201060338010e070f180b03070305151e031c090302 69
    0x1148549486d00341904a1006a842c69802003050540c0b1002c4014040c0c4c42c0305180c040d4066a484202c20b500b094241c8459205180000390300108100b41c5e4070308000415120307000c0707400400c29a460540031a104403107185c01c01c941040f41f00a00850f07801c03a0421201d038041c90340d020907215603240c40c02440880400400300c0300d035401c20303214095552001a0451152401d41d442200840000c2c09002c51001e071481400a1a10700401c8981c8580301c0c2a0620002c611030f9a8080e60f4a2801108440030151411004c1c1c100258020410514011444012990001d924010390740c0f64480c9042e40104403650004000e9041e9112070030405036403016800f00da4007082c0c40c0c400103c540131401020300c0c41c04d018070380d0311041030f42c045000d80f84a0301190b007544000f41881140030040d080d03680f842042580c0040a140e50010810101c2d582c54015143c2081d130400c400504003041c44006075410342d14000e54160780c0042c03034200f45542c2c0c082042840007200d42c00d00d103055403800180184054030341d000c10b03 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 759415017 1250 759413767 759413777
    0x70c17070f0b1e060103020d0e120a020d030608030901051602150d181502090324150f030c0127091b020d0215070c05240a0b09010b0f070b01090b01 65
    0x50386070390446000c0e50340c483e00d01c00300c0c1e09560744450043d07000750028030443d61044d41d100902c1c41841020061411001203004005441d010341c400024078240070014040304060400004110146000082d00c0d01c1400c01d00b86a80c8801c869030310f0305580180078801130b610a04040d009599010f02c0f60041003a25134956003440702003200b500901400d495100d00800a0b00006140051a8800c0d07004c0d0046850090039124510f09510038505950495071230142ca240d090000d200003400840c3c0a902c00c41c2c826211400d8a2000b9000a601d40c040d1054003070500c060507810380140c81c041c100c880700c035501c0550680c1801c1d80358400c2d107004040c03510000b04006c1c400008071145c0c0740002440903031401303280e00030210341c61045a10050044050300c40b03000d000b1580602000214103200b400c459094902c944220710000720300c508111913020780511001464040b0b681000c0d20703894505819284510001507403039a0210320001948114600501200d005034004980306115030840c9c0e600d00c0090740c803 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 759416267 1250 759415017 759415021
    0x50708190c021b06043204050c27030313080c0a2409150c02091b0703050c0f010207080406030f0501150f021002041517040506070c17070f0b 62
    0x201100721150301d80c01201691004a890000f000d022440f240400d0019181904080d520484028244409441ea510000311074260051001c2c1c09918044000000c4800344483d003031400d9a803005100d12000c00c0303c4842ca000c1e00c8100c8e0407107181c0300000d070712010342100e030348046d9034082d50010303686405554524003a14155a096107461081d04c0f0655840c00740098205920b01c0c0c0000000c800000c1c4101402a02440020f251082008c500751840d0a900d8881259803107104025030486c1c01802c2d80e81c2240045242e5a049481100369112aa41410241e55964003d43c803140f0300700c0e041c0300c0a45158000580d010400c02544081e00031206207880c08e002c0004070903041000d03200c0074029100141e105590303030060603104c0c00b88220316003001d0068589080040e00040207a0744541c00094169981c030301c85d0740d107107070348280d8500c048140f034003c0c09140e00b855500d01da21210b02410410402907030740d81420a2200d04042420780c1032004c4243d55440e41b1520300340082c59803000e815210740c404080 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 759417517 1250 759416267 759416311
    0x2011409150f061f030f0f05090f060c03070f0201060f0321020d140a0c0609240902031518070602072103020d030c2604060b010f08041e06050708 64
    0x20690003140c005026071071440c00d60907aa040c84c0c003c5503181d0101034030303060103404100301c61007031082d801000a00400c062903c2d8200c1d80c40d02d82442180c42031a0b0050040150b5040b54006803a0002030619050040c0929150120301500d11a01710b203250f4242ca400000402400d000c00c03104081c001c0d500d0101200181c102640c5a488040040c404604007031580c00052221030010181d100141c103280120030020f80b03c0c2411280500800c40e5202c509041101214405284500100480500c01d2007100c3e625404a0346402050034002d804c02c1034080070a004a0361906101d1a9913101012030340040c1d901c140003550390b1380900c21031521602145941c5010050410103140981d0103400400c40d101082508400410b5000b030480100814050301142640c4841e07540c41c4809031103808070745281402d0030b000f0202c4441c5d8005a040c00b030b003000f0009841e600000307010760098009003485440032224480ca00c40e000b0440f03000304528500810000700d55044900180980d459117120703400c03128048 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 759418767 1250 759417517 759417541
    0x3150f05011d090a0b0601030914060a0e0609031c0903030605030f071a03070522090e071406040e04110f13050f18150c070503030c040311090c0304020103020702010201140915 77
    0x804085c10a500e0540003884070b50082c0c00072400e403440380329030000103032844000a0605c98259044851241c903550480c5450400308000f913000541c00c005545000f03442885090304100f800f900204c81d9450b88200010306009078014401040c2c06401c0d142d180111082190311030785180600da003100f04000d02500d51368810030940740b1602240e281c0d1807504504100409000c00c9036140d00704c50307038849200480c100d98180a0305189240500c010b10425082894211340311380c480d90f034640101000d1000b00000000940e04d140c000303030080701611143d504140480c60314160581001d410200912605004d4803140d480f1b40d00c24a07803007000b0400c54031102c4140440c903030981001e12065100082006101c4903441089402403010000030349441e00c540c1d1035a066410448940900890124042080c4942d401d280c18070740608480405107850403120303500081c04041d201034100f6a0200e00d5008590007503004417281c07110151040e24900c0d2182c05265252694982c505008158102080c405420300d = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 759420017 1250 759418767 759418783
    0x180a0e0f18210c011e060f0e060f15040e250230070606090b0a0b0c03180103180506011403150106140d06090204170f0703150f05011d09 60
    0x402c051000b9000d2101c00306081e0300244440c1c501950ba440200ca443d60308943e041d41034440710800401c5061500100328544003c0c0c1c3d01051103496080100b12540e5107544400b249084115141c031076480e0084004110f9000380d80088903004810018403051030704810200940000d14a40c100c110241d60740e08a845006110041703c40202140004402d0000582842c0001c011001e81a0400000b5100d12003038071030551124903150341d1451f0004590502200c410003a240580000780f0303003a00302d03031041d50f05e22032a411122400501000c03141d80ba882500000031170200008a40a90ba0711400e0071600c0d1030003840f4403400d0100000c0c81c00b4260502260401c849003201c900c0307003200d81c0f03413020555251507200d0200c0000c90003007100401415507403240201500041c50010f80320fa040012078a401e15046680a01952140310404040d250001e10f4409503580648041911503100354000003819041c2d031a50078580c00d12001090315942c00704040700c0e03514490007001c2a6160403041c1a00c035511 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 759421267 1250 759420017 759420043
    0x40501090b01092901050706050f0f0105010c0302070b0a03020c1501180603080304080901020a05100e0607082a090a0603050615030c031807030609030e010206010f0b180a0e0f18 78
    0x90f080154181c21360121110541d290606205160007201d54031002110011600f5841102403c420301510342c81d0b2110481c0980020b003400380342d003405510069540c0e507540c810110b00290004038a52458802d030190303941d00c0c0f1210101d038006101c084a0200c0840240030b0107180d09007146103110100d495004100c2100d400c117819031b00d5174450fa220101c4541c0454906030640c8902d100c00c0340002c0c0304114110505854060009080c440d000c3d100d800c1120103010642007016400600148980000710303000b1800c5950320300f07440748800f09041901e9005800c00ca6a100313144800001c0d000340c241d080a1710074103046900701042000508900700900054401e1208a0400d00008000c044080c1c1c2c1001001ca00c0c0e1f04880c5125500e80c1c1d540b094030514034081740010303421280780c0800d580403c4201d0140034810504403a250400040706070714064041c00540c2411106640407940d200c881d4000e003e480e0040c1009041d1601c1900541090400d5035800316080c14403041c541142c0c00480d1450344002 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 759422517 1250 759421267 759421301
    0x303060d0f06021326060f0112140708010b042703080703020708270301060e130807170304021e0d020621090d09060905100f0512040501090b0109 64
    0x295944407140d641c0407415040b100d180d0308020030b501c40203030150980014500900724402c0c0d0010a885100700c1c000d2891011150340c810000d000b650840340905c281919019501d090180f05542004520308510004041c40344c0603188010840c1641034200300980a001c2e5024400780d100c0718045204d00ca41094400810b00d102002c400000c2d02c1180040c7d000040c514000d424044d99464018030f507840b40200600100e520200f540004c40340c50049000440100d000304000c40c85e00c2120b8200000042c020364083d07110003003000401040301d042e9020540c20108100481006890182d103507841520168400c401d100718992544085010b071410040c8084c0c6401c4e14407110b0ba0900c40c0715008040d12680645071034047d1070001582c4c40341d07a0300c2441070000410701018410800741010196400040800403c20418815500d800c000d50b4020840c61038144129942da06e0304941034000c07107030b104910744000c0081c00b09009054000714255802901e803500c003a6600c00449040b2498030340b17001030090b = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 759423767 1250 759422517 759422539
    0x5090603120a0c051501030c060c020d08090d0602040e07080928110402030702010603020a140a050907030902101205071b030f090b07060501081b090c032206020a03050702030306 78
    0x96a018042d01440999041c45400603609a0755981001c40d01c0031751900f0788600c1e000401c2400074003402c1c500100442d0924140b03000d0175402080c0d0781d400000c2c019003100c3c0d001950864545610151548030394205c001151680d445014503480c1d0034095079003900140881022401d0100040740a540513008c61010410420302a000305200038500386040d00e0700d00c2521448000307501d440c001144118455030001403a80d042d8410080c40b40310a0b0032440706615030f420503403503640352548c0710001d40e5811101c02c0425581d09804a024040214009400001580340c81e0215a007000701504c0c3d60418800501080d5207240e400c803146500c030a0b40c0701c3c11600200700d140101c1d01074a101591000e092500700c00c0c0c1c94560f01c0d45107030340d8450081103d12176a2000108030442003400062036042c0340c2c00740c80c404843c0000005804d100d0140c9034011480c80000440c407401010070510301c0480316140d52038440d01860030004029009141910046030170880003441062010007100c2c46004001e0440d9851 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 759425017 1250 759423767 759423793
    0x7050d0b1005120d0e011202030702060708071b0b1f0b071713050d050a0b01080c04060b09060702060d0902040f0c030b09100b0a0917031e0a050d0c020102070f03020607030605090603 80
    0x9000e05d500d1050500c001035042c0640e2240c1030008603c90300f656001091182050701d001010000d00812120801400d031a074803002c5424020788006040d04090b0707045082d180c0d258071304448142d18810310801460000c00140781e4203842c019190b5540600034500b1140011010f1140510805c59410840000f280003441546001043d03804441c0c000c5040311003001320356449240c0c002e003c4c1c01c4246968859a50030b1100d01d0503024400c050502496010f04111401c030108049008160b40240300300e8002c5031211202c106644031083c035980003041445200ca135210b01c0c0d801010940b40000000c0d080880e20043c5051856109004585001c06800020b2405400402d03541140b0124020890110f07000204984403120b210f01414040019551f00d452456211000e50910b140c2c000b04103c0901540c500f030f5420405803008920700c0eaa01160303d0410b400c04900a02c5001c1006255034030256408007032640c0001d00c20300c04d041549003041040d07283c104200303645000f142c4182e4140d011708100300107 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 759426267 1250 759425017 759425027
    0x182419080a02011214071115180d180e0606120a0510140d0611120f0601080f0c07080a050405060a0804050c1206040602070507260606010c03020307020d0507050d0b1005120d 76
    0x1503e040000d40d581a00001440603080704140d627240080c0000b200810440300c5e090020044d0f007030303050404903807140d048100040c246d106441688118000c0c4c10004880741ca9030f44c200c0c1c4080b11402c0d00c04071607260105c00304c0c00030700c410f8402502104a90f200480e402c14112a8925954001020040a02c40f0307551101c01070542c10846140700c4c4401d101c0280065851001140111200e1111a0040c509080010003640008055099a81c10501405113019020003240c283e280c000c02201e90b2400c000c04191040e204a40c00280c000c01d001071201116580020501e01882c402e5080d41c00040d9140c0811100500e68080b07900e8641107030b0b0201d400100d20303500601138580300d24180e03102244d032080c610042c40b04988a46038100c46010000001040500180340d200c5c0382403c00703500003030700c5071002035480c0600310700203000b440f4401144082c408204100801040002d000300a103070802d2500780d02c3c0380f2041d110244071a002301004655860010b01c03003900d801c465401810002c503c1042111 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 759427517 1250 759426267 759426287
    0xe01060f0318210e0312030109230c0c12030a0507030605010e01092d0608073e0705040203190609091a0c0c060c09182419080a0201121407 61
    0xc244002640c01d098242c17014420307003d401d00d103810742c80d890750714010b0800c042d60b05c80c844a8540800c4103407220150f0032102c58a90b04181007000c0309445a035110b5006251802d0485c00b01c0c0ca060012041041c0c903115900325a109000a0340c007484610788c7d81005403424251841ca00d0702140710340d8000d1180c050f80c0250401040304e224003000e04610314440c19911410300e504240002008081004182600100c04000b90540007200d044420300d1045041c000140580c1100354000c118030310289800c804102d0a400751030000d10440d27807810015080041c0076154401c1d107107da0309003c0c0010713406010707106280d60141c00c402505031000c0d111042a441e90401070180380350364004e0186040c02042007042d240b041c01000c09907541c0e40c00c403104002442d00000f0f2440c13402d40c0c1d000c0401200120802c81c0301c540040c0c44c1080c08030340d954540000d2012841d82050311000c81901000998140002040c2c0b10f114000e894001c02c4030301d03400d03605d07083e50700208040414040b04000301c0c958034441e050b041 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 759428767 1250 759427517 759427583
    0x1050f060910170c0405010804080f0d050c190e0a05010f09031b0905060409031707091205030a0306080703110603041707120f0201090507120206040e01060f0318 71
    0x5032038403401c500007965100558020500140e4000061900c02c90f10092444c0c010f0f0480d20228205840d220001f010041c0050004081140c0424805015040792058543c206902c2c0da05128618200d2202c104540050002c031561a10841c0c0e08550382c1e0142054066800c03029100102440c1804010365034079607080c025034100304907854008082444a203202000c17445141d50071185526054240050300c1d800350101d1b01c5540307420300c0800000e0700552003440441e44000600c8247c0d49450041e1500a4140d0140c140c241050392100b00301b040100c01002c07100c107a134404200c1192140605c65555409000040a848030002c08004501d4050061544a48180900741c2e540010035540e80d9140c00c0b01600b22a8600003000204415400c481c2022646034544000c10031000315848495403800148110400d000c17a0380381d40e03003d548490381114058416041011815603680b40004e280c40000310f004000a07107010b001480303101b001e03003c0114181d0031903001c502c1c40601d0b0345104281d601c40348440d = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 759430017 1250 759428767 759428779
    0xb190c09083307081605090306070305040501020f0d091209320a06180e0615160f12170408040b0309010f0c2a0807080c1005040609151401050f 63
    0x112200d4403801c2d403d03c42c2480d40d980882904140c0700802d405500440c5c0c84050060500a803480b0741c4000840c0c1d5070049403441e010a0b5501c03603081c200c0c028410910320944070302000070304100149890b08440c6000784170f40f0101c0c801d0080000211045011030040e9190114054129a4040100003101c100000902a581c00040d258000201d24240d40d0b80010007041c03c10f80400b03801034158281200404040c1d2510440b031501c000000c40c64604c80c550f544021a0100341c10700603051001018031584c0c2d100011601d003209908080310107010403465440010031600c1000b80d0400c0c802d003100e005030383c0420001c0c00d203800c210101c00c2a40000b080b540c2d15668a0602c000d00303002034021080043c40a886a07010501e502808810f91803580d050340e6889000b4000d810001394015086851081d04140419111265455400d00b4026000395084d0400c0c10038040c801031080d40e138411300c592031142c03440719968a000304401c0140c2d0f016a41206842c03201c0070040080e410180407403807c604004240c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 759431267 1250 759430017 759430093
    0x305031c02160309090c0f020712061b09051f17060d0c2312030906090a030b010b1233120a1a060330070b190c0908 51
    0x8400c942c4046005900140d400340341008001da56100f02c01c0d0001e49450f084000c90300c1008007030740d220507500ca0841014408120b8200b4491240c2c855034600c07400e40058044512402c1d0010000c01d458000c0501c111420a6a1344022400181d80c13603240300581c6611341032010160b580914110000c02c115007040c51a480c000c0000d03410900e000160003a14044e4002c403210200014101c0e08034000340e4054880703c1c1d01d0075007100c0e002040e508090001c07102c80b5520411100455200c4134158802405407102900128106034144094043c17001c501e2914141680d4640c41030b87d001c061400000459182802c041d16401885100b00e60741c184050a010020794801c6400c500e0305858903c1901c00030162018641c58011001c0c0d11500306a0440040030302c0719810000408002440c2ca07001010103005610071800c00410f8180c9541326009580c505e52443c0c20340391240480041d040c81c262042c40c1905c2060303000d004230f0303680d4103554084c0010440c4131700744a011410807141941441c59581344100e = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 759432517 1250 759431267 759431287
    0x90e0703050a0b040212190312180f050c090a020711010306180b0325052112090a05040218150301080d03020306120a12080703091e0212030a0509011103040305031c02 73
    0x201f00115401c610300c0e01d000030030260400400000c00e050039102d50314101034051506001c011a020b610a0700300a40020b401c02c6803401c01e01d0074845407005900300860808011000c100e5501070062903004980181c0901455001141210124011210a480c92000c108900b40255200c1d00303825501074100d550205c0c02c0f110b0000911203c80744e001c07501629510500c0607086c0004071042c50b040904100c0202220140c1081e00c400c0d5006480b50054000325102501e5a1041c80300d034000d060240045503940d140d000002070900c0000c51403402015080b94002c04c0c1445807041f04d0407103042401510880c92041000c40180d130001e852968054000d04078504240001d224418856104010080c14000c0c40e0320702921000c002001e00b0700381071800d0804c80c0444e40510041d29020b010f4107501003503511a200099602c01107d0503915a8440400e85551440d0014000c3c01200d000341c0300c10b81c0c064800500c840d900c0c8504d020051442d0410301100b05820703110424069503600a00c805801c25840c44 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 759433767 1250 759432517 759432523
    0x507090e0a02070c0b2d1e180901090507020d08061c03020109021c0312051330050d11340807030201060612051003020616060e0106090e0703050a0b040212 68
    0x42070080c5616a006c1c0040300d0405d8440c90244140d14010319107045c04066012071900b9481e402a0000310900003845000f0303210044100901000d0061403841c682d610b0703510250041c00c048445c4000b41c81804c008440b86406403021900c00c080c002d01d1440020a035a21a1506024103a8110155903e481010006980b0900b50a50301d509208a400c01600d544c01c00030410080780c1701101c10945808244a040004803624030003560300008881100e44070040094a00c444820048502403144404850900d6110f4024914011305d044140510000700b0440100c511602e405100c06192103528100d540c40e40070000e08061074002c0a01c402086580c03034008659116490880040c1d66170750060007040d40001d004000411401d81c100100d1400701403440075101070340006485000040b500c010010001d40606485917070014040c401c3c0e242060382c4902901e140d01910700d005c0d050502e600c1000000240c2c80080700d8110b0000c24011200780c6800c6421030700070f0001ea0b040004550001c112400030 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 759435017 1250 759433767 759433777
    0x1050a020903070e011404090c080a0b060102012004180204030f050604020324040303050912040306060510050c07170309152214010806120d080a0507090e0a02070c0b 73
    0x2009a5a800640105400d01181d40c01c256030f983c4040b001485031401c28012008442429100010740d03050b0360074011800921640040020302c55002040104200c0c0c0c032440c1d000c0c1000b03070000d00c94041c5041c400400701d07001c0d00b1214002c1d4400d020070011103042ca1215243c0b607018034001440c0c180c8a0310391083ca5600701500307661304da202c501400300718141040360044c180c00c00130b291102d0300221601078040c14000b91003c0d04058541c8003154459406110f404584070400ca40300d559a95a854000081c3c00300340b154610406003000303640d03200c03130160301214100100c0201418000d801c0c02000081462104d4040c0d00c00d100034030200c612500d4000514090421031945c5580f1800b1090308500d15400c076481e85150360a103100c080117603007030107600400003da0034205100300b60f07214008103019020360400d111141c4100c03e61008202d8100403041d01074802644288003958598a090310680924400c0083c0106410f001403d012525409070943da441042c0c1d41d611260b035200d03005011307000 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 759436267 1250 759435017 759435031
    0xe07151b02030f03031b0f0a0509012c031c05120907050a09060513060f15030906090f031b02100c050a06050a0f0b0f060301060c14070305011d16051e030105 69
    0x902c1200340c4060125034a03410a500302ca45803803d081345440031401400441010701ca40401d60480b6a1f00620600c0c4c541192141d0380100c6421114111205d10080d20340103004c0c1c0185200740b041aa2033b0207c00082d5601c98943d24a400701611000425460041055019005001000c181e5a503203001c058001d003a05000070807418180400c000d01081680c1400c4c2081c2e10b841d100b003110480100406c02194400d50100010243c0741c10300364040c080045009002e2450030b96010200401c1214041c400b9020f556001c80840300303841c06071000d00a021001e940080500c440a98052140c0052800300d4400c030300f071398224203141d0740380c1059070310960f043e40807951110340c504102c170144d100d45840b168044a0112031301d40107402140141c0700c103008640400070800010010f101c110281e0000da0015802140c0d0707015601c0c10114000c0499203000201449001d045856520000030320007003249000c86800c0d025032600040000d080700880e4070550300e0503000c0c8000c610381e0f030a2081d140710f440 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 759437517 1250 759436267 759436273
    0x1060f140307170304090b310204050a031511043506090a05300c0a020303030703090b0f01030302031209010f0606050408060c0a02071203030f0617010e07151b02030f 73
    0x420606c0340e2050b5200342c600300c2c1c005c080f01404035100d00f00103005200c404120540d07880d42405844091001b902c1141c100743d80184a01c0c000000b0021114403d030f04910400c41700300400e6401884024041c030a5108003c04510031014003242c010902d6112001c00810141c405e203c0c0c000e441015062600c215500d0300c41d908101d1210040c4007082c041c07200c00058000c0c500e40025024000792000c00041142c881c5401d401191a882c070f860104000601d040e00202201d40740e15210500401414001c0360403580808981c02045640f101e00c03410a060f00c0d4980c02850810300d8900203110003901c0100580e8841d9212801404c054100303100f400c0241c019a51090b54881c01d00490794a40880602156444e20040002800050703020175640d041ea048080da82c40c1c0036907141402c0f00507105e4105002c1c0041c1c64200d001a054086a1b5440ca20143c5c420080c0000ca054403c0305440300345520403201d032451a00d101c0c4810301d108d05000090248101010b155a82c02038021901c2c0072160a10064694 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 759438767 1250 759437517 759437519
    0x209040504050d020f0f031213060516020c0402070201120510050604082506090501080a0e1606021c020c0d1712040309080d0219050c0312040f0801060f140307170304 73
    0x741c1c1406070382003d4031707054000c000c0701c3c4400d01002c0e500d224044060b40014840008100350428003001214101c1d003200c014009400c001c450b6125000800c500c0b48098800c20406191f6410710b40259018160142c441a18884003c8140301c06040020690000d4950654000c50240c2c1d600000d0f20150031010001c002a6448a2250204119201c000442c1c42034054041010661007491001a02c000b86084111508d80441d0307040500440080c40606000710b011405284402503069811603002d50b080b2150032524107071441d00c80340314040180041e00200d00d5440c07141005500c2086052103080740180b4444124a089400c1d0401000d40e016440c108041c401071503072004804000e49012000741c040c9010500c00a035031206840d01142c180210346410038244002400302054a40d0081c080d03880c1c0a0a05c042641c01e54858013840e844454001000309800300144101d0003075501d0a07004030142802c0540040c10241c40380c8190340c2c14440d01e0400b0a200c2c00d03419106801c0c030741c0400159156 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 759440017 1250 759438767 759438793
    0xc0a051501061202090d02040e030f0a0e01080c120a02090d150203070e060a09030321331202150c07030b04110405060607110420071a04020607080c01020904050405 72
    0xc40195030740c0340301c0f130700602081100b07503243e041d2581556070480e000514105e0000c0b190381140101030450000c0c2002058082c500d80c0c11021302c61032140241e81e020410f60703c05030803502c0c5003e01003041071001e003024005800740d03885a00820b05044010030200c042481c40e60b415101c1100020715091482c0c011040c41017903600041c1c04040501c0c1191a182010014000103010700c14600c409400c000d5040c881891020b1502c0f00b1032403900c40420140600304054040850745d2240b00d180c00c2550001e001c007030000500c11282801030301e2a00c4604030b070004094003080406c00c21035600f0f0002c00000c0104010040c0100700280040d4468006401c82d032606003401003940e0003c5502501072810072040050320355985044811070b1358001d000c081c1c04480c26020034004c18a10704003a0103100c2c99a0000d220701d6000014004203482014040c03482000500040034003101030300d0003900300c5000e00a4000107951180a0072020784140d00040c184080080054207a4205980a407102d4120030010011 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 759441267 1250 759440017 759440027
    0xd060602010603050a17070209240609030d200d09060f02010b090c030a110a1d030d0f2604030507060b03070f15020c041505091602060a020c0a05150106 67
    0x406460000700201e0749507456160702c4001082c80208454203c0741101d0340c400c1c080c0c0c10384011a4000e4200b044503c2c0028420195402c8810b0458415034400800d00107403070b00350121100d028028020746480d03030502d103065804294150502004145025480c03070140010480031140c804c0725aa9071b88054504103010f003400400001070340440e4100310204841d0b03203c5030b50040e0418000100190b4035a00c0301380305801814140b409824a00000822070b10344c59000b803030410503a0403c01050b2121101d0400c0542c0d800000840e1404948400d0300369480a001d004080740503125021791804080400c9a080c41484003200c00b20007150011403ea4140040b0b031007091100c1c03030241d00078181c1134100109034545001c1c604c078509040300c1c11038101e04041d1083c80f041800843c050000e210342010f031001200c1501c0e150007014000c001c4000005d6185003803038501c20814403582c0107060359854114610029501c000807561080c446c01d10140005807080000d14a03030071031000c0c1070140794180000108 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 759442517 1250 759441267 759441269
    0x90d0506040b0109020a09061d0a030503031017060112050f0a030c21080a0c0509040603110f0a061e090b0a020615030102040506192d0305070c08220504060b0d06 71
    0x6003c0c0305102e0321b200d1503007102030001610442c5c202035203000095440085c4441c0d0120a154005041800002c10003400002860090681d04a01d0f402c05803202044500e0020f0640780e515140e100100402201014900c6075000e40e0140b01500c2e58403210a45061a04810308412000503039445003c0050100321009160003601083d4603209203182400000c21030f05025041040051f5079200010190b0700850403641100e6010b40240282c0c0d6490802c000c0022071503050300e00881e480700e08002a4642592040300b914200c2d19507422451554071042c4000641c0e04114040c418481d0b408140c076400c180c0540b8604400f41e00424451508034074449107610000b807540e0190303006100501c85e50b03603218142e0340140403118a0200000f403176401110316074400b801821039040400c40704495010060801901a440d58500b4080c84c2c44101c000c490084502e140500f5038403060000710b0080101010f40340c0c046c0c847c103981020640d01d9500040448245038810100c0100010301d2160b640480e004000c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 759443767 1250 759442517 759442529
    0x40e09060705071a180d0e24121504060b18120a020409051c020a060b1008060f0d0b070504090509030703020717030c010f0507020c0a050a1406090d0506040b01 70
    0x1c0d08083c0c06a8800400050001c000c103401400880018440c0c005039845003201c44070361003120160030300414050700a46100c0c101d035003c2e010001e20705c00451005010265070010f0002841d140c80c84006a10010100241c84140080441000c44081355680c0c000d4602410309841d08076502c030b2441c880b401e18141a0034940307001d8100381401044014001c01c00002281c1c06aa000c1204123aa24100f414028000c00a01d00701600070a45034a15030300088201c111803041c60100003400b1329100f04024494451442c20014000c2c41c00921079003424451080b202c0c00c0908102c042030510303611900c50640c110b40b03e20006070046020400043c0318002d40c0d411011030740213540f802c01e458a009440340d446000d2001b1005030202d020381076000420171200241c142e000200109442010680050170060ba003600040c401c440369202c451400364212403c5a00040c1102110b81c41c00410b441c100c416044a17980c424424400c5192644404007181d40161041b806000c40740350a00d080ca24500c4103821203 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 759445017 1250 759443767 759443777
    0xc060c030705060f0f0a0903090504150509010e071101020301080604060c030e010f0e0c0d020303090d0317090a0c0816140120010605090708040b150616120e060a0c080a030e03040e090607 82
    0x114011a4002d141b0309c06030b0f5002d98000c92051074036402088480c0440c2d0209800820b241c0002980e084440520f5000c3c080a69404040b00e14050700305003070340003e005510481d0041d001140024629a00400c0282d146090120780003141001c005c1c2140c3d02c460401048949820084000b0042841074408100d000c03107400007544442d40210b40e8900401c1c22701402265103400c140c06041c0034070380b101001000030120500c0751034050304e21b988500c0300d4034044512601408011444100100c0ea208803000c0304590341c4c282c83c1c42c090480e030000c0001c24186040c014028541c16030b040044d0240d001581d821070000c264145007100740038040900826007410028a00103010006e0f0184494540040441e11b1a000c50076009000422921411102d010f1038800043c00004210141d01008072040441d2504000001c00314180000303071003003a102c0740018a601e40307031400080300742000d02003841d031902d000a6060100c400651a607030003600003528031400b1350b00f004101d000401000d9440b0f2031a2403c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 759446267 1250 759445017 759445031
    0x908010c09030605041b0b0904051b1204110301111b0a02011710120b07030501061b15020714030c010c0c1208090a06020a0e03120406020c060c030705060f0f0a 70
    0x20300e0080c450000604030307038890010805101c001b10100c0c0303c3c0c14000d080059141ea4a100181300796214203040c40c0501e0504000505003104500754061846e80282d20901e8107611000f0303100b9004c00100100d40700100c0510081d05602e0901c52440d001d19400724807540c1d43d1800202804019190b00d4040d401e5001003001c1e801030340d011509248869854041598035207070101c040f0303000715003604540707080c00d054040001845840a11280914002d80b8104030a03600c41c4c070100c038071400001038205510750044081c0c002811500300c9403510180c0e50130042c00d121050703a51280000030610500807950010940380b007645030130701c52240183d8403402d200440c1e46803a80c50322417000d0324407181c400340501f00000911034102440f016a440307500c9201190344518440c0043c242044880c0c07594020300c42c10911940030703406801224140c0314550010036000258a0822400354000056490304d0302051003041e0004004002c018000c02091002004518100c0041d88207004020301c050340903420841 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 759447517 1250 759446267 759446291
    0x1060e150a1e0618050301051519150c031b06051e0717060f0a030605010f0801090b040b040206040801050103063e030a140a0504110a03033e0607090801 67
    0x702c02c4111400390520009603011a80c222040c0030403948401c0c0c1650078002001031403142003866680c100360454811040c12640c98020210701d8440c02989511540b40c100541e440340140e410980c080d11a00d000d0240c40030101840e0a84556003130b040f900701d6211000e1110a204c80ba03e00411001c10a5181089103003070a4001d207080d984a818070b0440c00030402190b402e44510344080d40050b406440300790f895640385008802000248500b682003000444003242c24801070185100ba0303908101003c01688032915544070301c0c2c201800480e48094200400a41c905083c09130038000d5006650000341950b2003000b40031000c000b0300da928a00303442504ae51503000001003030101045036282c00251a0f42c1e800e100c5800800156208155080d10842000004600c4d60011403156204040008802e4000f900b80048513100340001030200d42ca10b00380440b9404241400150702c58400140c1c84a4594003061850400d0403602e60f0f02250854020440040d401c1201c400c01050030700020011468861 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 759448767 1250 759447517 759447569
    0x7170f0a091e050d09080c0d1203020705060a0614010e03030304060f0f020f07021003060f0e04080f0a0221040b1b033c120105011101060e150a 63
    0x40c0500c9105036a16200350034440c88030490035229402c641c00c801c2c19025420200e54662240144c280018a80748000c00e1100020450392000d2030050a50703c3c1100042c0e440e880c0007031141c01000308041d400c1c80004003140007001b155001e650121000a506810000103030030001070f019495040c0002094641030549000080325441904103000240c03405a040c0755034007404520142a407024000329090804808500040c40300034800c85046d104540b4545d419001d81e0400c1c441e105801522040c100003965107076051940c868031414886141007001c0c0b240b8042c03900b03c00700c5440107a2041e404400b80039040d100035504082c9484e40581414a401d070b14030103038070035a4909150502d10416003070481c401002641c20001c0381d400100c49001410103024040c500890040106a1511a10152140c038140c1100c00052010039203411507801c000c01990582031481e0038960a640e01c1c100080c00300b044924550184841c0303103804108210310410414852480d8104900a401c1d03850200307440310032030f = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 759450017 1250 759448767 759448771
    0x402070803061002010e0d03060e0a0b031906110403080909070c11010f1403090309031908092e0201050612030c07031218080c131a01050c0705031507170f 68
    0x407283c290008007450000c9024140f8601800400c1c41a800d003810035940540209041d21401c1c10301a01c03603650052040d050700c2811150682540088010302004100243c07040d000038040c02c0049040845207418085541c89030b841620180d41c042a804400c0c9130161099402801501e0071800418150b29200c1d0501c039131902080c10b200d03003a2550000d079030198800c0c0d80c01c01004422a41c80c2d2401c94a0251682d102c816018070a016605080c02000305c48003007402c0241e04880050300380388401d810301080780f0b4400d9510660710030810801c078040d0202c40209458003540c0d800072a0318248402440610342d00d092865100c0c1d0020701c0500030810001901100704d0350032080c0f203909101041010703540d00e00c0e490b4510080c000c01c0c171030101c0c140c200051905030540080c3e601c80d4409454102031400c03200c0340c564091141c80c80828401b070390341c030401c00740800039a08016159016541c07000645441c00c010a200c81040310030702082070031a08110941d0076403c0480e01154a4903140c0808100c02ca00 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 759451267 1250 759450017 759450019
    0x513051009020a12020d0603030806060f0d0b1f09080d0c02030c060f09060d050f0606071208060f120a0b010911160c0f03050604021509060702010e1302130311040207080306 76
    0xc04241c000283d8410801418804940e40d8210354461030701d40c0d07610143c11140000e40200b8120b0300800d00c00c1c2448800c03180840010341c07a040c140313111150a4409800100d0546600c5000146002056030743c41c00019a942000c3d1100c0b25241d284c06640360038603000c1e06c101c42c203002100c46985d0150b10301183da003032220012a84556240005005040140180710003950080360125900f0350366005d952246014500b1110907058a95a00e41049031038442d814000308041da812400c8607096004046480c0c125a009081c032039088441c070003040d400b040740000b0324030030b600841c070403000e0100c0380d52900d016214006e4240103282c00c0323841e805010320411002003565600404800c0c1408000c400400180c500d5000703400a05543c0d0510995840c0700390f405034070502c5440a4030012400d410101c540c0048080c0c215402d2024580041d40d0f031003a0010440d40144c82400d00c0b5041e80345610041c6000701e10400010581030441c140003400b202c0c4404034500a9204200038004910b140301529400a8 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 759452517 1250 759451267 759451271
    0x90603030d0e120403140f011a0108180615130b060901140d110301140102060f16030e01020c0f0d17190b10030209030f0114040807031e090513051009 66
    0x700c00d0118926002104100f03400f0081c1c0810003004020b24a0f0015149610100480b90202114151035080303552550703030a0042000030b40b03200301e694050800c0c42d9002c2804011104074010043d050340c242003080300d4031104820101c107010b0040c070300407401001c80e000b00181000b82d08904004640c3c2c511608841d24107110440070030000683e5813604480d080d000140040c003034420703201441e80d89600700703010301d84880b4420441e0060355480000c0451140011030325440c042c3e1161702d56100c401009000f0481099143c901f0710100c104240002d0810998002c014118501d0381c1e09103d00f8072134415424010040f0020f914229000192481c3c1c0d00440600c04540741100d03181e00705001400741c3ca40399070704240701040c505001a010350151500c8071095058503180d4640b0300181d403c84035403070301c01c00c0380c1c4d0012804a0049040312000d07000f06442030030079212440c0010103070001072440e0421300c0001255414280b28030308003c480b801100e48248800d0005080180c542010601c140c0103100da215 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 759453767 1250 759452517 759452531
    0x30807080c12040303020c04050a02280203070618110d080319020d09060b15130311012f0d030524040f1e11031e100f0b030a0b090603030d 61
    0x8070510418845481c200002565141d403483d0103074440881d145010312452a00300002c44500343d43c022104001051402c80d0903058001042d88090404c408210003184814441c40380051050f204501c042c50350185c22924003022494003c002c040c80c6001540505c0c18074014800140300c03101603e80140d1b5001d021082600070005e494000c0c0201d20088070010304046c0c0080a0028586c011002a4820344481030044411602c4443c24416801e5821788001292010404602d0181503140152070514140440382c162882003004410354008071040c040104003c50303505003040050380040a80c6060a010302d11304861000c00c104c03402d8054400c1c05003902d0940805a440d940700650303107142c12000304100002d448180d4109144460110345c11450a0342c40c0b0540c00080095038420051580e1030203043c0d50b04410b02c500344d40043d201d001c1209196070082200400e0403a0364000e00a840303191602c0f071a0035542101550101035032140034500d98420321030f054038040b0440da02c00e01351200c045008 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 759455017 1250 759453767 759453787
    0x1020601090b06070f061b11030d05100807030c080f0a200103060f09200316050c0312160e180106110c0a030f0c0902031e0403200d030c02030403080708 67
    0x2920561318018050040e40122008100c800e81c00600c1c00e0b0300002200c8540710014030195228844d520b40b440481d0b005101620041d942a009141c0c0100d010204201565907400d8413403929845402c11196292880003d20180c2c8040005415012140c001030092518a440e00c803a8400c00d1258291011505076400c3c0f03a59020360044001400028082421282d8418007500203001c0b404101c107440501c401e41050710710300c410560b4082d800407240c2c100d02a00c842d41c15155070f44404007002107400103001100c040e50020411340e10811081c082803081c0600284014640c2090300c490b0391150a90204c0b00c0d06205617103e1490540d9000c0c00c00f2100700111010040c94000104010396001c1030305907010003008005102134405510842d080d6480903100ca683e0410303070000720f962000300e00488000c10b00300c0a078a0120b903001030281c00d00144c1d0020560074000c0c0f00304c51103092441580702c1a0045200c0d94103220766508540203101840c01d05065641d411618401c003040a000900007003030040da4 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 759456267 1250 759455017 759455029
    0x20090414040302060108072306160c030503090f04020c06040209060103090c0803040e0906191806020d05190c02060412020f0d02010905012019030b0406031104050603030901020601090b 81
    0x40e01440314000d03000c1d103040d1800959552090103805a940503602000883e0000c0c5202d03038034103002c6003151400c6640c0d14000e00a59030080360000010b640780219400c0400c0c0465410005035000e18051540c6400d12020311072050a402c016902440c41000703034000182c8082411504240d0481e20200030743c94410049000e000e0b90320018010010304040003c545800100400c203e884014201c103c90707036648403007515a42c080b96100c00413621080c0204000301070b64800e444070400b03100b0040c1c0405043c0c4800e401c81e000103a807454056642d005000a21204c50a0b403002042c80710000d010f201c1c105070b0001c0d02da9801a000410301012940c1c003240d141c0c0240f01041c2c1c508421411aa0700030080d410007406040200d2050f00c06520381100060114008824a40410a4610914901040002d5074460100c8c109203031800c059480c031031040c0c141d4076406220021405140c616121040d4801000222800605810303c43d40c0100640141c590700442e445044501c0c00300c001400c2c0400e100811a = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 759457517 1250 759456267 759456281
    0x20f011e02071806050d11060f030108031e0a0c0201081e04081c060302010e10021e071406040f05121c030204080d0c020a0b0903070909060e0d03200904 67
    0xc414411800312444a034005030400c2103840310354401144010000c98641252414000c00340c1010f01d9100301e01c04100014114403042c4c01c081d05080c070700b0044140c40340d4a0f4000b80c004c288603030000245c65007100808542c42c0b260f58500100d4529100c80d6441c09040c2283d0703507600906003c0e60711300080e0040a13010011003e80e502610740c4c0303150301e880c0c0361410881d03200040210800c18103141c207189020540c499801a00d03410b03140c840c0c62000c0d0b00c04101401400b40b000c0d01c114840c40f0a5000fa0944000d507119001100c03c00500c00300d8200402d505003501208549070003000700740000c01407641460001001c48030240d0380782c11614880a81e5904018041402014000d900f80b60200b80d558140e00800403201c51809803a4a070001d45422100d4520020000e940904944410b02054000070000c1c188040020112000702d41d071500c0010aa0741c0c041070070349201e83d50300c0040c02114424000020345520a01e410403a0150510344a880d061100603844a24075000c560700c0525201da80c0400 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 759458767 1250 759457517 759457547
    0x7050603040602040e090c0102120d0e0a030e0102070801050f07050708120c040f0e090c090604060812040f051002070e060f06030f070e03030708071b1205010b010e060c0604020f01 79
    0x2540e07031500b424940080d61043c414a01c480d038004000683c14440070400002c0c500050b400ba004800ca0140b042000307422a03030415540558449141d00e490404200080e8014880d4a0342c000d244511000a824548980d01100e1a039060108100000b0850304032030741c1c80703c00c0f410b0244d01c1d04d4490030900503e0103100150700f4166820000c0c448400d0414002c0c0084607007904088030355a880b480d203041281800d4410071b20560002034081881d00e007455609500401c003800028441d07588014451901245500c00b8504580024080c850360b4842c5c040c25002d0a42506d66844010320700c00001d68541891045069201c0c003030010800e507070355902e50b0003071041c3e00620440d101c1c2000c1c190300319039441c00d440d4580841c40001c0d090106040120981c3c10140d00328041c01e04042d16a100c540030709a81e11640b011104613080c0c045200300d081d0030000c078194000c0c00001040e010003c00582a4140f984199101e40800d20000c8101800050215806070341a21256000a00100140c82d901d80c0c0040c50 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 759460017 1250 759458767 759458779
    0xb0f070c023303310b0402041a0d060f0e07150c0501060e16030c1b0b0903090301051609050603040210051305040204171b33030403030501060f1716020705 68
    0x4130089200c009407003d000404440c2280590b1454030710a100c2c1c0c0001c2c60010141080480054003500d441d6010a22002c0f8082e80b1270010f420420000e000c1c444140c4040311a10303550041031482d40c480d8030442010701c42d03a10060201608140c40501c0e05648658003600304000d89001d8410405d0a40081c0020300d8144070313410b00350405284c517201585c0400c0721640002d00d0550661590f9118a460108a21030b1350241101219242c4445106000050801e20648810420000c558600b403040314840d0f00c40003500d007808070760620014201240d81e0f00c0244035406c1401071001503501e8001010300303043d441c00e1807651480281c0310409908069031090380c0c060303c046400640380d21403d0a508142d602441030303801158008d60b624a412000c1030303019410903030b02100464600f040b00d81d1294001d0000700351490700518680e4071410707607004440403000240c035800100005d41e00305e071250240000a081000f28011034a00d0030950210041013244d8400a55004050484c02403080710040c00c009442 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 759461267 1250 759460017 759460021
    0x50609131e021905190f120503040305100209030d0c1113140117160b04090b0607080304121106090616090308030a05060307150206010303050306040b0d0b0f070c023303 74
    0x900c100d000c1134071480d4082d1100303113a500314080c1c942c0382c0c020555200030b04403504282845290301000710b6044041341c5c030344020000400814000c00000345130a42400001d6170b00d4038001c082c107003000205220081071003410802e0000090560480140103101512000c0441c5d61031a03504000e0403010b010b103030340d500d10b04001161400c450800d001c40c000e000b000f00c41609280e5400c03092500546d21a110145a007800140000b0307981d6048407000d454000c05590600c1e00300d403a600301c55030042d10102c42e00d0030b4a580d01c00c0e409401c8000440104850000303400c02c1d1034420071140d180d25008080d41c51440012510400302405030b6044400fa41d00031440c152030740380001d4914004c28041e100c50b0302c01c1c45085000130306010544d503918500342c5298060b01c03859185035000d5506400241006502c40c0c0c60300e01d411560340b40e5030740aa1740701c0e008a45040d8203003803c400d448400280a480c0000700b00c034001110000d41c1751801301950320042c4603a207400d807203a0182600b03070f201c0242d80020300a03080001 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 759462517 1250 759461267 759461299
    0x1f0513060e1c0c0206090910081204030302070f06210e0a03110118050304140d02040f0203040309060822140304030b010f0f0e06060304060b0a0602070603050609131e02 74
    0x790103a91502d0499110041e1030700c4441078442104040009501c0901080b03070701001e003003001c4115002000782d20004038041d12800c140342071502c2c980402d0300c01d035000300b010420f1590400c02c0400408585c401003200904141d402040001c1002a550340360f555040d400b44407001c282c0c012600d0490b2013050f51a41c2085140c0203100000840e0010465828007100d100c0d2405148155030486030701c8402103107024a0090882030f94000101e09940c000c40040b90100540c44a0107903100b030b0a003c4800581e0303840d013450090040a01d5401c0901001460700070400f1041488008803d04600d6600308180c400040c50205c0c142c407a00d44d002d0310706000c0070030004108282103032a941a14440c0b002a00c07090707100c5040c01c0100d03515100300101103240d08042203032402c0900096410600400b07010621000c0003000c01d40740c0005030300100040c1c2c40003004000036a8544500e94120804851040050402a031000c2152100740005014500c40744034000c10700380416121380d51607a014003001c0c16654040 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 759463767 1250 759462517 759462523
    0x9050f0310110405150a0e01081b1b061303091a0706020d0e0f030c0c01030c120e0714010201020903060402010806011206090b040509030a09141503100312021f0513060e 74
    0x1c81001d008007003011712640240752180c10b0f1060070045942e00310380c0e20845401190743c150080c0011100d04e042d20800c0318004080c0004209403a07086c00d80c0e0a800240c5100c46213050401811031100d03000260003c00041c1d44004d0070011105a410317140d841902e040350b039a2203840f910000515092001a08040300c05050b00120103000380081035074049404d0301c040c20707180e21428080c0e01250304030300c0004440e0341c040d0f0f10844101d0204d140580f407010006103c00100e400c0074902a07826072003444201f1019184c2001c0003031055003072000b036051803000804a80e40360070150009040c80900400640242d206441e02008022002418840543d4400001008150301c03a801c9000d54207004c005042d50f01c0000403101380d0a01552040340c11440d02d0800142601c58044481d0711800c03040452911540c1070015502070513850495400c5140395280c20444800302c0d503a00001c0d0741110011445070200c00c0d03000103003400190710104165446c04020860034042d1840200628a090303403403000b03c0400 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 759465017 1250 759463767 759463769
    0x1d091807031103160b090907052203060e1603060c050c07351f0b06040602010b0a0f1d0604110a0e0a170c010e03032a070b03060109050f03101104 64
    0x35001d4862001018030f132a42c01101e00d0007184c0442c3d000700106801c508012040b140c0c048010703e080f50400303100100e00007264031800303000003540d0a4504148140310031880f40c0c0352440303a0500103015014407141d80c4035040c4464840944819a61240720315418015400c42d004103100400f910340e2241c543e04004102600c8007040a5107080c421300d0762043c1400e00e1541a102e501d10743c02082400020b0070014009000c034040c104940d510798500e200b0235241c100c00f4001178412a0004250901c0074410702c100e2540031ba0001c1d10002e9901070801003014641030241255202140da0740480da100e8010501030321040300c002807000400203c08500c0e81e4440d0414900c0441240c3e0740b00d109984102080c8580a840c3d040d40f2507800c50704100d0704940c0201043c100d0014090144ea0070980844044107214414034018460450840400c8101840a12404018240ca0694641076003810000245400c441e0f000c2c40313028100c0b1a452100076070341000450900301c03101100307000c02803400040c1010390b00320b = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 759466267 1250 759465017 759465019
    0x6080114030d09030209090109060e03120c0702100804050a0c060e010f03110a050d0b06040e06030d2303041b0f050103060501031e0506180703050708071d0918070311 73
    0x544400c00312030703250200300c0710030080c1c283e6600a9a14116001c11400e568083c0c00c03068103640e10420003001030300d01e000b014080790105010b161500c1500f180c10308000b00c0204144490f8070200200c03c01039841a24441222a0502d4058801e58840c500f003071070104c912501410390b00a6210018121782d00c2100d0b88003248080c3e030b40c8800440000f105a00b9540405401c1e00d11440c280040001c02d07201d80e004d02403801c900c0d100814154803040200c1c01e283d005802036440c0d11a15010003000781003c11206000d044e851a00c20740500c0b12810110340312060b0800b02e8040500080030800303100442d421a46044811010305c0049075940b20041d2034048144262400b003410520005403941c0a84540c0410040d9045c2c40701c2200204c0100c50300621006110a40c41440c00466900040e1030781d00c0c040c8a600c0c01c1c0c0340001ca030f0901e03580141030814010030080170042c1c0c0482c000080986202a9100380d001981d81c40702d151076040700d2100d809444c410300d40700c510684400100f030014810041e070039940 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 759467517 1250 759466267 759466289
    0x1050406050d020a0603020c0a02060c01060603200315010e030d0c020a0602011509180803040f0606121a04060209040e100e070509070507050307021810091a0112110301060801 77
    0x1c0d0710810712500c191240710181d405904408200300860090300280082c00c6030a0039948072003120750018005030494400c10240744e41d0385806003c6e040e01481214802e850806170300c07038404081008240280300040c1003000c8161380c401c1290583c0d00036200c400c42e50b07a0003815100ea0150840009040c10004a01031b4030440c90301070000b80320b0b8010701c9000c603000724082481400a081446400c0680108c6034040e5079034054503030035804646100041c0d07010300d101c4c0c102c005d0500c445041400c142c41e113940000d550300342400282c10020354000ca8291441d901c941249080d0b039181e0400700004d0248020b07990700a821f10410180c24040800c1d51440b64074074031010059079401e40b0510b41d131f40d18580606900240b0304004101c4090052001d040c0d0a44103504991030099194007003580c104012410950403c090f1090140804a51401c040500000c61080014404010503841c0c155030540c1080d052240c00143d042c001f80d80740d000920196862148555696515074000701804002d1180740b080034 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 759468767 1250 759467517 759467519
    0x3060b090c031e180609030309061e06040518030a050c010f0e06010506070f120309020418020306010b0d06031211061e06040f020d0c02030c0d08010f03120908120301050406 76
    0x32048050320f0081d0a40c11003c074800310546a96043c41c0301c054048403241a2482c40c2c407262a00c00c20403a4401c040d51000f55451341864143e0b20301d00030001c5c0203d04006400302a01003a0400140c800d64060303011030700811191108040740200e14a9650318a0301e84c04001495207119130410020300e60343d11000c00800bd651225921031003168012040101e050300a074004011600e800c0e4080c0503d107000380505400d120317150b40c54009250001c0c0f03440d4007094a607034440040d40380600c169031134416500f00c0b4042a5910341e00090711a4414000d444421001281189a0f500c42da80210080c50388030303030541c0782e02d902140090490051015003c105101e00d0002030f0700f030494142c2e84640c140703071030800700c034203840340420480640726484050448503828884509805c0d207901a0002e007a07056005107542d08031415070380d410601c4200081050040303a200400a94030707942c081c0002c40e0b422070401c1038a14204101107030b0940b8a60301444442c4142d070042a0f40e0a0720100450490703100300c504012803 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 759470017 1250 759468767 759468781
    0x7024e070203010603050c13020c0316230703030e04090321020c12071716060b06190f08090c0904060b04110301180b100f0c060b0613030b0106080c1801050409020403060b09 76
    0x1e4440d40c0d4800c0007a41040c001019034401c00e0f00a40f00c054840c00d01103a00c01c44007840dc0c4040e054005c000241644121010028540c00140c986016401501c0038002c07802d5540303014165141000700c65075600b100180b20035914400f503040d14424034410040e2a01c1400c44500c1d0302041d0400319066442410f030400c26079040508100b103491840e0644c0044080003180d40b0f42500070010b80310090b4001c0000c10800c0d8003a185000e000e20f4100c0180c503115929800c01e1002030010328010140c40c0107520080ca40c0b8119a074502503030758440d81c4900701003103104055001c1401340040041e01c0c1a201d40200011619507100c000310300190040c003a040002d81d03042401c00c141c044001e0900c0300411000c510100038644200803420100d1300415011401c1841c5e040418440e511100801c0390307440c0c0201090040182d4408141d00520051030140d2450808030442c1d10b072880f50744072566446441421202040c1d00400c01d4400901440e0780840d2504d0742c81c10884054050b40540e1886444000006407a03 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 759471267 1250 759470017 759470021
    0xf110a03171005010819060b0a122f03040204020f0406081b03240a0b0d0905010608010b42071203330b0307024e070203010603050c13 59
    0x1101e105940304c5c0a04d4a407015940b0401c1a245006a222915080b02040d1501d041d40280140d003031030354510202444001c52481140c00c800c01711780c0d2070300c40d80c2055445408014001490080d80040041e900c0d1681e2000800134401c4094510074244007007400103115402440803403060ba04605000c0c0682e1916480c3c0c06140f004841541d580d080104842d07140710321a040b000069440a030500c0320140d21030301003034101d4008400100300b07a07859070810003c100b820700604c0002c00e0b00300c00034001604400d0004000b00c0d0840c45441e00c249880002900e41444403100180302030308520b01c02200c0c400c104c0031419550001070140d401034091410007400e14400c0c410300c009242c0148021403028064038070480e10561607101c442d0030030718007000072803007800080044d03024407019001445082035052003800108443c180d1040310072210504240d81104200850102c210450400b1903240e0410451500034083d103a400f039050342ca445404010408001429080080f0880d01d0000711440c1d0001802 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 759472517 1250 759471267 759471269
    0xf03080406030915060905150f18071e02070e0f060907030c111506030106080a0f0803040f140d110d020c090628090b0f010f0f110a031710 61
    0x20590100300010040a07220380d0004500603c5142d86001c0c280e100c0c041d41090b41c0c41c035049010300503a01d900744036401d024040c0c1942038501c262804c0000110600002e140244103502100b6124650301c00140c2e00d0384210441e1000e00f0f548442180000c040c00e00095987c00c2c0d50160b505c50383c40440c04600c481c564035001034412200149500d030726580e07059007100607140103118039062104405508a07069000c0c000c8929418002c0503006107407030210308050035586250301503006078000021042c0440c0f0b410000301503458100d4a61071b0f0340d856500c1c003c0840540d40314040c0c440542c1d40c0043d104e00402083c2a040400c4a07503817119004020101561039907a82d0341c52030056480905041841e0520005003540302200800307082e50100484070040014401c104400320004010805201524251042400031081500d1010452081c800084c00361490048004148410300100e0100c8a1040c8808030203010704000b640c0c2c00c140185000342040004110b040b440040d5500016602607000745440 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 759473767 1250 759472517 759472523
    0x6020717041818030f0216090b100507020d030c1106040b180102070b070f0c050405180105070504032a090e0a0b0f090703080a1b0c2105030a031a0d030305010f0f03 72
    0x2210340c2c42160f90039518210a03040305e40550007001849004106031004001c001c021308040420707020b0001d800c201c0c85101c1c540c03070b07801171007020b000c401d0162f00c60b141c0301860154142499048101c160034135511000c424021300d0f500510008001c0f403105c0442e80a0001c2203042e10240406107000320069817118a18080c40d58581c6d400d01c03603100411200480b222069001e03540f440e0f1300070f071108080340654000301ea0b490030512403014583c0202000b441229409140d61a10300e0429044d42c0e2044100014611030284c071030010020b5025029200c1e0300c1d14001c10310043c00300000c1140035a0b281c0c44a03008035040d10040002c5000a003904484500d0610800d000b03009403221606598690881b50803c032010400c0205825040300680c0f021044007668500881640d05407a1030451880120384070f044100c180e8080c40d4002400254000040e40c0840030301d400c0104440f04440351110507052061201e585c40b1070001a101c00f4150158440c0e8140c40e604a50040c400d034840d0030510750003030188001 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 759475017 1250 759473767 759473801
    0x60f1b020309011206090908043008070203010213090b0a0906140d1b061e0518010509010201090f080c0c01140313141b0a1719060207170418 62
    0x1082c00d6108000440c2900c544d0707074001420541781e44100341260300c03402040ba5046800a8203000c5503e4003071450b60405c3c240141034103d24000107a204400c8280e12008100d002c022864000b195000c3d0141c0f0100b4080415401510340e851078404040c005105020f03000380548080490091003034001d50b42035034841140400f03501802801c0c02100c0e400b80600752050440490a409410341d107902d44030040c9410750700d8591908a171100c035604c0b02e00507000001801001c0103072545080310503083c00040e4400342070103078490081c83c2c0180d01400c0701707180c0189107040b0140150104410781019103200224002102c00701c0904030019a51561001f824021040c01170000034481170394015013400d181d00c40c0c81110824414802101c0c0340c400d5020300040740302000b003843e6013241040001100140417a151208181c021540800c3e268944110401c02680d5480400014070490313804541c6190b41c065008044106005021a92038210740079040b004211701088001c54a0140220320710112000a0 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 759476267 1250 759475017 759475027
    0x100b220504111b07030503270f280801020703050d0605030321040f0f0809151314040207052b2c030c120a0b0a050103080912150103060f1b0203 63
    0x1281c3c0c00740e4045400c42c03c41d40b042c8030002c40006c2d400d10140c5449801d0400041c440c04da40c100d49003021000300d02840c0205103004070f103444c0b40d8910200082c02080f0f44072150707044039503041070191440310380c000c240039600000300c0b078003010f611600031b0100c202885800c03c05140ca5404040e20303445a00c00d8410807100e6041013119075448898200d401c24407544010f6810f840c7d070703655501840458034003a6403030300c8040b444440c070741402c1c240f00c0d101ca03030360301c448500d000000290b1015891a40c003960411207801c40d03441d02c00b41c803140c0c1103c4209400404071100d40c1c0008030560714076034240c040c5050f4a0113002c1454030050041d01c000d0b00d010800d0170b8510708138940c99500000b0701809202d03e40e0602c00c4844609507900d0300d1410035a14000400a0501c010b03041c1041e00401d41c0180908010524001c0100081003400040c0e440d0b18100316225003010714200540c51412409028210241a80c080000100310701544030109604186400348400202d15140300080702c02048480096002080 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 759477517 1250 759476267 759476287
    0xe0105060a05120c030f15030316020a0e0408030711031603050f07231203130b06130f06060e180c0f04030b010308070b060a0f0e100b22050411 63
    0x190041100e18600030f42000300100c0c2510040500751100040e14000009010714880129020390713001410107051003203026120003207030740c038890944110700c00303812142e52300119640d091020004012240c00172440e0b00302421b21152070b910640c1e9850104200c10104003035100088240c03503901101504041800c2e0300350320159000c0d408940c04c40d084100400c01d107800940b00c9050104450000c40a81020f482400c94807460261034181d2010003803030500411440c411070312050020300f5801891a6001d84800c004989641401d95000042904203041c0d002d441050307034801412240c2642e01c1d0704011b46240c0078000005040d908007081ca03072a0078005a26040b802d80103000304002d000d41a0703d01541d94070361910800084e0400c030f602603000070700311003800341042c10799400c0f000440346803d006160164290300d089080c440c00b06882c0c14440020b0300403508000b800014010801026aa9041c400c0c0009a00e40d0f28043c020300c200030f403007002c00c450616201c1c68280d100e004a0652034540448 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 759478767 1250 759477517 759477529
    0xd080c0d1d130f0213080f01060b031f1214072103080702120705060105090a050c0d0515130e0d0207062c0406060c031e0c060c0903020a08030a03150e0105 68
    0x303800040850702c03032100d810300003d603100821941c1220306404582a003824641400d240d648007090b031451307040c0f10301485650211000c0b40e070815003000c8003076044848041c1007d60703856154086400fa0404d00181030a11070008803a2810007841405c0d1a1110b0300ca16100481140423101524080038034060407000034054440141c1142e43c2d40115100e615090390502c0303480e400004210307041c1d08031400400c09401c00801298212200000c2800a0f1804440740030441c01955808003039281c503038000c100305400d81403480d00801c401501c400f821101011030180030348065418074000e0f204200c1000001c42c40814070030281c5500e60746903040170301c101455100188038944201d0052010000400c525515885640003e260b030741c503040030701c03090342c10090071aa02d00e803c1c18940c03455010030050680c0d07100900b603e100d03a228900254400102204880c82c00131900029081070344403801080e84034001000d0701f180113445e9010f1210f030340300d020001810030f000c3c0316145203401d086005114620b009 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 759480017 1250 759478767 759478789
    0x61b0c0b091e151605070209040f0c09050114101d030f01020304140d051c020304030e0a0b18030304050f010c151b030b040203040525050d080c0d1d 65
    0x20307804646401d80405940d0302c5054546524880c16070101169000d580042c446403540030113208408050004084009072442c844c02a001f40725003c1c0d1030000d41000400b142110070135401c00441402582c450620000410080c061002c21f8100c0d414202454582980702e1070b510003441e41c5403242d403600c40410400604e242c6d4861a03041c00f420b86c844080350001d1020310b125901030140f2602e0305032900b5541d401e120481c4c00e0101000b204104190140c0c201c0382c0c1d100c0110039242001079403507075241011901d0944801120f940051411000594503101101270400044e110003140502d0b0080f804240c1d880c40b9910803190880021241080e0640c0030300c0540ca00036009a07070203180454040c042d1000c581d443c40c8581a05601d00c40741000c9281d052144140940c0103890451450030300303849056a5690018402c03061a00300d80d04442000c038a000210001c040c050b000c0c0003130b010305241103006604518444032051149a550b00c00c56440b44078030402812415460790062212181400103104039 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 759481267 1250 759480017 759480031
    0x7090204080a33020915030406050403030b060301030b0f15030a0f050c0a031a070311040e0f07030204030302061b04082d06040305040e070309020d050d030e01110a030e2503061b0c0b 80
    0x2c9000001d1b04140400194400e501c10b09001846190510380942100c1145d00200c0c0102014401800007805150f4400c0d04a50300c15005031452f6038003100f80c1c0d000312500d40b43e0ba4040c060780080f4010482140c110360352542c403c00548450300e4014060120000030362001500d12201081201040c00079903034125000200c0740380c0404c45148550540c0d819910951001c4ea081d0110410400b03410000a11240c0040706480e095180900d1500c001b076480f1030190026448104400b20054a64103072403c41d4024075070b0b07406641000c0b0300000c400782c00c490803103520a921546400c6895090401140c500e220710751640b1424101400c001c083c290400c0000c001e001419900c0e01c0c03250241c0c4d03d006092558500c22001000284d8400400030113807042c40d4861013550303052601c10080d000d200810303100503002a190000e442c01d20710007258502005000080e914105403842e0480c260040c41007042a00c0c00f6482c00c1c4280c90b00a40e080344506503800303850000664044401d800503903244001c940100d1 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 759482517 1250 759481267 759481279
    0x90e07050441060102010219030509150a0e190203031c29120601080613060f0507020c100c02030a1e12050a1803020315070207090204080a330209 64
    0x2001a032840d62099001c40380202011015010b50840c955441c6040d48000d0a10003941080300a40162003100d0b00c0d51014002e040d00d6400182d140e0341c0400421900b08007440285e200c7d410100e1070715000b0400d0300d0140d02103024142c0048030b008a104001407040f0f81c040e0003580703460100c8020490307240e0550b1529174460b0302e900491600d4440c000382402c0b1141564030500028028004014004212481a44a5801ca50010007440c1004141513910995000304c198000349145000001003444091221001d46054144140740307134002018036803800709841c01e110903148444180c6000740380713600085d0302d80c0c4904d06510002c0c4250541d41c0b00c220b4130100f24202161300380d840440001d4040c9001000810114510005550040d2140e02c500140e80390b400c215400c1d070f000720b51031700c1403038840300b0030f4030401d0000c50480c5108026140007420b0000c4219245d40e250b0303d120b43c80341c014242c252601c80140003490310b820210b13506100803075441061001c444503219182d4011390400c42c00b0691083c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 759483767 1250 759482517 759482561
    0xf0307080a1b03030c030522032019140f030415090e150405060a060c1b08060f011a091e011101060e04060e0d0503190908071b090e070504 61
    0x158114414600b07480703a240407440c6460040b0007400c03518014007103e143c03000d0f81c0c1710703032541211a407a01e404142c040c68004030b4152550009400101c00c00703c90002c0388035001c03121201110aa107204078051182040340c404000b40d04180b656940301010100c41d0741c10400040002d21949561001e040e9601d00348540b4047d92070050410461003104d210120030316440d03007140d5914151003000e5100344225031103620182400c20080c030040304414018410120b400d464808118051081002402090110fa0091400000010140d0020310851100071107082000703001ca0030030000e8400c0c00e00081c204d043e2040f580ea0280c64907580029140781031210706402103008110a00590003e071810002a544a007860301d80b03041100c81041c50143c1e80d8000b2036001e40382c10390050443c4d4101180c1400e4041e000c0f60301850030000c00d600a4010310741c07840000d00b0010044060102c5007142c0c0c029108400300d41ea02d10741d68042d6001c02200ca10250071014003800a8a001d500079403006a0749510444c0407 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 759485017 1250 759483767 759483797
    0x120c0504050106030203060406091e020f0904020c1f052518081b090405060721050f06010f09080c040f0e1002120a060501120c0302070f080910020f0307080a 69
    0x640083c0c0040002076000010400a402d16004040007070043c1c520400c00f09400f089000c140701001c10340c080000c1d4000030710300207180111054071501e4100600c1155500007000b611341e40e600e0311141001401710b909a0441039402c0034400d041c41442503c1c0201d039032046003c0c1c9009004203501c8820180711049601200c404814100d40010300400c0d070013404a894600c51001d842c0b1030f40c02c03400740301e41d9007401004000340005c2010740c0c00001c11304020041c41420341c0e090901c045034240e03d002240c9000c0c20820a12110f01c201800781c038080c1c0310004030b02d6408004980750f0010340101c44143d4000c080000c440e040035440069540c00c40d00c1c0000e0008013500ca0340e8281a40c10204414a40d000f00304070b0189405513005941280c20b04400304051480c0800103002c0f046c040201040040d903481c0c0c90301d0143d00a404451000c0ea000040c0d6000d1106443d101e142500810b0810b0b004982c0094010702290001030000c0c00307241c00706d0007181001159540d1b48002c2e4000904401007041e810034a0b000c2c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 759486267 1250 759485017 759485021
    0x60c041203080a2306030708061005060c0a0b070203040e060405091b06120c091009140411160303060312030e060f04060b0909010e060f01050d020f0604050a140a0b070507120c0504 79
    0xb816112404d81911414242e041600d46005038002c1c0c1d00d00e401c8034042c40440c03400740040d00c04030345040d030310592580354a42403d420b082022201618a6103000e0130442e58a501000400540d0b90500002c45103459034410b000881e50119042d00050b40220f4261411404002448602e00030041100703281c400150200f01110000380d600340c2a10034040341c1a0364071300d01740c1c003141b281c004e45141140341240303850501079824081e159854003455840c0e00300c506a004d0401100d00c0c40d8007100004580c058180b80050003845244002e581e000300841c281c40741c2ca03100780159800d554030680200f02e16100c14182c01400840a041207070700b40c0d980c01585d040c1c3c1c2c4410340c1e224407800785040001613901060000609040f002440820742592550051143da542c2002c4071030155015101d0b03001090780000825098480c640200340e0090102c18001525421040c000c2d1461109030b1304c108110380d594600c82c00901039070784000d14542100002f4028500070042e12459140100c10540456a549000c901 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 759487517 1250 759486267 759486311
    0x6030c03232520010203090d0c02010203040b18030c100507151b0f02150408040605180613030201032f0705120f070201030506030c090a0218041d060c041203080a 71
    0x41403210262540703c5031880e48001c0e92482c4030000303528510f01410710548170745100e481e0301c05019903003c804040da44204281d501414540300140d035030303264a220010030906600d045a00c24462859280014104005148180103040d10b40c01d0600c00e99603038a02c02142c2c007180304820a40d8a80d023072150074803503604440340c0f21456191f0903020b4050090003800c0501c0c2c0c4005228680d0390b0400c2c040042c0040e0100c90445071946045611084081c8850000d03030010020b00f039001101061108c02c1c1342420300035000300c074801d88041000000c03002d071000200c03031001165169132240045200102d1a01d4000309291481502a149503505c03003202211680c000c0ba0180ca4002e60101d010070031540c05206180e00b01d60220000e002c80d40320840042c51010780101040c440c03503000f00b5000d40c0a044040b0410f52050005d105024001080c4000c0440c00c075482d400100703a114004c04a012001d00d481104c040d01e000d801c04410341840c84d2020703241088003030154440c80e551000d1000c103420440714070318 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 759488767 1250 759487517 759487591
    0x60e06042f132c04050a020609041503120917030405040b010912110a0506031b161403120f041713090212010e15091f0f080706030c0323 60
    0x40c083d40d4181820b150840112842c00c11001100611021890004010621640c1101c400d59148446004207004d4800c496920094a0040001104001080c00350f0a11000b0342d685401000d075482c990f19031075410055402e183c0c1c3d00200030520041c10f250304480c2c02c102044c189490201d035a00905042d82d081e08806545021007002801c1c0c0c10315101041030002c1c0307421503220b400c0d4148100c1441520844004d24002c01c48006194018540c0700c004510140f40c002030301107078220050b0441d139100e92240c09003405071340741c400001b102d40b00081ca00c24080c90308003410b84414054280302c40c0340fa0303100510010b424114130400084410190004041e1000d6845106241354906611001c4642c005404076660710003441c0b84188503190902c2a9a00074224015075030408803c070701500200480b038100071070020030080042006480000c4400407035400c0d503030800c036504000500324100e61946210904803000d55a001c013500c011440110f8225402c0e00b50f442032800000000080001800050 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 759490017 1250 759488767 759488789
    0x1120f080c0109060b0409110906041b03020306100801030c09022512020607031a060306060706021207022107081309020a0e0f0411040b0304060e10060e06042f13 71
    0xd83c2044030a00542c0550602581c0070703c112100e90ba10034413503120200e02c45001d10b40f01c02c000342c415030302d036001040586d450215001c2d8102d00b41600034041d520803207001d40650691001841c0b940e2194142d40e04076134225111410490400e51104041d50100a8080d882030203040c0c8042c8a0700c5240d0f00c00942440390346444041d8003c00700280c108813000340008145031405422050001102e43c80450750101111016904d59580e80098611b016000d0084c1100f480401c220f031071080100c4009024218030380840b1825882c9241403000780955801a1841e040203100d03200000d0400d4000c0e09411039a44201d041e09030b2103250a030101e805c80f00329240000c10540039420103041c810400010058140c1d0140043c04030160804d5035881940315121000c10004005014007847d40e010f2101c005030807040e03c4070144e80d001c1000162806000b8407441a60300e40100c2c01c0ba103007510401c410501c2480b0b00071420320100d802c0541d40d6000029400000c0070410212034600200c41c0c0da00c0151000706c0d80 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 759491267 1250 759490017 759490031
    0x8031b070b010e091b21011e02130b090609041a030a03180b03010b0a050702030321010906080d08070f0504090603060c09081609020703120203070207060e031501120f080c01 76
    0x4024a072520340700d0542105074064088417043d4640d041100d42002d0403580441e07500003103088280c0101150040541c00d44486240703c51a402c0c1a0020420000d020340034045541c0c03141030310000c40c858803e007160701000c2005076510074146900540c000e0703402402044007195162000c2820308015076401c4000a024050a42d11040d141c1180c201402d41007504908560602080a1040c4514803498040c40300c042101811581d00300101c03070342e141e4240c0c0c0340720b60070b0f85010320524210001e005003440142419804a0341010015121122400e185c0e0703000120b4848200980d50041010350440400504000100303070400d86009410003184030b00e500050180c0820401003c1c011f00b034121a03400e070048c1c0340000302403d00c801030700c0035540100001659446240b4050f51511300e8a92202d507542c1c000320400110720b4010131041c088410544900000b020301c4002c05880b0f11540e902e140a203e003200060008003032402c01900a64070518081c0b44100c2c864a46002d00c0d040801c01455580d19004 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 759492517 1250 759491267 759491281
    0x303050405010c140d05180a030905150a17040201020c10020303100509010803120a02070c1503110328020c0f1c02070e16092d0f0308031b070b010e 65
    0x20450003c40c600346482a00e0700d9100400d070b5000d2181042940c40c0c0364565000caa5840120958244200725440444100071928a4040c002441e2071203514480d202c1c00c51410381505025044403100f0006a452004001d40c542100803100400f4206a04520403844d1002c2107845144661000780074a400443d101c0c40c00c2c0246003215501c0350812030050300c00200422030080004269002c01220b001546140d40c0c0e00d01550000380140c0402a043c2d41481a00080c6880c11100785c05d540d4986903070920001d130031030302c005407280700680e481c00c20001d296240e0404924600000300c4029410b40000d481c000490007072624000015070340e2003494201c0c44e00c0d070001c503010b180320300d1074100f00340054010503107048102c00194100600e1941201c0b0806041211544a00ea03410090040e0b039003a900c0d809004501d5801400d0300c1d011480b0b4980f10020046103403281c4103a001c04903640407a0891540d514001149601e0200103804a280f44045c004000040e400041c05030107407503406140540c904d0404 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 759493767 1250 759492517 759492521
    0x6040b0d05060a050d0206030718090c0e0a050616030c080c0f070905130210170708091603260403170d050c1306110f0708070302010e0a06050301060c020f0d030305040501 75
    0x140c40c0390f1107110401d0040085803242c640403840380350112906030f240d5035000c8054034250ba5400504001d000403600100e0f0b1700b40b1b2a48602c2c080d4401d0341d00d00ca401c14101080c011011070300e0180741d031700c00d10034042e6008546041041d0160302c0d2080c60110400d4403a0743e10724003203800020111019800000500c40130704010880d4000800f003401051008d400c04078910310044a190f400a4024800c1c2008010014040c1050320501c0500e81a11141c0d49000000101a120309483c031800601845001c203101c040b60900010a80b5085002054a00010520b42140d44101c4c0e100b00381d02d500501000000c1343d09000001c510442420380d090360340c440014980100c0354004c000100c80740c800d0108070150428079407260b040d40d0ba1820300160304031001c8003441c90305101c03600f0234031144113070302d03010414290200e49e482c200c1e4403e0b01d42c50041e040c00d0007004200b00c0a80210000120184010464140301d140040c000724005010610080e1207007011892106003200b066003c04d0720354041c4000c0050074 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 759495017 1250 759493767 759493771
    0x403050304060f02060705070f0303061e0e073b0607050c01020106050a08100c021e0f240a0213050a03060c080c0c070e06060c07060f031505060d1a06040b0d05 70
    0x1813024181c0f501d00003202030014040c0076800b410803440e046c00c1d41c0415029520010281801e054a109040c40440f03034442ea071442d9020b0350134a0192880800c1e50b45019058607000da00460750700c084000500e44c030b4000760143c90400c000c210031440f46050f0f81910360740c00600909024a01420341c10f2500000a030031341c0c4040e44080e01030280d0402c2000300400108080c111403403101001b04550100b204100c2c900030002155582c040c00c00706816298800001d00e840500c44d202050300c01450301030007840400708110100f03484080e6080006400300900394003d019680040204800d0341d03407600085010510940c100b142c40c1551200d48202d01070700143d0075540542c3c03500c403183c50709850011071130316010a03103e42c05403081028086800ca07507640081c0d0782d020f141103045804030f950700c54005003000101c20000340484e141500c6040329800e0064944144c0d81c002e0956403505d9441181d00009042d1b0342c5144003c101e40011840703866680c0303c0148010701d104071a1035110031600c4d600b0002c903640 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 759496267 1250 759495017 759495047
    0x11a0d02241b0c0913030507050106031e021c0203031b07080a2409030516171908160801032a090506100509090a05180607080a0b0306190218030102040305030406 71
    0x2075001c00c6545c0641660002500380e061621984034040d618060f405050941c01c01015241000207900c0200209034282031000d0080321001d80c81c130380382c8489002c0701c019924040e405800400035a90041a4800605050140401100c0c0c0b102e9840b030080d81021042c80e0700304c1c0d15500030001c541c0820004081c800300302c031540c0400c010303000307035a90090300611541c84080404801880c602c400d1110b1404280c13440e000c6100150341d90150340100c0c010214401e03803094049204030020401c90014003100b0202c55546456020881c1d003141c0310300d180000d0303400b04140122400760070207119625400c103e0740200310b170350f40111701c0d820140100480c9120110a80d41003000a021001044d81c0c3d480d401600400749803000078041e19040140c5404440d42a0100450300c03c138414060015480074029100b40346110742008044085410161140c40c1602d003280400c1a01c101c8810340d1002d9401425841c07d989115007000540034040703401da0700030790b10540300d0ba00041800c011840d0840051b0311080380c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 759497517 1250 759496267 759496279
    0x30903030e3d060b03010603270818040e010b0f0d03080f09071d1f030302030a21060f03060c0503010e0103030c02030106030b04080309011a0d02241b0c 67
    0x180c8005201001407a040240e608003526180c50942d0300e156030549003900040201c18080540c803100d00d2442070340b080c4035200000b85485205144a810340e60707010b600d845100c104456400c070940302c40d4980e803c00280d510748120807007410049a66584a40d01482c40c805001142c1078070703030740e01f0000030080321000a8000c040802003540029400700700c10f90b2103014824111095101c89407a203180250071b4001d01400d00c0c059000c1f410881c0b4800800313215071700e0580390b0b0b41741c0080074812103440320940c440103025920034486010018068468003032020005040f50604c030350740341d41e5070007500d20940c0110f5070714000460620901019000c0c1440b0700c81d4905285d80307075525009030075060000500c406401c0111640c01003046542c29084480110b8000d0008026803d281c14444140c0d8010386503c0300c15880c02c10445402c0c000d0402e982c440140041078541c250125400b84070714400714582e0b13540c817070981d40e810240c0d000b078000c082c0141100c01c40082109944896230b05281070751a8241d0b40c0700310 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 759498767 1250 759497517 759497533
    0x11409010f034107020114070507060e060106121503030c021203040b0d050910050c0a030b03030c03031806090606061611030a05010f0f1103010308030c0c0d030903030e 74
    0x298102071981088030700c1d46000602c074840d161180d101c2c46080310400d6004000611009001c0a8000c0040152440720b003182201e511003520590894404619448100c0780707002c0003540b0317640250090f110260041e80045101d081c01c03c01c09007000741c01d0700138001161030003400da542078100b4132031174a0610074015584039140c06e544016001e4101444000e04c40c0402e0840a50150824000d83e001091401c035201d07100c100c0c14111002a000456941080e44107a090060403000720b80605d07405100c0e00580e183c0703071240d00c42040380a02803000d009500341c44208080c0c46c20320030400003144503001c1c441241150010060fa1141001e2001e00012080da200078140160f036032325041103c012401d0880d9503510400c0c0391500c40c54454a40304402d5141c061080c4140070b2003c190421f07545030804840401602c1090412402111b110703440c45400401d00380b0040c00018074150007103422070f1203485803031b007000555110185000403231a22a400681c603031b0740e04820150140a02d0340d5244200e00508414 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 759500017 1250 759498767 759498769
    0x631390302030a0b1e10060f02060709151112040918030e0405130b100e010b0406022d030301060e09010b0406050919050607060204030c090e0316060212040b06011409 73
    0x140c040800e003d05960036420210390445d41a114000041072501011601840c010f980010241070510600380800d0a03000001d03419440404c0300b9201e081c1c16103400710708900300500b000311030b42c0000e1003001b4401d203103074800031800c1c0804c000b2421b06204c802e819500c50802080300c050741c0848003c0e4480c82c5041c0c55400009400080f0404106c5050303400180542c0e480c0142c54410800e1032002d00080c07011001e0251703185103000228280c80c4240141344107640d840c90751100d40d01c0b0320711500006030040c6041e40000d11000d00c000240c1070302c00f21b00103d041c45500f261070071544281e012001144666040b400d050402c0081c05005064040c81d640c10030b8507041025241d40f00f1045034921510f508802c0c00501114802070700080c01c4050700d416100d02c07203464290025482070009441c806600640018030b858540280390030139a40c840a0f505000300b034000402c40320783e42141240c401d9003e004000909503025001849540207808140c00da0a000e4009485c00e04a08240190300d50100941101 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 759501267 1250 759500017 759500023
    0x8030c010b100c0f0b04020103110a050c1612030e0a08030408060a0606080601090302040f0f0c020d031407170702120a090e060d17090102030d14060111063139030203 73
    0x407a60300170406207001e030385a01c01203008041c0c0140d2201014004100c21018a034000f0240c0710301301c000001c035180540000c2c051441c4130325510030202c1c0455016165800030b48600c007400d0394510301800780504142c481200f24190341164200d40050f0b407000c4208000700704280516001080360b802e00d030703003181000c400080081402e400b001e4000c40d100c21100c02d04244962024a151004400070450645a000029140c415000515000a0070444100c81e41110700710079500410041d01d94101c410517a001e0a0351356078008143c0015070090b40b6050084030308041c000c1107050708580e80d8020050a1480d80d1100301c00291250740515104031005002071080303c100c101c0d12440c101016101c1c014000101e03e11f100d071a0000c0c0c0e1660501501100910703c800450703000d4542602c8110341464141d03001782e5140c10840c0c2000d031960300b0820090410000a6801403006031101000c400c400f40b0b41c440310303a61516003e03048107440d44c101e034903c03000c013880b40040c91020341403080203070f8289035400082e0317 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 759502517 1250 759501267 759501293
    0xb09010b1005040f150e030d02030a03060b12060d020a03060501030f02120d08011404020702061605061b0304020f01110d09030b0a150e0a14040c090501060e030316030908030c010b100c 81
    0x10249482045604803601907070946c003510304c00508441c0e20f602e0401c8025241d0f0020080000440d06214001c28285440700036a03803881410a010001c0d65502410850480c4240340183c0e00204c07004c5003c000303d4124013406010f540a44072100d510305142c81480b03401c0302500040012500300b00342070542d06078000ca031a41183d148111481c41c002c0d8003c0054001e101c1d080000790700810004820b42003041044554404500403015500f507641c0709580346c1ca000b04000884501580204009001850829000024030740c062401e440f0800440940c9881c18009840ea5408556504010410815005600c9501a01c004018000c540c01400d0600c842d2640740200180035810200180c80345406030300052054201c607804400c942850300f000b8090104c00e0003911002d9041600100d10940662040201e155010f4025881e1800340341800e08211201c074003c4007004140000000e44d01000c0025009012059000103a6007956030100420300b0340c04243c200902c01200303181c0d00803070554101c0076 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 759503767 1250 759502517 759502529
    0x5120a0501142e030e010b06040f06141309021305030f030d091407060504080c0a05010e130608060a0605120607020a080318100e0607090317160b09010b1005040f 71
    0x31640540408100662441a054a0003943c0380d00c403440803076a038584c0000c905008910b000300001502c0c40c0034010144a9409003039040780005004200a900c52500d0b0450100743c03071042da043c48402c0c681510f000f29594070104203190003258040f882d501c500720482c01803101300e0041c43d407900c42c4500345899015408030100400e6032804200c0c140031406036941160320366541904c5510762039810281694002d40500800f80c419031010343c82038244510510150f85058550321405070f1540700b040f030300d120319504443c185a11034500003000b100c1049801e0041c900e00c240821700e01d0401e02441034040c0780c80141d80382980f041d400e00c41c20f80c1e0041007070b40d400c68000215603926901d1a00002010f034889402d905c5900c034100d40b10030540382e942d0001200c03c0f610410b460f11130b140c1c0c40c070840b4510503074080a00106006c6d40e000407031702d0704000200b0003444271781844522180d441d19207080d0580c0032283c00d001c80e511027507980e1862034140e0058800402a040450a050505651860010141c0990 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 759505017 1250 759503767 759503779
    0x906010e13050304150c0b01090228030f0f0506040c031b030b1903060f1b090501030209180a020903070e101203091e050307060c0809100513030305120a050114 70
    0x740c060040c14000ca4020b48802c13401e8540602945d4001001412143c00c00c1d03400e00166800803810227207034000c8039101e00344a60b4240090790109081144400e00080010506031360782e940260076500c90095002e16902c0b00350004051829005000980e400300c4040fa040514080c0e090007207014541d1180030044103450300041403444100481c2c541e0901030780d034009400308810008204941c2d0703003046130710100c014810300c10303046100d10000d02c2803100c0c0355950210740d100c0f90a000382e52107070b03016299035940203004c00c0210307510012952a0a205803407906140d0f8000401c4030040c202048040c0042240c0040310301d1601d00050800b0600e00030340038034011142c0c0201c1032400d0612455002006d0303c14010088090804510460750300900d600c56217000b4001e0081c005801da0169120301c1030340d6040b2403031510b80200c000800c07801d0340c0c0220045040c4801886600300380050504550003662080e1034040e0b0311085401d0304259104024200e80c034150900780140007441ca5035132072008192083d910 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 759506267 1250 759505017 759505051
    0x380717030408040e0405030a0207051f080405070504090c0f05060702060d0b0301020f0d02190509061b010912080406110403020d11010309050115030b0105030a17070c03060f020a080906010e 83
    0x4070300c00c0b61007241c0c0071400c0380c03040038240b1080c400080020107480f01c041e022683d42c140d070381c0144003904446c020f6125611840c0706180054a00511a4a602c01e100b1010b5070002511900000e040f0b60014106841098108000307100a1002035030f080d014100031a46a03041c181150700194540c03103810315010b0516142ea210301c50340c0c1c07025015207102282034008183c490780111404002500b08420340440c44044001364042d20f17000b2400c03031f181180d000c0c1c241c03440c2c851800b201c02c00c0000e08040603c442d65a80c2544c0300410102c21603420700c0c041c99691018982440c1c1031100c25650708444804100134104000c0006a907a40e4030400685e034090759000701c161807000143c2c0104000d102c040c0055003000442040800e00041074420750317109540a103501d988420238566149403c1300c000340b01301e02191100c0900c0c5020409010707080d10509013070314455202c0e650002621101c90320700c410181c020516a5400d50000c82c080c0e8805012002410076600d0040d800d00c0502000c0c081520441689030 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 759507517 1250 759506267 759506273
    0x2506140405101713020312090f061207090906060c171204060b121606080415020705030316030902030c1c080c0c010206130308011503063807170304 65
    0x16640200801809602407a20910010b000c03c02c503200c400701e082c0c01002c00184d491892001800c19990098020501405d00c1c2c175001c02e45a0110300b0381d50f441800c164802420b9500c090050100c03d40040c06140103080070000600b120529820800b0550f040540c10b00c00d01c1e500c0080204542c3d00309070505070610206882c1002881940fa0140610200300c007084180945500684558070b0706641100d90321350034a00c020344600014050f68150706c1191000c10140c5d12440c40540c01c81e024060720070703612202072100c800300e070300402045440c0e41005c0108440d400c001140f40b031918a160605010104895000940b18070030800b00364801d24030b4042e518002c407405050514105da00c06980703982c40005001e440c0e44d50300a50015801407084074001000c1c09010320082e1000799140c3c03140780f1140d0030000203001c0d4440501800d000c040e920400000d9a007103640c0500c28031130180940e80d40c0a1010b00342c400400d412680c8545070300c00f0030086000001c0c074280c000c00312004440380c03250300c0b03850740d00d = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 759508767 1250 759507517 759507557
    0x203010e0a1a0a020f07142509110c06040f030e0d0201020d2001180501060501030b100815180f06060a0e0d02030307061b0e0f010507060216140d022506 67
    0x1414450b001000806c20400b0014910318060b9282e0b03a050403559406104000b90a62036a0400440c0518480040030403e144c09030f001003150100c44a00a0706140b03816580d00e191040441e01540c0320380d0340070640401d25070410300049141906a8441320060304940010b9510004041380104126003100e0380909511041000000503c13951b0003404840e800300c0c407000d008540f00c50b00380c94075480c1c5140022030b5800780c89030480c41031015041c0000300b01030840686200070001d001c601c2040314012660000e507205034039403034800003a03903260000381003e50394054281c000070a02e42c000c2400f001112417264000036100c115080c100e0300c81c131070803081b840442d0840c02420001032442c3d003420070440204a820054408e502c031240e031915102c2401c181009042d00c0d07080c003098042501000940003082860f0002c04d002082a8070352900c00d04d132959006821050008070220301e8005100510320250305001c8450001800d0446c0040040d51003102c1c144942c0358491803003800302c00c40300c00701c0c440e80c02 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 759510017 1250 759508767 759508777
    0x705030124090515130b060c030a0909060503070e31061406030c100c080a0917031c05070e031606110105240a15050307090605130519030506130203010e0a1a0a02 71
    0x60205502c07071402c524900e1741c070382054000000bc06c050800c0480d1002c0b0520545c1d00311400100249080c500c1c103d5560301c02ca0014150707540301c000d058980d00380c2103e60108066003910718054041c020000303061040031503080c4034081c0820030400083c81119600040c148003201d104440002e070071004004183e5154140b80ca0003080b42d0310209100e038003650000c000001b150003160314100070100000c4e40c00c0e10307486100b010113210b6840f5100140400c00707070350215174041d84a0511442d10800d0303a0001c2c1ca003410003521007500700441801070210942c0320300884e801001802c0280224200076200c01a01c1c0701e01d00088500009011840c0c546543e0044488014091261440c284403002030008013242c0c8100d032490702141103e4400a86203101e001110910400c1000d44241903013414100004014001c414525003901c9110210110b4001d0048a0091101d44812005440d02c0e1041c1403e580c003600c08600c0300c2c1c0102403200c002c41d2400441d4520b9040a007031a840325906c00c1031410080c011 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 759511267 1250 759510017 759510019
    0x20f0403051501030b1807090c05041809150b0f041802060d0e0d09060e041509020c160f15030213090c0509030111190507050705030124090515130b 65
    0xd070303500b00c0e000301102c8007400341a00d000751841c042560710140e0840050514007203840a6038400c840c10040c1e03018607440703100b40040310714203d45000e95030382c0403c0c0d25501900303803910310340d03581c181c07900030230504004060705003403445018060344045c48005455100c400061500407911244cc0300c3e03541d02000084410654020030040e21458030b124403800810001101c6000d511407010036141b51f46c05100030070121061517840e400f0740543c0c4d5040c00054107018000d4501494030000205140c8254000b400182c000c442c02130032102031012401d44c0f040c05607400a201600310541c10702c40011709400054030010381d402d016076117000603803502030f550038a42d001001c070320300c2c0c110740320001640030b0020680307408200c00031300412003a8516054148a4180e84600c50200b1440c4c84004034023030700c041c1400300c1c02801594180380d541c0c0c0c08a403c0d1340444c1585207103aa00401c0801e15011000100006000d04110810051400703040e51026140d0700c01a0030300c294141c072540303070700c03802e05400180c00080 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 759512517 1250 759511267 759511273
    0x71716110c1203030702010b03192307080d03110c07150903050307030329090114010522060f021f020c0313060e0406080c130e030f031e0c0306090a020f040305 70
    0x211010b00c0e140c994200b950300394015400c2451100040c07400050703500186040c0e00c0c41c81da1860a45d522000c0c0440403950300610b000025420103521141400004010000a400391041200c00d4a004046504122501c030340b0103410300921040c002c001941805440c0c034850481001c1c202003606480550f056071008041e440000307561000c159150300301298100c0181c0e40d200499046200f46104044c001c184550407400c0100100680d0741401c4001800c040b040c180700c2d00d0000c059001c2c2c040030111162045422052210410405a02074a000d8061001c2d1001e8441407101080410020310200743c1c4141241d0040341c0048103013000d000304e0701090151203182540e03958480f400385c80e920520000354461807404400027209803010500d80f9181c070b40100a56004840418940b00414141840d002e02d480180001c031014500203005600a180c050030341c0c080c1e0f4412220202d08614000c1280c04003000500603c0941c0e120051220f800005a11000d0b071213900040301401140565403000c0c0c6144 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 759513767 1250 759512517 759512539
    0xc0b01091e020f091011150703110304060905060f09070506031914040311010b1302070501090215030105041d210c070e010f0801050615090423071716110c 68
    0x601d40b8002d00c69004180c0e07480c104060120020350741c03004121000306c613903000b42c21b810090040c92904540c2c40101410002120013520380040c0c81500200c4040341c1451341c80c0c80c0401030140c20808681d02450072031000f40d480c07400001203a11407070903200d024080d020100c0810401c42c00480c14a400200702c41041240e03040640d80d1307041d00c0c0020703502a408103c10b04c4504d039048034180981480c00601038050125680c03000c0c2c425000b035001113420f440c070355a600001c400694903110721080c0004d08180f0580c485d410b260070041102c402c66500c055001112041c5a640440403c0e0500c0d10809004514140c0c102201a501303a8800e0b00d160b1700c01c601602001152459800344058140e403043c000c0d000d0410344500526003290f4040d56070541c0054003180c50001070000074010b25074240f01400124074440b013041c1d54049829005140520381401134204a20300e540440040030134240d07aa502d89003800e0040004180d421841400c10400c480b001c076040100700c0c10012180384201c0604610158 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 759515017 1250 759513767 759513787
    0x121112040b06090109020a0f0507080403080a080a052d040c0e0c04090b030706091e09061202010f0e060a03020a031401080d020d0905012a050615100c0b01091e02 71
    0x201d40c22110184900700d0107002082c08151403080c0c07181c6906584562030007542c04007094406070017050007110f890b08200004400a441007014000c60b4002351160601303070400b06408810748400500c07466000f01c0340e070850880401000c452600c3e00c001c0202d4128280c0b120f040985901c0078641110b02103120b02414003010000c140000e00441c0e0200000304584a4694101510340e0f01a01c50076000601808040c0300b100c00c100709000401c081c8800001c201e568a80142083d614280d010101f0034082d02020406d41d6003164682c00e1600c41e40c03402e0840d11000e040022514090004000b04055001c200c0c4030909000e903200d0a091144483c7c40542ca603941d1051540d2142007900c4503005010310070306010f01d41d000c1d034405000d4800507101c007103070f80d40c6106044000300440c0e1107400c0180c21061035078000c20300500607107004251201d6841030b00b0550300c0c14000421440e031a01c2081102d010365035000700b20205c180d40d05403040e05001140c1c0e1001050002051000a01c00c08000d074400039480c446 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 759516267 1250 759515017 759515033
    0xa0e1207060e030304230d0f05010606030f09020915011818110a02100b0a051810140d110102010e0313090609050601170402130e0f0f0d12111204 64
    0xc84074203555100c910aa01c400b030540f40d0080d441420b00030080f0b01101000c1010706514070141c000090a820407145017a26891924840c004040e40d081e595180c00707100c4240d260140720b2540904050600011000341e011070a01e480003040804400a440d021410581c0300c0c0515120b000c07004032031044059103a080d0302e080a101c511422011910f0542c984002804c40000d890503400241c01034103480002c03203030715005880c44d1403000da4411650180420f00b139544003c034401d08109404100e200d8905460704200c60710750703504500d00d500c0c00031619410540c0c4205003a0b00090f40502c0c000c40740d68940c0010f030f01404001907805004e0202048903006c494240d07281c41308640b0200414042d44bc0d4034606142242e03016621140062034100c241040381001810160708544040e1801c68980340c0040b45000b1115032001242d002c0d000300c600400390f5035003004078a41c2a0f0103a00a0a4080c0c000c1002070310f41000003441c0070045444904544802207218140c0c1c01d1015400c0042a0b02e00d014540071b12 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 759517517 1250 759516267 759516269
    0x160516061a0414010e040507091a04063006140c031603061406180301020408030405041109060405100311160204050906240604030602070503040e0f09030706020a0e1207 74
    0xa8845070310210322141c1c03a0900500c4a420107602080840340d0030001941d07803004000700b0550780c62090302000500783c4070501c03420501000c480c0c40c584e8441414003c00064a000e0760041000711002d10040d0603120303406642c0300b68102a0b02040c0302ca9513030791400c01e000e481600041881181041d040042d028880c100442c8988141e0b00c6495900b0107486041d0102c0f00d4900580164260f2040c6e110b90a0604000a00c2d03004822008654001854000642660300c250414407458101040421640c285400381000c00c0441100d1a400c0084800104019005078800c8622900303a200040343c030039009a03c061000c000b0b0a4071547d440480f2415900c5034a401d2008034000c901c5c1400040000304003142050142e05140051002c0c0d5100700600302c802c03100b442440e68440001c01001001a510f07200402249105a001d1a265803a01d40c4894001800038120128643d0711800c100c450100402103c502a41c40700c0c00580300c0c2600d40302107403440c41c216141c5400c09418503901c0d80c0c0e642d0002c0c2c060 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 759518767 1250 759517517 759517541
    0xe0c2101060f240e0402071b032f0f0103110c0a0f0b06010c0b0f061804200a080718181407080f0309040b0d05120a090909030816051606 60
    0x14100c05483c0c2ca200355140c40c1400c80000040d21003580309141d1600350010011580510035419400301c03c0201d040021200d41e2084030f2036240c0d500611240c0864510300c40d03c01707250003505e0b40c04220040100d40030008841b00a4100f55032100440100075460041d1000101004110f41c003400305440c159160ba0032408007078a0304a50000000c00540c8548840c541541e8444c03104030040e11030540d070044c0014081c14166021302e0040305000c88809800030144140e0040c52001e10800f1a81070402c40c40d8078254041e4021041c01c82d084c8400d01c1c00007040004c40b1040c1216050482c0307100e070b00000900004400b42e41c5901502445428042c0900e214000c10b50348106440c580d0341d4614603280ea0b02c40305510074134a5003041c489141c0360300c0d16a01804500348050031003079018900e6999203040903d20090049460030204100d80302690000702d0704050100035030200704403140c544001d0401c00c4001c2c091000c0e418205240780c40a4030407000d540c000c0119030400a041102441c004010b801518601 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 759520017 1250 759518767 759518789
    0xf0d0816080d1e1e0915020a050d15060818012c010c0e0a0308030903090303160302010b01080601050f0901020f100b01121a1509060301090c020f010e0c2101060f 71
    0x40c181e943c00500c580e2442d102001c01c07502d40c0050703404601c2c020b8180514150b658000036419183c040010b40000d0841c0c41c01940d030755a8503800380b5440700071070304c40801ca00b003030180d241d000b840310a411111094001100e43c414000701c10405162901400d207c2c0d0001d200c603070b1210f50b80d04030020314101e43c81450070b0500003808080102d139030031104070282480740e40d44031003450720400108010f44000c0d80c01c444094181c92a04201c82d011a00c4c561003000307800f0780c540010091005055081c4901c80d030800f02403900e06070f175041c60f80008006000c0e085010082140002d0312800d0741e802004585800045641a10080c0036000d503030703000410b0303004009404036600e98801d92000d100d9106006840f0104004200401c82d02418403803c0f03c3c84000400c2c118404110080341d6a888401640c020115004003180b0700c044d00c0c100a060a04146180a89030705204c514030081a0100da80740c0f203c24240c600c03044011205256215903082c0d034401007815482c054000c100700ba00600c841041e42c0c80803005c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 759521267 1250 759520017 759520061
    0x51213080d0c140c03030d02070f020d1a0f010b0711011701060201020d0c03020702101b06020304110f040b011e09030206120a18080f0a0302040e070c110f0d0816080d 73
    0x2010303243c4440c18800c171391541007000110940750085e409041058050381d0002c3d6500450342c04202035402c610006e4811810b071340305089406840c004401d40c40702031f107072603503c4e554584105066103000700c2c500207042c0b803180d21542c2a264403c0030612405c45034220110001e5944000c084e0007580403445604109007030006260b4054028002c6031050f03075001d0308006000450010032078080c0708030300b42d55100d080c40c2c10000c40400c0560000d503004502800b0920080100f220400400300d108540b0302c0e000f035050119008903607030445000c40c040e0240004042540d001208220740c3c18000350402580618046202545900461600c520500c11408100f00c0450a03294a0b41076003142c0c80700030048041004840502c09015001e405441d00d20300700941403c0d01d500c40d03a201c5150840c0c240e0006400310b07042400740611202c0e22411042d050741c9568400c0b200501180304401440005040c04600140003081c001c19584081500c507001007034152100c0ea01105030020302460350001c1c941c01444c40c8 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 759522517 1250 759521267 759521303
    0xd110907020703210201020903060703020d1413020d02060c01020f0705071202060703110106050d080c01290108040f020307080717032a160902040e01080109051213080d0c 75
    0x2890003c0e2500301c01400700d529400d00e00c0328010b032803074202801195004d000a034199107040107031034016501601c0150711540804074003001c88049118030b4042d80200410310032404084811502040e4041d80c20f091414418008580648100c0c4130403840c07984001400d100d007000500c0602640c5100302c0544a04650380d9448041d00c02000d080071b0341c405810010100028010b05000503030507824400030a00079980c600107143e40705143c4041d03459900c0029195041e04d07083c810700c5018201c8524520302500d12045214042050110081c14001075002080900048216681056a000701192522519149103d484010740e2041c80b60360100c00d070707401e0101f88000c8241d41e0410100408a00c00b4201c040e415521030030401e010000e00e0082002820400d98001090006030404580c050f0b0740d02d00c1c04082d038042c400c050784004103030b0349400c426400241020480c2ca06e080301c1c0031000ca490383c1100600000070640c5510001662150061540d180c5402100d805007480c0510b250729000d5207051 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 759523767 1250 759522517 759522523
    0x20a1e0212010902010516110604270504110d170d0207050d0311030f0421050a230711150a020d0e010201020a0f0f0311040806010801061e090b0d020d11090702 70
    0x40c0f0024040781050000780d0040c0d12503149030190501a82c414075032502c80c117020891036030113608810305001d980744081e04800c080542d00c40e04c0c0743c81c0d04002c0106240c943c60300f600c84c22034442103a100d101114044401c0c000403501d00e18001d6484241d55903203603d811040d40003035000010407280303400742140303440d80d860091280e145070034101c1d09405d107155134003540e00130500070040040341c80d0700302e540300c42c44040246d111394210b5146075120355907034564a4002406030301c0240802401501d4809040103061008800d44440c01e500c0320ba00148400340800060a15014a8108604407004610f01404690014a141e2194160341320a10151a0300c4012803e034481e801c40040031400160318a00468070580181408070b24900e40007441400f50b6142c48103d900035405901a5400040148200321081c031420004003c000d81001c44070aa40c4800d95a2040e58820390b1200c0b0390b41d944030f10f92502c41c101031010351a8000c001604410643c07070048903001c0c02d021980c2c054400c1ca0300103401c040c000 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 759525017 1250 759523767 759523781
    0x60417150f0720010f110414190b0a030207060f0911030c0312090a051002010506040b090f0402090604150e100e01031e020315010605180907050403082a06010801140610030903020a1e021201 83
    0x707101110041820121035a5640d40700bc00c6050415038200601c1d0f000c0b92561180d40000040b100e00401c40120798285101c00100340c044545c800e402400b402030a0383e03400a61a9030000300d1090b100d80b988880d00005a50486980c401900003181403000c25441d5410361213544511001c50f03080228000c0340d0288840c690007118500045249200818094030709607140d558051402080811003144124960314a40800d6118550401030b0300144040194078400101c068401c0942e100e071a076146440c0c0154a1114408610204003412248010b43d04c0a22501c0c3e000c6042407004440da50391a0703001480759100e800d540d2200c10310040603c60b28903003003400c46c0c098180b65449500309821a250040f0076800b1918080ea248082186103030a025403240d401300c2180d00030040e21240d0b00d0281c4a82c02c0d02d0400b0100e042013034070350b020031503240d0f2a05075003d000d040c10328000071412507602c0c05a1404006000151003221440c0c6091503800d003000c0f104031114402d4420010341d81141c034009007a5244 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 759526267 1250 759525017 759525049
    0xa11070c0501030e0a0c0b041d060d02090415051005270121120c0201080906061f051308010f0608070f05040506060417150f0720010f110414 62
    0x1401034100a00d42c407039082003042e0342425003036416034610740d03075841c2e810f13920b9034805d903002c40d0041420407000d020041c4400001d0070440c0c2c56000c51801c007000505141640b0302c001d105007409000718092040e0440c1d03500c2d41b00703800e040807c401c1c00e00140c031208101091082c070307200306400881007031840ca040e100c614011040600641c0f00e80d09004600c0c0c41c0061183c104031000c0c0614071031038049644249482440046502c032241c04584a0000420f100c6006103103058a602038000d100180d196244045500400d5040040da083c1d40408100e90340d101740010552042d540220100e8040010340c040200b41003079590030400e582c0e0720400760b62110b00601c0741c1c1507503551101e0300f0001401c0c1034010307d621550081115103070a440310700e0b028441144d140c0c1d000560f84164080030300701c1106007040781c0100600b42c3c400018545980010100011803100940840c440c0c000112042400d40082c101d6607400e07041480302014214150049801600c00c80c4480b500071a851031032800c0c800310600407840 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 759527517 1250 759526267 759526283
    0xf111c020907200a12030b010c05030a0305150303071209090603110609010917031312082a150f0c040b0a111203042301020901021e240a1107 62
    0x15070341e0b41c1034442550480024065990303281c038a010b10348082c808506280e1050480c0303203106000c2c40b0010101d03905640a40d06019400340c2c0c401c0484d10020541300b20008616002c101c6076144050089504e00010a0035090304c03010840b00100500205403d90041490765183c2a55a481024100352180c80c800a0509001c3c200003681504000b00106034030031b0181000c01ca16070341c03200445007100b829101c4905030380000c1800c500460206070888020b084049036444007036015268030881e8031803840c0801c2442c0d49440303240c15000030554200e5484506030291011041d1350b940030207280c94202c415110942d90000015000310b004000c2d030f810b5401602840341410800350381959501c0c410030020030648905d105482d180c48142d4011841030f4454044001512402508085075a03041001304606034018400d80d2820303680050181900000c6210648007070183e68000b604000019210708101d8080a40415a460700c250310a80901d550b03400c10800301814540c172450900070100300503d046 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 759528767 1250 759527517 759527521
    0x1103150108070c1106070c0e0f060a0605040b031305030a0239010c060908030c0702031b01080c07140105161206080601050105071a15040b031203040605040c030f111c0209 75
    0x200e13200303484141e00402400d86843e103034494403103418940c034503400b012060030701e1020045860240c40c16150089003d840d403080581c00c041c000b0300f89002d603001d00c0e01e2400b07003c00040c15441c7c0d400c0420301c9203074214003a00d548014400c1c0094598040410007550f003030040f0440518181106035041021400801d03d200c211260801114401480c036030a9032010386502084020601c1c0390b0055014039860780c0b0176981e50303c040c41818240604540c0307107485c6081e10b070403032641d07a604599410307440404c00601641e1800030345051150b801e80c1c501900101d40c6403004025801142e585480402c0a560312041e000c124040024420394540307010703418881c0c011400411555018802500005102e22002110a040000c8542c101803080300c1d20b83c0b0307034520340c00b48041d00e003018810190301e030302c05401500344019132507914802d80c4000741000702050b6542c2c0001d0240b000610958010390b600033600c40c2540365906081e40c0002603990b905110380d600c100040f003284140440c2141031a0b02604090190b = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 759530017 1250 759528767 759528773
    0x10e192901080f0a0905030f040f03030f030e060601080601020f1204050a080604030905010f030617060402120c030a260f04090f1a040e010b10050408060703061212121103150108070c 80
    0x20b005417940c202c070320340310503c500c20807030040c4400b400103061350f10074202c401459402d0040c234020074462031005045c6000c2c541510398002061441c1e006400703082050301500c1d40c900407442c0c44446d4140c8030060241200341407003034041d80000c03c111282141c15a00c519281d003143d603201c69080d40e000340070070100d40041100d5406071a06140e8041503003400110f1310b81e10003907101c51030f0103101c0c2c10510390403110401045103055030300e5141d920099001404848089008a80d40d00d4500001400705004085850303880c0d03900001c00c0010304c41d50803815490b0210308440a441e50858042e154160341481120030710460b25200301e0000000071031b0003540400048040c00b004001143d400352465403601c500d1502a21041c0c004071440f0115079031665280d160182080c00c0140c00b5010804140c2401820007100c1c0041080b15030030b40d00302117a0b5014404850043d105550b00c3d001c10055141861a03980321000003101030351042444284903100610820011107402c4412a01000840d08894030003000c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 759531267 1250 759530017 759530021
    0x714040b03070f27091103010e0d210617030a17040209150d0203030c0a140607020d050a02010b041b03050a060509160507050f06160801050603010e192901080f0a 71
    0x4d00070714520b4003019801c41040001542c03d617510542e0f00c1c0d04a615001c00a0600344640210641d101c80501561800d0201c002c1590030040419903c4158840380324036040010b60200b00180315070805080d0411400c01103d807030346c100e19041b0010500e00f100801c440c010410400e8802c82d40100503104581e204050102c4180b01c0508180d006940e4030801001614204000c050014207000101086c40d00d0b840c00d40c0c43c020351510f12540a4200750305000722a0340000e078225241c6032604000743c6078044003004900410b5441a12507109007083e80003c0100214882402d03c0235855405000540e6404041d005480c100e201345600b040807800000d64482c4206001070703070101c2606d40a40b900b034441d00c8552400c04120120380d40307900680180b2070990283c987c1d210010301e060500c1d0402d5850140004c485000503c204403013109150000740d007040300010366081e95410020b041050302c4100e001c2120085041c800302441400018070700d80c02d98011344140344a07444c0f038030600303000d90345a40395000 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 759532374 1107 759531267 759531299
    0x504060614061608220b040611010c020721170c161a030a0603120804120e0a0504020a0203070c03050f07090b1806030f0714040b03070f 60
    0x10040802041d01801ca812940341343e01d82194020b4000964a8003040c200403610711840420100c0b00034018100b5501c007980c900007481301040d00b440c00c861b4908501405a40001030410080e0700004a004014000b82c11802010380325131b07101c1ca005800f42d903801d04041070109480e0f1107141c0410100401201003201e2001c00c524190b00d030091031000c441e441d003440304000009140d1b00055040040150f40c00700410b1100b0743c05100c000c10007041038a0440704a41c0440215044034030a0444100342d6000074110038206145c0404c1200940c40b00c1041829408103004480100b00e036080036400450203000a040304c20320760308105082040b140c0161580c1480c00e180c131030b07660706d0355110b900ca600300b6424450040d8941c400003038a011840d04065543c0c0c86030b5007000c510300403805031003c461801501c041c064210114200740c1c440300303c0c3c051451202101901081800c0780d010f0108 = true := by decide +kernel

theorem cover : BRFrame.Cov 759352517 759532374 := by
  have h0 := BRFrame.cov_init 759352517
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759352517 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759352517 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759352517 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759352517 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759352517 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759352517 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759352517 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759352517 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759352517 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759352517 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759352517 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759352517 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759352517 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759352517 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759352517 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759352517 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759352517 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759352517 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759352517 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759352517 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759352517 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759352517 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759352517 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759352517 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759352517 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759352517 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759352517 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759352517 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759352517 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759352517 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759352517 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759352517 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759352517 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759352517 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759352517 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759352517 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759352517 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759352517 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759352517 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759352517 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759352517 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759352517 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759352517 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759352517 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759352517 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759352517 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759352517 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759352517 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759352517 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759352517 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759352517 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759352517 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759352517 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759352517 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759352517 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759352517 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759352517 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759352517 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759352517 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759352517 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759352517 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759352517 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759352517 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759352517 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759352517 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759352517 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759352517 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759352517 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759352517 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759352517 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759352517 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759352517 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759352517 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759352517 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759352517 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759352517 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759352517 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759352517 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759352517 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759352517 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759352517 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759352517 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759352517 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759352517 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759352517 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759352517 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759352517 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759352517 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759352517 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759352517 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759352517 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759352517 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759352517 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759352517 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759352517 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759352517 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759352517 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759352517 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759352517 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759352517 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759352517 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759352517 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759352517 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759352517 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759352517 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759352517 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759352517 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759352517 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759352517 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759352517 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759352517 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759352517 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759352517 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759352517 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759352517 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759352517 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759352517 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759352517 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759352517 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759352517 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759352517 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759352517 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759352517 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759352517 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759352517 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759352517 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759352517 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759352517 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759352517 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759352517 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759352517 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759352517 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759352517 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759352517 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759352517 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759352517 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759352517 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759352517 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759352517 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759352517 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759352517 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759352517 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759352517 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759352517 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 759352517 ≤ n) (h2 : n < 759532374) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
