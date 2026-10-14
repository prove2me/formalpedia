-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2642
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:19:08.153572+00:00
-- url     : https://prove2.me/submissions/3517be14-771a-40cc-988c-12afa6111110

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 475000000 ≤ n < 475179856 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 475001250 1250 475000000 475000003
    0x6051c020409051005160e0a08030f030907030f1101031d210409091101110601050a050607140a061a0931050a05030a0806060a09060f05280e01020303040302 69
    0x12a100203105541d5240a0703020000c06100840c1c1d5020754100804c081d01d0028844001940c1c03801012001550030010a40246442900c2d442030701c0425004505050b0516011400c0394406450300030280f24041000001859049140d540c0c00d1180002c445451400d10026007a1402e01134071201d07036080040708180d01c0c0e42c001690100b03002d140b04669841040018448590f2050350401c6402c0c0341491000360030b010350204a02c081e20401c0ea90340704056000c400094880c3c9007130242c2d42e4481d070410000c101e980b4050b030241803080d00a411401030040500ca0941c9003000c0004101c0e02c035500c604800701c0c0510031141086460505603030b901010301d42804180b0b2090700c80034090f50015400d01943c00401480300011416551010440d1440001424500e42c2c94005803400d00000b42410002150740c2001d406564020400341c070746520640c201442030f542c1400e0b0750a85030804ca02801501e2282b0800b004403915420258180d0107000d1150100400307042c0700c54009419540204148400030b0360 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 475002500 1250 475001250 475001299
    0x30403050415031a06090f1224040b19060b0a03090c050103020c0c060c0a020303030c18040b01050714010e030409090b151e01140307080702070e07050711030a050d050304060605 78
    0x342101c28980d103510a00001f0804482150429000341d03070b01040c0f45c140c41000230640c03000090071002d2590850311070303440110010300f103c0082c010700c03101c001f040e10b1481d00625020441a501808207060b80c5421801c0059040410010006610340503800d051200c4c000858001c1c000a10f8203615040540c00940c0c0d8a4111304e030801c0c0148800240113001c00c01c280031840c000c540c0203094940d20b040c10018070076150080d490f4015003204090301c0901c0d515003840360b0810410107854141c00e020140c5c65207140f080a444c0703584070554981c0400c10460400f0b00040c8050300c20703d10000f0fa80d07946400c01825800b8014540c0061601440e035001d10396555003800a400340600e1720507442e504c1a940120340400008883d008850300220a10a80c05c0d000103406e407042404e60b0032541e1643d070b10582d49981e01d10a03544500442d900304941008512030b0b01c801d0300c0703a5101130203c0e004a12030b07030b440c68682855582d186001920100c02c4c002000794500034080108800c451a040741c1d501c030718100c9140300 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 475003750 1250 475002500 475002551
    0x10c0509060c010b03011b14070309060806010c0c060c03020f0309010e190f03080301030203101a012d020106060809060402011709010b12071404090c170703050303040305041503 78
    0x7004242030b88125401d42000e512420058003c1c0712032040c034544c851444501c2c01c080070124082144030210850060142c51042d0b03059070b00c90381100d103401c4080d00d480300e01034007281c1000300a00c000700c08140003a03008002400e0941d41e0300600180342c00c00a0800303841500c3c18031260420802088607071780c880548210300404a40a82c0c2c94484800391560040c8940d12142200040c0030001040c02000000755040320b0080e025148958800d440340410bea43c4030700d5107001050f00d000c0204480d48500c12000b80d00c0808180d011501260002c8172094110f8280e16900503034681c5e109002e41c1d54040e44480d00302d0390801c014074581c03c0542c0068001d0785500042d9407911511000182c40d103e094004001010b80a0b02c50b009000c3d120b400182c9031001070040300102c140d250070101c2607090901c603078064540c01000e494606824481c40802e52050143c0c2500544990310011010501c244021405540f09885159580307142c055030a000400d0025100e0070b040c90580c18190300140900010300c1030 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 475005000 1250 475003750 475003759
    0x301030506150d050f06040210050310230a08010b041d0d0305040c0b0a0906030c051c050c0903250f1203030e1204032f1507021c05150108010c0509 65
    0x1d6504002241c0001e20101c000781c06845809029117982a0204151740120700039030748000225640303541916548070603200301340301d1007000404102c441501030304141c0c0b10184581103e00070305c1030300c0024980c510a4000620b01c1e50768a60b10304491070507106025450320116412155111100e140c1629410004081d80a240e100c000160820942c100920003034542d1a00b013030788451480d000200b030360315140a0200820b25182426080a00420954811124003002c0300c2040406035030000103068042d01d00c00765810240705a203907035601400003a100502041121040c4865603c54843d05a101d85c007601c0d026081e040c0a000e00280007000350340d10b58160401003000080c01440c1860100c027044800ba8110009c1004410001c003200c00b40400c40c3c2d05110b606d0703203800d00d824a8251170b1212a44590203440c240101148440110107804110700060915580d40b0103440c03407040d440140c40080fa1141c002e001c940c030302c40848402281c00362114038020044483c030004054518480c000da1280308 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 475006250 1250 475005000 475005031
    0x60a0819060212011401020f010e0d0c0204060306020f0721120c0c120c03020c0a261203130b0f04021018031529090a0b0112150810020301030506 64
    0xa11165804403410b601c20401001ca1940c1c0d07400b46202c1070510f0100290050088c86030f000d100d100140036499100d148003014250180c0c114106a4801100f50000c13600701d615a5000001714005201604624000c0320f9416520035031898561000c4050b10004814a003000d8031103143c0320f03400b12441502c3c00c200c0c0000030b8502d44204090f5038440f60441c005010480d2502c0e07002c4d01d250301080c0005003e20980845954186078410008489030501414031100c1900b0403544203034060340a004d1011075440d054400658052101500f107a000701c0342d80443c1032041c00c02c0d500b04085130b6a0140e10141c4003001c01800c0c02d040d40000c080480e50000b40f8100844c45070483d551112800c6140015a0300090b4401848000c100f040040d001148603a9442c04c1c1c01d209006013256540a4007400c458014201d0f1015079030104048014203035a110340381000352030b40c2e8040350b070400e610501044c460a030340b455011a1905820320f14290150032104442d80c014001000082c1c0c000030315542160440d0f004034003 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 475007500 1250 475006250 475006253
    0x30a020c061b1e01181502131503090308091603080310180606021606020d12021b0616090f090e0a0515060901050d050c1e0a09060e060a0819 62
    0x2c84198081d450081c602988199a0700d00035406070b604420030208009004004c031240c094040403400000c0a821403d43c01d41c1014800b040340e00801c1c010701d25660006101d9114806100d94101c0c0041580100ea03441d1072807001d240d044140346900441000050900c009460703541c80c000c0241d80b200403c070800c0400401c0105a1541091018080d05010176011107e800400d03c05030510340b180394003500500000b0301c203807041151600140c0b4003d0f00100707014101d1800c111009903201035081010366080c801041d521040380040380660f4900d1004110034200f00401c8210510f010705840180541800c040041c113601030796030400c80e940128001010b80c600d01d0003c0c2444181c60b801072150091080305070002042d24607040c09184180d50381c1101e81c4c4c0752418481d0781e500b2010060403a901c418032080451078920001c0014080e501201d52001c0600d10110380030381055005502c640b61502002d101d5129428007180d4817a0003118504207880c07904062a4999584001c602003180444030102c0 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 475008750 1250 475007500 475007527
    0x30f02030c0d1508030a0504170129220e060a05060d1e06020c0a0c0806430e13091a07091a0304051606140a20010209030d02030a020c06 60
    0x2c004c204080580303503114191940100b0700e51142c0075070b0510031040b400700c00c0d11800c14410049030306484504200150b804a51070640410401e243c00d5024003405181c014840e01498150700c070501c07144c80800c0c0500149460b80c10490b00800080c0103a2401d0100119075440140c0c0b510301c160046840090006101c2d0303940000340f40709902410340360000400052094001039034400040c018a002000142c98041c02521600c042c0d60f107410142804445030f811003610400a1034002e04801d003080ca1340e245607600b0411220400d40c0801043c54101245806d003080400c0d100c001c07101d500104518420707a0341b11100c14080d981041da03030086150004001c07501988514020300701c2030f0300110004992030100d030010f41c001c8a0171156800740002c0741440801c100e0820b03003a2050364485130b01c4641c42034a110000c0e04807504d00c0080180881404a20f0410600c8a03503440424200243ea203905840c1454a8542081840000c640c0200802445207a000c260a020f030007040324182c0c0d40e1540b160104 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 475010000 1250 475008750 475008791
    0x151602031213020a0f0321020a05010f0c030c02030304120f120905101802130c031d010e1e101e0203091f020903190302010e1b01030f02030c0d 63
    0x900d541d00190140a150b02c5904000303100c40d88200c401003045a21244007800142d803030311008024400000100c01b07048080d000802c4c0380e846a204903150071405032503140c25a45c00c503409140441c3c4d01c2a481080d50340c1030144408249880c0000c40c59400d26646140084001e1041c0504001e0101c000303003c0c1d03d12601011a00000036403041c0102c40c0700307040c4962035201710941036500f5440c02e00c1e0403c00c006411110109150014003040006110540070006480024825001c05650700d80c00d0340108020b445800c1b40c8070004000042c03091002030301c18584001003087da52000c0380c40d84403550b10200060140607101c49403101250301c54030f40740340e20400941c0c01d900000c0b480c004020041c6101000801c00604030248802114007515032207194202c0c880e016005400d500074018126103030450056018900d8864400026516401d600d0503003441111480425111002c0080c81c3c0a5a4140520548650031110451035400c011400400620480192189440d110b00006282800f0715010 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 475011250 1250 475010000 475010017
    0x18010905030d031a010e030d0804110406080a330c0210110910030e101a090103030801081203060d0f020409140a020a0906050906061309060308030f0915160203 70
    0x2190b0115801040c0078014080c542003c2c02454504800481e4a6201d4480c003200c10a015001d450501c10204040b81c651100034810744202100161611a6403620b11800d0021701d041c0e80603155000341c42c030f041d00781c2e4a40042040303c0c903440b550001c500e4011804d550b070134801810200107007580300340f80c0c2a404d2424124400c0341c56071800c0801105003c5c90700080c20b414004035864008a6108c1c4000c0d802c9840032111503541e603200071f41166845078640d101405142040088000ea50304400020700900426002103001548460041103042030030000769078031a1014100038218680350303011a0075011500000303825142201f80c07500c29505c40c2e500080d004d90300110142d02c580ca4001d44e0903610403422008030b020b9090032600040780c80186c400d250a036100103221016070380b14881006040d4011114690b22644060000500e01c2010702c1050004c603c9012184d440b807409020150680c0c0c80104000b2450300300e0360080105000c00500c1c00d91080d0310042c400b04182c1800c2c1e00300c0c030f1409031624 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 475012500 1250 475011250 475011253
    0x30a1808070308092d0c0402040b04360914101d030309070e040206040f060c0330050702010612050f121201140409150b0a0501090b1801090503 63
    0x28a005101103a4018200e4a01907100d85516450303000d589a039403035288211140900354184c010314400507001240c10000e000c40100c2c1d072060250f4000804a90180e80b01030306940000808202c0004840341d0a094000e4056120780404800414040c41489900c1c50b88061640d80d107002003040b007001c2e0600c0c111484d20080b5000ca028800d25200103044100c5411001241955400141040007044034441e625201c00381009514002c134020354264054803c03a03204e0414880468500300c19440e84000b01030f50b0303170303041d0201b007050030040c1c4900310a541c20703c42010681c0c2c0c0842c0010302a000c031041c51052042c005280e544441d82240140314582207000c1c0302d1202a4001c081c000e000039a050301502000035240002114070906195201d02c1910305035030f00f00c5000420160344030610100c5680700c05040810081050750b5091496554143c4025009985003000400e5041c01910800039040a0824421007401e00082c0300480c0101d6403110051070b005180c043d0385910941801005041c040e0 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 475013750 1250 475012500 475012541
    0x40b0a030b270f0a0209040203030408060f15010f0804020d080d020a090503010c080609041e1502031b03060114130b070803070e04060303090b0c1e10050c0702090606030a 75
    0x101c045460a0b6201c5850744a0244032882291000c0003203030003503000c6101c1c80140402c020035401c0c060501030040c8203a9240c00280000640c04506200240c45501c0c0c29208500c24a005502200002c0499410b281000984541c5104490b0003100042c1c1098040320503403a19029490b000b50144641c00f440b10100340007103a01d81c14075400c0070034407082c0c820850003401030801810088590700d40c101c940680c000600c0300414082904102c00581503903a11600e51000d089039142c15a480780c4000c030285409500104002c0c01c605020a20740b00754945100700341c554105280000c03c8074100e07200d58803a0a000183d07400043c07010301040402481c0e40303500c00f80c440c9280d080c8100c894004503a1003000c179034850030b140b440c3d10b094403d14047c1c0b0342c10b40700c1d00e040ba4106251605190400412410188180c18001c41c0b101c10307880b0030080c50311400c0010089040c1c0c0d900c070ba5064030409032120136144c0c0c0a12501006a503014406980035406490442d120703a1485050b002070100507003e83c03170100980 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 475015000 1250 475013750 475013761
    0x1b0e1311150a0504140f100c03261f0303020706121d0c180f0f2a030105040c03050c1e07060606050d1428060e090a051207080702040b0a030b 62
    0x24044c01c201c84002810b07103491180403003400b0085a0b04119558009040c050100c6000e0007070340884c140501074500412070b2040d072100b49010740056a0050103c140c500d0820028807240f00c200d021a40d1928510341c00c040c80d51b40d0107940e404090140f40f05000722110712490760012039000c0e0980c0001044c02031001043d5210b83c4e9202c47c4200b101c030f409442400c0b520b61300318958034402400303484401000c0f6401d0351400466060402c002d003c1e8580598949030348600b101c0c5000ca0500d00d24940f1030031540d40d5244c082000216a01c3c000740f06e09042c100b808105e01130706000d003541d0036441e00000000301e09e44011007020051160480050289140041c0461042d43c05009080071400307510b4100070f0268000140700b04000112081d40c3c2c1c8440164000c3c1000e43c0322001c0798911181c0507008601240c68100c0341d8601d03d0211209005540701d03404240c18081d0401030f1401e9a818140d065142007003a84030880184112a0081d00498032410002c01070748450030020300841c1c20242d520801e0420 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 475016250 1250 475015000 475015007
    0xb131d0102040e2a070206070602040b070b180a0507050d02060f0a020102040807090203010b0d3b060a0905070b0703020c090a0b03070f061b020409020306041b0e1311150a 75
    0x10346400720214100c0c24131808045100242e03801074601c0c80106400d050843d401c0050b5030344441021030342c5d99001c0c0800206440010040d0000030700c11426101203146c54030010315040c030740c000340500c0c590015807d280440c00100701101501c034142da444208511034004608244907012015481000000303280900380d5040d40600b043e1030701030042c0c52000340d441c490103080e0b00003030040c064940d008201c5400c0d070080d00d600034000907080d4138410040380c2d694030704052041d1403141c071804003094041095400c184180070b0280d00a0341c040b004c000e81440c5480343c5549003428007a0315115070b400a403c509040c02007280301710001004005524501c1c0c040300d14406424401c0d03449009101e0840c01084954000e0790100950b5943d9807001d44807202190030921120260006a070011390b1400d410000d0388081c060756124500540900a890301c0c41c504544001c0c140790300207004219241c05004546840c48180c6c02c04c103400a000070349070741c115000a0048120415020450f00c00006e201010540 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 475017500 1250 475016250 475016279
    0xf0901060207080706090b0a0e01020f01062d1d091504080405030d0905060a0c0206160b090708010c020307020d02041e1d0a020d020405100306060e010311040b131d010204 75
    0x5100050b84e003103070313900c1d1000d840720700544c01030140c402d00a000405180d03104100d10034120f0f00500c1100c142491000c1c0d02030840340281c0107119a5201d8151800c510903100c00840c196070180310311481403926041300f4050382443c6109078240c05a00c8808611120010002502c501c03003040651790440c2044c2c0382040141c0c2c05486464001d02035111140310480c080c0c007140c0115040503100741d10380414803d04680c0650200c07030890b4441001e224040d00c05080350301703070b0030594031642c1b810365242056001c0d04e00d4840d082d40a46542d07818015444040c56000c0240c501d82c03a4141c4d240e41603039410744000381c0074040304a40903075200003107a042c0043c486260040c410340c1d28940e0000251703401c2138110907110704000f1030281d0402245c1e01224010b0402e5032040b076000c020300180c100502c0e100d0b500c00b0b0945800c3da0000000035001030050051110310740620b080e1403812101000070110110110301680494200c5c10265030391103e102e00500d02c0d0114509001c0090b8000319680c54076407001241d10300c1c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 475018750 1250 475017500 475017509
    0x1202010903030c020307020108011802040e0109020d181101050711131a031b130b12010207061b0828090503030a05010f06140c0a150c1706060703030b0f0901060207 72
    0x20305110f06501c1041c0007204641c40f15406a4400e400b50b2b00f420145084a5401d4101d29038540d0b0800000070380c00d034440c078081e020f0b001c2d0640241c0d0750519181c000d01543c0780c4591091881804902d00380000d102405290f42502081c240140ca5025604103005070219861200b1b0700700d4500c100f0301e81001e00d43c1d480078a00880c03101c0c2c5001100740d168240340d503440030a072102c01201d051500d1400305203000044031240c03042c0f849021881c481100b01213440d100c07143c8001c11b0315a40102c0c64a0070031440340220a140d0b0396100c1c5441c0e100c407128800902d180809828a01100b0f034904000201a202d03440c0f220003450700a5060003003210525000b80d480c0c5c011100b191400c0d00c0c2c9000450740c980c40320161411590140e80350f40c4515800c118482031980228100219481040101c00000d0000000c003201a400c1c0310000800c007290040281081144100404a9540d041c041140c03039921001582c0e1215014070f40000d1612012001c10480d41c412031525522010403400060b0f89540042d080c3d017681c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 475020000 1250 475018750 475018757
    0x403050105061f02030409150801060312022b0c151e1802031e0a0c0909060b0306010510110c06030a06170307120c0f0c06120605010207051305060d1202010903 70
    0x543c480200307030441a281802d4480142c1081004003c0c850389a080800ca841040311010401503596444c01d08544041d401113652180d5403410707072815070301401046050b2601c41d60085881c4810780c0a500d905640300c0108041c0103172205500140a019650903090100d241c4080084c2c0c800407800c0b84170040c03080f4852054a0400034940810390483c400d1031012580038005203070704003ca00316010030100000041c100340c4a404924400b00e60030041c400e0007046d034500e0025820400d414240c0680300c4401c9aa8041d40c0404010442074440e002a8101a180c0740341200004003d00501400c0800e484425030307100d6008820b110035003500782d0080044408402991049254803510607480e0f000302900500b00c0c0c01c16800070041c490044101c40309051180a101c200645103580d09681c00c2c415410840c00600c0300344c2c01c10f0700e0408501c9100040c0200b40001c6c90140d24080000b0b1080001d20170000c00c168035040442c1550302c40e00b28070800564009030001c01a941500000c1c024803443c4000d4000 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 475021250 1250 475020000 475020019
    0x106080421020c030c03190825030806090106030b03070e092d070609060c0809060d020a0206010503010c0c0b011701060b0409020a0201050f090303240409050109020f03120d0b15040305010506 84
    0x1744c030300017a0049401481507a41d5451400548400400f50003041d0810102c0641780069586104480411410503109466407595405e1100503c2480c4030160021014103140000c404210b035000240c610446e5111207030340d00142d403030a03000c90074400004c1c074031516038583c41c6503013080072412686043c100c1080012102d05550311842140c846600e8440e0b04085035101200b100402c0b8100010515a10003402503842d000100c803094040341d010000d0000180c00c02c0c001408a46002e00400032150514a00050005160346501d600840e041c462000c00c0d40000450440f00c003020340100006240c070140080e2607903038806110010b0341c07260701441c005503c0e202c0011125804038034010702a07100c280c021030035583c4911031001c0098030241c0c414562200c0d20200b800958650161400841c4141d0002c128240d45206010705064a504403d201c0d400810800b1140c591680665600d080c0840d000b09802c000407010955010ba60030540f0440c40000030080140072054210b02d001e0744060792820721 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 475022500 1250 475021250 475021273
    0x90d03050d050a2007030e090f06040c0f020c040203041106070c03150203010b070f0219080102071703042d060903170a0902060d1d0a0309061e02060106080421020c03 73
    0x4075183c40c81c0306800c3c010701250f001c0c52440540017600b0080e02c2401c0c044000560a800224a4001165003041002c003031030400009041a00440d8040040c604040410140e00c0e0406502c0780010240c00d8003441c2d02000140504c0001682e4146c00e50019050715035440d500d003400545170b06c860001340c070464843c9140e082c203c59a4421a030480e43c1c1c10741d965027410025690003966607516441680d00c2041e9111019000d90000180da00800302c0b80300040c0e0720748244c41c10141c2041c0d5076800321641d50062003000040303070784c1901f03c0940407030460400f0001040d402810360b1030707070010303602400311490141523000701900074481901191a886003515195101c104d00313015a4145c090094201e8010700800160540d1a04440703410300e0500c200d05540302103d60910714008088805600040184404000068014242d002d518424600b408150011044040c0d59803d040c4101c10800c0400300001c0c5c140032014034a10f505c0d268603464034025040360304000b075171441500d030350f14803038090442900d0 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 475023750 1250 475022500 475022521
    0xb0316081009020a03200414010c02060f0309030403050a050c0405091f0c0e0303070c060e060316050d0209210706020a050705090702120310090b0402030105130908090d03050d05 78
    0x2031050140c0080c0c48141400c2c44102d10194008400c00d1042c503459444a0403102502261104c2100d05080444e44581c50301044a000141c080103050502289604e6880507890b14401c907044c084000101d2540c948401011515500c1140d2000e0824003400c1c0c1940100100402c4009120f507003104c090040d9204d003c0b04549801400754000100741016503e03010000c403681007010100d0807424205407022a010110f8210360140e04100e031481010710040c8046500a0b002c0480302405607826820f40c5464607100c07036294190b854410621801140503800b008041c3c04451132200041e142c6851842c07044190a0b00d2500c14030a000540108003000c00c5180c4001402403e075500300000b050140d29000030720511040241c020310460046018811042c80d00d540110f018043d40b8041c0c4001d5440c14001c1030444160394000382c4110300400040207255607070041103000241e1840000381d81c00321441d20114600c1034800c400e400100c404901024103030071101030450318940d0131061006039038400310b14 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 475025000 1250 475023750 475023767
    0x31101031a0415080703032006010308040b16060e01020c0708011a0f0a03060c050a08011a03160c0c1202090c04080d0507060212160219200a0504060b0316 68
    0x9481030100c0d55120080c1c2c1c5440d030051581e001c41e040b200b5829a881c0c980b550308000a5820a50110311a50814079000d40f009261507211100c01c07000d840654155030b02c04420b403286204d180d504e0080410f060390075274904800c0d0a40d06e03a0200c4100703d401c8180e06064041d401c0407e00618500490400040b0f001040c0101642d4040e000581440714030b50f0030800c44001c51000035107030407000c2c0700d1000c030010700144214410a45a0340341c094680048000050080405800c150000d40031503540305449a51141581d800040ca00740c450480c6140b90b4080ba565081d00750301802c0440c007100300059144524286a135058001d4030404500ea44400540215200303500c01c0c414681c4c1314401c01c00c14a4440c1020303080840c40303090058607001c01c1c04807100b9246030031f0380d19001c005c010386030150030f00da0108083c00d814000013250802d5400c46d9140d0032046030102c08400182d10782525408a42d503502c01c1d0400c080c00c40144108460307526103000d40e01c0350308100c9082010110103503107110074a0091000 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 475026250 1250 475025000 475025021
    0x50c24100506030604020d110304030509030d02070b040308030a0e071403010606030b0d020105030c0c060127091110030e011401062006150f0907020d02100b011b020d050d0903110103 80
    0x41c18955204c65041c4802940700c031360035405c06503859200c0000a0440d90085009034003d50f10151a20020003c04d414582e00b901c06105650002e041008001100e00c155401c0304d0300448882d03100d0f82e031a40c952014154a21102400e405500c00114041d0f07104015407410f95070a500800042d51145000c4c0c044412413010b641e404010052031400540c0724000131903101c003500c1c000a00b006808482d1520f428800c2e008109100724070440f0041c0500c441c440142c0c1d40c2d003805070a012040c429107900c0c1132313010058541c1d40190b00c07980c4070042841c0a40c111216a0565030020082c815010714500c0500700203004410020f044078004204012081d0b9000d0200078031080a40f455407185151412041801d000340381e08902c042041d02442d80e905000c1e02d114512940250000110100e00242083c254440000701641b4050701c400716030764050080600b40141ca12020f80c0440c00340000b40072100361080c028007620901e44e02000d929407020140c02120712401c1c07406031034603a550054059800c514413 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 475027500 1250 475026250 475026259
    0x30a0c08061803090f0a030b13050c10053106080105031006050112020d0902060c03070210020102040828050613030e040c0e0105070f0206030a0c110a08070f03050c241005 75
    0x244040c80d0a5190000d030304030040a000086d50f40b42d5442c404050100c5515115101000306281070020074440c0c9002502d0803107160000f42c45800014082e806008079440000b411414014042d955048252075010b601c007040c440d10a07551000201070340024003a840c0a8010140c0000000c0054000e51007610016100c08030203042542640300290021140c0032b00301502d4519000c09612103c0040501c800d2940c0a10b03610001e50041c8641b510080004504683c41048104101100482c6040d503041060b0b0b03000c14003011b901002285c0c1e02d00c014001d0303d18000c11041c4169207118036484d13a4054800d8640c202460803c0c0c040208492030380d00304101080d89200d408040390f20aa0082c80c156206500004216180ea0041003e54104680c0000c06698034850201c005400800358010100c80740700078601c0080a56030348e603d50080c91001044049640020002c143c00380d0141d0b60844215000c80e03a08205c4000401ca4241da914511070454003940e002c0f41d081084651b024040c0d03123010f803 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 475028750 1250 475027500 475027507
    0x3060c030417071209060219052d1608120403170f16080414040e0d0f050c120304030f030c02060c2203080c011422060605030a0c08061803 61
    0x2103401c1c854a01080a01e00d10306010070040d40040c16140c44e5104001150b941c000c034803824110080d241c01111a204042d8000c80b103908000140d0015201803111011030083c0c45141004220680703070120031b40ca401190295001302d030030700c0440d60340f82000c8801080842d890301c0440d201c0900644601d020140c0600d0445a840c0101d502c1c120007008010440501c030743c40c0201519000344e0405242408035080e010000e01000020780710101400010800c440c104100100000010760300e02c500c41c0e0700c40c244240c1c6201c20540303134040c00070b507441850351009503058030302802e40c4906140d00840341103010400c10a80010700c3da1081c410390300c603040c040c1c004040f2038884181500ea00e400960455185146440c030128100b5400410b26004620810003d515126002c1e4420f00b511080030915902507a900204a00340c07464001c0b44c504003e0340042501e26100d182041c0018025603044141c2510844e8090010402c0e81c02e105e01c03c0b41c0603030082c0c0704c2d00d07114501d00580d05446038001481c01c2e030062 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 475030000 1250 475028750 475028753
    0x721032901080402121f0509010b0a03120c050307050d02010f0c0804030e0406150206011a070209042402070809030c0108010f0927050304080d09050a12061d0708070503060c0304 78
    0x1070500c2030304213000501e18822000c0b141d02c024038051040d4210110130700040040641d000a03030181d1600500c140009211034202140070544664680c400605001c4c0d402c5460080c141c01782c1c241c1884641c1241c20f40c2d80c0c07003c05041495590620304031940041d0701e004020820803559120380074820b00155100c2c01e080c0c9540e20100c4028011141d0706610030340e00d980010f5004c2154100c2c407011211030b0090241513250110400c04400c00b4550380341c89210412040c80180e079030540d025482580024101540b012001c000d0b003e8005000c41180907503c00141c400901119401a04c07040108808031480b05044000440f5017002c02c1c803030600c41030340d0345ca001c0c00810a2504400441605690300011289103034506142c00624442e0075501604005001e10520708180081040940d641c01d01102c0d091074803020503040380341880b54502c143c00750b070307180c1c01000f8058101651b410b02e070300030011491003034810a68030380301c2754460903000b44a90740e00001d0030b040204881d03104000c1c1f40f08650656689 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 475031250 1250 475030000 475030007
    0x30118020901120608010c080108010c09050127182313060b101e0305060105030c070618080c010f05040b0402010c0f140d09080a0210050c030721032901 67
    0x1e1114140859482e40d1007910b07000788035490042c040030001242d01d10800300050b01000041e003020340c41ea41480c04e40070765243c00c40303951022202c5c28070b80010515121403080e1845810051000c44040c1900e03c0040c40c1e9200040741d114648034910200106250611204280142580c048240c91a0840010104910203290b0740e002400303000c01082c3d040341400002c04000401c0300550110307081030440d1038801080ac071451414002820100824240240003074050f000c0200301098080000a9030070400c20345400c4901400342d210700c054800c00031440c1000c0c15412001100030b1561034031400050051071402224011500324600304510785460b0011241a1207654055400e80075112940000030210314400c0045000070025240c04024110006c0c00541076a1100030107074044806440903940d0003084404114090822036600c0000d403200e43c0c11030103000c1d1b02810300710030079000b404c641c108062000f0b10004943e034100410740e402000300d02d0207202c15560071180d80c0c01d28a500d445500 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 475032500 1250 475031250 475031257
    0xb03030c0709050a0b04021201090e070303090e13082b1806150510020a0b06120d03050426070605010b0a120c02031c141b0f0d0204080d0512060603011802 68
    0x542d00403481c20b0b1005c0118050743d21851401c00c64100020041250001d035219040708021200e018020070351075614000c101c8441d03401200480c00b030310400308001030480c050024001e5070220605454400345111002624425003544c0260040b0754640000c051f52481201b4044881d00c007000b07004100d584480000f40076962020800002152000c2010303a07424201c102c02c10155401024886050f25001080c040702030103584c0103601e025100061500003003148540301026240c0080c02d6512800d1004502c801c8001c4480104600c10705103124101d140010148940186802e00c466665013100381000d110b10948100010a505015201143c807900303c07407a900b03907600c112801c01d60840c2c2c0301040b541c03100d80441c001d035a0310a04021240f800211542d0721880162900b1001e40f5402d0b4607249900c01c3d00d40c03083d090f110007e012585940154140c501810071941110402c496029001c0c1c4030b035000d803051400002e0f0250004000d071030f02c40112816924441d80c91038900c002880b84402940 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 475033750 1250 475032500 475032511
    0x192607081b0f0306010e011d01050a030201030c170c0703032f0d0b0303281e030903020a1a01031a06010c0f0f1b1706060d0b0621060106030b03030c070905 68
    0x140300d0400002c2030380c08111540c084c00a2054900c80f41d494408114201031603180740c6e0000071a200300421981e680c40b02041e007101c5d020708021450f03c4048000701c8450038042c181d11039280314a03050244018070381c0042c02c6400d2003074600300000c11040c2240704029003a120a21074030010b11452001101c01c07040949440303010380c03c0c04a030300456000041e0840c1c000e480e200e0a0b0b6180035030200c0340f50800500c0c0c07a445110318100060310001e0182d80d1018568051020b5040c144c5803c01c5c02c08052080012506072030b0450b031980c560031140401201d103050280b0043c1c80100c0180e803c500110440e0400502800050f103882c14000c0080e0750700704500c03160417020380f15540003090b10004100134212580c40520a480d002185508003c18207442405034150105580d112908001d070b151204041c4144042d004072107600b5541e40c0e80d000070b04400310100c41502107900203441440324400052064141ca00c0341e00d050009030121030a01d075481c020352100310f4186d44040740400001140364402900726 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 475035000 1250 475033750 475033759
    0x303050c0f0d0c0c0b0304020904060b1521010806070806012a0303090308070203090f09041410090c051005120a02130602030706060501090b0315192607081b 69
    0x300c101c00c0354141031505410300d240116030541644020002c07610b54003809000340c8040c80d070450a02d07030041402d41c40010300041010380e031381d480440655602c88245018010f030480c0c841d40c4000100103071064194511007042d0005694002040104001c19001d11560700e682e42c02d410741d62000c00440b41d4142c12801800c10440c0c4d103902004412201d084201e65a020b91400300b10442940380092580000a0141c2c0440d0020b100d800d03a80c0c1c1e550741204802000854100405441e107090603600c4540040381e10f0389500c1403d101c50640c14040e00091546405402d03602440e80d41c40382070140c5100070307800002c00603604100307045e0354582205550341c1203000e1280060030b0241e080001c2000c1c0521350000e1000d80d001042d00340400815000e0b031000360000f8070300051610319083c40c4960900014081002e020542080250700b92914422117014084132035044412954841c4032507400a2150743c0c03204113150700c821600402c2d40000e03422040301d0305400213085040300c1c141d580c0d02c4e589100d020258007 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 475036250 1250 475035000 475035013
    0x60a1e0504050d030e0127050402210f0f0105031209060a0c230610060f05181e010816020d030e1009080a08100e04020105030a02070b01030b01150305100303050c 71
    0x15844800303c80c00310a11136103d003400b1a013501c1c005002052090126032031400004045511800602d0002c41100e4094801586030700001142000d450a586158000f0b0101c0340108071042046a241c18011641c0410600081c4d880d1410b1648070010201070648082d000c000c040201c0c20720100801081081d840d2956660f1015a9051b8405240c10000802e1082c0c44c0501d00d0212414800581c0042420480c0c001081c640000a000d102c2c403039070389506114020031a60701c1e0440c0d0202e160007180d402031100c28905074202c80005a0304483c1541d0b8001000e0400180d52000400c02e00e16400c003085c0c00900c601c1030107a404030064101d4410810701c40c000c510360360340c2c00d1040b030144002070740c401e1441d10348400038100001d240183c014031001c0c08000c4010200011001e000c10303103400c1502860240d44c2c036074a1010001c0613102e04c0800501914070030000006000700c4982d442c0c10380b54401414940030112100460070344006580c4001c003002d20000401c0040c1c00b5030018000e1613401d070290703a00c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 475037500 1250 475036250 475036259
    0x30501150804150905010c0e0901050d0204020a02120309100608150a0b030c0d0605070324140604080d0e090117070e04060b10081501031b0c020301061203030209040b060a1e0504 78
    0x1c0e900920b004171601d0b0b4450003000403807034100a451103074007402d4a29560035854440090600e41030f10310007034003a990016040a845100740600040017109105841d078a0610000f02543d500301c081d41d1042461502c903020500000128a01242442042d003600183d252440341d81d005000740c8103050750500c54642003002c01e4076116540c881c5d40d8040c0000080ba890a924081c0903030f80e98503249aa220700401c4035140482012403c001680c25250481c61071000300307000302d803c40c450780c1c02c6064548910300c00c4040072544100ca58030b21450564403410240d0b6540e180b492061540705165041c3e8001c554184100c020300030220b688a0300480b0b01007000442500414004484282080005802c1c5010001c0800d0041aa609141c0302886e0030014a102e809442d00c40090304082e0500704221051004159175007500998041c002d039080b581d05001c0c0b540307005402075202103180c41c0264100038035160507262040a0341d5503540c180e2100800540c0620565208122200589081c082d05010104 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 475038750 1250 475037500 475037543
    0x213030305030103111c030302071b180b12070605090a05090c0c062d1003083f0112081c05040203011b020c1201020c0115030210030501150804 63
    0x640c020789440740e0300c2d411818a040400d240301c1c001e50081001c17003090417407180e800c003060391060380500c0c0041c2c49564600c5c00318055508a61700180c000040c500c0458000017103901d076031800308599410088010020140020501c80c02048109500a02c20410000c1e0107180104600d03c002040380c1c441c6600c0d0000107c0094054900c00505d800100e4802605c050405c686c40d00100c0c1180c107041d04d1783e5015400c1781003424100c00442c0716824031000c035074032484503500c18001d198000c043c0c58880741004221070480b245150300c0b40d140e10880100c1d42002114040801d00b01140c00314810389a801c10030032108810010500329409401004800300c101002c04000704d02501c00d5002049030b051a0041500f9100900c08a030b03248207401c0d14606a0300c0e00010380304981201030380c41e1542030b015110f040303009000342c010031591340d400c22103140055800341180800380c0c1e1080310345401e9011002c4080f0102c440034050000b6400b02c4d0b8543c2e441d19030082411950142c030821700503c0d550024940c80 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 475040000 1250 475038750 475038787
    0xf28030c020c090f1603021309020a1103033303060c0d0c0801050904110111010e0a060609140f061903050f0d0206010e060103020702130c0305190c090302120a44180402 74
    0x6414554040bc2c01c402d21940280403100c01c0f242c800041d410b50034051811028800c0b0540082d000c0840e00c14070590807500c00b01c4410303c0000c001e00351803403850310b03198454055008a048010903454201d1a403106070048988034141d9501600c0e45c201c0d40d4455a50013629503c454181703050003642e40e01d42603649001d004400b0a202d0b80c201400080c401881c010041d0f444075045250414101084c8044100140e403125030f201d6000d0100b05216181c100203d20070405039554066030022185011041c824005810036502c01e6070b40c2241c50f0400b1400d401c80e00d425007802500514442c00b000b051880d80719401600a090005120450b83c080741040343c82282c070640c4804000c60f841c0e0341081400c0d440e1034450310580b01a190140112040010000e002d00300798040240b161100340c145d0510b51004026800e0f880b0703809100484000805a44070604500c03d1701031625400807030320000c04241d41000003240300980003403205c0c186425103000980680380900b0080e0455400d1000185035000540603 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 475041250 1250 475040000 475040009
    0x62c0603130302210a0e040f090c180902061803070f170606010302040609030f0609022106070507320d03020408010e030c030f28030c020c090f16030213 67
    0x109030701a01500e0040c2c10710584000720b5840c00041640103d007007a05908480c4000194540710180210040000d4000c00070102c001035980d2a0444c84010450f440203000195920106205001050552400700b51142d400000350018014000c0d884608481c45200150301002416900d065445070988141c021460740032007000c400b000341031140e5035010310140340c000c4000c5c139040d0316080c00d2000c00381ca4044140b1000b09208800c201c07040902c1229807080c80c84950051904000602803a030048154071f404005407c54010600030a615a00550441e15000e500180c020409101044c0403040360a400c44854180b440c41480c414918005002e0800c90f6000b0f914010f032a64144907a441c21600c140c6c9130701c1031980c01080071303000e1010300105980c0c0d41200e26100c2035444050030014680341004442c6200070320a800c540341c4000360190031282034042603908840140c207040b41040060a81030790b40303428030740c035541c08100d01340103c074a2110400b0f480d00f07000d0310b060550054001c005020303501 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 475042500 1250 475041250 475041271
    0x3120801060815090c0c010e0f16091a01030b031005070206101d06150412030909050c07032106170a02210303011202010c080a080103050f07062c0603 66
    0x501040350818445038000000c0a1004040f03511040440e0031407002400c5130000183c04a240c1060001c250881e1034040c10348400d0b64403014244040d5a944e880c0d4580d8280862803030840030a048000b07205d00e004036101c072018414003c143e64015401015024082a05401b0b07155025480d5015030203040d00500c0290b0060420b40b810244846000300f10760840c480d05038584e100882043c2d80d0b0300360070307801c003004882900079810343e800083c0081c42582d010610814502014030281a04100190100d40358110309024942c0ca40320004c1c45449903140040115941026041c42a54414448a500f10400400061031511503900aa5403101d40c94484004d521031001039046040c41801e48a050902044805980d100c28904035201d000500600c0482c02115050409580c4510b1302d22544036044262241e884040e602c00908603a802d000698083c822004400ba2241001517510101c418981d200d40007000c030030071050001c0002c0124402c60701c0641c4050041c5945880c01540215008038 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 475043750 1250 475042500 475042517
    0x90b0d08120a1b050d0e191401180230010f0b181012020105070c15090f140909030f0a05070b0702060c03390409180305041e0312 57
    0x51600141d4003661203c250008449142e10b90058002003620900040c201002c10300e00b0701c0c3c4a1291074803042141640d50800c05042141c180443e944004c4d54020780d52000303101c29111481005004400c40e08020b41100c06c0c1c80310b01030204881d1564a440c4543e810213034440306100940301c1d080d695210003026080c0d56503840141d8901d44114000210350001040c0c00d06854001d804429110f894031502c1c140e003070001501011a07108504680b409580070740c814888684960740c00150160001068000c51560440814429503a0f040301c422a07001310741032030f0620020020f218000340040e040c1380d4148024070020080400450140c4041c8000e42c0d50903480380d26904200b00300e0301000d044d05d01035400c0b03101031000c4d056000b0300303c81d03020000304460380e400344421441e01d40c140c0940508032511181d464858850000c000001c0c004c80d18a0310080c420000c40b90111214030504a070000d010541c200810071038400720790303240803200c80c085401801c11a034a45072103001d030950340710107030000e85c144 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 475045000 1250 475043750 475043761
    0x5010f0609200a0c17030f012108030a020723010c08010905060307060507030e10050a02010c09050d06151a040905090a170903071809050d0807020304090b0d0812 71
    0x2440b4840c000d1481500000385051850b00c02405485106403450801c10107821003070078040c030588034092607a00008007658034503104201903400d15007070092480c080c1d00203100c0e0030303009040800e4065080d049803500780303552070b03611491009501507802151048a40c28200481080c49010100010500340000c28480c804810003004600d05800042e5264544002d00c0a02e0310005640000e5400340c0c28010340e41c070700038101580c0040c1000001d0303602100e010403e0280c20b60000141038007085540007440040303c40070064a50b01d284c0c1c0540e40d00158201d80390700100704580c008969031130f1030740000c5040b60307261140c0c400c54582000c2080d2034903030006010000b40d40399100f501c1c0d110600d00090b204166044d6601c200c0c040c0013407146607c1e10000315042103aa0303414810b0350b00600d4a201504800010384820030b000c0c0c6045403007a1070500502d0180e10301240504011441f54400d036002c0d51505052450520050042c0e00d50305d90030503e000c0c000400030b03a061005040005070710920b0025850300 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 475046250 1250 475045000 475045019
    0x90807090209090610080604091110020d031104030b0f0a060f171905101a06040602060a0f06030305031303030605040501080f070b0a05090d05010902060715060605122205010f06 78
    0x50944c2d4000d208a030440c0d040c03d5031240116801110071140440c40c01c10301c1c1003078009800400361455000021581c0c52042a4000403c5900b110307454409220000f00c050345001140182c0c03001502c82d2444500040c1d2030400a0241d96122604001c00601c0e281c1341c0c2c141c40044600c41c0c100c520003412541803421040707402c00104133315242d194440900d04510f5034071192501c040c4540944020340301d544100240f170141c80701403003108000d000540c03281d58690b07000b9552a020b03075040c1440389c50102407210345030440c080c04058a8154032a10300c2c5072903c12120b0041048018141c080503610f410100307165666000e440d000f0300701c4030024941801c06038200c6050010a80c0400d5407080100120301820b5009030560301d50600403900f84101c0d018900744135001d0616107900960148001409100700250345140d458540343c0303000200800758403810140c030540b2416210414402d2100c001139928526051070800010b030030914101c440f02542c0c0e44c00d081d5a54500e089204030344032075090004604 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 475047500 1250 475046250 475046269
    0x809152403010c091203092102090c0a050403020904061512050610060f1101020408030d020705060108030306010e0409030e12031e04030f030f0507080409090b0f0411040b01090807090209 82
    0x20120003c00944240410103010041d407845410720b91213418101100b0f05000d0314400004008040728035000c101d207a909101801c40c0050100c3c403070188040841c02c4c0c41440d10686103404c0c41074890320301d081c4c00c0d0313002c2182e20140180121901c0f512050300c580c2d00c0d801014004010540d400352507505180500d802400c0c900020100e9074800c030000410440c80f940051503020011480c100840d140c0d60030004140648580c1d040b0512a20001131100200160381c0d005201c41409502603400c90b0b40c035561519100d02c01500c0c228000f50b02440b400f400b501c0c1c554481404e41d4401d0034401071104180d40441c40c13180807507000b80d07119003000c0352039a038451050700032403640500d982d41249054150382e212140d541e8a80400303400c00c414501d00c2511a03020300100c3d5001a00b008141b515981c0e1504610064810240c04444005441e00401c80e251080350f0442d003d507500004505203644920705000c001c14440c454181008441280001d41c984144450710181002c03480240c0da0740340e03040074818803c1 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 475048750 1250 475047500 475047571
    0x60606080a0b10090b0f0714030903010b03060708190b041a0f010f0c08030907080a080706150b0712030b04020a020106080d0f020d211d010c030b0f01080915 69
    0x60800c20043c0354158000c15440a40b40b5000082d40c550089412448407802007080090441e01e5a0036a1145000004054034140310118024440b40d81740c03205140d29101c1c00d0b0781030400b00e00030001150803520002c0c80e03000c060844000c0014141205000039040d100c000b10103408860b029040340000d0b00f481d0a2850f030280c028201141d0309440b03844020181e01c003090700a0540c9034044003080c00c504041c000f180003004840c007203a8602d00c02e401d00007010b51080008643d00c602d030800006082c104019071104851001840b1418000d00741c0b031f034040e00007521200404140c4d550914034919a21071003d4414920719500014656050422192801000c01081014400315044a03c2aa54001100d0002c01c190f031400c180d401403008151244041c1010404640c80d0400c22000c4022019421411384c0b0302d030140083c042c2510702d000030b41c102d41d41001840c1e0000201981c03c6c1055000301c0207680c20240364411078007180c0d40c0b480884c0c5441019101e01c0403621b030a008445600741c03d00c0d003050790803 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 475050000 1250 475048750 475048759
    0x31506050910030209090f061023010e1e09240a1a0c4e040902070221010b0a0b0f0301090911040c0f091403060f060d060606080a0b 58
    0x1d08181c802c0038841082c07880003c0c4a12044400241c000388107001c030291349241d100444184d41060403110311507a0050213050b540c2400b006450300e0604010807000c4140c3c8040c4c4405800400c21000d12032061142ca407031440440e80c01d10311120580360810403511811812244c030700d400d9400030100c4018040310002510460720b04005101c01c00c00588050240c000326202c0c1c035603c261040d003180c00c8c071104c01c0c0c01580000b100702880d012908880101d41807407840303001e03242d0301c40227070080408100d180d1034003505840c1d41840248203505885d4000d0450900042c00310312100710048010804040031410380c210740e510781e40649983d040065000700945200a03800b41000c0c10240c82c030a01e80814800c50038000d0301c540c464000d101080441000301c00c0e01410610030041c0181002d000310800c404444001180c0700b00008500503000e1501000200c018003821040c5c41e405000b144542014019a80c028001c90030b01000039880d2080d10000d005544901307a040c68030803801d4040340e20004889015 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 475051250 1250 475050000 475050019
    0x302090a05040203150603130602040602011e150b030c040f030c17060c0d05070c060c08040201080601020c01090314010204051309060b0d0f0f050c0406090614220506150403150605 79
    0x8065011145d40c5298140c40c0d081c2c403991008200750381d0010a58001d0708540c0300040c040b4000b5419081070013103044c1044000801d0b4240050101225081c1c2c40c40c0c03101441110050200700d207000021600441c05a0149003040e80380c400414604020b5070045640c0030190310b0410002ea0418a0800c1102d5024040c14091501c20f4506080c1d200c1d01c034030b2002c0a0703960400252014040c491858025410041c1000f01035804500580460000d94060340401c1d41c01c1c0004900b0741c40000c0800603503006a55000b00d81c1c2c0380d40c0d110307000c5000351581006d0554080c040030419131520002462104030035030300411800c145040920444a645581500030002c07010341c13202052601d0403521030b660f40012001c0d041d5056050179402c014000d405030358000d0822200140000307054000c002641c4401c015500019000c1d001c0041d601108146000b4012032050070a0704040c09911103a4803440151007480a0035907102c10740c8d0b41c3c0d0301076001142c2086035280d030100010054441d0801808040d10704820 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 475052500 1250 475051250 475051261
    0x615021e0609120a0216091406040204061403060f19090b0405040c0b07050c12070305060c03070804030c1e1a0a06030213020724021b0109020a330302090a05040203 72
    0x3c440507111441c8404101c001102110a8801c215032003880f0b2900504a901940b504140d102624992034200080c116400110750186410b1084604403602510b07554080d45a00c841c18909800c01081e00e40c0c0854100201c0c40103864020341d446140c1145a9109112824480781c0c50171204003000c510700a51400c0c0070000090090010b42d01a100c0d01c9040a4440707140389002481c24044600843c6c2003240100c4140c0e04000c00646c007420b9a00c90740589109030745010010786103001c02c5441d00c0004030100c000c1b4000c82c1c01051100d120500644000c00c00b11050109480390080001085884100c0003240498100d03040c160a50030118158080c02000e1554000030b9078000110309d40c5442c9680050018208031521110444021a440c46280d1485956a501d0002c1d040300304070411a0303141252001d0401c20602c1008041c5900800c12020305040c24800c0b04004c8040038080307000c00c0e04e00303201c58a41c0740c84070071085034049540e0056a51014030082c1302d1514100d51140340150f005205114 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 475053750 1250 475052500 475052503
    0xc300312091f060f23040603030f0e0d080d090302070801050423030306030d080606090d0602040f051203071e0819091d0105090402150c03090a0f03240615021e0609 72
    0x10304803401c8140701c0400c00c00c650008181c1d540c90f141401d1b0320170b1405400004168202c071607104046c8041d1503a08142005409000a06e0012078001b01800d07001c22064085020710391014000c103001e4812603041c6911a00041c0c00c444055070242c6001e10021400315080000a656481c90b20000c1d01031400e5007010404a0750f80d480c604011000e2101c00400120641c81e0b0300c050304c045240060032801c0d0001542084002540300d03010f0303005085410103022a09060080c02d189000131014000c61031b107100d41d10340e140c41c0441e00e52401a140c001500e400c0205403c0b1001c1c0400300342d070b0215920300244080c40a050b00c440c42d8091001141c003041240843c0d80001c0c0303040e0448105454480c4155078500c00030380c9008100705080700743d51021440c00a4010b00202404000c00181d441c09120381e01c0b040c000804800701d00c00100511034400707202c0c0c03401c0c04000400c0e040310302070500429510340364140b00c01c60f07000c00a840d10040c0e100e4500b6001183c480c0c101d020b9161595070140589080101206 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 475055000 1250 475053750 475053779
    0x102903031204050c030d3c0e130504060c0807260c0c060f01060e040b1302070309030501020307050a0e0906030a02010f090b0310030201020c300312091f06 68
    0x19803801c0001e80018040c05820702000074254401025038400700c4401402a00c1041c50700c4582d625502c0100c0001c90042d81d14106101e004000e5040c5680c5841461049900c002088a02d82e04404414400903020a090044c036020710312800000c99018039842c0d0082114100410781000c11180c24103143c0b00610030101c201c1c240d043c04041a0040d81c4801400b000b07032081460045440c07081004201400706401040c9060360b00c3d9030b0310f10009540032000c0000341da202e160099031106090000c0c1d18000c00035030040c40c025200382000502c960b901d4944a00b2a01308480a40200340c0005e4023800c8a0341c4118900c10000c821603500805040c1b0b6004a55940704401c1d0003030500643c44100911079000d108008000d14005145a50740c1c40c00d140b60700c0c07541c49a071000324050712503840850250300d48900c80000c003d590300348101701c02840c40220103148044c005600b0300c0b40001c2019806420042200c948920300800c010f11150750b0624030f510500c212030320b10200c1145072910034004d01000c4801c0 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 475056250 1250 475055000 475055017
    0x18040b010815030a02030d0f110c011e120c02010203101e0e04021503040f38070504030206190801150f0513120f031d0604050d060b0310290303 63
    0xc030311a103019003c02d103419500310003c0d5061140300181c2c070303a16a0065542c03089400a96400004900300f0171100c2e83c1d085000013003800f003901041c0404a1b84410444c221038034919241c0303000d00a12540482c0e044401c00040c80d00140d400008220031300560042a100402d0312618009900001030416449000a800313000f8208100c880032806550b162119480160541c3d02c0e40c542d6800c051030b001c091082e010354104d9040c0c11b1440145000100a684807240000907000e0712698055840c0c48283c040000341b8610078000c0a00c4080056124807001d4180c0e40b030000b6080c01d100d01c2a00000d001c611050788440c80c242041c6418a60050b84020f544c08080400c0c109542c03100280028290300c5400c2c0c0c0c100e01d05050080300c000c0c0c00c2c082c5416007110618040e807500150b4010024000b0007541481900c20b4000c0810041000719052008048010501511000500c1c0300d6901c0000d0a02c151205043c01154642842ca4048613034a800880d04107261411038842010910100e501c90150506 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 475057500 1250 475056250 475056271
    0x240e1915090326071703071e050a0807050c0d021b0a06090b090109030210050a1413030305070501061707090c0c03080c0c010603060c050a080109060302092703030c18040b0108 77
    0xc0e41c0b0f40480344099035100ca0340a40341e010745403584003060440340c10840b0002c0018203401e00490010f1400500480500381c15a926032500629282c21780b40f00e00054800000c10508000c0303201c901209000d00110b2640540c003808403048180510407460001d6560640b1a2040c2c10041200c141c00c041c0900858001110090701c3d60260360040c0c4241030301c1c1d1700194000c9403058442d008a9405001009200c41c19129006030301c20842c1e681c5075034081d140c591144500758070400c0c03020074018030240c0042c600c154001b0504549883c14000101030041081c580340c0c0c403148080c4017806460041845100131460300200d8030b4540d46005101c1c020150400740c07000c0e40010380340c1042e03000390001c5e0007454003c0e10920582d402064010981d9110680b8000021030b040004a92050240034070812241c00412441c120307206c500d502c4006e04003407428a807400d103404200f40c0c2105814005184100007210800b82c58901c4a17040c40b4856a0744074403540325074030f401c1d1231010983c0c2110880e078010602c1c21 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 475058750 1250 475057500 475057553
    0xd02090f0306090d0f0e03070e19090c1a0f0d061517070c0201030b3001050f0a020901090f0f0e0c0a0207180e01060909020a05030601240e19150903 65
    0x700f05982c00091011b040d0b4043c06003900c003080501d85001110301a0680c0303002002c03502c0034020100e00303d4180c0d080c01044042969410000024003064103001e40c0b050007101868103c00140340c51150b4050101c0c1c6042d9521940c0402652045240c203074481149802c00580d802200017032203400c008018204020f205510025000b5644240d002100e2588050b000791b25814a0000c1100c2800c203a0b40c001d81200104040d0171542c81060286c5405411011400c0403540c49d0420440040e401524403035040000014001400e40100011080140100215403c40030300340301d000c20828900419944400e171040094204555001401d40100c409805c3c079101c61490409010010301500140d10700d0035070801c0d10218000c00b04c0d50203030483c0b901c220f8207810855550780c02d05071500740c24410b0b04404d280c0c0c200400c50001030503464160854062038642900c82c0764400240080c99001301400012030821014030060031b107d44900c0e59049035007410703400307185543e4401c0e0340d40c6c4540b600031200100c001c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 475060000 1250 475058750 475058777
    0x6060d0b070c110907030e062206050a09020303040b0307120c0806211e07080106060203030a020702190308030402011d060a03020d020d1d0607140304020603090c060d02090f0306090d 80
    0x4169440403c01800d2046038249014010068400d0150111080c0692004074020403c121004001c0b9118420200d2051240361503d5000300002828130b1011a200c000150060341e00b40014005408902c10300f40d240d0402000042114420444660f030652030300d031a000d10640c12014065102c1000c0b210341b00402808006844a84000003044065200f0140d820048103c400d0140d0f110741000c4080b00c2180365100b0303485090784c055100d60005030f0020804290248425002002c1c1140081c02e040030070b40752070501640d091400e500c00d4a0043d0040b0602c021503074852010710781c034408038062004560398100094002d2240c0101c0c10185039000480c20041811601a02c000851042c0200030004201101140700072050042502a029890010355414003883c4180041282c90500f61b045076159800c1c852954000790464685206a00f0341c1d0080e69143c400030550f0b41c850381300240c2c66040460038000c0010150a100d40310340c001c1c60400c054034200045940c0c45100c0c0c0e1802e0290098070 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 475061250 1250 475060000 475060013
    0x60406270f0e18030c0705013c17040803070e0f10050706060801150302130519020702010e0a03030e0f040b10051e0a0c1101020a030f05030c041e030506060d0b070c 72
    0x954140310701c01d01005c1501e03035140c1c502080110441c0d0003a240d40880341801100c403003600101480b0724440a1804c2002c3ca000b0020306102d00580c102801c1001364044448201000ca180c200c40450b2050400000c005401c1d40c4050300449204050f030381800f24645e40c0000481c0050341c9507400c000c000f0302141d40c00600c0807580121006001800003084018404144449108250300060740186c28211080c0702030b05e000d1050f5881408030300c4111800c0100d10b06064081c2d441460300b85e0402001801c1300b6581da861070b4204004600ca03840ba071461100c2c2c4028040c0c011a4030000314440c510745140418181ca41c0c80721a030600d42c00d443c14550303400c0c410b840350a40c0c01c07140e800c040b400400810540d5190b5000100550300b94007600200250311410401244e85480c0d007640100003a401c40c010310030060050340a103421000f5001864281a01c0380ca6200ca10b5403221411040220250420024007005000603500100103030b541120588135034031825000700c800741803001004160003901e01480781 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 475062500 1250 475061250 475061281
    0x20a03050a03091e0b22080f12070c0c0f060e0d02061902060403020601170c091009020f1803062e0302100e030f0f0a0303050c09060406270f0e 63
    0x107014004c1d0605a41074000d00c052400020000c8420b240100086900c0030526141d00060201c0d0190402083c085517a800b0340e546c002407400442080c041c000400020041202c02d0702c121030300e40d150810310855060901c0302030002d0340841000528800140480380e4000265080118103031500e000c1c440d0300c0e02c0403d00701e10078442540b0b80d4001000710f000380e00346c1c04a0440c0c0103a01a908541c196602c881c4070700382440ca590402c00d11940030b0b00b0b40c02e0760b604004040f0f0b907200c50f03a100c0c0c0c1c1e030300d0302c1d0748048a07002d0382e103d048411040304000404445101d41c6094181000d40c05800030100c41c0740c01400d02a00140c0240d0700b0071740d048418038164014400d40c002034042c40e8081c00d06c115800b6000005041032013203521140c4240a000e26441c0840c10000d16410701c44c2c0c04000034140c01e843e58900764001c1c0300c05040030702020f50811624501d602d1309802000100407555504e5684c0340c103400001000140507114084094030203904000b64a90a800740c410f8510300320b961101034903104900c041200 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 475063750 1250 475062500 475062503
    0xf05031e0c030f0a0501060f030b030708011802041d19061b08190c050f07050a0803010e1608040804030204180b0a0e010b0103090b0f0405030c030c0625020a03050a0309 74
    0x2110200300040e070740d85010394000c81e8a000140c4840e10794640358803e0312400d02170000090116508070b040e2034840e4200502c2000050141d5030115280c828841c21b4031284c1c0c00918a01035241e030b00c08114101440349040314400d40b1203413040788102115054440c503000200f126094030141c00c01052107a568851520180e03075580c2c0d110700c1d500c1040050850344003120010300140c008c5001105c146628020802142c4180e0340b080e14040443c40c2da903001c0e0300100420340e024456441128001202080103502810192200180340d01c2c0800c042445000424003c2c000c001d001d5090100041203541940e007900d0303046801150341144101261061185030304050315004e15001400103000d0b040c0c4c0300081c09100d0b00024821f0041420041d000d03924940b600074000440180000c010152001c2c1d900d030030512a9054900e441002c400d00ba28681101c5803118413504440103000d0800544610742d600c4041c0044070b0f001010170100c02940720031043e0700240500c172000400401c42442640000c1d03805 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 475065000 1250 475063750 475063801
    0x16031a120f0318040c08090705060c0111280f081611010c030b01080907060e09060301020f130501020105011a0d0c050408070b03041e020a09020d0216060b0906060a0f0503 75
    0x4101c0c0d451901400360328040b0540c050791404405940e918415804103110b501c0003c0142390b00d500d068180040790340b00c240094481d540e900200d18040219034010433070122040344010070410382c6203503001d4828182d8a04000e0200a00c1107455080d000b40e01240c1c00784510580e40e050624a00064440320442d400c140b009500c1c0c0045550381c0e9404d580451494032080c1e07511409a55032850f000d41e1821b00c2c2c043d03480400d02000342d030900c510703014140c284c4c065400360000d4141094001c0d400e2458015246540e0306d0200f04005114a590910800380104180080c1410b110380d40d0b5408441c5106c2c10344c100070380a40f200c4981071250701400c2207a004080300002c5650140d0785108000d045d41082c0c2e8211103103080005001c40d40203214158504058004246038001c41c45d01d800280254003400c4c100c0034058080c8020040c01e40c111800000c41801038602082c2083c0340b03020040c890f900141801e10582040c45241001a0702c41404c00c2d40c0809400e2035540c1c2c0d2103001e02400c000002c10350b204000b = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 475066250 1250 475065000 475065007
    0x1202180c070c1701050a1e0b032509050c070b0610182c072a02040f05073b060f0703020715140313030e0a030b16031a120f03 55
    0x320340c07029400f001c00400ca034000c001c02e0b01c549645200350303400111100c000071003d0903104440e4025034048003074518001e080703c1911000c00c09030040c4801070080800841d42d11082046041c099024295102442130207480c544191591200c058450207801640039400b84107507528006c2c0651030040200f99015174161480307030340b104032408020502e118880000c00c286449440c880d81038521030300584075907c034050008105c1c0802560769a40448174400001e1103604200561586d00c580124061076031070124482ca0704038409044080e2280c440f503c182509210381c51041500c03c46440340281c0c0f8640d030b50722031000000088442c0101408043c00e16000101001010380004201702100e02c1000d9403140c445117084291440d000028401485100810004207195a4220854003048c070034140f23490618010f00104200f09120b0700304030349000451040c4012200c06005401c580113252a090114580c04040900b854000008182c010000060fa030022420240000000891041d04903600d = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 475067500 1250 475066250 475066259
    0x50406080a090b0a0b010306060c050607111e0c090601080f06060a090b030907032d0615031b05130b0f210f060708100321030e1204030c1202180c070c 66
    0x400c041c005c0e040c0400c2c42c1400c00110300d4040c2c00c0e0881d1072500800680442c2c2d503204000e0b5941d44c00c040741040c8600502e09410b8808000101e8440b40510f03100091524258a0081c031a07145800340245040c00085001c000c40c0140c000005030344001c040d0360440e255411800195184503d030703000007035480d00100c104900440b00203803190031270b03014840c207007240d00600c90013038900c4a40486042501d40c0050b0345402142070b9412611107484041c041010309641c0ea210a00322480c0050900044070701c001c0300300300340e00d440c403d41d140c9040700703a0081000205900016030b009840e02511030044801085016143c0c1c03001d0200004841040155a0301e440361401c50358444808448950100e598030020030346044d034005c0c6c10400c0d40d5014840440702d000c092403070140c45003854a404c0405031190103008941e0340510641300c03904070200c500d5444509518107160418225004104100b2200540072301580d951100c40b43d910000d4100c0d18142d490300700f6407202910070b004001d04400403001c3c002030b = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 475068750 1250 475067500 475067521
    0xb030c0d0c02122b090803040807031806180e0601020703020111071e030b010605120411150a02010e010b060f071203110a0e010206090f07260d030603120e01050406080a090b 76
    0x101d41d18024540380307251400c8540d001e42150508217000c1c024070000d000150000d1580c3d070081c001c5500905000010810840b028440fa0700b85810100029003480c210807081c4244401c0c03a00602400001e00023207103442d00c0002c3d61000603100107170421550304400940702d1003d0151101a285481c095552418080d420080000b40c138413040742c82d03a1917a000098401d03c0b4a040d01d1140b2030544150415884a458080e8020958002d03c1d50005081488515040e09a001060040010340002c0354948840c44d015003111001041980111420400c148240101c0411a840c0170380c4904240840e52034403a00720b00800c8081e0040c41c603804002161042150454203508400300240c1c01c1300c5099980130801926580846084038456008440a1100c030058403800c64001c20300548028100030101080d52030013281c0c480d048086a1781d5801401401030804001050b880c80d400c002c040c0c46a503400083c114402d40c030500041119100c0803400700d502c0c0740c0165441d26005107801555042004103030 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 475070000 1250 475068750 475068787
    0x30c0d0f0516090b030423100c020f1b03030a03110d1505040b0d020a05150d0510140d0506130609020909070f050a080c120a0b100603060b030c0d0c0212 67
    0x1400700d0f640d81000a00d030200c07042101e108591200002c242c2005450820b507079840c42d4584105203019004030b8054080040c41205251103007a0300500d003d20300202a1400c1100110312071043e18454805c8410079100001140c40350001031900044845030301c0c00f90040340c0160907968400d9410001510100c500d640b140c4c00580d10f049030104442c10390201006002088542e000313401c02420f0030100900d1070f1540e00a00c01d4000b55114a10340781c000d6100700c00702c400c1200c0c0c44000006a100500503000084048103d00c10306071905c00985c81e05454890740c4800041650781608000750f00a01048032035000081d4495000e0201540c0d410000301890321110f0342d0040300f4920070a188006034601c3e1401e000405c880c81170000c1e140901100c0144811000c4401d43c00310144030700311004000448010845100b2002e1000304142e560030701600601b43c94166210321525101801400044400c41c6d007112440c04c40c14400261100004030709a04001100e000341d4040d8a020440748401030080002 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 475071250 1250 475070000 475070041
    0x22030f0e0a03030c14010b0411030f01050613090b0d0804081c0315091107080a0c060b010503041a0711032208030403110d06090b011d090f03030c0d0f05 67
    0x10103120314a1203090281c1d00a9030711003d4005841c4a0540300469040000744800103d04000131524101d000c000c24251146018201042d0100008021400c0c512540203800340004843d02840c010841c01c0001c1c107040b0727a005003c0029680c107404c1c0c540b55150b0708441036080e03102441944940d614510143c998800c140c02c11840300c261030345c40e0b60140c4031b4400d045102d01407495040300f81d41007031440c00003010740d01240580400100064000710384a00064004207080d40c0d101407100b6100d25040060301e05520300b450521005001348400650ba04102c1c002c0689440d519810b5075542000c00c5a40041a0184980c01d010008a405490700c104c150304044441c41d02080a809688042c0a941c0e0f11441c8005050500500a91030076440c0100c1e00c4040a03001d03070740202e0154015101c0d000d4804080c0d000302020010340c0000c65038038035161013241e03011010341e014080c880f911107c0d40b03031030344001840161681000110300b070b07080d0155030090100174000305080010346005100d1101050306881c9 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 475072500 1250 475071250 475071257
    0x10b03220c080d020d120b040e03070f1509050a0308070e0924030708250906060801051203070201080406020901180e010501080c0a0c020409030905030a1506090608120322030f 77
    0x1004180613000068069160381c0c299106544051b1841000c00103000c0ea01d03809901684074030500032101410000707484000c0c050140c81341840741c140341408a0305d0300b04480202e12401c00002c0b07404a00c0128000f02d501c0c0d0942840001176442c40412200500c1404030030360310203000702c1840880c82214071140140b6090032421074034022100c0800d0390740c40551103219802e900c0705000314036070202050040c060345030841030301d01e03465101d540204c02d0340c080d0381003030000500450040095282c17803001d149003050510091441c1c402e07e500000c1c08000000c2c8090129500014800b1050b403041c02c42116030540c404190280540310310290403003800038491140015401400310300500100411101160741a881d0040f1039041e603400c9c4005805440829828010408800591501c082c07140841240c8038443c500840b03843c80c4031120459a4981200b00d1315450420140082c200000c2c0308042c1070080381e591f540fa075079a034100d01008010307402d20082c08803100030068205a006401300c03011100546 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 475073750 1250 475072500 475072513
    0x1803010b0418060b06040e090625050d051801020c0a060e0309030d0c0609060216020a080303270109062301050906010c020d06110c030409060b070209010b03220c08 72
    0x800050754040350342409007280b005449070008840d13901c03c80758120080d00c80f9041c5640e5508000c030145040b1061010381c1c214404200b00e18401000b8604440f080d200e028400340c1011100600c5030140c501c2486c1ca459075480428042444500120b0315076905000965480c00e41000340c0740c9400c895101101c0075401d005031110f1580c0007000740d4144010180041541e501064411981c0401c0303081c0a035582036480541202042c0d10303000820f41e202c00c685901500b40240d1051080b480810740c4240381c50340060007030102c00c803041017168030217814100740c01a02072071140304c141c018403050030001d0071146407400b1640345140c05880c500c180100d001d03071130070141c4e41c03801880b0843e0001c451381c0b4001101c08808100520b403070306514540500841c0b0000b8103120400d0101c803690302c40ea4400c0c029510108081100c01c8050080e00d000c4c003041d10b004da06040c02640803800090341030044540410001c400034009158040b500643c40039410300e610452902c0d0706101400031001d0040c405c4500858 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 475075000 1250 475073750 475073771
    0x510020106050a0b04030803070507141009110d03081b09040513020a140102031207020f0615030d1407020f0d120c0b1614031003080301030b07020d02190305030403030f02180301 78
    0x70007600c5c103c03900500d4072859039603070b00d500b01c41640c09040121000d2207020155130420398104511001d0602050000031107450506003a040001e115000794850380515035600006a07003d150150405010324204040301e00c82d41d0440c1503170040d1880650072030700d00001c101015030050540d42c0300764001d507646949140c407402c032220340c8521404c049002d0380c0100441300410740007000c01540000648143c5d04c0644025107807501701181034079500d5a9150003041800b02e4941803140d4003104480f03040100090004803050035030b900400d44081d215400c81c0c401814680c80d02c804e55002c0560140320508502d00d8038902078203040c8000d0068071141350910000360407955503070561403288950385170400c41200c44012100503920050024070750009415000000428400140d4080c0d4440c2005066a2801441c020b2410600203081021940070f4006801c8842c1d020000ac072580d609864200e59903920307410103401500524151030a0300e440018807130b4000032849100d00c00114210001c2c040043c15 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 475076250 1250 475075000 475075019
    0x210c15061a040305030703050703050405100c1b0f0b0702061306080124050d0902120316020414190e01060b03160206091b0f030114090a0308010506130315060510020106050a 76
    0xc07800010f04c60360040051102003801800a400224420300c0c00925098407031001c01cac040d4400c00c0e0a48085241040300c0410400c1c0131255000308080401c402d8000c92804a40f004001c2e664450000060b000156113000d42d22410122500c114205948000041d0b5503040145110001d100d0041e007a4401c0b841203103010342d8a000030424040035603c140c10030200fa41900014981890220790195034040803a8000005001404e02c09800070240640c0b07050328010b10041d6180600c020000030a05001c206501f01d084460181c080b9134040b0004c0c512000341149401891181c021002550300802080b215200d0003010520041d500e03400c0d14940c8d101d103041d403a130300c0078500b4020b0000b07031090350254100c1c1482c0f0960f01c1d0707504c0006c00101d1072409446440d001c500080e80d042515801c41301c009410306421907001d500620f010740755140f4160a54040b800201681c1c00014440c1c5101440100140b0103600300301d010706801088070034140b8198001034001e044601c036450050300004030005040c0700 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 475077500 1250 475076250 475076257
    0x106090806092e0615031401080303041a04030318121112030106050a0207030b0705071e030206070f23030a14190903020328090e04210c15061a 63
    0x3001c241d0b40e1140e1405481108040300f040c169842c180c0d903201800212000110704100034020151400991140c18001e40c03c441441600320b0f0503107510403c1440002000103955041e068410b15444081d03031504d14048003d4010b0f0404d25030715055402d07660040c0030100301e03c1300c403800f215190800728920050181d6103800300d140003000c13010001d0004011190240c001400f01329003610542d8200c94896950000341c440a5441d40300049000c0340e900c0c10401c004034035411400d182500405501c103560340095588000034060010408100719402c0c0b0b09010301c2c0002010405062107940d180c3d24444194059002241c40c00c105c0c0741426449080a901d12500303901881e80301d0303058181050600303000405084070910440443c8420080c10060b14159084d07400d010040e40700340441401f200f0f40003040814182c0207810450800e40030320002440b2494140500e0200d41402190311130b61031020358000e90003090150006024844818412000e42e2046068030001d1202d080265000802c3c49814003 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 475078750 1250 475077500 475077523
    0x412020d0f060507050405041a0d0b0a27060605120d18080a060f05070e060f07110a060315061d04050702030409020f12010e0f010311040204170303060306010905100504050915010609080609 83
    0x7214ac649140451002c00c40654082c00300b00c2d00ac21503010380645040492104440003000122103021b000420503140a40b00040c2411240703540c05903468000180c98031605015101444545007100181c0040110070000410704882554494104d074149032010b828028007840101e403a000000b00c4032030207440c102c0000d0801a15030745c1404100c011000b201e0344030700f0050b00c500c002172054600380d6a60307502c01405040c003560040740000640700080202d80440d0011010322400456210010100c11a0604c0c080b038219004111a100c10030140d08601c100e400942d902c40c0001020100c0d651094010501600c003c24611102da0b82c410922841c02000e40d10307100b2001a0400400100b659580d1803038490f04000e0005141c46e54079240020b50301a92b8200704502e030000b00030056186810b01002c0d0040010f00d600303110a18008031000e07802c0d113943c00f5042c412680c50020403c0312604011030b00803180c4401e4403040c00e584989010300042e101c1d100307118840c45030030006058840c000c01c0180e00030 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 475080000 1250 475078750 475078759
    0x60f0f090307021302040801111c0b060f09010c0206040605270d0b090c03070306050412030905070501110a020904060b090a092111060705090102120412020d0f060507050405041a 78
    0x260440d82085800006001314240054007440301185401007072007400040358800008540da010604023040107010070018081c085480c204181a01d41c484c0d2040310314540070711f84040c1da541054401a02d680c3e410040107904890b02280202e0b11a0304000105104170440c5120305d0110300382e841c54010302d1411480c0315080107100c00594001403c2065468200c62183e058400480384400417078940306446d4020b841203500d40e401e00c014090300756130f91540002a0b24091007480ca441e26026500c012f14415541000304056031100c2e0400c0c20b000d075180890780101403207041d0905080c5003020305205407400c1e200307200d51408110640610704c106550190711011500c1e0340d20700b6880098018110390b010f0b40c1802810b1202400c0c1f09014041c10703200b0843d5880b40e0b0f8441866100083c50600310351089201c07080c0400040c0001c01e920501d030b000c82c0381d0465158220424500d04420141e0351003100811140c180306c240402107802401070310503981f094908002c001145000c03452081640c05055410 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 475081250 1250 475080000 475080007
    0x11404120c051009110a060e0d031206120503090f0a030c09150803120732030c0705150106022404060b152206050c1905070e0108060f0f0903 62
    0x203004004070303080640580151010003008800b114180c0304d159408442400896098600c40c2c40c1c00301e10100a04000d142c180540e11845010031f010080c140000780038441c1c0038800303012040541e000340010b06094940c01e0a818080e15280340e8903000841c078284a5014500c001d012820845252000c5981085005221628060b240001040340100d0450f5940c486800828800800c2009007580c40d500d441415052400303043c005c00705080559007010303000b98030030b0000c28244d04000e404104940d4071031407552034403050411600c074454101c008180b4040c1d003013000640f00e1240c0e42c0c50704941464080e0307101090f10703070180f041100098000950140480e40450301040c03c607440a159150003a003808a0004a0b002000b01508840000424502043c07024850402c103003003450300500780e50400034206941d0700c094940322014900f0940c030b103150034909002840002c0120000031b1416040c0c4aa442d611108151384490040314407000310b095a0f00400c2c0c508032450b049500c20040040507508 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 475082500 1250 475081250 475081283
    0x50909150703020c1c0e03010b0312070201081314030a020705030d0c080a231b060c0301050904081e0417070303300212072006010308160b0f0108011404 67
    0x84d003184043c2a402d00c5262003c040d1181414070000c006030765925110300741c0e202c0600305800c5d01c145c42a101d0180d0084a1174211501821040c0c5200c00e41c242071148680d50351498907166950980c0005e403030701910f0011070b42000c1c40070005025a1046900f41e460194030f9034103040e81c803166902c0500026009007c132601050786080030342015400d034900148907113251342081c080c01c10650b02e04d502d04070001801c0702c0c00c401413a80000207404108081c202e580782c441d1000b4850300051182ca0b00a044201c0081c0410150504076400e5810b500e00c80c0050200f40c4440d034078107800601a0000c103600011a4002110000a4860842c0d03403641e04d104a028198801010894900312042007080050001c0c0002d001540054512446500814425403409580c020301003520381850308410f640d001d00040b00403c0100314581540c0d04117002c1d0b40d0740c551042801c0c14401c43c10002403d4070701c013901070080d00900491402d040b1a2410002e01003040720004000460310166801000503c24403045035 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 475083750 1250 475082500 475082507
    0x801060f02100f0b121e060c07110d061503020a060519030209030f19110604120803130b04061401062c0a050910031703040f060e010e12040509091507 66
    0x442c407500c03d0041004448807000c550a5800389140850b1904030354002ca2420542d9101070446440410003042c00b414121010302d0684140c4402030521101103004007a1034480011500da0b0300e074080c4007000145561151490400e520b404200d03c03401310303440000f0b10284070314159500b4010420412410010141b0141c0080d4480c0444c90382500034034550354400700d000c0c005c02450102d18050300038040d0131031920141d140c5055210510943c02400280500c0100d42c0c10700000c190b1044610f9500d40b10381540400080c59000c00801d007a40c5001080100240340d00303c1d01d00c0d09240a064423040e40c944070251990030340304a0a1190412524648065420900255030041c034040c00141c400b549800218048035012141c0480c449000402041089024030101d040405144810750031420541e842c0103100810400c09003960b900c444a5103214032080d4840c0500081c89403c640701030a9640d00c281d5150002e10500e071042c00fa580020710f00000c04602d83d580200001803200d00ca80c2c4007202038 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 475085000 1250 475083750 475083761
    0x90f17101d0a0f1203021318020d05090f060106020133050402040312122304031103180f04050103050d0c050703060501230f1014090a03060207030801060f0210 70
    0x1c0450744022001400303500c014090010310318000c07004034404841c1410040e01295845100340100352040000300d00394520040010140c1e80d10301100f140402c0c1c40703000d000103070203400c04640009140400740070115400088980b4540f950400780c0d40207a9070340c00b05030300320b900302c5c80e4007600a8000001c0300b1880c1c0901c0e40c0107480d480da0402e005452070720381c00410b081360400e80045440311034044030020210340100d00440d5104106c2c6040c0034800e00d0500010404101e0090040b01d6a1500d0103d402c040c041d5100420044051007100d44422a1454240d0b44802c03c100090103a8038844d85400d00d414a4003c46040e250088010304050101603c01c4501c05058242505c070b5002d034038030101c0050280d0003010300800070303201003082880b0410301c038665582d481c0c0d44551140f00c00d003d010005d0b03200c0040b00c8003e2041401c02c0c4080b480059440d407024804d102e00c10303520244208000c410890654094000b09001b60b88042042c1c2e2a80c01c01d641c0407650078030b10f00140c0d204107552840702a00e038001 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 475086250 1250 475085000 475085021
    0x105060f13020f0c0606013005150d0c0f120c0e1b0c0a0b0703020a020c0103020c0312091e030f0f03060a21260417030c030a090f1710 59
    0x43ca8080785a1880b0355030b401101310300c080b90f0040d0341400807540c0c0c003807000350740c0150f0781c50280c0074080c1c0030608112620003000841c032026120000100c0c030700000d24ae02d241d03601014101c10b805c40141c0c0f40c815a01d145501864401108840012070f0802e0031042d50300065610081c8041303118240844000080c1c0c008212034041031340008014903d101050103801450300c0140105400020340c40c00c40005080102144209403041c00340c003004650015806251b800282401a03803241f0200c134050031445106001210400c000c0305001c010302d030014140b20f000030111a101243d0000740c582580ba4403031703004402200c0b40284500385050490000460304080020308054115070b40780040c03091008200300e040c01c046000d80003a001d02a1426180340e03c3e01c1c211b0000c000034928105002c1c5a80903500400c02201c0780784280ba0b1003008200104c07610010240120303030b1101c0b02d4050003440c2c018103008000d41d003100803800103000c01e054000c2910324041c09025100c0c1000c1c500b210001000303066035 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 475087500 1250 475086250 475086289
    0x50303090904021c05061911160503130617130305220e0403020a020102060601090f0b070f060608030a02011103100311031f0b1e03030301050d0501060e10170105060f 73
    0x40f030724a14141455184d1510b8800c6000c0c140910b00002e50103403044825000c85181420001c0038100000c880c421a03c1549504d8500100c4032080d00b4500d20750302514000038140408a01c0c081005c0d074000c00096141c0b43c41c1418090541d9031a9025100f0649802d00107011070018080d0300f012804450b511001502c02c4150842215954200b24600f0841a0b0f010b402681004a140040d541d040c080d4030f80c40316080c2410a6141d141c10710303016190b800c44c45554038052020444c0801c001c00f02030b104c0b00580e00903030280400b40e290b16240f0740702e60041c51400e0240d0b28201c04e040000d00c02c101600e1080f07000302800011107145448209020040d100703225850b0291061420710b8a2401007001481e82c085440080c83d040518244003104044a0f0f03144000e60710000803841a80c0c0010441c1d06480c07040d140c001200029151090150045402c03021034240b40c2010070103821000b6841c00203c0d50310160804034100c1d401100c40c200e84041c0c502c0c5030480aaa054008503040007461022413800510 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 475088750 1250 475087500 475087519
    0x31a10020604030f180b0a0210050c030c0703030b1003060e011719110a030602030604180f08071e030f080109050601020601050f1212070507061103031f1d0108061005030309090402 79
    0x5c8071808503441d074010b100a1540400c020100c681d0400805040d9505584100824100700120210314000100545040500000c01d0020548280c010b0401d00030054000d0b80341d440c10a0014000c0c08040c0254104052001c00004031400d900030090f855240c400d01404810100150031409450454400e40b140075444a8010103a00e030050311100450080c0340050b22401d00d60208419101043c10a4080058001c0b0440103d0103025441070103e511401c4203664840a01c0e0840ea6580760480300c000365905001e8040c00d140d003011918010454983c2e51120523a00e40c2880703c101c41055400500603441580184903d0901103400c081c007410003013030204000c1021621915180320380c0c0300c4044416011a504041190800a00c80034014034240000c0440000f05c3d125030303a0000518041d40c009580000d800200003070418200a00580b1504400003105424032914041007885003102c40d12511000078002420381628005031040200a50b2810840804104020703102420582e8000c2442 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 475090000 1250 475088750 475088777
    0x80d051b0304110108070c030509060d0605090405070815150f0112020c010b040e0102040303080f06130f0914070b0a030e07170714060307090e25031a10020604030f 72
    0x7031841140f08805103900d041c201d20005080d00e60140c403070002d10040b4078090b00001e40000c20744504031010303211103840d14403000030407014048590101d6007210514051005029002c03510401f0380d9844000c5840040e0703a51421104d081c0c0445010201742914541d454032440d10709507480b0740a0341494850700342c17460340170000c1c226400818401840c0e90760b2741c90510507080500030016640b0140008504052464a01520342d1400403c0e1800b0800c0b0380c00080c0d010781d070341101500403100b0500d0801c840041440184c00910308100140d0700c0480385451840c42c880009a44400c0c0d507070010301c4600f41007540c2001d5020381107501e0500c926004024021a17141c0404000c4046040902c00030b2079103614008000c1d00c0070400b480c205005850800070400c0300d5420010840858400b0b120001495892502c480a0041c20b401e085501004d101c14014000380c2c190070081c51000010202c9000354041d00c10040020280410080540c0001c00058042806120f113502140704908064501c46200d = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 475091250 1250 475090000 475090051
    0x60309060902041a09010509070f050c0f060f060f0d0201050409020708190c170901021c0e0d06050a0b0a1419030f0501090c0501050903101104030b09070608090604080d05 75
    0x70305a2007100f840120300b20309580e1a090f2a086d0040c2010b542ca0560b60070068002051525100921028004c000802d01d1081e001000009810035654040c1d444904080c0300c00c00540000380c0340c683c400c90005843d10301c1c07440c10041000b0b21981c161120703031030980791410500c0070f900300802c02d48401c0410700c001c20708250084016a0410351541d10308411881c05d28000c2c50303c1d140c4400c02c55102005000c8400715903000201d5003c81c0c0000c401c0110100251003084610b811214100b54012901241240c01c001d9250030203070140c00754440520144030310200b1320140f15041d200309007001e0072100700c0d80f64a040c0b9015003820500748032451a01c0350349a07140c0300010582c840040b125031390355255000501030a40d41d04400b402092030010300e01035071140007983d280145504003402c20b54605107401c104122000300d45c01158011440903052904c00078003900d4022600c00c1c0004200c015000400041020905e544619400004107040c00c90b0306900030300620b00108505520500402c0008078910b0b07 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 475092500 1250 475091250 475091261
    0x2210a181a070f0c0b061f0306030201021009020604090203060604030812091005060102030306120c10030213060305040c0b090409021210111e03060a0308122d0106030906090204 78
    0x30710390040e944041c0c1c505030112104001c106a0070015101c400900c21540400c04003241500301c00a000c2c0c1d52596000244034001c0940c1c140140e2142c0c0c035500c0341541d010b80008084034002d07000c0d24444c5400004141c15984010802580481d080209114800f5140c1c040c4d5005000a0082400c150300ca50f00e0070b04c160b00002081d00c109003000104a031302c0c4403c0202c01902a21402c2c18801030410100103981c82c0000b03000035109029a01300c000480d8010030408a03e5034005044007900100428090000d43c054540d0204040c424400840d600b4040e0080307901031541320200026481c40d2445807989c6410010020b079201d6140c0c0100400741c1d0b074100103140d42c0c0000802821308a40d100011200710750440c0b81e559104a0305000d0810580070034000c8122060342d44040315076a6684000280018030136400c02415208003040c0d401456880c03840342c5215510310300c1511100c003c184074100e40100600500f8038040a00d0300107010081c882d41001801c544500c0c0c012036140c0701580081d00355207 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 475093750 1250 475092500 475092503
    0x5102a020c121c230c1005060d0c0e09151602010e0c030d0c03021609020414030a15020c0c0913050f07051f02010f2405010809061f030f08120a02210a18 67
    0x41c440300c030075031b015202445090b8018004640701240d40400390b80d0000540301c03900c1016041c01040000a861000901506d10300b00441c0710744400c986403480c1c60108010b01500044c00641c03801c4070b6081640400200001c004500800030702107602c0035401200d0009803964110114000d9840440035054001c0d40700c0d0103049040c8015071502e084c0301443da04800341c0c080c160b00c65404501c8500c04640744a0640844841041c405640e07035040702c8842c0e107003600314004242c00107a01030800000c80402020380010a00c0381050310b00910030885029170b14003490041960044121a403191a650914860307010f240880c0004118604440d1441d400c035812498228100804112081440d03164010380001400c03007405e2000b42c904003089180e59804000b0318140c1c406005038051080b00d002680490700171076009400101c491801d20304001c1c1034201f500407051540051000c185240c0c0107000342d40c044083d074159884403140802c000c982216001e0880040c199540000704e0704803805116840819 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 475095000 1250 475093750 475093753
    0xc010606050a1101020901090501050309030705120a030509070e1311131a010309030c021c02120a030201150e04110f04020a080f01090905102a020c121c230c 69
    0x1044440400f828900324071140e040584d104000c40310082e03070403220385401d9944c00c1c81c0254499452488191075071283d000007030107a204440982d00720060140c020885541c41c0e44c0c00740202e0316400001d641d00c1c481401208075a00c2c05000003001d500b01c07d210b0800301343c0110b04090b82d0640650101c0e105040c243d4614802a4031450034003010100341c20300881200c0c0c05c0c80e04000072011030314001c16564000320004d20401425a5480c40d80640100300c40403260010070b541e00c2240c1d1803843e141d48103180c42045025500b000d5510a41c420600c40210844641c206922420f95559860b000501600c500e455405004603080400e640c40300e00c0a0580c6034250384400d407282c00d00111018034250140d100c02c1a190810105400250021a80c1c280780000f1040c0494402003c0d007607524640b0407101d0034a49080b1152400c04002d030300244550550b101510302800d000d0340300d07141e140c03a4040d00b0801e83c01118039481d103c0180703101e0001d030048440392800900390940c0031a0280b4047d40150f41c0c45044c0d = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 475096250 1250 475095000 475095007
    0x203180f0a0609020a030c1410091a070503040f17100b09041101021c020102121302060a0c031407290601050405011d061206190f0506160209010b1c09170a050c01060605 74
    0x149c10841814091400340b8144103402d80d18042908284071120101c06100c00360119030201041010800e84d00600b411228041040d6141c041180c044444000091070b54032038041500c59103c0c591203200510301c8040c200c10665503079a112074540c84010355943e81144108010b52902c1c0c00940080810030b0402d41c0007507a6140280b000101001010300000800e907600c800d40030060740c0f0141180c1482000781880207040499003800c0d240741025104103101c0d01000106107003000045c9104500c4040490448018100920084144003004039002404103404020502c00c5600800124145000e405144800a0004000702e041c94002c0350381841c07a811500c042c0007a40c5045182c0c08d0070341c441e854081d07141c00d01e403520410308030000d171241d10b02411000802c00700750414154048441c503000f408003c0e80c0c0d6541c640084a69020f4101103046096540b141d03c045456400707603d0b41280c200100d00a10610108284c02950189030404140003040051078203034142030003580d0013000c0b1922071a44 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 475097500 1250 475096250 475096289
    0xf07080c010f0201050c03011203140412031403041a06040204080307140705060a02030f18040207030807090b0c0c0f0612042009010b18030f010603060203180f0a0609020a030c 77
    0x202d0038001d200c0c01964182001c110a159106056a044606a01c504540d0516504059030180e030640c2001c00048400a40442c8800307040700e1100945100e991071807852401014a1700c8a40021b490040c0840c0c1d00c41c1c094070117200c01030140c90f00070340300400041c5080e0743c61503240e180d0790246030219240c03520381072a83e180c2c0e801880440010071060740c201d4a44218858000e45030701c50a00e000f90001004640d080c5c0e000c80c0f141e412014904050021940c8036402c0c1809800b400c42250f8440003c0c8070001d002c82c56005100035200344144003001030541e4a00803003042606850203001d0f68010000b44129030302c00f0507c86115015034000c0410080b464013440c0c000c40b6200703000500c1e6015454040c010011103215400f00c0b1b000c0c003140c4d010407255001d03150000342803040c0e00c5852085982044000f1040c4200b03075005501501c0d17041d075000245e2048000541c0c46022071015000b06e84c2000b0724640108519800201441d8030040c22890182c1d117076074441c100c00710700d6000505010342020f907288 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 475098750 1250 475097500 475097507
    0x50c0310140702060402010203250c03030507060e070602030405040f0222060e1509040c020708100f0f0c0509150403080a08150405160c0203010609020a0206090d0c0c05040e0f07080c01 81
    0x641260103071014141381d01e410b40010355648900610a00c0c10f20380350200756110303050310450345c040750313030001142b28071a41d40c2c2801829030b00030f104152456458103160840c0d468000a0110880c0c4041d005107051074500f400704001409080c08082c44903808010201804152007540b9800d1a0b00781600d07801c1074100b038002170004020300040743c002c1d8502ea1a81c05980d900100341c58040f4411240455540300c0d21400301e040c841e160f4003248185c41000d05040528256410039202c43c1c6c807820080211403040d4070b040b015204a41300d5440440c008022000403802c0c80362100c8210040c0e69981d510b8a5960b0703494080d10f6100040480005190300103000c004140045200807540d0125402c0c0100d00b0a120480c2180050b800c0c1d1005100b45204201c0031510290800d200419041c5c00454441a016030042e4980c1411100101c0e80e00542c007035106540e000700310039a03140303800241001e0705a003404280002000c90b1030010465102d99030105014400411403400a4080d0102506c5030340f83d02c00014 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 475100000 1250 475098750 475098791
    0x5030a0215040803010909020f100f14031614041206050601080a0e06010501120f05010314061305120d0605090420040911040b01030b0a0303080105030d08070219050c0310 75
    0x7007520300500050101195000c02643e06603040078500003954160352000407103c400e02401250808150350f9a4500d039904552010009045600c40d120750314041d14203a503903407100f00c46541081521a1048a80358800c602d804003441380040800d26051300d03800c16071400c03201500210342c20358803282009a6541e20401c0344d500400c80701c07001c0c008402d01000762a102c00050103600d04000d048006150400d44580081d82d0508070381804202650b140d091010b01c1d0941003840a030148036030350100b9000c0c4095000010141e80010203407200041e003c1074078241c0e901101004803015107526003c207090b555409041d01440c49402804001179000c01c2c42c0d81c1113002181c65920442c90409140045400c0121100011004940008140100e440183c004010312194103411500c4600080704050300911036074180c0d2400c074111212294101405c850000c0100d40c000b0040e0080c04045855a42110403039440328494420b07034807451241004a80390032074842c406105580c440e0a054040184500d00 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 475101250 1250 475100000 475100023
    0x8070e040f030c15111e09010207060c0f0b190b010e0607240507050a0e0d02010e060702120f0d0905091b0c030c100f050a090b130503090d05030a02 65
    0x5141039112608454640207000d020301000103030700003c201c02c5038060540a8440f682c100011006250f1080d156004080b4240614402082c80d4502a1300031040d2600c0445c1603000386942414100100c2d00c82c9510803084a1410707460007900c1c00191031807500c03441041c0101040c02031143c0803c081b0141c40c069000707241072201100c2d018429840d200222202681c010315403025a00a0030b15100003040114610180e0b249040148540309501c40d00801c03d020356655214164039a03802004040503000d03400034041100c01c03d06945509044000c1c0c910103000034007450040e094542500d003010300c0094100081e400401410a003250040c0030310010302001c0da00e1108034542aa126402c00315080240c83d01311401003070000c110802081114041c003080350a03201b0f181d2034401448081d00b032640450040604280014510001074403038942e004d500900640400c1c0c030340f968510030014074000140c506000420404510f91280c00216030024840c20055603140308014000741010810b055 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 475102500 1250 475101250 475101269
    0x3041109070801030b18161e0b030c1611042c070323070f0608010f091b08100f12140601141306051c12050418050417070c0807 56
    0x44c004a0a6001c040c0d0340714600b0031104600035030140348145000f00300e0314564002544800c01040100c07130904401400d5810940750b41402d501c40d45201101e0000700d9020000c4e00b02840844142d84498001c8800507008900c802c41b0302c40040c0c040f905581e151500c403103241c168074040720100311001c094100545030b00c1001d0441070382117564240007850070401c010301e61001c1c0a010100c00c00280300350001030603003034400301040742d072280c0181866000b44528a031a64002c031000a0000c1c1900035241540e007040c01c218850a007030001913909000c05404084120010400829076004040101010341701c0502c8500c4580361a2400c15011282c0c80071698580d0403000040098986206004101c142d044503840b103603020790010340c4000d20141c0d01c0300d503001540705601c0904c0e070700c0e0850300c0142c41d00644c0d030004922001da42c252030500c1584145000d0603850100005044c82d02d600c001d0300720380b0900d001c10359110321164003401d503000036000b601d00d10440c070340c01c105064040140000808100c04c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 475103750 1250 475102500 475102517
    0xf2a1407081605040c0e031f050a1116080c120415090501081902210a060f0b090f0d0503030106080709050d0206030402091e0703020c07050d0f021003020702060304110907 75
    0x101801240c0441d10034113004c2d607111602c9049842c0140c01c80d04080c113000c0e0485401c200c41840c40f80b0700d0782c2149032030780a00345810080b464820180c000d17040ba2141d16170341c03640b4040919074001070b19411a5030559240000340704103190b51100f4002619000301010455446a04011030742514812024688040c89210345040065036085004142d02180d0a00014010180c400510010340708035002d604a0103410308140242c0c0b80c003020340301c1c001d035000e00003040038075114038031411003041a008030780b1a03140912140409250a0818844d0918040e20743c8109000603a10b8a107160002c1c0c04c14404202e06c0420890311680c0080104000c010848442904040c550045002d40c84050806070141120b040010300103840cde00d00283d13150744030300119001454010030040c001d410810f02c19903e40655200002d1618069406006650b0002207c00200340c0325802c1084c0003201000c1d81050580a000d2540587ea444014501c11805503c0c0b40882e520300d0f80402074080001080d00c000c1c0600768 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 475105000 1250 475103750 475103773
    0xd06060b0c01140f0f090a120306031104060e060d081303111302030112060507111605040f0228110102030717071b06050702071205010c08060901060f2a140708 70
    0x1c180790b600180b45c0c1e41d18071803c1d150b8901080c10400030300c41c0900017009044200b1036495151340030f13000b01e0340500043c0d10544074035420007050b0303911441403000040407400890154a41071100b064071074030402c180c5240c0303110050f415003000200e5109880803000344901f000d01c0d0910a404107640e182d1544114030b5981030400c0d404144808840c051715156540f80040d024070301500c0c01e64552440c4000702c400c00306190140c6800d01105000740ca00560404000320742c0207550f4001e965403400d1184528100c024a41c2e15010480303241c078055002c00c00342002207014500c0030720085010312a544c1d04c043e00c02c1d43c42c0d0440d420321400030700510200000d50094113070741003680c051440080c0d03100501086684403518100c2c90406160000c0024030350300d00101007003200550188500f0000c03511101020340e0382504100d0030340402d21502010412080020400500c1403a91001e40410710090702c545841c1404203681c00340c0501c80407603904801e41480c0020134800c100010007071180c1320050081c040c41 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 475106250 1250 475105000 475105021
    0x13020904050c2506060902030f090f0a0201020606060a02150a0923190c0b041e090501050a0612110c0c030f060106141b1c0801140a03110d06060b0c0114 67
    0x3e2203150400315051030350a100b001139541201d4018100c2a90035922401c1503000c085080b1000d940c1c1d8404c2e88106280e5500c5124003003500800150140c02800b199526801400020791004120908500030711154101d44030b0f0304000315008a00503000002c540300c0354901b030b410710042114040ca0320304c1d400240b048241400241c00e02203800100302103002110502d4000282006500040043c01c000701e008200c0c0206061500300d51405028681206a9540005012202c0030701515400c8040c20000380b1400303000e51000d200504103810700089088046401100b150050a190750310341c0c0110b0350410951808000b103940c110030403005482994508400a0b10025000c0c000410080000c034160b40d15500210180075980c011030182d42d062140c00340190340340b4100522090101d8402000400c1c01821340030030540e00070700944501150b03821611681c842942e120110f036804200b080d0305100140c2c0c0340c014075000300744008005468211007442542960030122107468a070707400c8000c02001e00c10303 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 475107500 1250 475106250 475106287
    0xa1406011a090f04020c010222260715081f0b04060e0f03121b030720030a0c0602011b050c0a170d0e0a200307030b07020c13020904050c 60
    0x240d40350703603040310380c0415810b600c021030f0325500038030108400c1d4407a1810b40041c100403485550946d080300a403030074500c41e050a4003c0382d0f060741040c0c0403092000780f17103a07041d21040c6844044414059640000e552211000d0070020002004401840b0700c0704440e010078041540c1c08076540b9492810400306180d6030003207114810401c50301c0c031101c03001500ca50303141c10b41d11100034080d103207203500111250040383d000401c03000180c1b54003800b4441440c0044290781000368407070703640d420705410400300a04406480b42084d41c54011452034000058241103008000d015507000803602c2505d00611054518490181c2070a0103401c11502106010218000c1c4111f548000c801d60000d40706140e491050050039807003031200d482d100d0003011102000800d2003140c0d1090306011080007000d01c12061300442c00540c5c07030f0950300003602032000407046041d4907800003451044440d00480100011004c070081000d031320016500055020880c10240526644919030240d00c511b82141040b0b051007484 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 475108750 1250 475107500 475107539
    0x30f2208240c0a1e03020c010e0304060e03030a0804020405041514071215090c030b15040305010c030209130b060c101415131505181009050603030f0306041b020a140601 74
    0x405110711320000c0d40c02681540c0178100880003c004a01c07118403050f9980e4858000e00010034604102d00c0100c0c5000011200b042000c0c0d5204101c68485509000241c2000382040316011801841c2082d800c401e4401d5001000482044808900704054050070703a500c0011070300c0829040c40f41098070080a001e400c0c045460714400000c0c5900440d40c110010110000d00350703480790901048462082062010300f054a00620003040030306c2000400340d0491051000054001c0c003c2080700d09070b400c00794480382028002a0546117080c540c030840c281044000301240a00d16a1165070960380740100b5100b0764052010303082d400110300007000065032211640000c27042d9640302d02c01d206010a09500c5000180000340c4181030358070459070b00700c0f401c01e402c89070a500e00c0e120000000b00d02c0010b00440b0b0103a140030b00590b1411441000140c619800208429003240d10782080105108030806a480990036550182c4040d60240c81c00c003207c10f000542d040b030a030b44000010701005095140c0c218a80 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 475110000 1250 475108750 475108787
    0xa120e1504051011040924140d0206030c12010902033c010e042a12230609120a0503060120010501030b07030b03030f2208240c0a 57
    0x1941c407403a180d807034075000d41c0c1500026800d0141250340d084e00d04019209a411030081408924490619100311550511418031540d510303d404228a80c0c2c4c4201480041d070f4060200360070f2464980200f043d07580152203c031400000080c090780c402240794051800b4000c00030082d40b840c100744c0038884080c10302c0031400c01181c29804a0514501c0c0c4030700c81105020f6100f0001d091036075901c0100502000450382175a104004c00741c640780101c10240c40c0307500182600e990545040c00d00f81c0307a0858000403803086803001d02e00e003e100b00c134010580442080d50301940091000f8500344030302504240c0c1d41551414a01c00070300c10382200303d800100740c90740300034203181500781e00503540350300c030114248846869195460400080240155904924072410140e18280f10082c0035000749643d07441480c1d44111552000c0c0001040d00010b41c192100d03103500c004030318101c0d60704c1c0d040060038801c000244074072110700d80101c100c1c19a240c19007554401d0702003418900703101c0c00107005808411040c580c1c42c4607 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 475111250 1250 475110000 475110043
    0x80102190809150106181e03060c0212070c03020f0603010605090438090106140706051302120102030703140405030702040905122101080f070605032701020a120e 71
    0x1a0300c010000b03680c2c03036488000d04030900d580d44c0c4006000020f6001511b10b1900b200d00e404194044c10400700d690090740401032280840c41d54403001c00a00c070900880003140280c8420002941c580405003180b5401030000013105860361041200e030308040c3d03040c03d02504040c8010064542c201081d80d21140c03041d900840d10386001d01e55042e0f06d02940003e0b42040410071f000b01c200702800300c900a10170718190788002441c0d80340d05056510b5030002c5040b00541104118030710000341c4d56000103400181441040c9000441940065960b50225402e498160360100401c032015915018603c07048110a0020080f030404d86c83c1e1946a00c00c112020b400f80d92920b8081c01081000c20182e2040030344518010307240e1a401e103c110a250145401a92403001c040011505140100c5c04060f81f4030700d5401402c40d82c6c0b816105a0f21900014840801c40540c030f114040c80c1801842c21068091042e030006944014540c00a081040d841400101d240e1078085110340701c034800141d1000701001c0ca40f902e6007 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 475112500 1250 475111250 475111261
    0x180d090815190b06040902040902030a050c04080c06070f02220b011412060a03150605040b0f0a05121603111003140a0f0b030307050a03020f01020702010813080c12090a0801021908 79
    0x11807217a80d00040d510380c8001000141140c0a40c05180100038044041c00542c84543c00401d5501941c003170601c0c1d94000294805551601d00e00a041892068060301045e29a5400281240007152681141d2200310324540c14112074501c940c0f000c162007400d21180980f180e8003526864080c01c840c1801070042c1801180c440e503a11240340c0015940510a1046d822850503454040d015510407107003c3c070305000a00a0919050389003c2d1076440c06000e0700c580510784020020300509114081d401c0b4042c4001c414101c0703964038000409075000720050489a031101050040090361006414209403a1505c41119440d40c10a580e401c200701036404610032034a41245030081c0010380510341d01d80700000ba00410080041180d1006e18003039002e0f84c0082d580c2c040c11130b00341d00c111003000380002c0050f0002010460540c080e003210714081c1c040182032800e680340c0b1618180000080103861100841c8039000c520b00040407002400311400250b0034288111807004121038090211000e00044100282 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 475113750 1250 475112500 475112509
    0x50703080c0118050c0307050a14042003040b150105030405070b030a0e03190f051201030308041401050a09020f04020a020606060703031b0e0f0904030203030609180d090815190b 78
    0x42c4a01e03298514183c07141c8407071600390b5880d0000740d00301d4040d008500001a903480c000800320200d40190411114a000c1102013000030000c00076420343c18030907100307041d80488010780036600c20340c03007040c6c0c030342e16800c011004008483c002c03140d00b0f041090820410000503400710f11b4800300c030642200c2c1c6480e40c40351148100503041e9100c07502e00383c1c400801d041030a070041044c9082032348066120030580c000c03245412141e9105245490a06101031b800401c0000c1c459a4141d5009000e0742c801685030844080f04c41c20340d582901c402200c1c0b81c0310300140d402d52600e00c1194030024401ca230218a00030070008080d4031244020302c0d80d0311030a001308840c001e0500a8000e0302180141c83c0d075a903150810041c0241c02c014072039100e90b0050550220281c0c0c24100783c0c41c241d0103240c0540083d41036a94000c00c000c0340c10001411440c2c0c241002103c0020303040c1c10016010301c40a242c481c03003807403030401c00c100b40f404c030780d0742c0c09039151880302c00900c407642502500c2103c1c014007003940859080341200119 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 475115000 1250 475113750 475113761
    0x9151742060d02031819150605040207061d1b0d020607020612010e09030a0e06030a061701060504240312090e071e0903050d230c0105100f03050703080c01 68
    0x280c0260002800820188030b40d0300070b42c46158403030400c0095650040303003d503580c85501c41705101011850050000305100121740003d40d615060301190147c1c0340c10200b01617070014501110150380703c008503662103498110442050b01103100501c0d0916075072200d8880b409407460303214003a0980c10824030944d142c580489505980207021070781e4a8a81c07801c444504202445081d001e10701d100c1c086071a03210044115540c034442c540e81c4081946200040042c02d600c0a42141c40380c90365950002030003000c0e804182c0c0c801032264000070b80325151a003444151121250080d0007581e80c8005d0072906c0f2140f800000c1a26085020b04c9041c03076017403030140c45017801e580040141c80d074040104680c8035404041058001d0040307a15512402c0d07841d42c00e582d040000c1c00018a41c1d04640001210680728040018640c25a40080300325034180080145541d401440c901c00355075114010090a804004407100050106070032480d030003440d507196103803910441d00004140c03110015450082c000c0c250000d = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 475116250 1250 475115000 475115131
    0x1020f040518040309090e0304120b070818100b0d020307030606050a0f030209131407080a0c0b070c090c2102030703140f0c030c0d0e0a030f11031801091517 69
    0x10502c05d2200e42801c0002810440e04600054dd040380000d0710200d507850b20b85104440b42004040515104d480d0001a003000504150046001c200311005070b541044080c000714069113001540f00e0404051144402c0290840c6480503080901000143c5900075020b9100c0c1114240003459401450000001e158005a124951081c00800314250101084940c45244a8032032400c19070b90383d00341510705028959010304502202c1c1c00c20050b0340c010350810284200d9900e000383c40424003a09407000118a01d5441038401d43c08010042859007511400b8401001c211061441d071500c84081c1c0e8943d20010700f00c9440d1b600c040041707202c814201059500a0341c04d104c06004203442130400580d5034100c600180d0000d02007019500550340281c0d0640c12080d4690041c51030b00d2208000c90155118020320382d41000b50391900082d602d101450302d103e0400c4e940e9110034098401c8078412030400c6011b098558149403e914140d086a40050400c954a2800c04040103a0315807081c400d5024400303104 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 475117500 1250 475116250 475116269
    0x2090604051e01031811010f050417010509070f030c1a0f031312030203090a020906031e06100905160e0307030b011202031b03031c0b0301020f040518040309090e0304 73
    0x220709161200d408100d071042c0280c0e02003203500c08001015000354102d0700c0c05003240b1448880400c155210740d0b015030f41c500f0f2a007412450550380b501080e00501d00030030007080d240d64a030b050046404051103c10700400306800e200b40e0241c11906c6000c0d000009102d24000c44c00c10580e4500303507035403c02c140d4030140300c0144c2c1c0c103440385071408070300720083c1170260110b48850074020002a1140280f099a001d4200c0340014404d940041c1c1c01d12100c0300000c1c2015070706125040072480322400800b242c11020030040050302c1d050901043c0103100c2e6031240c002e8145036040c0410015200c80e4614040301d42d048030f248c81d001c52032810001c28284803c0340c001618401509001043e101103000d00c0c2c0301c5040c400d808595683c0c1041d846040040c142040031541a00100006004001d0030700c09440e088192180010b00000d81d20002802c91b807000c805c1c0e00038880c1c0810b0030005840d084189400e0404030940181c0d0034078013550024071183e441d000340e44419540b000522440c0c00208140d4019111512 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 475118750 1250 475117500 475117519
    0x105030129040f060e1915020a0b1005120616050d18050102130b0c07090c11060702150f1312030213030c031103070b0306010f110d08040b070201020a02030d0209060405 74
    0x41158803144000c4c0600d00120f80851345240103030078085c003d0020701000100c11414181441c161002d803c0c1034049207000c51090b00d22140102d031104046a014880e110400c0103060f2801091003c04071000c00d400d0703203e40108040241407070440c01d072050002e00380c0c03034803549d50304900c602500141812000e42e40e860701b1541c0c1507010080154001c1184525007104601a107035100d20b024064814202035500981100100700708c1001aa0481c903002441814880e1405108485540ca00342d42251010010b0340140c1c1000554030030210040e402c06a101c2207407010340b4180041c41c1c80c1401580f0010b0100308101000f0555034442d5040d208002d04000a98145560702e0616003005c007103500050307450140c100c140d00701f61700c3c0000d00c0d8011079113000c4007542942ea0700801910545a50302e040700a009480d00300c0f0600141c10310600581e034107240ca404082d814641031000220700c3c0205582d06581c810820042a140c0000940f00c01e0111030707602581d540000004940360b4000e0354002038000300940d = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 475120000 1250 475118750 475118759
    0x912031605040b1912060b0409021e070c260a0b1009020c0c0a06050a0807050d09080d0c112805010b090c0c0d090e010902030402180a06080c0a05010503012904 70
    0x4e18903003002495964400c6006202d2200d6022500b07244504400c100c0d08000c201310322911a0050040f0803003500d003d10124855580c401e000f0b030311241d41254104088502407140c01c9068001e0046101201d50034061007031403e4840d40c2d6002240f5001c2c1c06040354400280741301c8248208100130b0051140e00307640740c580514180c0e54031000c12042c24400c030030b409000300f400d522640a445416011303035101031158681160a42c0c080e401028040c0d1196150010040400c2401000f031204e10041d1300e0000b1410010400201220303000c1d2280c540c00d4010622800b0341041c000c820190414503442600740364823440c40d186004166500c426a0070108400170024103120703d1024040b11020b010031b0b102c81c0d2601c03035030864803103d89000c2c0101400c6008014894160703903601865010f44003400805913002e105940d2410380d4401c81c0c08480789a118113040c054094248512400c682068560040c1c26081070000780c4540014090075220b49003150242c0182b9800c140300d1141d11402180e02c0c0c0e500d507141e = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 475121250 1250 475120000 475120027
    0x3070804052b1403272a01031d030306060901020a0b070c021311030103060e01201c051302091b0d0203071b031409031513020102060912031605040b 65
    0x90050784080340c00b03d500071480c8522502101d12410000000c0030001804255510414100942c104190301ca03a12480082c080e00030486940d03c00803002040f810350030900014151a0920030321201882004030180341d181000064a42000081b0b403001c0d00c8501c5640101d141054603200540100d41513020f0001154000c8079503181e140c002e4589084100c819a041410740d040c690110380b41810807c01000400c606a02c40d0260007111800850114010341030304003c0c03403890107150213401e40010001106102441e9040500d0203041b018041840c0a501c901c121400c44e00000e80a0500c03040000c500d4202c10259000881c5c4200d5035a803920b40040c102002508200e42e918003143c2c2c840b0854840d41c1c005007010384039540c10750300c05c01d1948240f414011643c00000140ea0503105404a0f41c0d44002d501032120702c91800c54003000d03a0052980002840c041c409801041c1c941c21180d00c5049503100d001c1141d921400f6262030b8400800350b0300f01114148280e0707120017160b010204144040092 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 475122500 1250 475121250 475121323
    0x301180507080f040f03200c010906110a080903070b03010b0309010b0405040210120b28290703120203090c2803030e06090d0c0602010513080307080405 67
    0x40010800c000c0d0381e510802d4480c2c82c0151500c00c0e01041030400030b4005051200d4540d0302500c00e10340f0703c03403108160b0105140b2034103102160b802600501c8080240396130050f4403000400c00307032404c842c40c046040c02440d1111130703900c4090a9950001000310b6140c030308001741001007034882c011036502d6a4502c3e110001d40c205132034800e955401c014106425207810702900c4d00440c1c00800380b80c40404007010540b08d0040880612000c2c0d40c4845059503150f0311000d1188500e10f0301521070044821002c80c0b130540350f2007500a04142e01c01c2d04d4074801f0000b4003900f064190710417000104ea81d00d07800d040c00e0b10206011031076808020300020821140c50b10110303001e4841607060380e2280ca4407640180120b0750340040780e40d03011058043c2d0340c03c0000c60b200b0301070400e0006014251924040761440410845001008141d5460540354000c000081d4248542070744003044608503070b00e41d0b10030f944240d000d1101a00d1807040182c42404030341031140038019003440c5248c030015410111801009016640d0 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 475123750 1250 475122500 475122539
    0xe090c310b03091b06030606090d0c030b01080a05010e0d0228020901170c010905100c0c0302150a1d06041203021e06150402030c1e07060c030212070c0c090b150301 72
    0x88202140100c3d90034041c060740e0107941f00401080c14607800c1e030b00b0311502421703100c000e440f40c40540780008003003407020394903901a0800f1405040c00c0c4038181011400c0d595152064003e81e0711550100f0075030303540407440c7c0b03110264000c000008412103505a0b280032501050103903010303030101c00004204503140100e40c00200790100751000303014240d006480f410781d04e01c9925045450114611082417007803100d021058802c800090070345840b50040b540c07801945100300a601000104003507000d4202a0000500444000000740700701142c01040c5240036074410030502415008100042500070b01c0b044032400780006032104850802011543c0e144c00a451000225084000450090906000300d901c10312000c5081441d01040d0000c1d09520302100307140304c040d18401d210311400640300e40243ea140caa035a960240e2200d02550700c41c00c40131800b49c2a0418071400d0703280b1100098910046104407a0044800502220a80701081506030b4601c0040c050610000001c00c01d02180090080c02e02d = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 475125000 1250 475123750 475123783
    0x2010f0903060e1006090c0e1c240b150409020d0f0e070501110304030b0612071203080621060a050712060f080606010503010b071e080a0e090c310b0309 67
    0x343c6c3c0e2511602c04a41111026800251964900440e41d0a004031041c444011402e00307881d03146000c3c0c07107140040038900a84011002076035050301c0984071398003c0340c6807040c0c101c80c40da04203a107204140c0307102e215070302ca0480019008074001030641c20310382c0054500c90606100340401c513282400982c44180318041ca030301007000c04c041d00012040020545040e681e00402c6010325407211b90070801242c0c41c4449604d181d100e0840302080030302920030400c3c41c3c079200ba2505481400d042c01040310322031010780191500200043d101401c501c0c001407a9403c040391450028054541c0c8408882850b400d0850000380350400200044243c502c005400c125a070300001e40d0341d00d4550400440303945c4002e00c1030811102051006101142c4e005d003010f1101c80150103071b041492101da540290a8001d200d0620104807134012030080350070a0a1038951103800c0d180f00511706480a0740c100000403071841d03482c0410454000114001e1b103801c0c0b00d0300245c107924200940320f180610f9000c1d03490020b080b821010 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 475126250 1250 475125000 475125011
    0x9150a080106090f1406130b0c0d020613030509041401060909060b0a020715020106050411030402040507030905070603230906091b0d030f0c060c021b0315010302010f0903060e10 78
    0x441d48201c80e4082a51130800c101c044082c034004101016488090071a980482c0411590801801e14100d0000601120b04016111040c4014043c10b1840400000d01550040000c1204240385035580000c03085d030605220782c0303d80c00c03080428001d200c14140c0528a0110030004190190010308c00021181d5006042c0002ca8440c003180326240950315806015a01c00041444200d1041d480320609078118030000075174a50322400a0309035903150034000150100042070000b0740c20680665988a1395504091106448a0383d643c1d81d03904462003020105599030b101c100b82e824080d80d03d014050b0b0701d210b0848260801d0304606480383c4d41621004413501c240010301c00490590f40842c141c54030003c0643c2c00c040340c40d880039500e02c05505e01c05401c00c012a0303070364400280e55101d24418134040e0740c01801e001241c1c1400302c289441d0000c900d8803d901503241320304251250295903054070303820318054101310a655429a1b00d010f0035000204280c2c1860011808100d002843c0100d058800304103001 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 475127500 1250 475126250 475126259
    0xc0e060a0603180b0712020708070311030a17060a05040906050933100801020a020f070605040b0d0914060a090309050d03120b0111010e10141e0c09150a0801 69
    0xc581400403410a0311003e22615408100e80303200036903020718282440ca0040c010004150100d03400010211140c034800314043c014503901a26203100c00c00705400540c80d0803446500901400c036020441c80320301c1c40910016110361151201078000305070260080c0b0801289160180103401d044032154058454009100c50100d0000c9103240a0180003030601c00960b0b4600401d658210300600440e1030421204002882850901c010203000300c29a02901041c40c61010713140c10034000e688620104201031006000c0f28281c2011524040c51501d40010b2482d124540042d0906091004503140d0044004114035142c181d006902040c1c030a50360300c40080c1d150b03030802011407500c0d4800f40005456148a0800c65050b50200c04404c1e13050401420103100a0401400c1d207141c41621b11032074106409058511907075016500c0d00185a40082c003a914146404080c05001007210191003a1403001052030880070301304807001802e000d01008503442c1c06011303c0300300d82d011071402c01c00540b10900006 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 475128750 1250 475127500 475127507
    0x60b030c041e0f0b130f0603080a020f0f0708070e040f0c0f0e06061207110a021504050102010501080706080f19060902090111060709060f020319030e07091a04050c070c0e060a06 78
    0xc0980130040c01405044014500c0e60001c003c150303003030b044240d61190040049028038001e803000602550042c500707280c4601c1c1e06418081c5800070004940e00114003404a43e4001c15004159001001c00411580c1c0c2d5040450410b51800c0000d04420205000411210680002d00d4161282140c4a079815105d0031301b40003030752046842c400c540000050108520912074800ca29106410a0444036a4440e540000e4501c0318100b0b5190715907000081c080100e560203009950050850001501042f45003903405000810001c0041240c000d0510008a4070304190031380540e01c4076402c004021054460b1001c40080d0300080840d800314603000900c528141001800340d00c109070344d03903408950b20300d800c0c41943d141011401340300540c04140803400c410f0342020390aa24217401c81d500401c0001a545211741803009503000821303040d00b0881d00d03060ba01074030110800c082c40d0a4030000b80f9a910940d484031980038204006001c4a03074000c0000f010900c0d12401c60080c0005c03280e0f402c81d15500d00059 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 475130000 1250 475128750 475128761
    0x7180204080f19060504230d20070608060303040b0a0216050f18060103020c2b08090c0d02010c150c090b13090c0302041203080405010c051204060b030c041e0f 70
    0x10848050f9000003030b0000c0e510380c000c150460700c510300382d846980d030310703038103020099204140d03c00c0751b6001040c09000da07a400310a01e800c074100f00c00001c01c0c118202c10b000d0f455160300c2c040d441c1800001008202c0c90745040040310004c251100c1500d0b2942c1110070020b490f8502e1150034030701d41240d4040406c461a00c004806005c903402030440c203042820100391140f07204000d0265040c56420b2101000b010030900c1605041d04840e80c6540402034007900804c2c81d51000c80c150810401560100300000100040706c86e40c0c41d0307003141c2c0d8106103101440102c544882c1d40d400140201302500300382d0f01856454000f00e17030b600c5082d00d894664944a505030580340c095500d4091800607504010890b5201c00d5200c1501801030f8900507103400e40380c0c4035404a0805c0c4000c11400a9954070800c000d126083c45540c4004010b45001c81c41c1803400c0b401c60005004c00303000503200a81c0c070031007007450341c2d410058032002410192040c882035161214041c0c6c2c0003075210054240500744140740030780040c0c070f100320b = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 475131250 1250 475130000 475130023
    0x5180a1b090618050712090503032508360105101422110304302a12020a0314070305030403050d060503030d0b0f0405090705100207180204080f 63
    0x31a5071440c03c45641d0009803001a08003400c0c07000c030403a179081e034015074001da801041c007550040d6174a062841f04020060880c1d15003414004007958903040f09a848446c050f004010350402074130141e542085030300c007141d180315004480d11220302000741810041d0807040c45006a0a10100013940c5c80c1e0402c802d00c21100610399002c010b5030054038203d401100124421600003000040660400032980b4441e07109840513203405c0007010030803149502140b244071035050740242c042003000b02c4da4000740070041030f50400d1710030310441c102c40b521449130038085250300c07a080b88140300c01006601c0040e440b07405d13030181030300041e921411072000b140d031a0302283c201035850b58803030303103540d8658504484c50340008028600303150f110300b000201e6950070805094100722840001030301c1ea1030601000316841d84012410701560816040202d003c5010900e8400c90714165103110500d074600600300c2c1012803e0308450030315100400d2282a08000c0c0e8094002d0f66068011202050407584a42e80d969004064 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 475132500 1250 475131250 475131269
    0x60b070b0f070e011e030e0f01020c2b0503070e041505010912150c12111b0607090302010302092b050105070216090f060e0a15060905060d05180a1b0906 67
    0x4210940c803200b81c09170704e50b413999180015540340020300e014140500b010005401d0b80d0046400c0c3c00380d00d018090500404042014140f00903044a040036401c0040002c0c102801804000209040e0065403601c10b42032001300104550641d02c0005520764400c1e0180c140000d0100d54013207a103500204020a09a070400c06c1800c80001407900d210260060302e80d86010002059917929900c40301340103010000002d130a00c40c3d110702400072203000480c04083c002c2459803001c800e018246800c0b04005085e20b40a1030090b80d01c2c411100030420b0100120410170b4645500c228007880c40008480e0425400e200d84000c0c8099203c0c803200301da580c511542032002d0038000110800c0300500550180c40711220100c0049611661a00f1154003000229403400c003403510752010030005810905140081d10460600f01c14107800c04021034102c3c06504a0180456516000b2a02c031144000c0e29031000c040040c1140c000e4101d034603003880c0804684140311592075120390003042c0329159014410a4820000 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 475133750 1250 475132500 475132517
    0xf120105042a140d021005030108060a02041d06040605060a0320040320040f0e0307120801080a060b030c060301060c050f0613150b1302070b06060301030314070501060b070b0f070e01 80
    0x103001211115140c4191988a1358013101c1c900142c03a0302da2603008000d003644900e0346961401407030714140400107021440c044e00c104010301c00580d00420800b40c1800d030f40b41c103106c01d640382000f1400910044d0000d50344402d004c1400d00d24594142c0001000c07050030440513510300250a4010194040c85c00020420b00f181401440c0391182d06031802c444900040010a8180c1e80e10f17032503001c807801b0404c001c196800001d0320301c00344184d0304000c081035066450804242e61520344141c1d222146200c0081a40340c0760820b5140540c0d00300701c400e41c0700e807000740520350b00d507915540508203003401002243d01c0e015556038101e03000c801150362403180070000401c11940c00550b403540c440e001e210070704014003607499500280740d886a40c1c01c1000e50030040001a540c1d0a1414101c8605c11300410961184404000500000b5409140b0f805001145c0c1c0f14261105e003189007140c05045980c0105c010b10300041181001e12000803c030074000c0c11111411682901e8840c030498036a0710003080140401d5011 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 475135000 1250 475133750 475133759
    0xf0901120209070201020d15140904032309030706030b1305040201051b1c0e0a0812041a071a06040b1225030506010e0a0b01020613030c020f120105042a 67
    0x30b4425400030082c8001071500c3c10b800300203000c45000340702102c1a65240c2d0014803036010024200c29090300b0271900d0045610302a41e0007400715070010300c48580281005081c0785d03011241401d4540c1008004c040d1801d00c0d450381c40c000c00030071001c003000c1c0c1700d03040f403100d01311300510755201e00d90096130180d4400703180900c030201040c1c82591060700b0444500c80c164441500423030742c01c101c0d18101c41c141c5d6003200b20010881000320a0281d60070004007500f0200308a2444110082298103c907428000054010310f0f078241080c81c2c0c015142c01030002002c0312110041c0c031042d5080c031481114115001c10440000f80d090040c2c01003a03205210003944035a02c20008807509550001c8903d0400179040c0c14a5103c0c1c0d5518240402030380722280d4071142e07900340b02c4001602d010710034076802c080c4018941c601c1d043e2011440030800000140074000c0d418016010754990301316a81031744401402c15074101075802c010303074002e00c01103c056420301d02004800e0100c044013842c2402c8007010f6800928881c4c10b2 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 475136250 1250 475135000 475135009
    0x7050d03051c290913170a05040305150402010f0c050115080f061e0c1305041b0f0806060409020f040e04080a0e0a03080d150f0902090f09011202 64
    0x4000140e050000a004070042242002e1488807038490042c40411201c002d2000015030402c014804040b04089030a021003d844020100740c0c007085c0b00944410405803401d2001c00408840d401076484240000e9101240f0340000c01002183d204200702d034104035400e54038402c00b4801f65070003400a0090025034105c10701c96101c07504514080c4000140559074005081c545904540c4040c80f02e410906440c00e664106211141d4010728003070b4811804000240d4000500000038410f0505440219100d4102d040181040340030380740c041c0c0108001c2c80c001340400035491240d09008001034040d0041414640718176125805070401501075070170030b03040203903030710207508503007a189101101404000340c42508203201901960042d03c0751961400c03210f0004100c107000240312801149644010000200c40034101c0300000c060060020320f101c1025441c885528583d400403d11180f49000400c260000e41d004101038036048400d04009145001401084c1038248200030503e4000070202001d41003 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 475137500 1250 475136250 475136269
    0x2010903170a0e030309070e060301020406020a02060703020c0301181b0f05040c051e071401060806070c0609050607020102130f05060409050702071d060f010219140a0206040311010906110705 84
    0x790810003048400340e80500f075245801c2101d41d528a584851420800c0341c80e5900c400e5003111041d0029880c0a02b82140a0369446e08544000d000300c41c001120414540b0a02a031041c00c10010020300120054800c0700100007884842640d40c842d00500440400c552000200126102d105000320f11510303043c1044000d0071141000004c2c4a006c000142d010480e100c42854160b082c00d0b00d90b6220070703c1e4140364080c1c500a0212800a078500f041c180541c0000040d0785610911510f4044001e400e90301d00007001c3d002c0c50000030618030490040c001c4071a01900a001d44c1c0640604d0011260f40c1c4441c0c50000c0c0100f44a081e4021000700001d0000b4116604a0755000a6034011034000c9540c405030042c1c03440c0d801c0280900344840000340841481d0000c070400001d2401d1004041d145141701c400140700c1d0000d4070040c100003011201c3d0100c000c06100e4503003100c0d0000d00c0c031501c0740c0da2400e00c0e2007200880c2d000d590021b0609040401c0780360044001d018100213080040010303905082c240070b40d910 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 475138750 1250 475137500 475137511
    0x90117060411130f0806010308030f04060e01020a210b1302180607050c010201060f230a090f0906051315110d0608030d2a05030a0f02160c060201090317 67
    0x162207210074202d00d003060005100d003031a11020000e0b001e160107980c48060741c068110917910b81003800100042440e25064a810507050709040700151100d01d0f2810082c142800c42964550000c02c94200c0e403a048500d00c000c0c1d01c1e450400d04075506491440304200c48400d2402c90303006500d1003844420345450740c09002c0d0300c05600c06d10001c05c8d94905c001191500702d14001c5805a00001501819590a004a4005091200360200180d06040d184040f03a100320b000b0401c035080100100300e960340d03040340460044c80000e0042200c0384404c20034001421044000b40c0d202821301c004241002c100350650061079070080040a0f9104080101e00d0203851045980b4003c0c400510000d003174408984038050082408400855461044002642c282d69850b81d55041e14000718204c03162840305a00300c901d440106241040e40c03950b8200a00e0700811252003142d4240c0d2000c00c1c04045040000c07203040340d203402490b91a00360f5541c0e510813826160030401c0180056031000c22001c2d00c6071034080c03064101 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 475140000 1250 475138750 475138759
    0x203070c08130503072d1206020a091e0504140411060714031605012417100204080a0308012309060f1f030c0201060b07030c2103060e060609011706 65
    0x81c3c0d03603040060301e0441359400c03499498400361420194409000840d4086000f408006c00781030b468171210040d40095600e014012603000a10114158410000304014024400689410b0700d0910445403450600b4098940941d1411144400402c00703065000d00c1258008507a4020070324240610583d600300300c40c01c40d10200302030f076080c055500600241104210003200c0000c150810f003082402c0d01c0542d00c92010305010003d100c100841040001403d07103441d42d16191601b050908603611702030550403094440380c404500400c040c080401d214980500030390f02c07840c007030b600d840b00c035004609016411180309070f00800c1c0b80400c1c1001d007039140d8401c00040000d4107010349000448c0c6500748454100c2a4080c000c48665001505482503500e109400e1008002441c1018519032840c801c0d00c2024041c0030901a040e4204001041ca40351090214100001842e92085018000e0400c034040c001400321320500290140c200241660020b282c160b480f0b00c440700494a00f2011036030040c0c51160803 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 475141250 1250 475140000 475140037
    0x30501290409090807061406180c04080f07140109060c023f1e060a0513050312040b0106050f03060d02150a180807060f030b1c030804150203070c08 65
    0xc02a540c030400c2419402130029a545080901c0e00c0e604860341d04120f0145c0321681410302032280c039619070032280245666103401064032401406903c90140e81d0120304c42d8400d44040014003100821082c0468030203041498407504801c005407a00d1426009100000c0c2c001d8071403c0141ca004603e100e0020007510200c4216007039006040f4061440b03da440b0a01c07000ca200448400384200050740c0041005047d00311104403c0c40800d807070300400b17040080c0c06a00c0e0030116607454803000014044035800000c407542d40ba01420580107940044500f620310200810000564901420441d02c11400c000c4000c3d25541e40c87c41003010300141c02c00306030380246201d1045880401190010000e24925484644c0b08010b0590256903031802a00451800e0700300040400005801008489942c08641404100b10340030300089007411904156040281540714114411b01d074100c013110b4055801140d9040007410707540c00c804182c4c8025901d940000c0c030008400c0c4049030f42140500301d80c41100b0080e02c42c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 475142500 1250 475141250 475141259
    0x71115030403031506020d140c1e0a11010201150501030c0e04060b0408010b0f0d0b150a03060f180b060f010e03060108010e060f06011403070507050601060801060f0305012904 77
    0x1000e820440e0308402203a0b8410501c03103520f01c403c410070000c003001c3c40104101d1103a035900800b0720743c00807004825440003091140701700c2070501c4424801c1d008007502071044403400b80001d64506a00109442c070000018581d052948103000300000d149114000b80485864040110003d028038500390041001501c48042d07240d40758000c0d00c004202200100c0d441c2d504081000d0b084035007286145100714030000204c0032540b55038102c000401c1c0c100e10025202d035030340707070041c00c05480201425500c40040a804010000181d019808038047c0d40810000c00d20004c40f030a4112145c440042c002c031100d8400110113141004800d4030250040c9040d81c8003000100110b0301e010400c0c2c03c80030440e51183c1c1d000b614a002001400d5001c0e91503404400a0700f040c0300080c089490014880d90704150000000300080d002c0c50442e003007071350310400720b45081d070f581c81d4001d000010038003441001500002d44044017074403a0245a060b2441c00d1300c9814508840c048000c00401c08000e1803420080a01c400103 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 475143750 1250 475142500 475142539
    0x9030a0c1b06030606110102072001120c030204030b1315020306040609090501140c041a0a030b09040f0c0519090209040e0307030f08010905070c02011404230301200711 74
    0x2001082c0c10f440108941d0300b464009041120510900003003603105001c4000814401d1a00b0b0b00d00c91030600c1c4055940c101000100c07040803e80c01000c1c156410550003003101581070b402441100d005880c90001c03500ea00c41c0c3c225040c90001e001400345000d16400b203119034000d600458000c40d0040c0001031965407000c14200399001032109450595481c00003034210009032559503401400740603c1454103060024030b0303082c502d4221003031400c80e00100302c0700103090007a03000d030b034021f078008080807160728040c5401d0114029000003203411200d181000074a904001d110707501005001c5040725191030070702ca1ba41d0000d40141980a50207620b5040c0702100c0311040c801800c2007030081e40c5003030310303d01421070203020301406a001040c1da510304800c0080541c1c1c0160350301a51076091030701603080808000310986502440d000403141c0b00640000703136459a455003140012440a4000f0321004003d10071800b441c0f013280d6048072000740200310040000d0115064030075800c00c01409040140311004542 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 475145000 1250 475143750 475143803
    0x4030c02092a03011a1312030e0603040f0501060b09010210050c04090203040b0a180201050d0b04090203030409021b0c0a051c05030f070203190224070210200609030a0c 74
    0x81c040b100000041c003c116000400a101e4450034043e03c4c035180980b41d041c1e514429038482d03030180182c14600001010311901c040015040000c204c20386038145400c2c104c514483c201d00450b4290710300b000005400c00380d28242c0c1c8459105030041c11044001c183c4110140100600340e441d000c1d010000464281b007a88051030060b030080038119940d18250070424200d5101d00b11003401d80e001160b03460300607a800b400322222000712034000f003081e92881c000305001e86011800294540004580460614000d5014042d00e00c41068000e07404426826040e4960307118184190300311134a66828482414144d400c035880b40e40c0f109400c1042e12545c3c9940d42190044030707100c181c5600024044041d854104000103240891008142c1c200855600080030740d110707581c8403103221400e43e5000700310000020a4500c229009030000a24900d101c500826401006007000c804a0000301540d4a04500241040c030546420b8000d6142901c090b02c1a5050403417418220f84c0e06138000c882100041440040 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 475146250 1250 475145000 475145071
    0x3030522050310052703040303141b06070306090e0d11030706060f0501080a2a02070e0406050103170406090e0a0b0d150c0f02060402100306050306010b07120804030c0209 75
    0x342a081c0301d000f1255040100c5400c8510f44100d207850903005e07801000322800c036503150400002807a070700c040000c0c03103025142304400410449034400000500c0820f5141c42580154bc0c200070090b241c120702030862346800800c0141da0702401c031030b4021601a0f07038840c084908800481c2e0521105a69400a40b031b0140c120103581c81940740100b18550700112400d030030034040e810501140ca22100d9020300c0c001c51145a681c05420008034028003030080c044800074051030850496a441d1074180440604420f204c1221926034800b10300382c0d0a07241c0d000303641c03d03540c0c1a540c40b07840f84d240800c2c1400303100c7c000d060080340d966609421480c903604d4041e01002d16115411514481e0000c25181d0115041000d014082c040c1c3c00c4140e102c850382c0410960b501c180d04813000300c100300044204a000f00890380086805104020010031018060390117040c0340e500c60034007922074861951045400b0079090310010b003c500e0700300f10b0400602c2c01e1160340e030703008911600c42c4c200400210213071000c0c102c82000c1e = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 475147500 1250 475146250 475146283
    0x40c090f0b040509070e01081b370e090705030403120906140601081005060c010204150504170703030f03091a150909010501030803070c15060914060901030305220503 73
    0x42c01c00c003500340305000a070700c13041e64207140c1402001d44001810b80040207100191621600f407c00c4084907d00040c0c034200f010a40c0700c5501c00c81c03e07040c8005841c11104415aa1010540140e2a054840d1007400c80d20030000d0702c40401078488120642e05604050710803000c0c00540551511810140d109080000780221408940c84d090145005045000503003680d042003071910070444440d1848050300112a000d039a03503a615001d5003200b0f40207003ea50800100380b00580c1c80c0340b507075a074024003510948900400c191260590b15901950f1001a440018040780c04007604a401724041e50000d81410300402d01071b24900070182022146607800ca800f81082c1f150340300c64107917a0800090703103680072603540300070401c3c1c0d41140c41c1c1c00458040200001b0820100001f03410402081542d40c28007040d4070881030001c29202c0350300380050009211202c11007050800020314620304010300b10704807a01511614585120300c50a64410250345102d103038034084200000941e52020031144102e03858400 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 475148750 1250 475147500 475147507
    0x3150907051f0e0a030b0115030207050a210207060e1c0c030b0a060905040203060414101e0509010209090103080a022805070510020303070c020f03061f060507080405040c090f0b 78
    0x30b4000d802940c1c61010280074552114040c8006688040610705440b0002c081c0c081a103070100c01100644241c1800400c0781c05204c203220f0410003c0004441c0044444120600049242c0303030403661901944100300c0001d00307001e0b080300e141c14201015120084c039001e08005245682d15001c4000c50168012141e001140d001c0060440203441180064540301205200300e040c00e40000380c0e500030241010700040300b00c841142c40d41008207c01400d6909100040c4100d020025060324154845ea01010b59141804005007141c00107108407442d460300205108550703401c54503644202d4108442d403806622440d000d4504565646441403548005200c003d00c000c101458a80e0034404503910480c02000140135102d42c80c0d4011040d41d51020303040ca07080007400f00320b0002402c401c1a1801007a090f0250b0303014804500313010260030001b201c02c8041100050b0340c80004a606100d400f001400442081c0b2040c0014582600180751600c40da1a005800b6900c030b0b040d55a48404541c041d132640d0301d000 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 475150000 1250 475148750 475148809
    0x10c09051c080d1a10120b010926160b1e040f0303050903161202100206010f05130e031b0c0f09010905180d200c0315090705 55
    0x14061841c0400c07008400608801199840081a0081450281d42035454150094010455140594070024000c000c040c820b90380f8840501176040c04c0140041c020709240c601c04a42d4015003550703040741d54030340f03c40b801e00e9010003440c00e00c0f50006502480c0c42c054200c0456091a1011140700506200000203a403a03c900602c0d094501341303201002c00c68101071000300518805000041c00312034041c10010b944000e1500020f0030030102e100910f0728080040c0e0089032100a441c5800145403081e58106956408880d0680c0e0341e001c09d102d06189202003c4082c4402e00b8921180440490854000f2440c8a0340e01c860504640001051000f0035044c1e40781c901044800b0086610710038000c0d07030545a000010000319410400502981b440360303441b20081461102030a1450911000c90b40c00d8605d038400f51311004000c1c030003810100742e06480703070780e01200c4120020034940c2a6810040041c0310030315a804a101601200800c0019140900080040e440d1500020071220b8030781c07002e0f105980c8888 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 475151250 1250 475150000 475150009
    0xa0b0405150319080301060f031806090b06031c0c050109020a0e09071e050103020c0f070b0d140c0711120d0201020a0906020604050a02062a070e010b03040c0306090201090305010c0905 81
    0x5031a01010210f82126107004102c42d0f1003280e040d60280c2c0340440e4003070000d100640281080040140b00304465178881024003166a1152041d035101b402102415180d00040583e41c490080d1503c44084225948019141c000c00751904031030702c80c13000030030149000c0d00001c00d080c3c110f901a0001440400030080f0400c0305101c1403020704114101822a6802007085005000040c080c080c103040c3d0000304443d40704410004002c200b03504408503500c036074480201020a4000030b02101c1050b003040601c60701380c000c840800d88294443e1030b903941000b080340c848038550b00c22000b1950304038484001e042c0b1620810710003803c1141c0c45400250381e5180230200101101d8242c5d01c164215008002404005030011a103284443d40480302c035500c5003008a0b5090701101d0004410712000c5c943c1039403000d80c460201d80c280c02c0b60048602c00307041c0d81c0c1c5d52404408600c005c0360018071855010f802800054110b5001c030030114010301d0b140f01540e03100e544550844044540820200b901c00b60100718a03e007 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 475152500 1250 475151250 475151263
    0x11401021225150c020c031902030a08090f090103060e0c0108070f0807050c0d09030c09110d0f06050d05010207060b01020d1409060706020f0309060f040b040204050a0b04051503 78
    0x80400340c07986415a442020704894004030b0101c50203590484400083c4001140601d040d8940c4600800c45a2071296001c0d6883c03444042d003500034004d803150503088940e400122104e00e50080c0140200a807195150340240d03000d410803940c0301c1c4000d500760394240c5548107000d003e0351158000280804080d842d0303a1611103801c0d0050304002d9940204aa0340b50b011201c1c6d04221000d08000c0c026885081c0140d4840c001c40181c003001e4810720111034001644030900c90116401071118091844e02c82d902e1405840c00c803c0d0180c1041d4040040780c500d401640d110071003c00a02500194050b2110b00080f022064940240d465039004100e02060007264450070300c000c00240000d000042d4001c4001d08016132145800a00c1c02c1e011400f10b415131245021070300001e0b40001c04640d03030a944013500101da007081d500c4004602c1070800154400d805682007600690f0410840c14080d5101d50801024000007460f180d034994540e05084405d84480c01564050f640b40eaa0007124501300205040c5401e4 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 475153750 1250 475152500 475152523
    0x708031f09020403171c15090e0102040b0403082b0506030609010b030c0d060b060301030629010c080a17010e01080c01020c0901050111190501150b130902091801140102 74
    0x148100070800010b60360304c50350303840d00d240d080c21a40c0f19454000f20390a0a0501d194a616160801802d101c5203400b0187d00015241805000c1100f070f8140e8420900b00c0c003550103a080c10910411042c008103814a0140c2480c410300c045061400a46852036114080c441c011510116202d0061200910341031000540c414a001c0080111101000000c0c2c2d8806c075010340381d030180c04074200130030034854036401c0305440348406044155203503075038505400109030001c100e102000365041160180c0c000090405030070b55050703541c4111020f0341d8903942c910341e10103209641803200700e8400c200502c1428940e513009147c030391062207031341d80343c42500c90421051400d41c50440d00100619109a902d046001d41503940a00e40051400d0000d0b4140d480c201c80050400d100d4211000d03a0810000150004000c041c0b91038004213045076a11040880d40c042c81c110001c1c1c4d0582d541d004d1003982c10990107003011203002009200d162654800c0803859580a800c144a16494406a0580c9503010003401040c1d9 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 475155000 1250 475153750 475153769
    0x15050a0e0a0309061b0506040807020102240402011d130f0605060a0503010e04020d1a07030b0d0510051f030303060e01140a0b0304030e0402030703090c05120c060f0708031f 76
    0x20611a40c00a122080f58050003092058182c4101d02141a1082c885207095008044500c241040c2c00c0100c695000890128010312420070b507014542d0000f03000c4e10034001111030410311502d0b6540103548030f0318507400440444484901c0c2d144660b840301b1102e490101c603100001512104200980f060b100150031042c0142400c04c00e00c04100c1d03200048034112056129a00c0e202c1e200e6100050440d4500071000e8064850314503182000c00000720818014200e42c0c40420881c5008800c0c071001180c6048081c14a0b041041c1076072000070315070403940d80b194140140c140d11220340d401c0c0000403941138005500080d660f59052141c203400250342c031702500e000c0749156004809400001d000320410f0240d892040808808034003098098994440780c0030009109546a01c1d060710300600030405800242d0398031540740c4000689091500c00703003e0900c0040058031040811006000c0c06900176085001e510b40204120300108002d0800755000d00c1c0c0d61b4030030455090014662071043c500031b0f005000503 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 475156250 1250 475155000 475155013
    0xa140c10051911190606030807080316170c03180607030f060f030203070302060703170c0d20160326060901080304060203030a0c1205040501020a031a09071b15050a0e 73
    0x140c0f500060030100c05030035540d0303020b8400303070700d18291000c2c00c0c95600040422401040d44000c200c60880518462220b414005100d00b50758041100e00300784099541e5401140320000c01c107000d41ca0002580d119418860a401a122140c5070314a00f00382240e103a00000e507140c20204020600780120401440f5803880705c140a42180c00082c0c880841c2d00c0028803a50001a001007014000c460b5444000c003184400d441d0f0780350140506849901c254031910701c0304e01d45000d55103219a4224005250030f0808070050412a2020024405081003003041c0c05020070803a041c0040100c0e82c0e5003c20040d41402d1030240c50400c003062214800042c1c00a040341c4d003003800140310855000081c3c80e40518605000324149820103002d4404407002405021254100320402080c01030540060468a080b0340d000c00103004541d0001d03103103907401f400d4a580101d0b20001309084900c610540302103410b80c10b1900c8011402070348e40080310341c1c584021018203030b210360402034050030511442c87e01c0344560b005482c0 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 475157500 1250 475156250 475156277
    0x140c0d03051608060f01030e0f0102030703060302040b0d0f240e0a05122706250201120e060103060e12030f01030203120c1015090c2a050a140c100519 66
    0x2017008202000303d0400d603070342c030f850801c148081001d40b00084401e0000c41d5281444100200a001c4900043e030065040c200122103e00380400307901e0f0300c1c98200c07000d9201000b040d070303035180c1c00070000100b1155003c05128590316540302d4410080b00824100050072400014a8010700380500440f2840c031444060141340c101c40a40000300084803286045c800c039001c030110000b042c5014082101152010860400107a044000341141c01c09001345c86205824452104140a450442c0d90600040c0c109600400018045402842c0c0700c401490076114140000203490900b034108072442d014a400c00001007040d070606100942504500e41422071500005000d0240e543c000340035499815940c68186090600000c0b42c00000b509503803109101c40c90305000001e02c0180100d65510501e09015128103c0303132041c035100d1039204d5102018007000c241940321600b0b00c905540c00300714503000324076a020701d039540d0252424031070603917459141c0c66821082d0071205801c8101d1140b01841840e492154 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 475158750 1250 475157500 475157509
    0x6080303151504060c1406010f0e04020301110c0706030b03060c071e1b090f0b0a1203050c06100305060a090b0606460906050703140c0d0305160806 65
    0xc0c1c1c04105100386001c00224a40400c9107031161400c80c1c100d9020204022810035401404880d00d980a100c0313082c4040407112505480c0c407028030841024407540319003048065240348503280d01c240000c0c00001d5101c10040c0c020619400340c0d10020058010354418801990144506030f400041131300103010700c3c40e1410110405103d0700c80058160002e040300c050f11441d6000703400b85613551000d004221610208000f07422040306000d20000c04c1e00384400110b031044240f1401c0c240410080039590820300d0103010015014101105404120003000395814400c001c211407030241c5d480b04d400700c4802d4031710700300b4900307003980609140851400c2c80b1030140411320324070701caa0700205e040351480d948401c1e01e40c0140e1202919034212841d0b40c0e84000f22940a01c66070301211075001e00010302078040d404000300304c0e400c100c01d01400001c1403043c000c2c030300070070701c107501c840320001c50300e116a4a42000e002046242c002c068401c01c0000c3c0e180c0f010051a628464140808541c80d41803044481c108180003c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 475160000 1250 475158750 475158757
    0x90703060609140d1b1a0702060d0c091a04050a140d08160c0311010807021203150604080a060506040b03011116061b0c050105010e07080403120b31060803 68
    0xc0e50f0800901c02c0c8a00380380d55280c0703480d050ba0744c000006003007420b07180702d4500415158032580c4c4c02d0507201203220600e22083da040f10226603000703003950b1500c80003c01d03007402030089101e00400c00c10507000c085921520765005800b1114102c10b46903c031741c40c003810400c1400240d0480d4560b00f42c014200e80c070301c3c0c80307600244084540c0645000c3c1c0300d60b062440f0841d00100d185000e8025134082c000081030040b124a001c0c411700d401c1e40d03030100d581ea419a0990383d48000b240144e01039601000001c8840303015654030a91140010029413415603161559441d000706000c00b1f542d62650b98050105500c0c06224001074a0b20540083c41000312290440c190f500a02c10018100c0004007240004c0020642c44640349030040542c980030361894100040c0340300e03540042200d29600e03040002c686d54104155081c82107000c1e0340c401c501680c441c1d400305c503100103809214051070b8076401241010360f41c0a10001c0e1081829502d2501c140e10b4100c09980019142c0303250b1040340c500b54091003c0c4c00040203d = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 475161250 1250 475160000 475160009
    0x5150d0302030717090612160203070b04031409040c03020307020106090c0f0c0609020d051f0501030c05010513090e0c03011409120715021206010e030d081b1201060509090703060609 80
    0x9404110312407078000c065441907a60b040c1d40003400080e400c0e0341d40c0d07451f02124003980d400000c84031280105c5e0004d03a81c92040d40c102038482045200020000380c4161000207805c0040307038241d81000d900801040c15a02910083c6d0b000c6600441040580f65091044d0002070100c00c5c000c1c8000c00300401d021380038003008941c480801c52404030000620485030040405980c0c05801c019072800e650415640714a034590f4a01040c0412041b2450004014001e4605894100011070007117464000150750350b030b00a40a1680030744100100107510b0203180701c0c56440040b190043c050380c1944404150071600d01046030701c1c5407660041405414400014220515070841000560724070b580d0501c0d03000f014803065504000350000404070703542000c550546028071020b882d850040d00b00d403c00c15446140345107130140047c1c03851001070041e24560484455190150f0410b920744a01c000d04c2c101d072400300f40c00c59400700384001440e80c0582030020300c03564068414902000701c2e6040200051004403070b03104 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 475162500 1250 475161250 475161263
    0x1a0d0216050f0a080d200c060718030b06120a0b0106020616020318010f0909020a020d030501090515010806240a17090703081b06100e0105012102030a06031505150d03020307 76
    0x20b0039144201c90200b610700c400c0119402c0360302d45551703406256a41234102d0709000007441d40b003564501525500820301c2501e0340140c80340c03030f035035103010500c2150b038114410040107100fa507800780080b42c96890094040c2c40031341c0c064502031812443d00744004980c03c10710001c55108024151401c0c11011000d0fa02c1c020901c0c19161b280b05204080314002407640020001130320000351142c0c81c2c2d400090020900d0f01644081c01140e03a1401100200c1d00c0403038980200e420441c4007010713158030903500079520a90003080c040c4480700881044051096802d0510070340c0c000020400300c8107030040c03120010014041c042d00e09501d0210f000d140c0b1048980b01c020150080461181504c64204d12500e054204d545d08880319440c00e1030070b03840305035068070402191100d01030000c105544076445c80795050300d0224241903e494030303c0760ba40082d8002071101306040d80d510008000509508407a0800c0803011102040b6810714048101420036010062071055241c19048800079401006440c2602d4004a = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 475163750 1250 475162500 475162511
    0x1202060610200708060703020301082802090403260a0513020a030f020628090807060906050702030f0f030304050f1501151829131a0d0216050f0a080d 66
    0x19502c0d00d4840b6540041d1480d000d18010040020b9040d0301560403a03210000f120140c0281c0e184c140c4174038522586000fa03900002d10000c015040c9044079907003061007454104801080010b0f54030b4009010003101c17000c07050344c9043c045980502e0080c15000703078072450134801260b41503001039101a2144002000200b51915078010743d90b50f5020742d90006807203880c4d002d032403118a0b2001c2244000640440c0414040000410b1180c4009405020b075800c40e20365007550f40c2400c400317803241c0d0407405040341d040c0f01c5e2084081c4008011702000b0302c1c0f0020540150744074201850018200058062180025401201100101c820080307005046801d8850700d24201030300414202e503800150300009988001002c8000b500c0410f0242c021842c400c04551801c3e400000c1c1c03080348040c0700d40c4800c1c020504000b030040c0f0940c4481c43d104001d440749144054038000c16032941c80160303008007401842010201c40d0307060500100f8850484a4000800a8200300159035103010703c40c0500e5209aa050b0b9488 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 475165000 1250 475163750 475163807
    0x6140627030604060902011e0e1207211e0b07050703030e0105040506010f09140a15030507140a05011b0605071701030b09120c0304121a041202060610 66
    0x44a20800c051009001d403030461601d030900d0343c007074040004120300150b9026600b140c0e10382401891403002060b955045940c1c05200d00304a0010300030380b121180d5010b6800005001044c01e4240c22840304140380e20341d01480141444603220100080e42c140d41c00785140020001081d82c911994400d516003000c0340c80d00c109003021001071101c803540344030a40c40e02003804203000d000102c2a0484091243c0c5282403500e402c0c100d02030b10034155412030b040700d0030804101e50000d00c0e08020111500000540c181a586c0c0d11600c7c9002c0c013031b50140722105003440d98288542080100d540c0641000e083c50601590107410b04940340d4207071030000e0b1070741d070f603a4002c144407900c9483d0f04080240e002d441c070300c00c0d940c40b4200402180c0d000d9840c02410b1055042040355103141c201612075130190340700a142864079000c1054103286000d10200c0d030003001c40c5c1040044403903400c2428040c50049250840c103904500000e4940040544054440c600c3c1490210f41d40d0b600c040c00b55000c1d041901c0340400c2d1400d9 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 475166250 1250 475165000 475165057
    0x6010f12031e141204140703050a0f02030a051005070e010306080c0d05030d110d0f15030b0703020f0a020c1002070f0b090d0b16020c061e0a0905130f061406 69
    0x2800710981c283d100040c0d1904200e101041c0300e400303180601845042c129001104a03030760105032000400c6500116150350125000301d01c0c0e03e400500103001d56100038220350f580707401c003440f4440da01c0140342d451003480b05090344018000707140782c8207013400c00000f810046031550b940300344151640700e12100051903040100030b0040ea030764003c8154043c0911030602d14080b425810201e0112507080c0703814807004680d402c50142100606075000c1078248103007181c030f409a80d403000402c2141410303001c0048100c0304560000038280001d00c0d42c05841407510f55001c0280c440c0d02008a030003198000e000510400301d01090341012101c2d082c0d085961030140c000882e5412a20310780240c1072214420400991110a51716042d020700c0543c01c2c3c0b2854003c04007085464011001a0480800c848070111111010107000380b07203038011410a2100720366500006a0780b14200001c0340e80d074685440c4d044000c0c22040c090300010b4001c101d0029040540c440200b0f4181c003a503200345076408030b001d40c2d400b410b2a4 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 475167500 1250 475166250 475166267
    0x6030408250b0a061a04050604300b01050306070e01080601030c020f150402180f06120a020d1410020c1504020a0909060b09070e1f1103070506010f12031e 68
    0xb444481102c0ca4500b0031954402000b551203900703102d040c1000020f070b015600c0c40807a000d03118020031107402c19007025a00303118494500740e00114000710400b00041c5090554981c502207100d403403140d01d40d6040c04285420001c000e0424000c1c80300241250344680c0c3c0204466038000020f00c1c00042042119070704901d1300c3d440d81d025134001d00403c00e40c2401801c05805140c4164000d40c0d5100038040a8181580501d508483c50b400014480b80400d44510b045400c20010f80f0000046a0109000703800158006124440846083c000e40001184d4198140b149001c82a0174600c214107203d030038808661100d02c180b11100c107030814400090115920030380704002a00d5030000c10030a101035482c2000041c41980c0c0b40d01c2c4103650080016001910a900780c0484a40c0a001500e10101540544800082c40e5450784140f1003080d103c8580440c040000d8a400b6001e04011300255142885c4007804031400e07040807980c191034200200100740c1240310241d0400080551099005908504698805 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 475168750 1250 475167500 475167503
    0x3100e0703111b0705010c08070605040f120c0c0f0303050d050702070803070c50040f0614030304030314031906080a0b060a1203031a040504030807020c0603040825 72
    0x20b010902c0d80c100601e091040d080006050101c1c0c1569448000650fa04004980300424041080000100140301d58111680052150240102c200380d0340d501c0100c440d04c0c07039041100040282c0f80090500079112901c10007425031046a100719815038030014094850a10840200c4e620348001c11101c52081001d04010b020b03c0d400e883c2c684c0d802d4035054130321003200e200f20702e002c1c03800d08201004421f0110380440a8500c183d0826462029407008039190409000f90315050084a403000e400e5071110701400030194040b11002911504203429625000326030100c8901a5105000c117000090f0403110801010644040031a160743da5441c19800c03000b1420005a10241011030025500c02d00244c1031901074424112000d143c2d07100828040c6a181612a009194040074280404030f03020364400040c5000320780110421b241000042000d680c4152401c030000f50301c420401403c541c0c1031188419041044a41918606258413401450f0050030103001c81004540e0044c0e03c0148015441a0b486 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 475170000 1250 475168750 475168781
    0x6050c0912030a1e120e01090606060908011d030906180a0308071a090d0e0315091f18170c010905100c0c05100203040c0b0d020702040b030303100e0703 67
    0x15141c0d009684a4200c02a40030208000c4504641d101c1c44202c0c01c01d445504c02c1d90703106403d18019424070b010f06011402c5881c00d55903501ca03040440e01c1d40c00f998010703114079111030f1800e51408505a08480c2090785a1405a0880800d090246030110482c0c042d880c04550341e60f241c41040d90f017814107007045804180e00c10901040002000b00c6c51001c1c00703c19000d0401c0394055442c0c00c0105041d5007040300c481110380c0107000c400c40321074000c02c2c090400060103002c84188400c01200789840300350642d070010490740701c9041144200349010b4415441c01c2616020300241c20405c101306001540490000c1c42070484040c00c40c41c4d480c030359080d101d8650080c00240320700c4030103007029619034019580c1e624140d410b02c441a105180500c1103281c42c7c6601034000d041030104085014002d4101402c2100c4141684000086180543c4042e01030100c0403100140e0b9049203104002c11206030141d86402608203104205404810010100444240fa40c2a50300340d910444110024000d802070341c65074 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 475171250 1250 475170000 475170019
    0x509041a0f06090601020a020306011e0e01090f0e07030308280203130b10030201051b0106080d0e0301051302100c06110c0c100c0c060f03060e0c0d06140d06050c09 72
    0x181101c02100c14001c07203041d038070202c0701d80300c2400480e00c0d032408280180d019070111004000560011f420000703480304003001400410713160010070400d40004e0b4424483d4a032101c40303d8120200e14030034009441030420007490f109195075009410000c00901100c8030918003000a1012200d02c84146440c021101c0115a00d02d0400c0c1e5540000d09419400d0b91820681d07800120b01640c0030a0300d001f13a0750143c40702c6041052a0a900c4600112444052034070354840000003114001045400c421039095114008a210318105150851780e0040070103107140c44e40d440500160310741902108490f021840c1950002c450707424507001510805542000000300080c6800074070b00b02041c04100000b040301c10822290500004459042d411600501181c2c104039040150318041d9021119064890401107a1165a8191802d100c2400c44050b02d900c10000303003002102d1740070711420300036203007140d2110802082c11010925681c82c41c20010420740d80c840200d52040046c6095410050008215455 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 475172500 1250 475171250 475171261
    0x70609080f120108030c03070f0c260d02030a0f11150a0f140408160515010b03010915030c1202060c42060d080c07090b1c08040509041a 60
    0x3440c1e4044120b0688445101001144100c03020003140e00c05110000210700340325841d01c8451041c0844107085987c445200000211001144600300ca000c5240810000c074000076000326040144180c1810215002040020f82d03c6400c28048507490186203450350071040501003040c40c128201d4130301c100e04c03a0508108251281550400c94070102e00d400c9c20b0243d4034417450a900c014505072401881c0d86030601208903d101d01043d90805180101c00b2241c051190700d40038507600c00280c001c2d00b101e020006c014000318100c3d00510f000700440d00c550350041403460301d90800c0c15445005904003ea540310202e400d541d40c4000f82c400c4090b091054895164205400e05031507801ca1301c1d00406118141e19200c60030041d0800c030149084146030361140355a0701001c01400c05e203001c100f10b0b031001e4140305c10301410342c08014402c007070b210710380c00000e9011200c0100f2000d40c000001d0b141c0d03810b500020543c00200098243c40440300b00790703030000180d117592420b0404850040c01504191154204014 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 475173750 1250 475172500 475172527
    0x2f0904050f15040b060607170708071a0403091509081606030b090906041721010303090807180207020f0907030f060918030c020f04090503030f0a0203190207060908 72
    0x5800081c0d0204441500e510600d94040036102101c003e030112a68000241d290b091990041c40328a02c1151050501c03611001c0b4003034283c02c200d0040e5220340c1e021480c81e003003001240041c403501100c600402c00da480d195500078045a001c0c060404d050320306100c3c00c0c03c140d00400c44070001e0501d490a0320b151144410b40b25100010522030380d400a82480c04401e41c5003098000307a8091180b00c0094440342c4c3d03650f1940c4109154030540410342c1c4004001e81800c5080c04800d079290104010465012941342d82402050381d20a900404619040313048100107000080c213804401964030f110242c0c4556460000031840d01903011247c0d0480454000c000c00a54141c0c0981041a0030b4541040300382d0329000c8000449600140440310351a0003407044020a001c1d000030800684005c1000c0d03c0c1c0e584d5800071038160f6101c8442150140e20100520440360384140495a100d4040700045081d4a0b01c0c1c03200340a0350030940e4012102641c005944414030240e03420040190740c0094116a64003070014010 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 475175000 1250 475173750 475173763
    0xe0a06020f0c09071205061c08180f060702091312090603110703050a0e040e0708011e150302190b0a080411011106060103020c0102070c08030913092f090405 69
    0x114450700415402d40064030b00303101030a00462840e80c07501c1c40c3c0505403001800500c4050880c82e4010041c2d0708042c14020031141241040303206181c02c1da103d41c03801740040c400805002c84180f180c0c400d80c048403500d0b00c89030103a43ca11901100e541402c1c2e2140711106521000c14070018020614003641c444415401041c4882100c580b0365007000901c01c0e8040300ca1407801068401000a03004001c0d500380ca40c401c0000a62186000f84001545911308040a01d052265070100d070b400d03510b40d011081c15010014003c008403107402d0040c4407146201c4191421201c146c00000c0c07040012071054915604084a00e00142410389091a59142810400f0f414a8000c0302e08543c40d48103400000c03555442000c83c48400c0000800510b02c1d0b85454006401030340103441d0800381d070342d070034440000031600b444850701c020100c0c10013039a91100c985050101c2c015105080070740a03410040c0d08000206148461842c2005618840303400745102c152a5120b91180400d240e03000800b41c040c00140100842c50 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 475176250 1250 475175000 475175023
    0x60519210b010303030506010e0d12171303030c020a050a05060609090a151d0304030b0f13120f03061d0106092114250317090f040902010e0a0602 64
    0x2040e400a464140c0e00c80d03a00901800804107040032004000082c0290070803500920141024001818001c02003941c102c0c0040041d1803000c00349500184e41c0da0400c100d4498540d810380c0c24145d6203440d000e4454113003c20b100082c00c040c0e0303418220002e207100f4006043c1c0203501074165184403042c0e003007607541c4030801d0b540c562007140c6d6403011402e42ca00008046003091340c880c0c1e1294034a2103d000010090568a2104c1c481d4654002680000d03801032004102841c810111001d184c14183c11701100c01c000205076907040b400708200b0002003403c011402c1000440c510f031013100e000260f003040b805844c039a0701111024900c7c403000c140011000117541e05840c510307a00c00209079603c11180d19448030440b5180c0c5081c0802d003400d00441c50b04001c020101000b5811100203008441c004446914040c1740b032a80c1d100030680501c10003610049200b0906082c260700c50509588600080d2040707035021206104540d2171641a04590180301e41d22410100106242a46542c0b464045e4440c0f021091 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 475177500 1250 475176250 475176269
    0x7030f06140a0c020a0b0601120920040e03040e070903080408010207211704081b0a0c05060f030a0209040e01021801080f090601180e01060609061706090a0f060519 72
    0x2e01c03810451203801802c1582e130f070050014420b25142d81c400003a01800184c1004135030205001c3c801154010024a00c0c0b242c4040301010319840a426000d08452181a00c181c0c01c2c003001d02045140007060701c0c2039855524420802d0749840d0002e1b142c5203035540c40205468800304c0c00041c2120194007030a4118010f880511310213502c5080d00364050384158084001c1035003805014103003000700c0d400590042c4a4080300d80740c0b0540c0c0c141d00c44812010b203490440b43d8801e00000c41004003900840b030085c0000e42e541420114a00003007440740c04000c100440950340442e580500e0b513a645c01601c1e022059030000c56580400a10741076100a20b0600e0501054002010900711080c6005041c03280c00400090003059003840a90300c440760716040004102500c6007441c54400000303200e240c000300080e0f1100c8102d64030b880d0f0050008101c400c01036403d140c607407080040c6900ca400f0b0585d4072a0008400043c80c1e1403a08003013009110f19044540c000c070ba0310500503518200e2800d00d8041d6019030a = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 475178750 1250 475177500 475177541
    0x702040906020705190209012306131502070e01121e080a0e15030103030516120e04060602030c0d0e0612180606030609100c0c0b1906150e0f010207030f06 68
    0x42120240382c40017800075044140f000040210000c209288800484045070403554031030003400095107600900880c14080c140080100080200d104001e200241e003800504000c0d0700d802c0c10301c0800742e41403086181049003030080c041000b00c41001303603a00c0c030048008403100800e1030418038620b40240c501d0401003600900f07071103080d01c0d09109028100803407402c018030b1a82140d03000c0351240c000c3c821003410b0404006039000050700340c030700c511451200351b5030758005984c0403420003041e100715500100c2550010454034581c110041482d0801c2c40366400e01c200403204940208106114140c1c1c5819040240350600214501c049a074002098405d003c4500540791481003545404060355200030300d900207010a00d06580300d07001f000c1d085031142018401d1131840d845425180a00b12071032341141c0c00030044a01000000e2090201510001ca81c80000b848000c1002c0d0141c901140014400e8000346100031641e07100f00031990281d030303208031404d40741026440c2c88000391030020200480d103261003 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 475179856 1106 475178750 475178773
    0x203190b030109050a1725031d09060118090204060203180306090706030f0207080c060604140606041e2607080a02010512270a02120a1211030702040906020705 70
    0x280c2114a01c0b6001e1800030007409d040c0003140d0400244078010300c0d40341c5031313008280c3d8000780c00c4c04c141d20030f04601d008100700028540c0c4040822400001d0205600b80d001c401751080c003c542c40380031a00b0141c00c040689070f000c129241070803940505020003115210740c000408510050500504d4082d80341c0b6024525071103402040c03001d80c08042801b40c942004c1c80781d480000002d040038500c0d42000d0000806621a41c400c0741541c8003042c4080e8076500d0140d06983c003d1101d00207040c841d0b0115a40c11090300742c96400031980e401810070028006c1000300301c40c016a80d05030b5496140240c540100103038868041c2c1240b04458441944040000e044550031000040503002082104403910400c203035071400c06050080ca40001c0320940000300c5180180558403018142040003806d0000c0c0c1c6843d501454002944c05410700303403a50b05100c0558020070815001c0c0c000d079480c01815 = true := by decide +kernel

theorem cover : BRFrame.Cov 475000000 475179856 := by
  have h0 := BRFrame.cov_init 475000000
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475000000 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475000000 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475000000 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475000000 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475000000 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475000000 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475000000 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475000000 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475000000 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475000000 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475000000 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475000000 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475000000 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475000000 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475000000 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475000000 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475000000 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475000000 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475000000 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475000000 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475000000 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475000000 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475000000 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475000000 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475000000 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475000000 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475000000 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475000000 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475000000 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475000000 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475000000 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475000000 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475000000 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475000000 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475000000 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475000000 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475000000 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475000000 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475000000 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475000000 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475000000 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475000000 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475000000 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475000000 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475000000 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475000000 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475000000 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475000000 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475000000 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475000000 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475000000 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475000000 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475000000 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475000000 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475000000 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475000000 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475000000 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475000000 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475000000 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475000000 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475000000 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475000000 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475000000 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475000000 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475000000 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475000000 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475000000 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475000000 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475000000 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475000000 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475000000 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475000000 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475000000 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475000000 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475000000 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475000000 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475000000 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475000000 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475000000 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475000000 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475000000 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475000000 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475000000 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475000000 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475000000 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475000000 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475000000 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475000000 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475000000 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475000000 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475000000 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475000000 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475000000 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475000000 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475000000 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475000000 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475000000 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475000000 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475000000 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475000000 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475000000 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475000000 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475000000 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475000000 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475000000 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475000000 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475000000 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475000000 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475000000 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475000000 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475000000 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475000000 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475000000 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475000000 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475000000 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475000000 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475000000 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475000000 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475000000 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475000000 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475000000 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475000000 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475000000 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475000000 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475000000 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475000000 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475000000 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475000000 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475000000 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475000000 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475000000 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475000000 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475000000 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475000000 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475000000 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475000000 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475000000 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475000000 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475000000 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475000000 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475000000 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475000000 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475000000 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475000000 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 475000000 ≤ n) (h2 : n < 475179856) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
