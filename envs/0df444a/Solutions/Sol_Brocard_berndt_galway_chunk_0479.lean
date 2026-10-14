-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0479
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T20:01:17.350081+00:00
-- url     : https://prove2.me/submissions/30a5939c-5acc-410f-9728-e7b410f40afc

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 85971224 ≤ n < 86151080 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 85972474 1250 85971224 85971289
    0x6030f07171207020d0b07030b0616150b01021b0a03060c0305061005090109090917030910050606031b030402012304050103110307140d06051003020a080601080606270303070c0302 79
    0x311005c0319042428004140c89400741100502003440849030700c0180420510420710810b050308103494442e05940c2501c0c86542e0268007a01d2284c00f1190250300444146004c0d20b0855048080145000f071040c503803540c40b075680c203048550101e00c070400641e07a40200304090034200055282e4240da401c01904000c91740340024119581c9010309a83c640e1100808030800091072204010300041c2d0784026143c0c540003040980e11610360307070080c084038100000b082d010304084007180c3c0610740494500040314040500b01005620140c401c03410080314030f0080c41d0700c00303c0440a510a4501d48a05581c56191100040907298202e4529410841c10402e100b005604034081d00e4072900300240c915103501903901e190300141b10aa2080d500802d107006c501c1011070b803580c018460020542c0b90b0b03d0081d2070b820011030301d220302184e0030343e004041008807001d6500c005140240c06105140e46a28274680c9002013403c580000500311000a402e10b424030442c90031809041c2d103584011201c41405c1c220780c10 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 85973724 1250 85972474 85972489
    0x1008061e060d0e0f0706030509060c0301030f060b01050d0c030501050f150d150b0403050601050913050706050906070f0b01050a06020615041a031902030d03020406050d0506030f0717120702 83
    0x200c80050540e100f8a10050b024144140740600814206403101280e440d50081d001d0300b030888140b1054050107000800360040300d000c0d80d060b40d070010307100700700f03440b095458500034009200050706014051240c04108903607806100c0d441071140e80d0203d060351400e01401741c10109060b09600c103100c05441d20031001074103405d5070b4082010110110740440001540901da00844d0003041c1028170015010080c0180003074400e040311404d4070a5111950f0710380c1139044111a8640040998000741d40800040f4850006061001d8000300724030315015040c1d5032505a101460700c203d966800b000300403c4540f8040c0f104800910713a90001d07041034545034007010040c204902c00c043c440d99650200d5024079503540b00d45d600035540541150100154040a40ca2110014038124400e1145c60136866001d8400e00a69040b90825159281041100704500000d041c0090041360540310300c480c030b406003003020088180140019070310307800d030710038184000341c10041031000103858800200104c000580b103505 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 85974974 1250 85973724 85973737
    0x41e0c090501032310081002030f150303160206090d0f062307050c2812020c060711040b04110a02060f070c03050c01140c04050306060a030b041e021008061e06 70
    0x301d104c07594420901001e1000e150b04041160720900000c81c005540960045015005003140d40c02103a40c1c0c1105050368031806000309406030401e00c0b1f0084a11400d100c201c1001d0301c0140001d0600305100301081e02104120011340707101c408403201174148210380c841e03030516003620460082c401207040d036034510000340585014104000091810a44441442040035003040c107000c00c00c590f02201700c492101d0300c0a05080c2d854182d0540c3e605107540c0000f030071a03183c5002400032400c11050f6150401040c10100580350029110884c4500303655441c802c00180c8803007242040c2d19822200700c002c0c40d10304014806481c0c45569814010800e81110341ea07503625501d4581242e460747c14034551409009c9480715400300c04207000c180191270804030060420344c2c070164100e9550b80d6820081010084070b62201074144e04c00000070230b0104401a105407800c2035000c0790b101c0c640d912540491607050f08445250700203901c8009000c414581004c0c402d54010003490840028050300000a04030f10541 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 85976224 1250 85974974 85975031
    0x20f0d21060e06130b04050403031e0504051e0a06020403120908010c05190c0c0602030a0f03052e1a03010f08010902010206160e060304050d080907030309030809041e0c09050103 78
    0x10307803490300d0050380c98110301c0c2c170130794098030511543c00e0918010300900340079165240da1201600c821304003414144111481603400c000180102d040030304006200460360206030b2414002c21444034007240480c0000e100451207454410680610074200400d50241034200001c2da90400b410b00b20704641c01001e6070b44000e2142040218908190410340d031782210540010800001814006201c94010024240c0070805480c0c0c0f41140381d00307000440807604112111086500c0003030b0128001d540482c1c20f81c4a0981c002c80281c980c580b04c0c05400c1d803603851454800b0030300d00000300520291068100714001880307410300906c005803c60303001079140c4000501c124551003030400c001034014802d82e070b070201c0e0080142880d07076a030902d82040c5444014240d00740d00450403110100d0079408000942c0c0080301c2d0140c0d80d40c1400d03800d5544041d0342e50f200c0c080099001d901c50381c05128000d9061203110368881320020000b4034094a1102510711076042d84074606140c6031440144580c2c0c40d04c44030080b80540e4 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 85977474 1250 85976224 85976239
    0x180603050601110d0c031803020114030606041701050109060f0303020303060f0a12030c06050601020a0203030a030f0b0618090a0c0e150c0a0515010e040c03080a020f0d21060e06 78
    0x10038004a480c0804200301c040c207840b4036001811601d030000c41702060240203035502000c2c20b0101c15005040485444000d000600050304298491020000340d500321320020701d003601e01540d03008000c40d48086284001303420f0350740b81d0041108010030b10480e0010700c244002043d19510395200607443e4000144024068aa60101c0f030115030b8410403180e015000c5070000341c802d21502c0c10010b2124084010884465113840c020a03000e60000030301402e4260b00400031480d00b461101d00320050700d00c0c2c41980200c213407264440e80c0560b03034000250540c400c84018018083c0f40c4042046007101c1c004e0440070400c0e29005d980a00c1c503a2000e0403000b110f000780e80d440400c1180c081440c200b841450201d0440380075a0003540204034001c958009106501504010241d0326100005040030090340c0007440f10f2610101000010701c00400340c443c00d038050060b641500c00c103052842c103008061803200f0001d2104500d004441260368040c5030f080240f07050800055003020240e0003403020241c4030600c90300380f = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 85978724 1250 85977474 85977481
    0x6010c0203010603020a091d1612060204030218040201080703060b09010509061201060302070b07080c03130609121806080c070b0c0f12040b07020307030905040e0304080303010816050118060305 85
    0x1003d4008000440e03000d448200282e580e03c040700c1c0100b885003031814840715052001c070342c100c40c00a04042500000c1d010005048c1c64412150944107074200202c031090780a000010251381c41e400601d42da50040707003600f8447d28080c030004002c458010442c009051a120003031154403600800d0f0f48e0800c0c003c1c01c2503985c0307042110000d00340e130050b03010400788440710000200d1601d604d82c02030100d0500c0740c803601e40d00d41c9804070140da41020440b003d030b140d40b00500020700c24888401800000e280600030000d070003040745c0c0741c40301a01300c01007004000c40c2e655800041c0f07040381501450004c18007440c0010090410062002c51845600c1001c1d120403911310114070780703495840c2101c80c51602c5000295980941410540200b0340881c1d0948111040800164a95002004075841c069055503103280c12410407080100a11208400c40c600b1310091102141401c0100011800b8141c248001c100a03003180d5036145903001143c010034100040390560030301c1a1030702c59110040d94a070f81004030341541e = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 85979974 1250 85978724 85978729
    0xe040c0c151116110a030f061119020d0914010903020603100e040f060f0c0c1b1e08010b03030901020706050c011b110105010506030603030d4107020a080306010c02 72
    0x9401d09005500c1c0100240341c1ca640e030743c0c85010000302d42c03040d41c0d1541540d8032502048152134181c4070241904052190220015040d41d1040040003800104107060683d40b800c210311034804110a130025a20007813080d00c9040d00161440024400810604008542e5200003403c0e0f07112448001e01840d40800800c1494204003104805030a9210030000189805e090580400706030020a50300c0520308800303840c0140041c0a428070304d15007a100c0340f160a502c0d0f90303000c505502c10030851a60100e03143e00810605100c03842c04014841c42c0d41152199400c000d03025003151b1848148501c254030400c00600c10f0b980100e000340071a80d03103003811619264540724185c050002440c90040180e003141c40118001d411500070808c0e4281d41000f001260f8842007482318900c030139550b00341e066102f44810101d491050b0401001d40d10400c10898034284a1505460035501ca0a040c00c0c1072022040b01030117600d80c411100d980710343c591000b06155409512828031612000d04400d0400100400040a64 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 85981224 1250 85979974 85979981
    0x328060b0f03061f05031b0a0f1b0209011206050906061008090705030a03030e1e031615051003030809030a09030605150d030f02070506040503120a0c12030207030e040c0c15 76
    0xb0000c84c03031600704900a2520040032503004941c01400c0c0d13105100d038000003000c4102965402c19480d281c0ca04c2000040c1c40984107480882850808051801c407075000580f41c1d0b10030b0b01c0c0280408100401c10660310f00e4400180c5d94005c05011017036100c1401c211103a83c407882441402d01c0a03052030080f545403040042e0a0102c95000142c05202d02d81001080682c90703401403060200d02030661b845502d4030848903140304041d9015904a900a04c42c10816039054141c0e114510300c03ca910614581c2e04110f00010b07206c045070300c04440c400c008030800a00d5044100c0507070110358480554540741e1010405888803049000141400f5581da00103403203840184010030781c10b0001403408620319640e2a00818a414081b004030050140410000341c0b0705000054a06888000340076000310a52540d41d420507030043c003654400c000604140101141e040d80842d0007000b06ca5a01582d140150305014040e0408030112038051440c20072000c80e00c42e0b0005030b0340c40807a8031026400040040e080c00c84042c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 85982474 1250 85981224 85981249
    0x1207030e0f060f1005040c0e040f020c0106080102071103030a050327010203090706090807080304150309020a030c030c050a0b030a0f1e050105090c030412030207020a0b0328060b0f0306 81
    0x900c5401c090000800f024840310b4896a003034140c200c01d05481302c040c00705455207200200089400304500c00150301e0180c00440001c0c030040c0005052038160f804503403e640302c41d0301c95000340c0d500003401380a00c9030b00390819a254100740e000714900582110000c005200061004000210140401c1c0fa10140544500340d1411000020b640b80c0c00c1680310b181c0c03105128414132001c02c0141d0b100045018021404504949217680698142881d150300d40c082e410340b10060600701f40da28103030100181e80e0280120041d5028101d80c011a41c2903180c040c035211281d030005882487c0d00741e01005042884c0e130461b60300550741c0e41c0114454054484400c0504124458805441e0224803515205003107540802d040b103200310340000242e12032115100d5148820366003c0c0c0324640c8034005924150003074004090192020340ba0f050105d540ba00e003414590026207900022683c0310350b90800c502038000542c400e8107107210302004002d180c49076442040c0305802201c0240107010000680e0345e51401469030b007 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 85983724 1250 85982474 85982503
    0x1090f060503030f0c010917030907060206061302070204150303081909120c020f060c030d05010b0a1b03140703051c1505040c030b060a03061502060906060607051e0c010f051207030e 80
    0x2200340f5581c001b02242c09c1140c203a0628810140005400c41c800503105000715005040c0400345021b8000d4200a50321041099030065203c442071600b8001c86c2d0900d60045020340e48001c114145000300600100361201081085410148210041401c03164160801e000c20701b054103a4181c0f51001c40c03200c869a140056100c072010501440c0d449010004010f40c25900701c00704001ea88400090459015802c1e4a200041c00203206480128008520210082c0a410a6129180101c03a0b20445520092003180000c00102e4810b102503144104905040b0703c46030244144102016102469003551080b00d109a4031208105600742c003e03031101a00a04c040c20035070351580695800b4000e044284500e000c0b618065081c1c0d00b8180c40411500d00683c2800c0103462030741c5030502041426002006c042e55140255031420f030002c850003a10ba0343c244d081c10054111444c0440002d45000b0b12403482c001030100c1080001885084400a6980412241000910200524069407601031102441d98 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 85984974 1250 85983724 85983743
    0x10c050c0904030e030c030105040c0306020a110d02100b0102030c0a03030b0f0d0803090c1504050d080f1207020705030304180e0a0b07031e0b010804030c0501200301090f060503030f0c0109 83
    0x401e041d8004003060040600782c00b00d03902c5003042c1b002e25003201c02c2120080c1c0b510103100d10a01c001010f907001896070303013291318082a244040c80081c1c3e0411040a05c44c1c000369204902081d203503001801480700301c5009001a43c241782e000c2280c3e5031100c0d0007200c02000c141d500d90140700660342d4250040f514900182ca2a01203001c3c5180101460b40305443d02c175018440c3c900d48a50300d05e0142d00c81c454243c100740c09103051034640024042d5082024074200e5000d041801040c50ba24030b10009052494401d64213088142800000a0700385502d941090f40250020041480b40400170804da041c9040441000510820703240001c5042c101502001440740040105012009606800030400ba00c03200c40e10542d650301188031001140c44142c60280803604610015000c20b004007001000280944008655000110361007003000e40100f000701224000440140318242c031500c20081056401c1004115260500000030380c4c9004481d420001d2040c000343c9034000ca0720a4105001d816030040d20071 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 85986224 1250 85984974 85984981
    0xb19180b0d080a030504031b0309030c05040b010516020406030807050307020111030a0c0f02030a0209010605030a2a1b02031c021e0717030f03010f030302150c0a050c1504060903080108010e0606010c050c09 90
    0x903e40c54ae68031060343d420b00304c02c00108043c58a4071480360007110507102c9924001e4490040c1594021a1006990142d0f6598000010507270800007040c0311841100a141d80e0101c41c80003514000c81c1100c8a1669401032220800081e00100c03520300f0250002040c2542d013640b407000a15024a15030000c3d0414116800002c039103801402450050031002006d01024140114408004500c109842202000e03448420380f0103000300703544610b4206034203e407081e020303090300801d03e44140740c00362100c80b00d40c030030b09244916414003484804a4014258040102d124000c0603590151b0380941c03103206200769441c94a03203030200200c031001d9098a00e03480d12980c0d109804205280709100680150203403080528114200c40b80780c070301c42c440310b14001e82003501d400403c484079003149030316101521038070804143d004030100707086208038810100850010700d04d10300200036550690050965070304100104000c502c02103810b5074014021302e005800e464080c10b1030351412801c1c00032941c102d01d1210a2 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 85987474 1250 85986224 85986227
    0x6062315090a180204231305060102100617160503070302280303080f06010c05061b040503030d0203100e25090302220606051c0b19180b0d080a030504031b03 69
    0x6401120060b44010403100d011b0701652100740c11003150a84d01001d8440070504154840d070085400c5841032044820000d40800351800300c1d2040d0300119241041c0d41200c081d508020000c0400d085030f00c1d080c5001e001d01d402c000c6681e07050980802071150b81e07002144e052030149419101d40c1c8118500d082d100480d6603003809018548142c40810098200c1c3c00003402c0e0354004e101e45810a070307024004000644e100345151544001091206c3c100000400c40080d460750300300060301c0c828a0540005a4a0400e401c02d166103a4180c0d0040340d0b041252000c00000c0880405024024907005550007610005143c00f10380803901600000e40c02200c0d2915500405c01d04180c200c0d0310302c07606c0c000308201c503280c00042d20640101a0754610f07214446040282d0b40225400c4410742500c00f40c44440b40d400b00f000c802803c400d6a03085102c501c0d085c2800c002001d0501e0282d04200780741030302c0601400348161a40851849071810344c1d41403544500c049400c041c4141c040079244103201036400c0c0d050350709290 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 85988724 1250 85987474 85987477
    0x3070513030f0201020c040b0607030e060c0109080c0106080703150f020405130f14151c12050d060506070b0a0b0a0b160c080706050909090708070306062315090a1802 73
    0x50f80141b0504401e024a41000c5c4182d849101004001e5418200d059070125448416262410781018040c840d48440140034000c4241d11340c450101640c540200b0302445007168010b510200203984210810008100c0000010864601450020032101c40c2030443c0b10281c85113500c03958014000c185d1544122005a000a5003078810780303401e00c40301003070410106110b46c090707503078040210194001d04194500a442a01c1410300c000c14074040c401d1a440d4640461011944400820f60016030300d0002c080030320401c2c01a1a08580a0b030070155551150624040c1c0245601c4a903980c07261070b0307070481d40c641819100420303048409a40e41d01c0c81e03c0e9000030320140100200c03164040c0380070200c0e9000d40070512409886040e51524200b06c003440420580c4031021f895006603028540d400304079800305000340b0001d18060f0310301094562402003180d0100ba03200300d01041c0c1700c19401181003940e0341c0301703580d80000c01d8000c006a151400c0c0d2001818486042d848402d1641c400c181c5000320f40520340 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 85989974 1250 85988724 85988753
    0xc0a0f0201031503050304090c020111030f071701030302032a0708010b18090d051b06011e08011e0b060d050411240306011b02060307110105010504020a12020307051303 74
    0x90b0103015001c00008450040441808000c000d80c000340401d020500341c0343d00100201ea8a0320000c035281040e1100d000e403940c019500c0009a01c051420854110f0300325810011080900610281c1585181c8000f0744a020f110408140c0045510301c8180040c50f141c280b00d61840030f0825600e505585086031030003000079203500390007040d11740c1103d240030055201903480744000030080d200301c13800c50701e04550740d80c094000c055400740c00c5030300b0042107070b020042d890181802a41e0040101c100500744000110258010700190381040080c50403405204c5401e95450614000072404405000c0002d00a00031a10b4001c000340c41d001c01c01051090701207504c0400c20060301c890903590030b0035801c000114a00c1c41c200c404103100f000032541d1548a4851161806080d03040c044200034a540020290b0f80706031106000030b085d0240003215240c081c8903450051100310340071031030041d81c20b2004d03207103441a80900401550200028a945014004a0b4482d4235000c1c0001641d40d1203191817104d4600c0103 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 85991224 1250 85989974 85989977
    0x801050603030708030112080f0c0601090f0207030c02010806040219050304020a12020306040f020402040e15030105060f10030203040507080715030e06060906090405070b030a0209090c030106230c0a0f0201 90
    0x6400315006080210440c0c25464004900c54078581c240b80170030b070740903a0200048400c50340c100706a045140325440580201c80c5403101420a03545400264000d940d04030380034020080c410401a000640c120041c3c0048650a0a0210803999050000750090255603400e8120740540d00c501e03589607a2040c010340c400c903c01c4860401c4562601c10f078100100c2d0212000307415a1022011402041442c4403001d20a4170060001d468151509100c2c00401d800380c0d8800c4004610200304003840ca4280240e69005105417188003803e0407074400140d196868840d01000d040e070000204040c04028030003100548014000c441425640b055641d0a092000c01c213180003a2814244011a8001160007402240020210b03c03aa4a0b000200940300300050402c68003031085c0c020006a50005038003652144807640001030f2181c0da02004d009440600130321070844410304000602c001900917070303018001e14103203c0000c0007034036891520740c2c10322032403020a85501c41c85038084100821282000f10b840e00c02e = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 85992474 1250 85991224 85991231
    0x9010326030907030c0e01150c050703120305011d190902010c0209040b0103031e02030706020a1e081005010801030203100c0212070b0106141e0a090518040210080907032414010801 79
    0x1341c00703008906c00340a0280d000aa003e01d2082044030f40b141402003c003030b01035000e039141c40b5502e98543c100c8110001c61100880d48a60040000d002502d0360071209000c030a0314040146804181c290110410200002803655036590030000d40e4851000000d8017a4054a03d003880d003080c7c00c00051504092000f20005000e01e0751440011100c41c0d544080c008885c0c0045040c12050780c1c80c50013030340105803d0820401001310183d6120003452554046801c547c03229556804c2c94036003501e00c0000d03500300314103000300c0000410040e02d001a09a2031701d2b0391074500003021103007044c00702d0504031201922480c14901207890300500010b010824101c0b0a940c5402d54014034100e4609418040d032504141034110030b50f00c1d0b104c141c00280051012000b00e2900031281074540d000504c1c1c030062140b0300c1000000e903c0420045003003080208886806a0420000600e008030300260b485e01a400014030142e41303095807007500d442128100780ca124a210051141c45402c0400c401010001d10412045c0e41c00d = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 85993724 1250 85992474 85992479
    0x2a0304080d0513050a23100902010f090e0a020c0a02120f011a0d06051009020c01020d050105060301030c0b09010c0803090105040605060a1508092506030f0b09010326030907030c 78
    0x40742c2d001c00c911240c0c018060700d403074046511000e0072107040c400c006e200c0c02d244000c0042e00d00742c14480c440b0302100e00720000a0303815541c0001031151a035000300105200d00340009102c404103041010f03901c0070000c903001d6078410b80300702d01c0c500700110103600940040c07445011083c02a004950407140d440c5c0c00000f04080305440c0c4210140744190b502d601e4005840c03000f680c6c0031441541069900903014640d20003c2da0f038600483d0101c2c1d000d00c80010b4140d6021a845a03100114040e09004060460700507045505580f14090f07910740e00d204203ca0400c001480f6880da0b40100c00d40481d4582100311140c50b440d1500760366020740812182221440c0c58500050600e180c980d0101003a01c018503040785517414520f0040e5440303d406003c200082c803424420600045548159000301524480b8070000c503441e0140140540340c00010105805041c0020303429551a400d14182c1101d070080720013550791b62072181500c0c86484d0365210300071042002040001084c40004c4120449101d419100f58059 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 85994974 1250 85993724 85993741
    0x30207091b0905091003020307080d080f0601080c0d06050a030b010306230c1318020c060112080d020a050909040803091002070b010e040507152a0b2a0304080d05 71
    0x10080c01c4107000c104000310901a90500d01c00d038036800f03525800c1c142062a1079400191800304140d012280a070310141c101500c0c103607c00c003001e80202202220842604018002070886000208001c01511004c03822807584002e40e00f0401c01810060705803044a80c0303034145041306207805d020a4968505241c2d20041c80c0105034100740945403900e000c810142c4401e440b14105520621405e400c40340361321030125a1101a0760040300f65508440016525102242040c0c2000c4050303101c04120300d00c1c600008080f070201811601030302d07041c4100503500c03414808191918084d200314107800202d00c41c1004100420080154081c84000d005c07952007a0004020b002a44942c52008000c80c4510004002d8103030f0135607556070814481e00079036548a07294010400520700711403a050000d04e00a442c0c42e1302507044030362040110072041584c200340c0084d8071070403001100540800320800f0403c0c002c107020200003000c113820840305017120355241058180f040d26504201000d8482916280118a000 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 85996224 1250 85994974 85995011
    0x204031101020c0a05040f0f050a0b012d05030a0e0f07090e011e020d1b1805060307230f070b09010614100f0c080a03140901050c090618040903020709 66
    0xf441c000b0580c0c1007032404d10b014000a40340d04481052450f44404840d148034550340070f030714400d0036007034000103015003040d00040c002d054400317404042c0000100c0c800211404060365140c1c4010509116540f515a00401401090701140586040c002d6040c003c060349004200401105c202034028407411500359211401c0304d00010001c940e411517541c0c1c0240044d00380c0c024100d4024001340c00120901c0460340076140b41c1d8190600030000b1a0619455103d80a400c4004040c06d4152192815454911070192141840800c0340744813980b2010402c18a00030741044601200c1008007140c0c90766043c0c942510581c0007516582b0301035080090100c3c5840051240407001c43e401000f100345030ba0552001d45a56001c020740030100b00031456402c0c085480200104603451080d500051403a0360740c0e22006a003c005400c82c14164101002e00c601c1c0c0e1144026140b0859040390b0b810368804600117915406211943e89a070082e0800030400181a00842e8042c2141c80885040c0030034017203198010f911 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 85997474 1250 85996224 85996243
    0xf05090309010c0c030b0f0a0e0c13150308040902070c0905100b07030c02040207080c06150618031006030c151416020d051606170f040f05030708030901020403110102 73
    0x140e0090182900540c07140340c3c0c1a070316900540000c0200c544989814003801d03001c40c1d0b03102021307280405205001c181c510840041c805048040e260380a140e50000c0c00100c1d421444009450700c40000b8089299004c60f070500440c1c2c084c4c810780d5034981d901007520280d08030b00800c0e00e00345041800090312050b140600e42c80346048141807030b1214100001d000c459088000e09604005403112803d0058440780700414055004000c015100e65007030115038584030008140318005086200441c1140c0c58000a94501081000c1048031035001e6001180ca01078a0720104c010050030000000107201d141d0a00a09072041420045014621511b050fa11a0034440a00140d9001001800d40c19140145404007151005055603030040d01500c40350702e410301410040c842046200020082560058500401c26680d003411030300b0b914251030340287c0e0400003040034010b44004405001000000d004444116a200508586a09100f03803507a0003500140400c0b0740b42d0545111491040d8000500d8582 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 85998724 1250 85997474 85997491
    0x1a100216091802061b0109061a03030711040507021f0b010f0203040e010608060d060e01060f050409080d0f020f03042108010b0a111e0c0a120503070813050a080c01030f05 75
    0x151440d070138000c00c0da00c0319403100004001110031601161080c050700c007066004013000714800d09040007120045a01d15030070361207680100a4540007520300b04070b000c2040c108503000211235452a00980c1411400b00d150114002c138510b2000e01a500740c0c1c860f00f00c614003030741c44020b024141e1b0026aa44e104031b01030f400000001e000100200c0d80b181011581c4504050150180c41f40341d942c445042d15484c1324904681e9448220601550f4440f1038003000404c0102d4080c48100490b4aa0118501c1462a001401754955004005214244e01110301c0121801e400658030310b040e0801e142e0605600c4003080d102900c040e01e02c05810310a62029040c0c50b0111105403502e407d4040903604a40c0c02c0c10b001c000381c000c958801c007190000301010300c4c11442d40409801217412034030030000001c01a401c01c0a5941501d00b0440100314004191007040b580a101c01d0f41e0b8000b840f00c1070385615556401550300203a101404510100046017884403000203880901a10080c484220241c5104440410 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 85999974 1250 85998724 85998761
    0x11e050103051624020114040b040302010f060b0d0509160f08070605090a060c03020a1218051503040f030c02040513050606092814090303180303090d031a10021609 72
    0x11070b44807908110a2121213107000025907d001005001c4c0141000c5405036420b000010400050540a000f04545042078600810a2504000c052242030045c03842341c15860f039550740003504085003002030b031070001000080c80310003d80c0d902510140551038050800e19025004000031940c1c018010f480400c0030080816450500b840011548802165410341c21403080c1c54150010449590281025280756622080f4540ba2090041c40c0526a41e0015000d0310703025a20703400032602e07282a03d40148e48403198405030315440c103048072142250030001c2c1d0b1043c034020038030965496444102c0c4606109a0565020b50f0301c02c02000100e140c100c846500e0f1189241400b0082048580c0a55840601d403200160404001c03102d200c00203030803222804541c1c00041448014050810004d8156008074025859403030711001e90303a00e401e02c00b080d0307400303240e215100d43c01204045080d48000e150080d10002d003540700c3c408001e41c0c44280f961070400c94604070790b010a01c05190f000d40030a0000850b4281d = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 86001224 1250 85999974 86000009
    0x506010e0409020301021207120c1806081023090601210b1c050d020c0a030302150712020a090306050603070803030c0702010207030506040c09061508041202011e0501030516 76
    0x81c0403541d10413a85950708000c0100758907007201c0c080d4050501d40c0d5071304102c88441c2c5400004c80702904041d0050003000ca01044903101d41210481c00ea0b0542d20305040d0300d40f180c46d4524460505a0041c0424150701240e07500160b101c0342020100c00f000300c07003003003d984075200107646100040403420904074450302c070180303000d00c2c0c4c4d001003404c0c44015115030802000a49801503c440064044507142c10103480c5001044c9d0401c08003038001000c841c0c00700000c1c55642c02075501c1600080c42020912a1400103507141c1c01141c40354010f0800d443d0075580c404c06030301e004011000d94041203548518000c007040c594107000949000740e440c06030045281d611a2066001180c01c440d00482c1144500032002c000140c05100700303801644200c00c0e0050043c1801401c009880b01c0341c000c0405142001241048660b219803041d8110360050030048000003a400101d014003c50b90640540c450780e00c1210f1074500c0303141c0c4414100ca010f10165400c0c80b030100202c1d0240c1480d4405c408221041300600d = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 86002474 1250 86001224 86001229
    0x50a051003110f061e0904050906060904060507021c02010b1923130603050706020d0e091305011b0906030e030403050304050118080d0503090c010804050706050a0512010803040f090506010e 83
    0x102c0c00803400240f60300d051100c0100c001c01c01c03501c5c0c4a030002c1208408a41440c86090500031550000000c101405581c034000000c5210703584003d00c090062501d4074045400c681c02072002042c04481d22204c068050b00e188806406482140405ca004010140c64011000c001d24140f000790380075055a08042010a1411990417405034442507220829400b0307841100d280c2d104640083d40700d240a0440145403200280c01d18054903208820710242c8034200e001030391045801039010700416041031901031103051580c0140510b44407010288520480007100c6a003180e408000c40c0e0965070300380715400d04030b4441a1680a144001002a0302c20301043c0075542c01401000075848480340c49420045e44e44401500c1c0c0307114026080003003140001800000f00e014050348810350002c2c01c0c032040038142690364a580c1c021301e2040c5400c200c0d010030321a01e41c40c85201241c080c0d81c05901d072040c0c40d58403454105d45950251081041034108281c1c009040c0096011b00d5104401c16103416201d20b444905 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 86003724 1250 86002474 86002489
    0x70e101409060d06060f1b0f020d1a07031b030e06070c0f06090602040302090a020310090c05120114120d02060112080415080103050f010905030711150706050a05100311 74
    0xa980c0d100c00b06200304210300107a449500f0041c1519a01d4040c0502c03018405005540041000d100c0c214203102c652011a00301242c00b19480d5054500d40d045001c83e040c0007204404d09102e00710b400401c0c40a000c14540d054104201c005d00398440e02a16440030350040e000c80d040310030741441e01e4002000243c80a801208140d020380d0146001c42140c9049982c0e072030444161403421501541d0125081c800d500707003101519030001450a0441c514100310f9080c11182a041c420310780301036150842d1184952041d001c0d980851b020110600841d61210310201c41c00092201a90250080211041102d03500050f15918101d194020740380030f03400c10f501581c04840074101510092070400c40080c409040407200b180306202a61544000e504500c2d0060602c2031002c0c51410581c141442da1001c60004421078040550261890030b601012201103043c507002240384004541002c2006414000306811040c0708101d001d05c100080d0341c130215248422945da020203081d0446582982071070f0b003080c05 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 86004974 1250 86003724 86003737
    0x506091e150303040e09010213060e031b0f030714090703151401030912020109170328060e010602030c07050301060e13060e0607050a12020a050909101a03070e1014 72
    0x5060300c0c50a901c8516420417940c059031802030a80d40014000110590000010f001d0040361405024400400002030741d500541c4017010300352241c0010443c000d589603032240440381e8014056900c0a5170b12110a510078401104050040d0b4160000401e15071291198610741c10f8012031a410150501a29148100c03258882506055a6254101c086100c02070f0b81401c2045a07400801c290000c0c0c0b90044251b000c0d10682c80308040300b8024070039200e036040180e030000042c85d1208080c0c0702100703d034200944400e50182c06205099400894615400310040114414140131986000c1d95402803600700c1c0d4040c403601036a40c82610210702040c2002054480c958010800402c0e9840745d9828281003070710276143c0402103000041c0806640f900400391840c62984500c08505200d00400d0181c243d11900784407501c580315040000d20081d0261880002903d0402062900c0340d0321250a2034665006440f41004100542440d405500d4410030b40000d04100e584c40d1a0b84250030301c040e1603984c01c07a1 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 86006224 1250 86004974 86004979
    0x1a04031103040e04030e090f13060906050a090c120206030103020405060f031c120e0a0807050f0a06020d0b06070218060f090c0301032f010e010c06050a0506091e15 72
    0x150034a0084442000540702034038400752880e44038103251a02404840b0070b10f000900031110741d0100f01801003d040c002d6130240049001380e414030020701d4000d004020400d0010811880d20040c015020816070242d5582d0740305605800c1c03480c2e11620300012407038034228029440703007042005000605043d04004e4014002038041d5543c180c1d170000290070322000000042142000002881d24560b0040f440065400c00310020802c00ca9804411a01d40144a00103040c4030000115582080420070400382c1031032000302580c9150301c952800401135400480000b44403800c00117000c5083c030307103030b001c071020f295008210301c4580007150b210881d003010080c042d81e4810b150903c0404a5151015117610841040b94066a25030452510352003811410401108515024002d0b0b0f80d910049a01110303e41000d083c003446644035040100c03100051201d00600f02401d05052205200107072304214003c081c100d60f400da0350b41e20010100e8942d1020780b0000c1c140c0106202040c03052098554102c50703260003 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 86007474 1250 86006224 86006237
    0x10302070f061803031b080112020d0b011e090501150c150c0c051009020a0306020d020d110d0e240c041220030d05030a0e0a020301110d1104031a0403 66
    0x12600e0754011541e4024100d0f1401101c0110790003010351501c2003221843c0750b8018408003000701a00203080a0381405260000c1944128107025992400c441a4046074002d0740b50040b036031504190030380546098940b9510007041000031505e00c000e401014180c40c4580d40c02c2d0b0140005202c11200801d0140341510601c01c00c40a0700740150242c0036a085e070324516181d40c1140c0c05180342c00b0f4030380b41c0d080c1c5880c030499181c14003140041e5500318684040700d80040c4056140c90040301000000e1140740000180c0915001c1034400c0d007000400035007161087e02c641041150880491a80c440e90350401c1c401e85400150090b0700e507000c803580380303680040034600a1401e0035220140c000d400e46a103d0242c694202250004032001102d400f050340d0004103501070503003503440c841c0142440c0409800d003994241c80e000c1c0c0a03201b031000c00c00c043d50315030000e00038011984141c2d28108154440103440b40f5140c108145808064a840100c8003103079407058803448242c10320307071011011010240c03045041080 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 86008724 1250 86007474 86007503
    0x70305090f0d08040f052d0603040303020c07031514160302070c090c030b150a0e010507060905101a1903080f070b0c03150f030606120705030304080c01020c1e01030207 74
    0x400f03030180026200206003e80101e04210401c0021180012061014090005030120411400c0c400000c4140180c40d02034480d2078510781070f00a8043c0f02c04400491003a4200001440200084003212884440b81041181d1042c410441040e46c1243d07200b02440340d00c04100c590324440e43c010701d1018040d82202c809581c41c1e9002c84c040c0e400c0c0095600c002510f9207020405464603800c0e08501000d0102410310b484058880500803040d92034895045c0b2402190001c00d000850b04a828480e070302c0802d030760801307680190b0f20005101d1300c40f84140d41031124502c501141002d402620f41481c00040030341c80076195a403040003540c0f04445811a0441c1030040c400040c1101030f1060003403e020b40d00c01d45030b18100c001000800404901c40e0701c2441c100c2d00c00055a140070402d16000703003054031200109241e00008924290940c1d00664062000203400241d180021401c01c0f20304000f40d0a5614041c0358104124040400d16650300c10043c029100c03001a43c0a540200185485820000150103 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 86009974 1250 86008724 86008733
    0x403090e0901020c121312051906020c0f0105040b0106020c01080103120e100203040918080d0e0705060a09030209061215060112060e07020606060c0703110d08131a070305090f0d 78
    0x5949400a14001c1c9010071000202141e03260350b1b5000e80380b61007488580455540310581d071091502003503c582a116000b81051020940480d40740805d00341c100c5265440300c1c0750381802008212400d4482c205a54000b141c4148041303243c1881c41e1059444041e283d08648640388248001c040100601c250315030003402503120701800700a940d140341c02444c3c50f035142c00400d800343c404220b1061040204010f688001500140035128003054058001403401ca4034241540382040ca81c128980c000d0010406c082c00c1030f8403840a03401e9030306c02d0300c12241c2c0351260401d02c5003c0d11042c8105d08036401140c82d0000c0f00d9102c0b901c1d01d5101e44145020750b64000b1143c00034007100c2d081d42109405c13688a40c03c014103d40c04004150b0418000c1d28418500048c0b0b01c041c85c0c4580441c0401000c64510800b800265a91141000c40158102c9405a0349001c44005c0200000080c030803035102915465002ca0b21000341c10035a224141c26807600c518164000c2c0402500c2802001ca0380d6000103103061610108 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 86011224 1250 86009974 86009983
    0x18030203060118060902041a070201030f02030a0f0b0414070f0311040b040602010507090f1406120a020406081f2c040602090118120b04020607120e0f03060403090e0901020c 76
    0x9019004801c00c051843d10340710b4007941c1c02c07900318008507401000100100307001c840350725105690b0004d1003921a0b00c0d03440120050700c1610841e420042c0044280301406034039034021420b00e0641842000400b003d402030000756003101c5000da101081c82c100207180c1c58043c8250701c074032280d140313000034038856003510391511038200c0c1d08205800d040202d82803041076024400d86e030704440c450400c22450b915200400c0d4002078640143c410b0003140c10600c582c5610707031006035050240c4600c1e201c022440d10f80c0c2500000e420170b20440000800e55004079008034502d99842190b600d46000040c00d142c10281c03440ba4001540080e0034849801582c991040da01e9800058002d078851a400b69403250b10b840010032540e480b00d010303601d044a401080220064441100006560120080410341d81da0300010311180100c0b10060b250200401c8945181940600018200c1004a6407074072000d10240600d583e070701044400a01207000e40c0c4c414021303400c4405005174040d246100240c0780c079409110f0300b03040 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 86012474 1250 86011224 86011229
    0x9031205030619090f05090a0b01060f140304050a05150118090309030602070605042003032a03120a0f020903150411030304060e03150907090203040f0b0c03100b0a02030a180302030601 81
    0x2185d954a44007282003803a801959005103101000b00101800c60321244450751061040e0300c00d1005030004041214040d400303121702042502c107175544a2500e824081d031502442e040486103070080005980c101d106d0081118141c0340714030b01c5000f90500c3d000fa02401000d44100682c1071082e8844000300040741400103051040c483d01000c9514106031074400540080801e82a0756202c42134a41e02c80d9480c00415118444002c0303441d82e148015138613000c00c91002c00070300d0942c280000a0301c0032070101e96054080c015150340b902080504c10760b07100c6030700f2405606015980f541120040044d04607070300102d03e0b00540036011030302c03901d100500002e18652140e8480404100502e038078a209240c240003031001d040071828120a1032405c00100f9449040c907016a20310281d010dc003080521103080d80b043d01042d8020b28194560030098110004c0b5001112015995100031801190f281484026107080e00b0041d0015410100f0b1203c0540301030511440036458003a01500000c0913a9041021a00 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 86013724 1250 86012474 86012489
    0x70b0103150e03030618040c120b01060e0607020f0105131806030203010e0c180c09040603080418090c0b070602070503070807050607020601060e010e01021c0207080d09031205030619 80
    0x4024800c9401c00c0c0655550381503030750442d0000c0c41006410b484024100c0021200f43d5032140040e550751901038000c10390f03070b00150b00c900c2c01c8000d03a10400c00c10740070350b03416113400d0f8a035070300600070071303003c0200c0391048400080d0440000403120000d540514041e1600018550308401c2c070b1611010310149054008500000d0707217840ba00d0400a508003880b0304034151600c1009008868804004038281d8031410a030350945080f4140010060ba004005842d400e01340140144550755890402d680190024000c8640b015004a2102502000791041e552030a600c07088201c2c039685400c0303000406401c01041a01c49640810950740000c031f09100a1071405d104000c12511018681803051a0640081c101c030155445003006104654004d81c2d64a2650424a0181d10703555103100102d041c9582804440c081018002c40310034015000700c0e401003580c11030004c455401c0181c107001c845015803840050075034140c0c004034034102c41c03240004651108000e0402803444c0b680c1103400030000142d42c480302 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 86014974 1250 86013724 86013743
    0x110105070e011b020f15070f08040608070206040203060a050705040f08030316090828060e0a15060b04050405130f0b040213060302030c01030b1c110406090608030a110102070b0103 79
    0x80d0540e0001c01161201800305221640d0143d191302040551034100c400512840d60100d682d0407880c040c0c0100c070a01c80e4040c9141020030030790310b0031400d42e400c1400355101107149800050b140d01c1c80001e459114030b400070010815521025a500020040506203034100303c03080001180580d0100100001044440b000703650724500300b855201da200c20300c14203004001000b0000c011205c8001035040d43e6048030000207409201041c40003110b0011140f0051419090003400d00d60783c0c00c003003109007020b4061203c807143c42c00616800001c5075101d0003942030711042400240054240355000c01d60007540b03500070921380701c126107469603801e07134400c1d00700c40314400c036000c010850801d962a0f410000224031b0a012076415680026140c840a80c0c0c030307504240d0b843c0d894251a40d80c21110a01200307109a05081c4a501402c081101292401980d4000c5043c040001901e110b40e2240c2e800f1904010055400d1240c503000c03c980c6c2825402018504d0342d02030110300003042c041c0c81d07110300961003140d444 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 86016224 1250 86014974 86014997
    0x609080c010207080a060b0f0409050606030d1e030e0717070602070603180803060f04021c1118010f09030b0a0c0f080705040b1b0102040e040309080d02070b0a11010507 74
    0x5240c841140d060300d04541205004000c1d0780e00000d45000010f40c130410106016254802003008900c03041040740d8802d06000055003031003800f045a03405582e069043c0c5074800399107001510707840030607500444000d000345841004544290700501810b440340c0c0c2681c418960381c114070705840c0c40040c2c0c03040c0c142d080150100403c640400204d002040e0509041c08824030405400621130208a409400c903140000080c50541e501c40700d81e000c00000034401c5440b48003040c900b0030003583c0d00746010b04ea145092080000c9040b240d041d00d81c3c10002500c51525102c1100044442502c2140702100388405540040700040f0840301703040c4660030007000000c0c06584407100400350703020700500383c0034001220706100781c4590000031542079640e80e510302943c4984201d00280329075401100009503520100780072aa403d80411100c0c0585c1c000d584003001d0765141d40209031584282c10000380540e102c2c3c40c04202c40d540d400064948120076060901207109018203090070342c0c2c01250380500103961100030 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 86017474 1250 86016224 86016239
    0xa050a05011d060c0307350a0b150a030908120a090c0b0304030f11030903010203130b180706030c200a1401110702061e04030305070b18060a0c02160609 67
    0x84003140482c10001e000d141003c098200d5540300c0500b02c2d10820503084060b101000300341540c0144198981d0920604044420002e18000b80580da491502414040c0c10411894945003a0340c20408170050f2500c1d04191001c15001046a4241258600d005004803207100380305092291103107861140204411103585000d003c0c040142d00b201300c02c503070148284070200f94000309030310402c241400e2144204441e120354602d1801800121640366000200300a9040002c805070b00b00c840c41161030040e144c46010308920310743c101d08251035280e4042602000035074443c0d0801c0c0c24580e160b082144503c8008141e0342412000001002c8465000510700402c0103290584002c640084d4802000080c800000c0d1601a20a52030003910901002c540c102982510010345450060500e40c0d0039950790360b030b2030302030030307a400c111010b807a43c00b28000003815607014041000c40c1414064003500a60340e400035481c000b0702140710302d0400c40c0700b40701d030140303001c0900d8010038042c01c0d2984a100025140010 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 86018724 1250 86017474 86017511
    0x3080c06160309050309090c0c07080c040e010905030d0908090943080405010f0203270303010302010e0103151a1206030d02030403030809190305040603140c0405040903020a050a0501 80
    0x107182040610700720009011501c04002d41e0030440c012100040e40d9100c501404856005040030300040307000704c01d00015200c0c4005580e43d01e10300141da052140318181d402080c00ca079180c0e03401070465001003240221001c2070380e020b006018820041d0a0401400b000450b0644208442800720310040c40e00000d086525000707100320400100b01c807841100c1100c1c0401c950549020b040e4800e0100c02c80c041070800000390019202d0080a1070110344a2034258050382d00803011110410075203050301c2d0203840d00c190200c1100e059a4041e184e402a8090b81e000440040040003514440e00b801d001001c0303034642000004d404040c410b0007556171504034808251943c014040c1505200c0c0e880f0b040e03a001020b0300401550100c81e01420000c0c03666a400140a080032207210898440d0101c111800341019084000740c0309581c807a81d4100051042290210410306060f50030061380c07a8144020080d514040d085410010300c688141c0341100815603806141c1042e44a0131100c594598400c5614804e441c003 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 86019974 1250 86018724 86018761
    0x503090a0510140f0c0d0e030d090b1b030c030f0402040b0406060206060a09090b01140a0f1e08010e10020a0203130b0903010b0913080a0e03030304060e060c071106090a03080c06 78
    0x1504e90301c050804002003100c0d40b00e140b600850142d201e9490001c80a001c2c0251101c01c00240c0b030a20a00a035480c21100000e411030303003d8501303081180d83c04100b800c0c041c1034a104a001086e194550384481c108071201c0140240106d9006880b0750445030f03e034070b807070040710002c04094008084070f08241e020403070310220941000c45a0b507d0107030200e000c0ba80d41c8a81904503002d0080c03003a6001c0307840300810560181500007030030303d0a5401000500030301440c020390190012041c2903100e541c82da50501e090350800407203071031268007264451603802000e40c020091005140122483d145181480c000d48060a901c2014088400b0500120301d00b4280241071441e08203e88401c22407520b1003054825400030328002d401d4003000b1400c031410a000750720800031014002c048940340d107010b1604c0c2002e1301d01e40c04004614081c20300415110340140d815218482e6001d210626080702300c0040c8101741c0c01861000e540800d5600300000422500c000074a040d120103c0a0192071411907041d48080701001c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 86021224 1250 86019974 86019991
    0x1302040b0f22290603040611030c090102010f02030f370b10020102092202040b1b0c01020d0917030f04030c06030b03071a0c0a080d02040303030e0c010504060503090a051014 76
    0xc0450b000154400c440c3d2040f000c039901074603501c0c0d42c24200c005000304030401408100020030b01222222100c00790003c034900f64000c2c010000404050300c107030b0006542d2141004c0c111004600d10f450102101039250050117091034201440085a030110215448640c4c030040da0b8404030303c0c0908014854032038469190009500e440c0200011400e84c40c0700f12030104800c220b07481314110030030454046800410381002080e4403082086841001a00c264000100c580b00f200c0c2851000d50011420066102d01900d039040703032504e0a010030345041d240c1c0c0440302c4180010026542d40311508001b8001035401038800c40103190601c1d202400303c0714090240c912a0307210f0705041040d604040640762004030070800481d2589040036815244c004402c0009144680204880b0400d803140c0e806082280c4c041d6600b8052565003108407a20b4219900381540015400c0200348031550141c3d000307507000400c910441d03100314800e0b1180e500300313010503813044480354844a07000070001c0700304070854210525 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 86022474 1250 86021224 86021261
    0x5091006020303010e0a0f230a0902010e040903030b04090b24030705040e0a05010617120403020303032208040906030c0501020f1f0b0613030c0e1302040b0f22 70
    0xc0000c040e41d280014822121386512560005405440c1c84c1c10020065100d81028440700d2a5074015403d080102c009481b00a440100095044100d0f401007200706501038449100380f0b5105418071001d004110070039424940c441200080d191503a1050780501070003604040354a00303003c0004800181501c2c844403041504000c036402c140e0300803d11004549007110001744810080100d141800c12115010b803465180000006120032103804a040491102c3c0c16144001300c480c084401c280181d00000e5056802800020a011500f010380d4500c480d040184415403420303aa0303607643e03950007500070316002500d80c50104104090b082c5090f0203040700340080e10000c008126080d58614000c1002078084480c0d980b0001240120341c4403080426010704080d550305600313079000701d41c0002840120b075404492900052480e130744c54005406802c07601c4160a44003c0354080002803d0000c16555201150081c01e621956070480346264502c0c3e08001c4024001c3c2180583c0111540800140e951011 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 86023724 1250 86022474 86022479
    0xe030303100b0304020a0b0d0501051f0804080304020a0e04060f150602060703090c0512070e010b09010903080a050d09050a0c06020f030a03020d06030f0b09061b040306020304020d02060310050910 86
    0x1000d2040c81c00b0358800e05910340c1c503607560340001a4030440030f520400600c400040d16a01307e11403a00000d050b2001075800c07085d0a0b40e9015413025601c050030014000680000100300064100c100440c6c203c0c0c001401d2166580c1c46006003240d503803040d42c088130055912044062652820700452804845032003004111a00d0114085d44660000380054109640c4050001c10850034a680350301034140544030404034004400515036070165401030740760407050040002444050036080750850401079403500b00311842c541c0e510100742c11541c0c1020600ca81402007940005041c81b802c00b00c1801500106100c1049003842041e13440680c12800464014481034982051b00008841e0ba48240c0d18005a542005805400003000d451700300410b40c40780440081d0038086d81c110030501a1201301c044c0c036030940703e003074068542c107100c11080001a402800f007000031400c2c030380c05154403a00241002e0000c1c1400d9000070800e83c806c603030400b14003642c40820300c6903043c01c1020030743c80810090800c02250 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 86024974 1250 86023724 86023741
    0x1103030a0503060108070201060806070203120a05010b091203040b0d090605161b050a020904030f090b0712030905010b090103060606021005090319091a0415050a0e010503062e0e030303 81
    0x1000400703e9040c4410107011400c0b00740300f5886000100350741829039459092451000b03441c0e0307103d1640ba041c11007440001c00c14600080c803c1e03031b04844240400510388020b81084c05101d40420320144100d020900001948112580062142d00c03020040041c01c90140d290501c00c03544064500540000c00305030b20f0482c0340e0401c03418096100188803182d40703110359291241c502080c40c1030007034000c9500c1050204143d04440c07201c124041c181c80e12000340f512910600c10070b01621101400398445003851340021350096000c0d2042c0d500540012400c5007012002c1005c9900a0b8000c032016561400c0800400394184020b80711850507000c1400f950511180340c6542c0d003d41a401f107080e9038a03803498204180102442d200404245043c0b40c08000301c400d8111454006101344c00358036000c4081401c41d01d214900300c600e1400b460301c03040c02c4048405e004603420303000141550340280500040c0e450f82140035940d50b413441010700f4094118400440e004040300d10007801103000c0d510a0080c0441c41 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 86026224 1250 86024974 86024977
    0x30304030c1818021005252102061e0a060b16020405010803090a090506040b13050411010804020907110c031204050a051f030b010e1c1b0602120705011b08041103030a05 74
    0x3010b038a02680c5400c81d0090980c40ca50303040c0b00c000741030002420060104070f1703c600c0c1800108d0211190504600e21004180d0b1118000c8038000700c0b0310000f0b140420246407000302aa004081000005940e83d00d5120001c1c840e8401d030030009880b80700c0e2150380110300d8180241c501400c00080518103000402010601c010018025a440a500c880005140c3c6d1602d43c082021414020300101c06199184070030700c01030030b0a407000e54420315600c848804a500510025000e03c1e405000c65501d42d480102c00c54000706201a83c517814061100010450303074042040010300402c040c84580ea4034070309010000c11800319800103014440d2407245003004900080201c00703655407810080f840a800c0c4004a0341d0740303413920300d083d441005950b40e045045000101d44880c64802c0c0c21858441041510524200070203215520060380724520311075540301141d0103814864414800440e40703a051f09410304030b5070082d0441000103035609080000f8003e141ca08001c01100a601652070320700c0006005120703 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 86027474 1250 86026224 86026249
    0xa1e02060f010f052d09040b090609030702010c0f0f02060d1410080a0f050709050c070b06030109080d11040306050c0309060709050105090907050c07030c082514030304030c181802 79
    0x2600e03640003851350000260403030405600001b0010440da03e800c0ca06450100c0040d596031002d8414a030000350f0440002088481c00c640507151040010f1480d601c6400901143e10119962a054a14840180c40b081c0150084c007094000208a0100700070161000050040c0302c4500141d0025080090300000308900741e000750800740114004140d410907500e840200c1e4000c840d070529100802904801c800c001d00320451180303654150f141c5404040602b682c0301280c1c081c011038001c010032090800d41e58170820074440244100f80c2003550743d8841e07004a4008459240d9507150000c100b00d0030013018003507a41c0c0804c1501f004e45030241000e000030114000c203ca09405a0810000316403054000c00035500580342c0d50b02103030045d030b8480c40c00d03100b04110341c49000c00d1072003a00b1900800030245e00d00c0d040c0307443c011114000c51500e0b2070861a2641c0600707075004d03014001000040082448a417001c0007a1224402d43c0e0780104007182d01408079100429189520f100342e0804000580d50074910110 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 86028724 1250 86027474 86027509
    0xd0605061306030f06110c0f100e01090c0e100e09070906120507030b0c0405120120120406021602060d060602060c190f021204121112030409020a1e02060f010f05 71
    0x1b042c1d501101d041d4220712810969075418030030b4081007145d003030001803004410084403d0500105c1c00e001c01d494240c0f0940d500c020401105400e00740041c00c3d54404503a44070300d65042d0a003105a55a14442480000b507071003843c40e80004c0c00070f00c6200784078010000107104c694542d4000300040d889068842c02c01740002041650440b020038216000c100540f800342070014100c010028400708010700a1001c860260884001101c01003410402e800549540100301e00088074681d90b00c0c0d45210003544410070100e60f081d104251140962600700140148004054001403804d040c0a406443c203400149001c1918004000000303020691514143c01c1c000d25060420121110010503801c3c000080030f202c140a40114001440a1482c56a90101801181620214101e0805101031280e0401501e0040d07071040008206200c800d5005000c080c405240000c482e94481108586440c060700500c0d005078009010300200c4410443e02c5070042c1640700070035a885150801040e02000469010360 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 86029974 1250 86028724 86028731
    0x90106020a11030106051002030c060109050702150a0f020f1b060c0901110c09091b03010e0304030f08040902030112060b03060105011b0611030c040f06030203040f0209150d0605061306030f06 84
    0x40c02c07500c1c01d40110020700801000c1e890100c1d00890005d40e290402c80d103a9000d4803481c0000500140c3c00d20035540500943e501401c0703d943c0c1080d10303c2503490f014201640450340e80c240700400c0c103910b101801c40810030316021a0742c0c03001d10010b041016048203c0d41a180c104c0018000c0f03d14420045402e14002800c3c00c440340b09241031403d0400d4002c0403003c0e001005101007140b02c00000c00d090819001d44902030060f90801d500b8942220521046a039a540c000c000134000f292000d1811101c40d403190482614158403104400c0c181e820a03401645821841002d0104212040c02190080d540540003051190314100000381603122030359540d03e2106503146010140040360308000001c20f5402466560f90a14030503214441d48644240301003018110800b1640038400d000301d0b406190401162580d000b096001c00814103c090564000b004082c600c0c0e140b00d4460140c1c2d8034009009103000102481d08400780a4100382c10040a48a6490608144000303407080d080b40620700d40005001 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 86031224 1250 86029974 86030003
    0x11040c1103030408070c271109040504260c0604030302090310021303110607020d0201053001030b07020f0601060f110a0b06130204030209010b0702040204050d05030903160b0a140d020d02030103020906090106020a 93
    0x2340c2d86845984d0380c01e40c205e401d1004010030b005c40703058410f2003010166900f07004040746a401c004107000342000c08074142c0090001c030b400300b486900a40f268038002010745840c111040c0d01310b030403640f00e80091200f20360000400c00a20003d140000042c0c0410f88000303280212035800a480e064030000c0081c140305002c52080410088503116190065414004081080f440d40d030018510400b448101e03a135105072030001f8030b920f00c0803d15040c503089040091010703900340340040d80c031001103100c410100158100c4c2e9041d004407c10001900d540a1002942c2d107050940603c82d020070900c030410703003840c010001040181c444c2400307181102c00701c43c0c072561160118030008019220381c0e44825441540078407548248903002c4020120a01c0450494070786042001600003008243d12615008132828050b00d10700324025040e130f40301000a0400589860f6941c0c0c5000100d07003100004c002ba440d4040014011410144001d9801000c12680c40e1035562520b00025504d8019000042000d803200e01d5a = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 86032474 1250 86031224 86031251
    0x50309010c03090b04080616141b03090a06080a0b0406051806040b12030301060f03200306010c050708030c070e06031e16060e0f090411040c1103030408070c27 70
    0x48000c4c20801c04040e54503a80e464100355190010340d0000c0b9000b0300c2003480c1c400355010309200b800f4004104c0323489060040b41e4000461110818604094901080207081c01d181d440660f280701801642d01d461060341419851002280e5403600d619000314a0941c0c244903e58030118070184060340411440f24030b546903c08a4041c0c10984040b6410030352044c82e04c4054640840a141a22055a20011803018a00045013038607120b01640000f5042041003030003600b945d40045501c04818100b00d10110030369503500c0d2401845510800982d000854030001c42c41c01030110000401f100a10300038203042480001351202602e20880742d12282660501d080340c0300138040912459400380446405039500e44d40545106103000c1658412443d5468812141c508085142d024541101c0000000780051062000800301074011005014015140218031390042000358031480c400d0074070a8488816141c2203003c051641c1289100035494014010240c50300c04501100d1140c480003c102c5a410040 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 86033724 1250 86032474 86032487
    0x30c151107030809010f0c0209010e0403020c10110712120e180702010f05010e0405060c1303061b110708032b0c0806030d051e0a02010b0a0f080c01050403050309010c03 74
    0x40d142507805031400c0007007404200005008030034400e0b2100c05440d169a101241c074078000d000000d50000c1644014000303001500401035010f0300c680111a050b8001e840043c00c004c82c905c40100c0055580c0c80d902420351001d00c02040104008003030294006200ea4a11282444468520f070800c50040c40e0000140d4462002240d15101c00310030740ea4500707095000034060109103821000d039130304201c00000e052400c4188503200c3da8010300035085548416000200d40d90050021405810410401001240c030f18402c040c0f00554012030004040700e198805403803044846401021604012010050480080121017049020b00f052500d080c15854a1140c0709480c28141d40301b2074030b800da960352400d03003040d507981c000c0c1e00c1101100d05440c00381404403010701c103031407100d03020588603014000701c691280040e1203000d4040c00041242504403001c03842038403507540000b8407400301d50b41c2040f5940040c005201500c00a1904e2840e09007507482c1c40f0354a20070503100300e041184000b880da00b410310400 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 86034974 1250 86033724 86033747
    0x1090309140325080d0f021507030e010204060503011a04051507240f06150f08090109050a080d0b0405040309030b04051f060e060a120b09030403170403060b0307030c15 74
    0x801890544026803d140300101e01d000d0030b1003d214401640103110300851030039031a40419401050444a041c100c81c403081d6015107007809260310745680d50410030081c000761010700303800c0e50b0703854030303585010540305072500c10350302c100c2c0c50307502c100b105120070b46612001d0701a5110180c3c45580d14950791419440345c09103070401c00c143c00211704842902029640000c1140e286075401400150740714180d2070317042c0c8032146030840850f078050740d13030340c40c15000d074003c00c1c1d000d032074800000f0340320903a52034107401c2c078114410845242e040026130021a4000d842812007400e4241d50402052400782c0c2c3c041e05524040c0406000710b654800010100301082140f140302030214101404009040080703440038046500820350207000040c0007407828249a103003202169a103d0001420322441d03200d0500f07212020300020614042000084040b800e028100b111104208404566891440c02c02d03104403008400c216100c2d030003408041021992800540d01540c0c0c40081c01c045c041e00c001002c1d5203207801031 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 86036224 1250 86034974 86035003
    0x1b090c03090f01090c03050c100e130605040219120207050c0402090d3008061c0201111209040507020613060e0a021909060501140403030305040812090c01030e010903091403 76
    0x20015030800158085c0103003101d1152084541003c0000100300800d43c1880c0d840c1c1c0000d0146083c04118580800c2036011503100c0480040c020b5102c0c2c02140503a071100786c50082416035894408589a8032428940324450005400c50802c10b1664441c0d441d02c8207410f45500c2290041038400541d81e81801d0062324580c865200c2c4038900b4500114bc0b00300c0c5011807900000850440c0204480313000d03841c66446400000d010b0b846080703041440f07400e0031322a03c400342c1c10411005003820710304004104903da181c1c1041e00d1503803500940010401940c0005081900f15080401400b81b440503141003481200c0e880a004107001030058002c070710300f0840d001e020351301854040d16107004190201031501078602e801c0d42403110540b250011368081c08880440b0108580c00c010420100784240c0c840c68105105a40181c5007030000c884d03075403000c0b0060728400301780d0300200840641507070144501d00291286030028000402151000b4003100510b200708064025420540029550180300c81b0600c41e564 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 86037474 1250 86036224 86036231
    0x6050607030f0206070c02030a0b1807080f0705011706040e120f0d0b040e060c180604031a01080105070c0209060406030807030c110901050901031b050a0b0703021b090c03090f01 78
    0xa90030300500919951650001600490307011400040c4112040f030300051f0050001e084048450303450304a003280050070740058400e00c0d4144a11a081440014000c00140c002130100f290b0480000e802e0640c0c40d801507061060700d003006011240304000446c2e100408680c0003821441901081c0e060400000d900c2c40399000005042e0010012080030b00f072068161030b030410aa00d81c007801c2c08104c0d840c02130144e0003030348403200044085031214002d00c07101c1e150815000b56900580089012608107030401c403404402409600c00298468201d02c0c010043c1c0c000034006810280e80c0503048001e0340c0030203806217080a000401c50348407604007800442c1e004031a07550b29036583c10000c05804403050304440d07040e518101e14400e07283c000d0700305060340d8000b0403200d07440e46180d035080440100c4006070302c61500d0140c4001201d81e180075140c00100b415440442c0c1c0c1d203a60385402800d02c0703034400e09650360701003681494601342c80d030f892000d50150744104002d0ba6600c90481181c5800c60a5040501e070358203 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 86038724 1250 86037474 86037487
    0x20409020604181d0a0b040f02030a0b0402091501050a03090201021f05100e070f03052502011a090c0904110409020d060e07081302042f0301140a0f030213060506 71
    0x180c01c5408684401c00d0381c1c104111800e103060b5640c142d542034215038850b03020301741c002d000c640c0d04044a40c020348034031582c1c8006115a80802d04004c0c02c080103540b280701d000100815810000642c541c4401c810006507881c0580300700280ad280101c12000080541e640c1e86841164000c100490008954201240700d81d641462840b016100407604415400c080030400164008c800440ca4040c07001a00c440224200581c41280185401801da080e40c588000b002c441c5c003010404180101d029590000c5500740c44410a565102103003029903010b643d40c0c01c2048104400241502d450000840c0d000c2007401d00346003034403540d004541280041034400920840c501c030040d40000100c4200400304852079540c6070080d07600c0700c000c58410301c142888040101c01031030f056101603101c00005400310200d25074941801001500713150303080c45800c1c0000050200c0d0292107603540000c0400c07030701c242c501805d00c1840c00710744a0078800280140e4811844040f41c40450f04414081d02000c4c100640304c50 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 86039974 1250 86038724 86038739
    0x120c060e0303010302010e1206010e0a020403080703021006050d1e03020c060d020d050a0204032003010204080d12061517090a020d060504030305010906080304050d0816030c03110622020409020604 86
    0x82c401c0c40101d0105442002240e442d00340100074142c1c0c031545034003400103680307000803010000301d005107406006942004040300040308000030308000350199000f4449464004042d004403030094000d140702d04060310342d0310700080703196800742ea401d040c2d4508801104150724060749442d1054074031a5001c1c40200d140c145205403235000e0180b03503881441c10300c544d0300c17210710a901700e104501010303210b692804c41490344658507000348100c40300007074001850240d644072428280000030340d100300010b80380d400070b051850b098058140a4200c2007509020340d1a10203001c0c08201c0c1489080200c01030f40f40c0001c6030318200b4095584001d40150500c01500340c0ea20700800180740803902100480c0c0b07841e0022501031080e10480c01652410001140303803500340003c121040408650440d0305440400540103402c5548c03a41c000c416100f07844a18040c0300501c0d0240c50003101184100c8282d000d542000f11034072031448088001c6c030f44a00c05c80d1000206001103400741940c03000194010304006400280103 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 86041224 1250 86039974 86039977
    0x910020906070c1206051605182b020a09020f0a0f030603080703050301030b090a020105040603020d02040b07050105061c0305032805040b010911070803040305031806090a060b100903120c060e03 85
    0x340b04d41001c21041e602c00301587e04000d00d000300d607030010340240401c041281d280c40f0241c0000c000109500070700540359030003005854080c400c3c040b0610b0a0b480040c11810004400d00151078005003e41c01c10002c000c0c502210b0042000300010030410081c86050307a4000d40c0101c01640d0030540d116a031b1011805c02400583c0280310032100600441c001802c0c610010844494440d41650707094505441d00720210040c2d00400080b0120590802001883d22440001044000e116800100c0c80e481d240081000210105c000d051f641840d402c10800040c0e031060443c0c5e440022402c0308180060042080c8010b0071003024002500c500d008244400c0c40100300c4824100c1c0c5034104140030103812402034440901640b000204540401e20101d40081d01400165074440e6101040c2c01907108640503044c40c004043e80d152289401044101051283d40d0080d102420400c6c1d440705041000c40c04018544031241c40041c00c0d8000101540940794401c14181171101d41000c41484a01c8808014079100d = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 86042474 1250 86041224 86041259
    0x1050912190b01060e030607080a020c0f1b090f060409060621020906010e01170604110a09050405070507050d03050403110106140f030a03170702070f08030702180910020906070c 78
    0xb01649400000b81e8034810111494211809400f510064070b4140e000e44600c0c0d0302803c44c444094083c84080580b500403c0102c1c10681c00300e00500c40c11810007903e40d02100940c07084c80c0603100100401c040c014030008050b401200039180002c0064260600000a0210b5040502c008800202034082645074a034054a164022220f1f000d45880e40710044d52280460201c05000c03a00f000000c1c1c60321440100d500307034440005480866410030300c0c802001c4941c010f068903000b0079070f440028056810180300d420340c82880d82c100f846c9484066112182d64802c0908001c08040e01d4000040c20181700d4220001d0580001001b440850303140c0c1d1461000001d0b400889020345040d80d021011840c2c0041c544440740d070143c680c140d500700140c45802c403614009016205502c40c1d0140041c1c14100300b010400246881c070055034a80b030350340c0f0400c08100c480340d0380030060109a0042c018405400f0401882200304001c005175548032420200f4ac007402092000740140c01c10b03140000b12094940c00150030f = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 86043724 1250 86042474 86042483
    0x605070b060301020a02120711030a0b09010b040203060112020a12060b0406030f020307050a08090307020604030b06040506040b2d030d0206160305100e06060705100b010f020a080304020105091219 86
    0xe903940c03050180342c200e000f10780041006074000a040e10032200c00200500025000e4200442c03840941d00220f450011030840c2110340444040400034004000e06c035041301440121001d500d142440340c0024400c42404071907080580c0e0001d90741605600030711456551144040092000c16554036401c03405410600c2401c010a040692000040c0c2051003128403c2003541c81e00c900703014200700d007100c8281c0d004181c0180c03448101321940150307860f0300141008601c6540d0802061071312a0030312094070406008140500d00742400700c4840c0e9285000050302040202c4110f940800200420400880089415825010313410544403543c0c1d010803040e104503980c1c840480385000d503080460444004480c9a00302d44c040c00d0b01403107003507681c4e04000c1d00044001c050905141740c0fa01d0f0a41401ca2441188140a517207440110123960403810710f01403801c0d02c2c0080c01c11454180c4403d15203100c000c100038100140007565405039603501410090011041c011200b202d1031006040040d4100c2d1207042c1c1e13 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 86044974 1250 86043724 86043743
    0x3160302160c0515130e04051009080306040c0f0c031209240c110303070e010c0b0906010609051206010513060806070302090a090e030d0b03010605040e03040e0129091504060507 78
    0x1d20005200308468812084005c3c003800c03245040354003058258060821120741c040d00c0c0c6800b103a003c1030f000d140c10207401418100d9403428814100401c1380e241c4a0000c05104901d020311a610380c002c04400203e50305800c001c0c41c17040e0a0600c450041030880001001010328011220700100140100c409000342d00400300900084007000b690f0104600d85214810783c403c20000d20785074410000d91505504c1810440c0015000f96039090b203c10013103c0c1101168000c0c0b00400244d507005880c00020702e4103546911889000665454541d0014091680281c01c4050244071120103a408030005142940c10780710b841c1003417103004003c2c1d0b00918683e0300c035005411011811501c01c0c441c0d0744079080140300a624010603800d030310f00500300311180558195a50100081e07903498a0040500503011000590359950a000d007100640d441a00304042c181c2e0001307000e00c280301e4414005100400000c1c0320303d48458000d8001100a00c01d8092074050301000310300085e11075000790152a8180c480c82144 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 86046224 1250 86044974 86044999
    0x50601060504050622030204050c180f030709091103071d01080c09010302040504061b0e0112090201090308030405070f0b03091b0a0512030d050708040b13020603160302160c05 77
    0x4481d03070301880c01440e620900c1040240903481e0000c072050080741c403644500c103a460340d0790002411140200e4481c50386000024007000a02c0c2d40d054402c050304d070102c80548485031000b01080d42e8420030b0180c64000d80d60751003008113101c42010020409a0300804582d0903548940480e00c8058401c4141d1002c0425040045052000070803804a2660b02905100300c40c0c0c81c2d5001c02016140181003568240d40c0c904556004090504950600900b41d880e941c1c1d24a9500300014120595112086202847c2c42c00c03c0005070b074000c1c4008106c2c1c2d0000c0703009441c0c2c2c42e00e050041c03c220903a40000e060408a060000d041400322000c0e51182e00c4400a80b0903601c0c40801111103483d0603218964003a071112803c0c091032400b059005195910b000440313060070340c042c05520858a0030b86803030010401000401c403c0061258107036501c00303602d00400b02508141d9010a2250001401341d203e02410b4401d1105242e1103941665144920b610318100d444159003812030701c800c09070142c42e0040c001311a14 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 86047474 1250 86046224 86046227
    0x2070602030406080708060415060f020c0616082a01060f080a0b0106140f070f111c060504020402070203160512010204060801051e03100515040605030c0405070207080d0201050405060106 82
    0x3030310121543da4491080a03950b24000300c0b811400104941c0e44656a0261114440d40803031110001c2d0a1030b4484905034850424080e15044128028034450f19040003048a0f201c0c0203070004101c10b5014000640b5400c0c199880000c010046440c000b924440c100c8440c204001500414110b4010a07031580e801d50f2101301f010384581050a0103004441070400411109100b0103540d8143d1314120b41140c1824903052203840180e2242d241510f4600c0301810880502c219480070003009201180c4601288006240300900100d118001418266541000900395261901111412a8018260740e210001d0001c80041149540642c40c01040182803134031940c241442118180c03400c649582065030310702001c01021b0b000d4010750340d04c0d6580d0f40c002c0c203125480800143c81c5040e86200c0100b4940752250b4240c48254507080d20b035105e14140b031003c2000342c5011407031100d0a14280c4011543c1e59408d0400d9240c4405075211a10511407a588604002c0d0f065200602443c42041560816641c4900 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 86048724 1250 86047474 86047477
    0x703020a0b0f0702010e010905030114010905070c120c0c0911031e15090405101503060b061303030e120615010215091525090302040c090e060d08041e05010207060203 73
    0x340b0108894041110102540c010401d0050a200514046002c55280c0022a00f500c01c0c0741c04149100050704014443c1c00c2050090070b81c400d0a52910b04001e1407952240c105104486610106100c08002140c051103200c8030507101601c3d106a060045041513440750509606c12034410702a40402d4031426a1040344d02403243c000d4105880c51403041101400300304410001410480e142d22600348190031411081c000d40b0300c0307171841410f21000b4a20b5403c081041ea843d240001b41702d010100804880c2042201c0040b043c2c80c2c1502e0902c0c1c00d1403656020800102e0072000450303e40c40303020300b00095600042110302c4882000c2e803d070f032695208a01002144032007529502c19541181341c540c60800031500000d80c1c4980b04403110260301c64401c507008502d204202d005000031b0f480041c18425820300d0300803444281030914104d1501480d10080c0740540202a1010707103e1390031607200c03a007481404400d5902030403c1403800c0c60400c4100840f604c9151982c4140d902502542c00c4c0020194000300 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 86049974 1250 86048724 86048737
    0x15050a0f180527181510060e030307050604050c190506030c0f070b01030b0103061103060901030204020d020f030a020408060105030a0302030936010825032603090703020a0b 76
    0x1088a080da0741000108600d1032040d1200c0d10038802c3d05290fa9012580b4030740e12a01450101024003080c1c2c2509000d54144001042c0500340406044144508806148496421510189400b1f80e908680000007411441180d802910b10320608060000340840411503d006540c01c4070360b0f24003419102001c4c0007200c5248109948810309000003581c03d246c0308014a4510940b080d0302d440c141e010b650321025408207801c10750b4021844801441041028894580541d0320b400005040d485e040c0002f495070141400b000b03005540104565602205c0c980507900c0f01c1c46c03600d0100f522803600c0c9040f000203402901c0307070400621a031000010917080210b254001150158042c40c60661800c0500c901c040d84c1b68285616250401c2c41001120b006407060aa40e582c01d0701d41104075450004000c0c94a44405d1051010302030b011450307140ba07a10041c070740d02240ea0002560420043c80e02d940c04031209168a604040507000081290380e1001292482c15240300726481a40703103484070000d9407035001e4413 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 86051224 1250 86049974 86050007
    0x130f060f080c030c0c0607020102093a03230306041b12020310050603010905060102010608010606020304120602040b13030b0a0605010e0d020a050319020a0e160f050415050a0f 77
    0x140802c81540c0e0030300c01168862082542c085c5000300001c2840d00d031034001c984450041c3d41c003141c0042d15143c492005d8010307103107200400e0b4a20781c40c015195020300182400c01d490400700300f013250406000b041c1681e00405021311110000203605c5448240f98802c441c420710891411080d4a641c00001087d812206c074107035900e2074245020700303160303009501c040c1c4000b1b120040c141d8002410799802c0c0045019128200000c140f034145103002a084d10f0050304031581c142d06100b01440030319800000d58044540b000300c480c10039881070070600002d2050f83c100c80007401001545000010491103a00216445010741240030741e50b1088141c101d45950140900140c00484042e9140c6003900c01c2182c00f600091262503016603900c0041c2c500300e100300e903038400103242c80b00e20015450105102002070901104840d054a03081c0882d286115181b82c035141448840002070301303075500c100142c1d400b038418441c0a20454054020103071450300804407100c00100c0c8211881900c61217000b41c9102c080f02d0 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 86052474 1250 86051224 86051237
    0xf020c1e0f0c01050a02010f020301030303061706010e0705070606030609080901020d0503010e0c07050f0a03120f0204080606010c210513090e07030602030c130905150118060815030102130f060f 85
    0x4042c01180c103a4070003104141150748681c017090240c2258801107000750710a40300012503501e4607004109090310329600c28202c0d0060001005000c80c0e4120440e8464190f14000350f4400e12480c2541c0113005940000e4505450b00401e0703000c0045030300003081c038400260202c44c2c11180d00003046a03188001d001e80c151401c11280070941d9040c4150283c58898410003e51325180040e400036880d1036072502c01540041c420100e095100240380c0300b00340c5003000742c4a0561502d4100560141d88401c00ba10081c104058030a0542c1400381c04ac02c90810605400070040c0d1075000c07000000d1450b0014001c0c80c0402e103000c07034000b54034002445803240b00001071020b0400380c2c1c910b8030368600a40008201001420040051000155030881e01e4070150800b624009460305100c11201080a00d450041d070503c8008580c0030050140d20f004542101c65a14256420f03580742d0f0399108440f042c0350381c015010360000c0f45580d82c1c509c90902d4041614500c00c2111200c03640c0300f10444403246130500d000b001c07420 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 86053724 1250 86052474 86052493
    0x120705010e041b23040b0403020909011d031c0b0f1203300108070518040f12030c032403110a031209180605060d050a0f020c1e0f 57
    0x642280000140081c4005588403c1916840880c0c04a18010f000266009402c2060840140d00079038001060580c85090505004003100d051180d808003a20524044000401000d0250030240001c0d0390b185002064600300c00780d943e0f80c5c2d00701c0300502c039215043c03052041000195115001041c0402002c81c003110300c01e030044c00074001c50080280390502003008200c040702000f41c0c000c501c43d4044500390032401480704202d0b00f62001a0410401174100d0361003000320b0369030483d000a464010900740c40b503540300c92400408420f602074000300208048181080f2031505540525a02d44098030103010703c40a03d0f000c14411400d000e404108699020f03401c0c00468141d00410031a020050180303004607132681c445072640f16a074883c0300c000402100c0280504006100079290592002000b840b0301c07400c203000141c0b0fa000b8604542941da40d80d0b070009000c03c2e004d40005003e41d09200c4210b5403801e07040d154036240c1d998244080e074000a000c0350118a043c000807255a08008140600355814 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 86054974 1250 86053724 86053727
    0x801050415030228080304050a09150312030b09010902031e010e18120f0304050f010c05180d06060e0601030b010c0b0a150306020c2803020607120905030f04090b12070501 75
    0x10301380d92030150000001460301410500020001c030160214000540c0c41d18036042c10096405040e802a500640c1032002d40320380d1b95601c01c580000d607544a0403850b114600380004800070b010842049503c80084400010800c05a6004500074003500307540b078210206c9441c08600700c65080c442c0341d5140c04210001801c1c0743d02c81384040d2110910000380e801001104800002513004a0b1003038200003000010320041001c104040f518450602c0c0c0280280c0a402c28003400c107000c0e002e042030084091a04010041d0345114101c6500d95005808104607a21080d1070030380450216880c0340420710740218904158000c500c1c0c91491a48143d21b4031450b9512010030005c1c007040c100c1065007040003180440000c41c98005044094543c03c000c1c42003c0550396a07041e04071807403905201524181200da40440d03804a4034561241950801001800440e10400c1c01040c41c107801410a001c041080c4e5881d20002c4024001c4808014080c00b04050311800c200c0e201c000d00c0903904e016031210b10200801e5 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 86056224 1250 86054974 86054989
    0x170a03020d03020c070801240e090d120e010903090801050a060302090103020609010516050c040507050307120b03030903010903020f0c0f090a0b04150e0603060a0615031808040b030708010504150302 87
    0x88150209071440a5076541e86c0e542502c602c003900041d0700d22a2690b01080c2082d00c04160003e155225031109207040420a40e03441d070718018040010800600301c00380e040001500050b80114140d0000c1020f403400e0304000300703034200c80d0154605035401e03c008100c0c900d030765002c0e030010380360001c090318110f03482c503406c0000617404a80c01c20f040c0501801812080c482c0c00c2208003030b044c005c401404905070306071708200455400034803500c140441030052001540c2d001f000c0c0588030418100018071040300d140000d10394002d0b00180c81d855800e20314000700b010b41c0410304918800041e01202c0c082200041000881c40c0b11540e0241c001d80e02000103001850640c204507000322019000044000801200d020084e190784c001540720381b0380c0700a112441c18100051507202407948000c01401d818460000d20745c0c0c00030f6119004042e10382c04805200409000f5040004d640281011f070390303907502c07400300d00c580c1c000316035030800b00b50104000030700350030306004800b004c400010340049501d00b035a0821860 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 86057474 1250 86056224 86056237
    0x20406060504062f070f090c170619030c0602010c08090601060e1306030218010e061e120c0a14091807060f05120405011a030102130b07051c050301170a03020d0302 72
    0x1507907400004401c40d1318061104002401604490311101810981600c05858251400c8020032a14660201e010020040b4080c0c01c42c0b0200c8a2950950051180d0b4090704190b8001800c40688440009066901584007281142844d02d030b02d60195113000b0741c0703a00c5031000d100f08030204004000000341071419070400d003103440d0b04400014042d502ca40104104442c228034000039001070b000180242480300d07602e5680464211010300e20400b80b0781c40100501124032045000f28014812101d600c00280700110914201030001c201e441d65800264021441c3d298800c1d000d00c03151004546140070309880c0540180701c450040800c544bc10303030102c482500c00c04843d4100700051020f100d61f01280380d5a1130040d4054400401d0f50301d81c00c4405076401c451224014402d81c4100f08442ca1207014407120320442d40620215500d51402c1d0070898141014500524102c0007c00e940d105003e400030082c5068480304001c202c81c41d00170a1640f542d9040340700c40a00564448031701e80e030340c0301e00c25002001c4 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 86058724 1250 86057474 86057537
    0x7080f0c0415080f0718090c030b0705070b04050c04050105010c1218170606011209020d0f03020115080a030905060703080609040206040902070302100b03010606051204030e150702040606050406 85
    0xb4155036a2549414070a400031078000a40000004000220043c2c03140d030700324148100d04000e80007081e80c421580c441c081c40300904030410382000501c001e0054065400898004a2441285c946481d0481d05c2d6031081c0f204900c103626000c000b0401d54850110030b0303a203e0f840440c81119861050050358603610f040d048e411608084000071480071130040d050000c0c011008021304440c1450030001d0181641200c1d01d82c2c0a5182a03940c00140e529151860030361600080e00e003108507842e0604902402034a403130f0b12001d000320000062a450009044440c25000703aa03240a1903464000304142c0b40309481c005000140741d440898002d103850702000d5040343c801041540350035500c016590a0f0780001c01c050780035030050750808403024510300a178480698100e008102a905110000e800380c011010040710360006400000e080501541d85034500020040800c9614058180030081c25408480e040f4012400c001001800c0c034042c40585041c0c49440e218035030310030510102a168410202e12412 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 86059974 1250 86058724 86058761
    0x20c0303070b0406111204060c030e0a060203040204060b0309071a07020a03060506011e0201021b0a0c0b0a05210412020d08130201051e0a140f03011a0909160207080f0c04 75
    0x8171000414001d1802801010451030340749000d00300501180d80c841c2620090604000030049031000100d0760441d516800030006890352114000318000740b032540c004000c046000414000c514000050b100111060508140d400355210400210503000b0b54030700940003150040d00f0301c006006c0d81c100300c2c0c4c00340b018500102d41031000081c05405a1046c00f036500941d40c006810004844051380364200c0130300071002041000d02d1a071300c009040789a031081400e10380012407000c418900c91002c85a010028400014030080c03500b20841e01030390182c804a0f00300154840c6015241e002080c074610944aa403500f0f040c4d60713030302c00ca00301061004050490400000b0001402c40381a180100c0d000a00c0d840055511180c201801400f52448441c5210480000b8000412a404910b08a0b8159001c40c10b00401621400d01c62107540e0040440b03031076126403040100803079089003001030349620440d5800c4807030103583d07035060a844081ca80050320494001d041c480701e031070070507400400742e40e5417460b07010 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 86061224 1250 86059974 86059991
    0x70f0302061e190503090115050d03110a1401061d101701020903010f140c040305030415050c0a0b0402091005031903181203021c0518150406030615020c0303070b0406 73
    0x10310f0201c0c01c1055900c0860804030a0000340c050910628410b034903981019890395043c2800250050342500f4001e08001d4011807184024806203c81c1414541c00310700001d000c0d2401a00f00e010700260b000300104140240d00301050420000301e07050090320454800e00f981e83c10800110b190101081400503159000c200d00350700754a00340324240c00310912510003c0d17006041d4181c2c04d22444003806910710010184001c0c40843c0002c8101d402b100c400c89203040032860110015192401003001d541c80a0141165407000d0240e10b01009100324130840c0c100601307690790f1240c02e110510301d00a2a41503486500700804a10000201010242c040c3c1484030b102c00c0212104800d4841a40105100003040a107007410075404000b1100040c8486001a005504200d0024100e024901d010014070201c00302003003041d101c0d00240d20514103041c96440d9680c0c0c9401c00a0046e08103442180035060a0090181d141403000c108200000c1009015516180ea50b0b1a8143c503800041c1061300c140d030340c03407090 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 86062474 1250 86061224 86061247
    0x110609120309100c021e180405010e21090f0406030209100e0c091503130501060f05030709020304030905210102071203050702010c020303190204180608070f0302061e 73
    0x11096468000c8000310b40d101258814000740da04440d5000f010b2000c00c021a00041c0d981c010841036005c2c906c04140c035164819000603010402454000c103521804a0511051000641000f00303846024000c4810482c01400c5981c3da01d001c454420584183c14814214589041401c034900c6180080001c07a000351a500018143c00054904540004590310200f0410340140d0800b40d01840c2c601070581070401c900301244031083c100492060140d800000148804c1644c0340c81030075181c014000b0015281c8800000d80a01c0490094510074403a03a07c001401102c0e1b802103d105c0e03641950355104403881c2209000300045480d0b43e202d401d01005008000c50502440540b814034022144d40c00706007401403000d421110090882001c44e414142c0144040307400004403a0044155011039118050502d208070083c00350340c1101e9081210540308001e00c4550f9049041074607105000d440b160703699650b0381c0d01d260402e844001c0d0400d1085c00304058005500849912103046440b40610300032030182d4 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 86063724 1250 86062474 86062489
    0x120e0d080402011413030210180e090c240304050f03070303060306060b1306110f0109081e0a2316060e010b01031802060310050d0303020a08071b110609 67
    0x41040000d40080100320956a00072861000e103001d0800c0680340a40341215480480700ca404041d009181c807260700c2e2201071017903003442c80d11050f485c0e41e50389854603104001c030805815602c0759003074460900d021002c1c0c0b6110300c1c9078045180b40c0c00303945d00c0100d902c400040113400080c000c1c0c1d114000c400c40b800d0403a9085c80100b18040c480c0d80c001861505624005d030446020790040051a5018010580c01403085101305050f1022400c0a100342024050388074035141607400000c19030b50030070554404100e00700c3c0192240c0c0e100213104810354a4101c200c840f65001703c070220f0000130000000010f0100c000760100d4034140d44150502d00c1d1690388000d8aa91070750451040340d51a50b280b02c280075160080c0300f609000d201c02d180c1400345104c0d1380111417600c8a0b090000e84903483c00404121004440081d90009040c00352620b002140103080c060020340120714050013250703a090001329020b200c0d00131145900e4180541c1c04845455440d52103c3c0c01c141118107400c50380030070000300a50f0b00c000 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 86064974 1250 86063724 86063743
    0x6070609111003020901121109010c060e0f03030115020d0c03080a02070b010e04060e0606010906050c1509100c08010e010e04150e03040f050f06070b040c12060b0918030406120e 78
    0x1240985c2c0c4411520004080c10600c000601e086864504032290701c10f0600112000700409292000c841a12420719400600340d403203418080c0d00c91402102910f00020001c0c6040301d000c20f25001d403e240300102a600da080038030010380000c11a0001c00006801a406242c005210384c20050070070101c0da0700c0020741103080e0000144000510108800c1001c0e900903900c42c03001c020058811801c0c10720001e807240803140903910a01001042c0850130810030800800210740c00d48145419061807040300e900c030b40605001d0681c03641412140d12815004040b00350403110401181841e50f864002d40041940000c0c204507890000d01c0004680c02200340501c00050503440701956540d86070034503030305280b880c540c050340c018a840e0350384280c00e80d907100a035228603401000a03134890741e45140030518030200f40c0006c00b5031074444030008103100c11640814103038203040d604403a640d02c0d060010364040c000c1003150080c5074000c00003842250b01c40c0c04240c3d07900c6038881c8046000f00140d8000e070309201590 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 86066224 1250 86064974 86064977
    0xc031315050402030f15151503100e09030408060402010e0402120c130f080d030b060c010c21050f0c0a0e0901090203090106060c051203040c03061407020f010b060706091110 76
    0x244280803c2d85001e1010482d100301d400003c00da0007000301041c42c00020000c2c50303810340c2900e100034003850b5160700b0458907040c0ea4001600f5568904444501701d004c00500420034002c2080d40003501244001040341d0075a1071907401051182d5075503004554140b41c162060340c102d0340901810394174640c044600342c020440d8215940c1c4038607414010340d03010b454035403100e518100060f6040220000100380302485682c0c40c0380100360f9100000210700c29102c2c0d2101020150302c0c2c0300148001d207070702c001e0749034102c004140080b502e01d41d85000f00042c0d0340c041d1004d240d05944407000c6800b140c4d452005040520320742c10b00340041714101c1300088111400b640325150903600002080034144080c400c44014180074103040e2000c202503100d01c0e03500d0500c19018071901d1800800f16040c0403582121900070b41d0700240a000c8010030700c0d003c0d41c80441c190350860142c8906c0c00650302294046c0125140d581001d014030f420450580c455402500040c5400c0d50881c2034500000709644030381ea4944a0352205 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 86067474 1250 86066224 86066231
    0x21603020c041a1c0302030c030427050403050a180f1205071e1707120f14030a120207060f0c02061b03010302060703031a0604090b0103050109020708030c031315 71
    0x910040c8029211200c504610150000c6404031a80e600c1080080360303202800b071200052090717460107900d03500c6124261360b074030310002c140007a0f012074421725a4440018a555508250031708900310301a542c054900501081e001d0100c808101d20401c500c43c05030040525010f603069407201d0400c485041070f00202035621060b1000003e0120420029000302103440706041006603001c008a0b60701030502901100c070354000c8027100e0030a41000b60030040d141002c1c441000d0400c1d031030051181c80b00318204032041030780400000031894000c0140c1d801c1800230788034260300692040e6503200950040200306c82166a403800c04c400007c5602ca88240c042c2d503900202400d08140d1494079000b00c140c9812940c805041006000580b50712040e1800c3e5541402c001c102c228504549a1761500500700440d04900e0116000554a4141d0021809440281c0303040100f662920303d0360307090388076280b40586141400c20108801000302d03030055a00003030a2400b411031a0071035481074110780c540045042429203 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 86068724 1250 86067474 86067493
    0x801020d0b030307080403150b0901180c02010e07120c030507120506090f0a0201051605060907091a0d0201110a0b0c0a0e0405060f04051e10060315120b060402160302 73
    0x1440c4920000781e24124029800c0864982d00c200300751199000c014007039403601c20040f4407844103030000c50400200a004098a684900445908420340440e4014942c14040c80d84009070044c881d003030401d01540041c00c900e40c2800603e20704128145400c80781c2400610000000c640e01388441400342c81782c0d40c0ca402034041030f030402a107007070006884c003500e135001480b101954170340000e403405c40799a080c20304a8907444a0406540700074602d46020f0000e01034007080110b07010703010030035505550b203800301000071506c100b803681090401c00103035136002180690a00e01560144408031982407030034040701d41405140c2c0d11101100d6068480c03c095540110351240c0b4580c002c00000b4002030140d60070000c618010001034003841001f000e580c080c56030740380440d0707003c0c0110842003220107183c03282d820b844c202241105d254410724800c40000a1500a18034007512241606c60219505018040422030068036240c0c0a00e5000e17044a80c880d43c00c0101034034188404039541411802900900f42491 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 86069974 1250 86068724 86068747
    0x20d020a020c0a0803030105010c0f050a050d030e0708030403141f0b010e0607030c02100207080d0206011502150a0b0307030606060e0306060a050616020409061401082401050105030a1104080102 85
    0xe040b0030a80e8880c59150800707102241c2d00100703980c110354091a0100038003626041050f242443d100b070203021801510700c14024008001004881c11916075003c201460517250b1080d02c4000c14010005c103608208010000706207408070b0300554500110640b940e8980312512403484526044402003040c1d00d0706500f494542e080030110200034400c2e01d80c10f1800390380750703002440c00411400c020312501981e15150200c600c03c0100402602d1030b6020ac54074003000a501030340d950320922941c0d4000540342c3e0b2104a49101080202e480c0c01080c058030f00d40d44407070189001400c20800e181e501445483c20000101d8214051813004012035103030140c0303c0945106140c2803180c01045540074002884042080b42c88440440d4000e00701c041100c03030b42d01e41900c00503014095141c4040e00880c10103c1444110102c155910304894845045603940c801c080003450852441038900441c070040407004010b254020401541d000300c8420002032000c0080d0309090b11a0003070382040920369030104800c400e01 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 86071224 1250 86069974 86069983
    0xc0c081c0215010e01060315031209080f070b032d04060603120c110f01030609021b15090a03081909110102010b0a05030d050a1704050607030f140105010807050706020d020a02 77
    0x4081008000ba859030400032141d0307643c0e006109040426950b07d00c6082d894006400303010195034031003415022803c1c1990024945616402251118041c040700c6110312200007500070300300c45190300c2c018123581d1000100c1140307c5040100701644a242c980c10390803411200c4840d84102e204000004159041d82044010403107140607500a0003400d400790808181e1045d01050306000840e03645c1101785070040100c000d0151603201c0d03034246001042d1030320039240c900094040024000200c4003848242c0381340e1481c010069810148540145842101080c4203c440c10317484060900100701c0c060003500e0304c00c100c0f140107000b41d030800719000c24040360f50390a00540729009401c030340780c2d84000d0501d0700003521402d2140844040c4603000890541035401100c650001c286900028102440d007410942d07100d405c1107400d100000d00d84078808040082c01e104820440d100f0a140b05d000d81e0070310005442440020308030342c00340141031090000007117090000b4282d003180507201503100c40c41c004020345071 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 86072474 1250 86071224 86071243
    0x50708090a0507051003110403060e010b06030c0423090420011809050a1b090603061d0609061207080a1a07021908040504140709090e0a030c0c081c02 66
    0x403500701c0c03802240810800a01c58080c2c600440b115403103580c260800350020189907240740d0f800800030400009001c0d0551010200000480091000031060010410f60788000c031455109840140700c24020f0b001407036103140044c0e490241c21880c030000403000560709841250b045501503140c000c2c0c502280450007200403440e02c20308007840031800840c0242401d40140c0204200c0564510018103485002c1c0c01500310042c00007140c800680c0c04ca00d0040800e1001d0007407001190500200148030380211218003900d000c010048071139a00c1e04070400021040181403142c3c0720040050083c40d1036014080d020041003101300400c8441240e203083c40794030b2608032411030300401c02c03030401200c1ea80103d249000c40650300c80c0c0201143c2c040c5050f001c9405560802e03078005281640c1e4000700800b640210303004030881c3d100c1035159a0303200c542c3c0341540c3c600c410140d0342d038010180940000c1e000c0d9040c503403100d10075050b1071201c5071204c0c203143c41c007040c000800c21a6003080200040680d0144403407102c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 86073724 1250 86072474 86072491
    0x204050a021b0d0c020108060f0a080d0305010608041101030504230307020108060303031003021507060c08010503100b01140d060b0c0105010510020613080a03020c06010603050604110717030c070f030201050708 92
    0x30101c0f0592026000220742c2c04080c2c1401341000014410350343d45441d00c4642c600050510129030b8030703401070a50300d81e8041d0105012a20303180c00890741038014107e0340d1040d64000c130800580c000032801100a000e0140c42140c1d007200b040c21140309042514001ea1201d18480015600c40940340001004080d0142085000350420801d01c01c6d000c410040c01c005894040e1a0700c1c45604020440d04c0c01482400d1000c2c01035882c0104184440d54000403890403100102c08a4a580150b6280e0800321014035911501003100403141c881c003104190b01a02e0608080027000030788540ea0140300040f680401c504001c0703a5580c0e0018402c501e8551b11400d40c40c00070b84010300113494803041c026011820080b0151540602150008406100b901128050100300d016600785507507520003d009003400b900c046110380d0510070360303001c1c04031820151203911f5084401c001c405121207c440050740e00c0941602c2042100300714000100710304601210510344694000540c0e454030303200060111002078400712 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 86074974 1250 86073724 86073733
    0x70e0105091b0c06070305010509061206010e1302030102070f02010201050106050301151b05030c06060102060a1a120f060708060109050d031d030304050406171501050a03060b06070204050a021b 85
    0x12034403400341050b800100303505800c0c1c2d00041c0c1800340d0b07110b00800200d0040d500c2000f080203103260b45030300894101c03041600d041c034494031303101c00300006081e14080e2515a503204c04010000030b01c1240c3d02c160032540c1c46041c60111910381d000b090985e445060141d43d6221420000c40865a09104141c0104070340d140403230455050140d5140c940d8414984c120070006600c0c80c103a200e030903a5085080a55020701125503a20b0018800360711940c0449411380075001390800500443c07020f00410b84ea03040b40100c603524400f1211b0411075418402c0e0490002c074440c0714203003807408408110442c060580d0f41c80e0706549152540c00180001d10b0b9810217402500100b2000380025041108895808104201498010b6034a4080303031a50149601070f039030041c00c00c60001007681d0040046007514058500751148640215070f4410016030070300c00d051304880d08050070008940640d1010032802d1000344031500d40300705500050706a4105036098501a039001801401401c100980c000e1810040d0000e40b = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 86076224 1250 86074974 86074979
    0x1704092003070504061101020f030411010909020a0203040608090f12030a0c031404081b01020412060b060901081303140f04080c0102010c1d030106030b0103111305040f03030207080c01050711070e01 87
    0x400f41c1c0218881c40301440103040c19044130802c290107a400500f403c407030890300da19081c1080070149080070101c0740829159040450043c145001301da4000c0b0782900114641803030108116450580104001802d0003207a5000b9440601800250304880b4100b500545038105800c0c520111103109580405152030000540010701000b41056403040e0010f00c0f260301c410001c40b01942c00d0885a0500070103501c0054049039202210781e4840040c0d0291800300807100018040c050355214201a050108103000000303100e00c0c0d42c0342d00440c401c520034600000f05d42c0b0039146560050300624803000c025400032905004c182070400000101c1d2409100a00034171281d4840688180c2c0e1000a41000c140c080c0150741e0325803400d41006000b036074001601481933a6905108441041c1c2d2030410344580d280f00c9981c4450643d60240714051a01710761b281104440a40e070581c000e5000d60401c8034508400c1c0000d03400030400784201c9201d40b045460b007462901d0081141da0404115400c205031018121005 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 86077474 1250 86076224 86076227
    0x2190c0c03060507110f0d090504140109090311030406091809150b0307050d050102180307060e0d020f0405040f06110a0905131803030b18090604060504170409200307 73
    0x8400c00c590700480b000072140c440c0e0b01c04035010043d12a0345c003090310600c40c03081d000700e000243d02d281c8001581d0358004000d4943d0200010f540c007504000d900c0120320001481188055808440100d100e414003c510966a0300d48600315040b0303074031181c003040e0030301d07030404c641031302070340000108003820404200345c00d01d95035045400e4a03840c640001e030702d6036909030f0601d0740c600308440001380000501d000e21461481c0b500c54003030b40c444200d0001000040c480c864075414009408000d48a05844510304c03443c0c0384c41404091805240180c0e441008220f80c050240c80300e00c00c4c50702507030040300041150216410300b801600c0c000a402054500c08101d00110564404086000d444088810229490b29648280003070304a100d449000e413a60b082c104010160540d02180010301c013507501c00c500c0c4030145411014a04220b07906429a00b2120016000031301682c0174560107407081c09002e60036001040795607101c1c0c00c180c1140314419608c440400121030700000d6251107045020b2501d141d07141c82c035030 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 86078724 1250 86077474 86077493
    0x903030c030e210c011104080d110303040605070306030b0a05090d09080d0c0501021902100b030111040605031b03070c0507050d020f060c010212130201120c0516020f03060a02190c 79
    0x1050214032080400c40c43e41c90301c40402c94401c031500d6402072020480c100b542c44140e52040c441d040b92403161000300b804150040d41d0140c03030030b05a680503509599a50310341e940a8000149075204155590ba0b0100001ea00d111101d40540300f041c00000b01850404a02858410ac808040040c07005044040100c4840003034064406001032410b508500e0b4540340045c0a03000303090041030001100e501341c80b0926400540500441c900382c1c014011101c15038141401c13074071507a51808240c00100018841c0c039014100841c1c00c180b84051110b10f0f207049510311b03001a001514040d000646aa0100081c00020030001000e082d04448070000308605500042e03070f5402a580d01e50040401103440c0303a6014007941a504080f402c1c8102c96201d2800345128151a0703480407080f130108042e81000840440b6920840d1449407480e100c03240f42040803800d200c80c0c0b10106004a80c0140090952076540d00d080c8482c82c0940303180500903855801c03010584035003400c154100403c100e160550040031849212 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 86079974 1250 86078724 86078743
    0x81e060f040c03090204020a111204080c010e0612040503030106030e07081903120e0619020309071404270c05012d0c0206130303021204030f080a18090903030c030e 72
    0xc4002903407030b44030482039000d00090030300039601510100300d6100181c1c00c010301c020307280e0045060b10f091341400300900707840b40250300803466507070720801c04040c0e07030750081d141020004002846203042030f640d940507880030081160122859000800100089605030240012132406603001c8c007807490801400c540e451074881b03131a03c02007807002c0c075100c1403501402140d20b02d07074078001080c400b44865000080d680c1d101600d9144042d4104152040145024400e81e4042c03842600542480d40c42d020052600c2e0740f402409940c030954925008010880c0840f0a45100c141c40c81150074221150511551032056644524180960850004181c09060148103102e009146003442450044581150300041c071140082d00f202d0001040254030614254030412248a0780c00c03201d40c10300001c0c030800d16000e144401800c400ca0701c0034002c0002ca03004040e0110800394500000f00d49504e110000c030480907036128110142e5241011410301d0ba040c040c9942c43c80303040c1810300070544004005ca035648501c0 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 86081224 1250 86079974 86079979
    0x705090d02090406020c0601080307020907080106021b19090902040b06030127150305030c0607020f0304090203090c03010c0f02010c080408030103080702030a060c090905060d0b1602010219081e060f 87
    0x8900250400c501517040e00d00c080410f6044480e15a160510295207500440301a4071407024100000c4501e8032602006059442135406000d00211061a0104641d104c0301c0050b03010030756911040705e50030380c2d4801d48000d0060110118120100c1c0c014481254616141c0d68011801040180301b12000d243c4051000d884500c6140034000074480e0302c2000b0003945080c400d88001c210f000205111001000d81000100101550a9922242c4007681e46884a030107030b01300b540050200b001410501e5003c1d41d030007460f45041d10302200710400001e08440380d0000a0000c5001004c0040384070754244901400c1a000341000185401d058031212884c0c04144001002d8510000b10310b4219101031005000c0302d58401070511025400030341c041d160016600031001102d2502c40010f85070701c2c01010074600e40d40c02c141e0501203a1524001d680e00d40e030740d1480071010756408105141c0c800305907845500e040801d9590b00c0e41e075410419642d030b01003100164118885031080e4144206036940e05080b07144403004 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 86082474 1250 86081224 86081239
    0x806070503070504080a0b0601080a090c0603020c0a0501050106051309020405010e100c0204090c05030d0509060a030504020328030801050102160e091e0106030c0b0307020604030f050c0303040c0e0705090d02 91
    0x100c02c0200e5091059402c061000d014040b607000811000d141d610b4010542601c0e881050780d286e02c42c4104842e103010019101161108080154038080e50041036041a104241c07462a85140c0360340d0300b502c00a80c420070020f00000b40c801d2113140c00d110b240000d01040e09066203000d10f407500080681800300c00c1a0705c6101c6c1802c11a46242c0604005c00800da4080e01c10f01450560f402c011101701e100b07210707003402030007a008140348051007070044840c10f14000706428180074100344214014140100708903018824906e00c1140111040040707040c0d49090380048072803801910380107000031810f0340501d0543d441000824040c1000c040303070790f056512401080009580341045645000c541c1d145840d49290070780b076101641c810641105050300d00800c00240943e0340d810800c9694441240c3c0c1070016080785d4045400a4841d580041c40420545040341c1000d43c0c44a945003542e0050741c0840c0c80c036400280030441540b6601020717501c079500d401c0c04c83c185049140032540e009410701c0000e101d02c04c6d = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 86083724 1250 86082474 86082481
    0x2060402010e0a090c0206090c03010902010804060b0a0305070b3007080c16060e1506011b031715030f0c0a03230d0801060909050c2d030702150f010806070503 70
    0x607410f0510b4000c010010013030102d11003440c0040e407100d00c2551024000d0240070080c1c0350904050043c4561141d041e51070407411382e0345445d1030b00107240c08031620b54003c40c0b400e00003001c01ca00308000780107003207a01c0d1019070350b290381300102444d201c080d5011000a505000003450f0118041030a5602c0140d17410202c403144d0314000e480d4401d224060b031640a44280c440000107004030396011040500e003940031610011034600b034108a41104131041d03070004280c2d800c1031000703801420f90440e409101342040c04d1051280710368055a81412605000301c031050010118040c40d082000034072542d00e01029040c0001050041001a2140c0c000039001040c44411440752007054180c28400170301280c2034900704581d5440003040800c0c20b208910004001c0c602c00f04000131103114507400342090490003440d24001880d1a501124800c0c20f250300c441d0b06080b00560841c042004501c910304660207046980030740000c1c003c0440002d000c01081c0704840005202c00e420001e4141d8002c000c2c6e0800503101d50f0b = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 86084974 1250 86083724 86083729
    0x110a020f0f01030f050106050c120c07050d0c0801061d070915030c020c061b12030606040303030c02010902040e030c01060803031303030b0a030501060801050610020c090705091315080105100602060402010e 90
    0x9014490405580b031700c000016800e038080301900155604809450030341024030382010440c00f40c41c1d0710740c1c0542c000050801c22880c1c81c6003508840d03840750350005d403010317a03510010b402c40c2c406500141ca2030b10a6807154219515104440da486011070400c54400d0f404e01c10100003442c480751050051580d5100d040764003034000c001000881400800095403000840c4041001d004480401d5005116458030160562292003d40748514000b600e43d0b401c09186440c01c80203404610215070030741d5650540103000d6100c5000300c1640104d110021542c42245425160850788540e014038140d4000740b003804450b184041c038800c04030707405180110f03181e1041c100081090348183d20040440d0f1900500296040c4190085032150b141150b40030064500050280d03268145021000d03071090100700012101c41c018005007020100c050040c0c0c0310081d0842e508401c40f81c2c0c60051103211070549408200700c075400d0103190b9010044801c0031340c1192034010042e541d4000904000c1c1032040003031188440341c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 86086224 1250 86084974 86084981
    0x10209030105041103150f06060d020d0509070e01050a03020f1504050613060e010507030f030c031112010e0105010921051516020d0810090906020702120706110a020f0f0103 76
    0x129001030081055061070702e002c1403501c0d41c1e103824078024000c10304851224a1440545841011607841c070b06441e55915080001d50744c00720469202c4a070303090154244000300c0d482098810349200c0000c0841c542401048000c07c6416403185200b403d0b01901400103885583e800400b543e0180c8035181e50000c1814458843d0040750040b9802503000f0880c2542c442c0007030341740800c03101551240b0703100010010044400d44141c003409004110202e404228542c4668800d41030404940350010305525140740c003402c035500c044440481a0082c030018400381e10003610040c01001e090a021a400d403034a01d6111031140c41440d90031030291000001014404280304211aa16450900c40c5040c9409010001400e038000c051301e00500c2166407440d100b900802c0341d2402190300d02d0707076091140e01d4408104090705110300c049a1280c1c00f48001c00041e142c801d080f1085407114005803540381d05242c1d00a08500300f0b651000b1003030b88450b00301000740c0c541109407610050b00780c0b8200303180701580b40140c0c0036 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 86087474 1250 86086224 86086237
    0x3160215070204020a120b0409021e04110a0c0506010f030210051305090a020d0f09050c120708030301080c09130309300303050603010c110c062209050421021005090102 74
    0x10a0000400d400000c0c6d0044001a09166861040000c40c1c00d1000744400c842c644440250820801c401000d141c184811000714540700081c400f0841d03010f95400720100e82c00035411840400c205071414010000140100c41c00341c01165010783d40649940c0020700c0d0105813540840034070200190a002a00760401240d000d424040c0c041440390503c100040300a501080d04841c1080c584840040851001d000d16a682d0b50808024111100034404106d032028588140d01981e1150b0540014003d2050020714002d100c40000b400c4e10716802024030807484001001209159034000406d00000d8010b2072000641c0c04004900da0031044003401040d4049040c40c10340c0c00d5490382c204240405501d904090302c04c1e0802e50003032150715841013054400d00003100c000c480b1a0000500499181001c0d4080e000c1c01442e00524680743d815800c0c0ba00806c03080750043c010305030712802000305114401d0350b0150050200c9016152400034000c000391a08290b161040517241c4883c040b4241d0034094050310342 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 86088724 1250 86087474 86087479
    0xc0c030f04080a060506010516080307030228020d050304050a0b0a0204080a140106060c0f0f03020a020a090b03150c030f060111030d0212010b0c070b030709030b0c0702010809031602150702 83
    0x55940c2c41e00b00a941d55003440c0003c032041401d280c0040c6065214200303882c0e116002d44501d12802c41140e440e06525040144a81e08240e070901c1080c3d10b6149140c1059100503403010080000305541d54001d0401050504010034400c04105010003c2c600044105145802100742d50329506e40403420300192081d5440030680d4490420040e0911401c1d0741e0a00310051000b00801402d03581d0b04043d6801404448080c1490030500b210f0004034800c400380c1c803042407181c0f0598101d2421540001ca90820030707040480040d550342160449400c04101104c030030000100002040c1c500440e0b03201c03441c440217082c401040d0b01c81021981c503034000c00c414000b01641c281501d07111660178880200035000a904840c00c2d001d61000080e027408110101c40203da1322a028040c0340d8100f5180340110b61000d45510100f14003108000040b07001408254002c049801303013960307508503900004100e5500641142d40c190810031100c00380010090308565229419550a440251407101449450003a804081e4 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 86089974 1250 86088724 86088727
    0xc08030913022d0a0207080601050105040b0c03070b0c07050f01050c1602010e2805040608030a0c21080702060907050306060d020a080303090604051005060319020f0d03030c090503010e03030c0c030f 87
    0x112040c5600001d40340c0d180080d1700b1101c50340d644a00e4950340700d10030301c103650200700e0802083c8040200b417001010500d00d030100b124034018050380e03480c070440c8040b40c510f000184c01080107810881c2c107000e41ca00302c0d42417a00038060b50920101c40641ca10502d0340e0200f222054428220459006078907128007842c0052825000001c50700740480c4080450082c46207130900c0f01400700d250b25141c8070f40c00507030b0034144c015400c2141000040e9600c4010b4041500c6207680d200c14490804120300300c1c01c000c0000c6a0b902c6400381001a00030f0300e024009031140c0f2030b5070403860b802e120944000510580c40300084840508505650001c0f030840e01e80e079000440c09010001c10000641c6001803030b54007952040d01140c7c0c204a40d982210125401501c020f42d044ccc11482d9401d20030800d2025030410703a030006048051282150700040c825036820702080b800b19803680f07060700c02107400031120002000c0c1038009010391800c2d80401c0741c4a01c401040200240404203041e5003001c803c006940a4564445006 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 86091224 1250 86089974 86090047
    0x30e09040809180c0708090604090e0307110f030615040f021201060801060c15020a031b031401210b0c07020d0506012c07110c0a060c0c0803091302 65
    0x6030003584100c2c01030b070043d0f500c0d40e07144140e007140750740940c42000b403010001c0c18080b040d030301d00d0902e03031002d04000d40c802818000810550f000e88240070b0204010001540d40d02411b1414001001071141500d1064890340d0700744040e41c034003194140c0d00240461010b61141070450000d0300809015040e0f101241c40481c0c0780d4020b0513001c0115040e076401c0c0e140d021043eaaa078904031081d500d1020300030a2444054500354a408682e005450b507000306080124512503580d0341802036540002034080020b4550081c1028200580070791030141610320b0041ca620348a0482e1b60030028400c0354000c00c00c410010014002e2100501514840c80e4001d20b00d004907582c0782002661114280540747c194170035900d41281081c1c2c45182e440c0540c1502892405035a2a90420307070b040d450f455070485080c02020b000003c5a40c0c0c846810b400b501e02274030340401c004450b0500b400c110750395030801c805d00d500802c05500a507035402c00d91561150b9251001d40d4404103807600c3e6040d0b5500ca15049281c03480382151 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 86092474 1250 86091224 86091233
    0xe03040b160506060301020a0c0b100510021b01050a0c0f0602090d080d0e01020414130e011d010605060315060d23190510050d05071e050a0b2104030e0904 68
    0x1d00310741d9016404072030300d98580c0c600b010f00300c0c480c500b10b0501052040c015a8001a030f115040303980951010740008913a0342d11004140341c0c4070011010303401a00900300320b040b03d2142d1603a03644400803c0c070744903080c03130381d0028054910014200c1c040e2607040c0c070601c00400c10040d9011070760200009407c0c120002c5951401400603000406232018803810300082c800a05414401d44007103445402407400042031140900511003248100400707041d840f080109400301e0f003406801a98696102c01603401441d05400e9400c48045401c42d51041a040040c00950030300240a4082100200c0325290b035244d2541c0301070001c1446441540302c3c160b12000d44035041c0140d1800905c100070500c440106445d054100c0703011540c044a0403580b005100344184000d0801c00011080c861180084030b01594450003405c044c0001082031180c1c040420340e0603c01814421000801440154105814014440031110090340c440180c50400d2050380c00007014140314505004034000064034020709400c1c60b062 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 86093724 1250 86092474 86092507
    0x20a03090308180c04180b01060f11010e250e0f0402040501050315150612090601060315060e010507170d0504050c121b0102070314150c0702060a030e03040b 69
    0x4150080341d207490000f85100d504034101c0400c0000341020740200e880403020000144061240c49030100034090a0100103080e001c41c9070b01030b20b05529020b00600700300800a00c1c1c6a0ba81d0382c908a241d04044080c0b02221f0002644031000c07280c40c14014200d8161018840301001c1948864040c2441e401071200c03480440a125000d0f44c000d07981844280e03240c03018076954104103143c1441d0400e05000044044001e07420b04000301070014881c3d4a403100c051983d42c0f0410056075460500e0b0030420040001c030703800d88548504011070407908c0076080c1c907000c00503001d280d00c0b000850610100284003001c20207500240036240c02c82c81c0c101a2a007450001c41002880d0443c3e044039944a8056092410300d020840b020701503022400804000c00c20201c0000c540091040381c9055200380000480001c4045851036041c0c0b20500007031201520318812090b480f280500659000c480030000d203005130322190b040310040d042b542001b140040d00320307403880d145105640c02641169000b01e44441506103520 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 86094974 1250 86093724 86093741
    0x1061d1b07051b090c07030509010e01050405190504050609061c081b060a060609080304030312021b0a120e0105040504150e18120a0504050907020307061104050108070206010602070b1c020a03 84
    0x114071070020b03505d06844a849119003140500440e5003406001c0c210341c8503a08031806d400d01031600c0e40c2015580c101143d101c903d030b0071031852282d0b095501030003c1c0c01c061244039030142d03080311641ea0604000011840400c184031240f19020f045981407014098a1011a44482c2c0302c81d00d6140d441c10b83c050456121201580c407111100d05000001031440e12800310070b0107450308600994540341c61a6802c0d101440350b0a60070b00174035000c1c4000c0341003131015a10001d01c05400e4010307040c0082503250698014021361043d000303102c40f8205500b1144d074010140c40a0b1759090724002400038005180740700022055000b6020f180224080014030341e400c56034040caa00303040007110034560342920941c41714084c4c9c038034000004106100800240ca80421510340002030360043d2450501d8607210312081c2c8110300c00c201c410010000d010001960312107500e03030b072000c020b2020741499410040f009450320010300c80c0086070480451604451145400041016420403000b107580b09613058014015003000f1 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 86096224 1250 86094974 86094979
    0x9080d0c0e0a0b030703180c09060501110304150e18040c050406060e030303060d030c1208060906040519020904110c0106080c0d1a040f020d0c030501061d1b07051b 72
    0x11500d60780e10306260300400103a4101e0040941141ea8003d03040b8000c150b403034017462401d10f20181840215010064410280100100101c0d00f6410a0700260840c05000c0c2282e50552040200300700c10040c1345d100924a070914508400c0c40740f000c400040c0f00c003403068815418050f15009000410040c050400c0071158150b500344045030350380758152110381400010507096041000000d02d0b919107000c0042609110341018640c242a0743c5620744984450410310300411028001d000c45d07440d04402d410380c000e9084030180401d10b040422950341c044155514010281c0101d08280682c0d281d8004520244614401540700d80c4e030711600b18003811303662168440b580a00035242105041900807400380c0741d007000c410010680c0800000e0781d40c070401001a110304080c0440c0700300507035481da4401003040c00362003c058003906500340f090848810741d0007526411a4042458040c19001c210154007080100f210b036015075548008070704034071a1800080040c000d00074582101c00310030b00b4440242009 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 86097474 1250 86096224 86096237
    0x506060903032a1501120f08120603072106050c09041a0406080a1211070b0f0a03050601021b0f0d0209040f11030a0f060c020106030501180620040e090109080d0c 71
    0x1510065501c420300b0b1121311000c80e81da100140040c02c1500700900f64207200d074a58042240e0191901403180e080146850750911100051014038682001210b018020901010310310180e42e50300044a550000c0d40140764685590011354140929026580c0741c1d100600300344040b4000750494190190703114a202d1191f072401c5800320342802c0001300300c0000c0707a01880b2502c910311121710a541604002d141c600d003500c210034011400c0059427002c0d00183d039000c0f50068584500140180580d040101010304542c81403610580c69200c0400b409400304c0161414450741441d01c000c00c800400605000c0d400022410a0004104030182c4c014000c5000c1c1942c0050480300108041e203d00d8005d1002d000e80407072030482c002040d865440503136841c0460000103822692070f910b250071741c5c0c0991006142101e00c2c4280400780040780c02450300040c03202c81400108446c00200765100d0046007e10f041e1041883c0010350547d009500010046422050480d16600304842c0000035003000005500007400 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 86098724 1250 86097474 86097547
    0x62012040906061101022b0603120f02010c0f09050d05190c0e0a0c020c01110c0d080a09050f0a06180b030a05060f0117181f0204050f010f0504030204050606090303 72
    0x2818821f031a21a903c01c40e00081d0703a9009071b001c06014442540c03d03c60b2035070f0760500000080e0005046244501661103403c0a003160140c0682181d42041d00e900a205075441c0e0b11010a0b07000201d4416103400300c0b61000c0905103414040d1400342c20592180841d00b038100c1e0181402404140e000450303110000003a5582d403412040c8040c4e4400940d020003690012074100490341c01200244281040700084407069440e100002e400114000d8065500c2d920000d10200c1065010310032001914058641c0e170245030b9050042000c10170144904e0041100414000c001c480c06500440010106209400d8490070300c1c20a00d00103000c01e60b140351140200c000340c881b031540194008800803201c44420302d0070390b0310001c1d5a02815030404d0b1003401409003c1c2d403216000c0040041c46480e0300e00100040e100e60a1100b0b000540f1544a802814860a807054403041c0e5440340c200c070b00b525030507100450315882d50400700f415030056513441d0360706001c0802c2c01d5107046980b1b009401e200c40404600780f0700302d0 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 86099974 1250 86098724 86098757
    0x907020d11070f29040b03040f240c091703040909050f030a0e040b01080c070b040203011d010e010e1615020c060a0512060a1206091406040506040c08030406201204090606 75
    0x11171441038140000013480028003180c40941507001d824060004000030440704041c124010303070654825050165188040808564001e201e035014150a00d0441c80d02031014803250343d00c3c000d52042e007030b06c0c9489041d22001c0007001d0143c02c4171074070081c0449032074142c0e0340005032007009a081001c2c00380380b4041c2e11180302e40c4550780c09070080d005101020b180109c01d071a40c04065100034800e90b0903640780c004d111ba0303240d400314200a107440002c1c000034440c1c01c8000e03894251031002c1c0e441141e42d070100d1242c0040b60082c0b06008100c80461400c0480301c11400da050303061a02004400e84c0c003403400300d500c01c415a0044028410544d8680307c400306907845408015502c802e80c0505d00b68000307010303801c000003170285e0f002e412241c0c015884030150300000c80805281c0b40c1d0494046405802600034070041108900d840805800500040c50800b8100340b401000b0b03600f100d11903c080421a4103905d140c80d014422540f104018482ea01c0e07485842d1114140034040501c924030005104650f802d4020 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 86101224 1250 86099974 86099977
    0xc12031c0b09040f020301060803031e010e0105100f23071202060103081903020409090c080d02030702010f081f03120e031c050f0d0204030b0708060907020d11070f29 73
    0x2088002c007244040d8645031110318a600751444200d070990740c3c6210100c0c1c0f608040000d1449034801041d40c4400b1207104840703100121040e03100050900315030006005543e54500d080300c022045203000703000088030503411502c0152400000c040300c1d664201c0c000300c00d0101c600400c81e09000d610140a001001c001c100c2c0e82e14024400078185038424040599582456001c3d2814051507190150401e9140c2e1104401c507003100c04110b40a0100e08030410100c4418003020306955000e002441c00c0a42c50380001e0002c4d074005001008100100c80011075142031014041785102000e1102c1d103100d903d87c640000b848956000480209110380c061254520300006c00d404800041c0b801540048000c910649440e00070540c1c215000c0014081d1403001842407028000842c0a13400c0c8515500b00b540c80075060b1500689614000d6404c40b0420403403171b40009048a02c0c0740145403001080709030420450401e0f00c00e802c2650050300302500044c00b0191255001d10024041c84070314071b801d490004040d90ba = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 86102474 1250 86101224 86101241
    0x2010209120d020d08091002030a090203160605191b0f0204060803040b0f18030a0b070e0d081e1c09020a120308150102010f0509060f280207050c12031c 67
    0x50b03202c0d1203000b2031340b032140c0b840d0781c2c000c43c02c0000c45119121000f0604283d0b0401c0b0340b848501ea550b0600e402c29032800f004005e51141c0e080141d200d20a0601a000b003444c07280070a603441040c44214001c06452007401504a040340e42800381c105106945020018080f0303a50050780310300e05080340424110004001c44044586100f2006e02d04140c0942c81ea1240c2c100144034004102504001217403503e050002c1c07040c00d8800c409000151400d2500500700e038400b000814020051036031a400042c52000848442003200070040c11440680d8958071342030300c9444880c5c140142c45480c010030440725900500d03074180c4215041e10b144c94030740100294050a1303500c0034000a03203180100d004d440c0181214101e034070041c400480c00540003400d420a4400503182910190310201c100400800d042d81059007080c1800d0101010005000b90000050b04000c00213107410350020f0130000300300301001400d8845ca40a00403084a00f0310b09020303601e941001000594400302c80c003509505400b28400c00d040c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 86103724 1250 86102474 86102477
    0x9070908100b0a030b01080a17070206070f02030705150a1106060901150203120103030509040c030b0303030c0a0c0c291201030311010f050f0612030705030414060d0c02010209120d 79
    0x7a414150600c4018120303200e401500300c00007090101c00300d0f40442680780a04101c1d0001d010480071480d01c0c5403200200c1d102d082700310358140028001a0303906070440f4421508284511413a01b214000641041b000754402c9502c022908403841e25900c2c2c42010340503451560300d900c06600c43e824550743e16007000310b801c0d50307108500c90010310108203081d0350084e404210344116414000031400c514080e0500380c10a4011490200d0300760384034a0940a240c3d0322071000d2606000c4040e035240465568040507061074002031010400000c1d4501c07410640100b55000b0341c1c0f510842e96104100a441e080c5414000141043c1c0303a1040e90b48c140883c01c9030400707181c20322101160fa186480c2101d10150f07049a4030b085541740c1c0c0d500c9003110001e00880d8015480d00c280620b86041c02820082130308801202082681c00c02d1210501182c400300030b4500302c90899410400000508001441c40d02c00c40d044100418030340313510300403e50b60541c00b400341c440090713410300340c00211440b44940d9564500700000 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 86104974 1250 86103724 86103733
    0x220807050d1a04031713060501151e0203070501062409032d050303070e0108060d0809041d0709020d060b0903030a030c02100c020303100e06031b22090209070908 71
    0x242c1c1211884850751150191030030501e0f0324841d66220185910990b200342c03012030030314400d00c10300440d8840e6500401c03403814201011000201c0c040c28009603505551a01c00201c061408035500a008030703080540c3c054000c02c1481c0d01e031078501103540039850000d160300c800e031901c40c81401d00605800c01641c0c3c01242c40d41d426001926030f0b0030301c681c1a00c80384140625000d203403400241e040003d94003a1120351070704201c0340da121000410185004010034801c2e003c5c040c400c404911101d04444141c07506940100b4910403141c20f004400202444c0e0424910481c0800951144207034041c01c40038424090074040382c1c1c4c2c2c56180000324001c1203081c0d42d1541041180440300380c000d50043c040701c400742c0161498412001c3c031100481d1900500640560400810024808640c0d010034000d42004909101d05051400100e550391307004403400c44464104110201103036441c0e4083c9840e41e503807078a00084c0c002d11100e1040107080400c1040340110f1444003c10381181c001c00909042e106140000e2 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 86106224 1250 86104974 86105003
    0x4030305040e06060d0f05070206150a030204050606130b0307020606040212010605090d060c02010209010201050c0304030917030c19031b0201050d0216020603040803040327060302030903220807050d 87
    0x840700320400f8003a15480101007160007414a007500030b0300100c0320581d0001650b80b40006007c0c0c00c2100c01800c0700204078950260040d01c1da110200c070010f070390b015600001c003a91240702041c200e1240c54181c40221070035920014407110b09400440c4a004158284c03081c0e80c4400382444240c2c00b5038807030406001480780051003010b1051000e003202c1940104000d20002c0c00751680d0084845201c00400140d40005540055580900800d030308180a00c103210319524082e100100807605e5400b610f10103031074503245607130203180420a0300e840c411901c2c01c0d102c592651000a02503e81c501a045012403000c1c5000036a6003031090344100c005806841d01c5280c81c000300d943c07500030340c8240c4640040d082048451000750b214100a50b1041d480741d50758555a003024240500b201d08003518040402c11030792684510030500700b611408941c6142005032b104d4451008240c114003d07189200c0c0c072898100b500680e244002106102112005000c0e103110949480074401074140810f00030f040ea15100e00071 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 86107474 1250 86106224 86106239
    0x1b0714060d0506370b070b04081c140403080618070e1c0501060611030403120311091207050109090e030f090103090210080603331b0d02030f0108030403030504 70
    0x55600000c014000c01002d050381020003003810203c0300507411100b85038030382c440304c07003501030150080c2240003c801d003020450f64840c944190001d1009009100c0440d103040013880c541d82084606001c101d050007240b161070303044696440c088400b5000601c0c9000803a003207040401401810486041d110b001603540c002d4247c8080701250b1080d50803c400c201d41c2400c24100c2d00044511600c01c1001042881c41d0030001450900c201e45801c0f82c40e00208410400076200341c066070450041404e020408121700081c0050034001d407105c4a8001001d03510100000390080b4011080c0d540980302e0203800c41d10351245400303c40100182a105a204000c200c1c01a01c0c0080503240c81c5a05141c003082a24003540490b95488120301e0081c0401c5800d82402400d00d0203100b5800c10b01081e8003900d9400c421166550101c00101035004441601c080208108034260381002e8081c010b0000d81954a01c041030943c0f0083d80b0858099000c1e80e26000045401d41001c4100c0c2c00712505075551a040c41e0078000d4 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 86108724 1250 86107474 86107481
    0x20303060f03070911040e010609080a06050717070206060907030623030a05010606050406030606051207110f010e03090a090606090513180c0302010e0f060f0f0f1b0714060d 76
    0x682d5051056007000103000c0058056080000700304010251920301e04034080100c00d4041e0407040034414041024041140c00007442c0301080d800c02c0340810952503031101566001146004442a074000703404100b142c03034000500354043c8400f601d8000d49503035100c10807000c9580c3d80c0a04024680c1c01064003c0c5800e600ca0300022580c801020394850420b0b5a81c0c4a003110b03942d078880008200e010404002d2a40c01d446108014551030428900e030461036641d000e00440010b088100b031290408009101c980c08210007485c440c1400b0007003094000b0318034026541e801038030400d403288000da58046000c1c081c034040c0c90121245500da0300c40346424071040284500c0c5d00e10b02e9052541c0c0c0c0d00202d9000400c9801026219801040c0c082c08640c20740c000101821180d0000f64052424800001000d45814084a52008030654203544560094020305901d02c1601c0e500320611601150307a1004c5800d0000007408098100e0441c0c03025507950043c4515060f044850b01d52102c0c0501030502c445040b81c0 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 86109974 1250 86108724 86108749
    0x80609060d03050c07030b0108061003030210090809040c02070f080304030b060108130b0c0403030801090506010807110316060608060906010b030606280c050d0c0203030702121207060506010305011502030306 91
    0x342641840c10144c0c0d61440c0845551096070100003041c01000207000c24044030f41c0151819005410f0700b41180c4011359036008040c505901540c0e40c41261302440083c030161824103600510500c1560809140250f407099113005800000205603000202041c00000300c9040b40d41c0f24007034401070ba0707580340151010080244240701d2940200308200000e8241076a540c420250f03c048aa00e607800d42c1801014050142c0140e0081484e00040c0b160584c1c102c001d480d4801c88500e0460b81502130012680e0550280d42d00c032040c05a0308400101c1000784c0c94201d442541d80c01401c88009666035101180c2c0c6035828441c40b1078044003040403d410342000402065001c0c0c20700c0315034078060703c0c000d0f03c11140c54a100c0c1590003e5280503d041c00c002c410f02507130b070000d6580d01e844000e0784055000130f9168860301400900c1413200d010f5403242d080007807003440c21581071082825240c80140c14400064001142c4035030000b4078050021a074840ca20000c0c20015010354000e504540c1c038441480410703202c09 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 86111224 1250 86109974 86109977
    0x1203090b0d150f0e06011115041b0906031a1b07050304051302030414010c02150a0e0105180105070305010b0d0b120f0d02010b060a021c1119030f080609060d03 70
    0x2e035550740030011041440700c001c05102c0840520107181200c13186800102406540c100320340581d42004c1004005503031240a6140006482c00b0340b42d602e40094401210001440140e280090001e43c6444d90350001c0b040340e000e0303840311900a80e80c12604608085c2255050114640321085451f0061180007800186d40710314110391505031a070001030b14400780f11a01d01102600001000100310320a14580006080c1d4030003400310383c01d0340d2000f07911000c1080c8004a003940f02400503114404640140764041400002040f60b4182200c80c51251101d41030b00c44025820200032884161003407046604842401110b10b017068114030240c0060718a0405035540509603940700f4040c2581400392646003200d2400506030111904070107401d40301d5030503115101e00d030709000d580040c0d600492411000604410f42104801e00a0170030381e84400c0d803a003e0102481381d01c0314810700210b440031000c4018060748901110354107602c021111202c04072a19030304001d2444c04200302e400e050395038000c0039109 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 86112474 1250 86111224 86111231
    0x19050309010b1e13140a0c0504030b0115020d081302060a1112030114060f070f050f0a060501090f0203070c080d090b09060a0e0a03050304110105040308070605060a1203090b0d 77
    0x55038001004070710030140d21440c89003081d02c40c480c28038005515411a1892004c01c0c00340001c14550114002801019500c500f41c44e8503d2014191043d4202c7d00556404400b182031541c56414240d041c104280008025125034003d050700d00d030140c4152351054100440040010047d6402c2c084941c02440d1501c0c20b00003010009c00700c103202845800c01c0300e4030629030151690b1400f5030203203d101040c000c0b540504400c01507400d0902081048a04c41d54104c070401340360541902d0f1261400114006003611030107400715090400005801130342c12501200c40a20094100041603012480242c44c40030111310307403450400025410802070460042d03c2c0800149070407068541c00c494810032100ea0104d500a60308122007072040780f140500d50300380100200005c0e5020359000d0f00e288030292001c0c0c04e48403440f194410680c4038070f086502461340101880e0b20350946190050280000f601e055108414540c00441c201c0d201034402a00d80340c0565401030003500d002103841003503000c0c030b220782841900c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 86113724 1250 86112474 86112491
    0x7090e1608071806270f0903020601030b06060c10050a06050405011d0c09060703030f060b0412080d0b040f090507140d060e070b04080d030506060301140f010e040608011a061905030901 81
    0x710b0350f14013201c9102010448003090101707070000403200408405d0401d2450f124007100843c2e80054082c0c190307644403440b0a04d9849140004200d409003d2680e1800d200382c00190004400d15082036005900c1c0b107030140030503600d900c100020b4070400d001d0303540f031190741c00c48800e00000025802e0350400442e1f00300d1450b05064902141c0e090340451016400700e0b850384a1402143d0791849450028600d0303c1100d4181800c090195414445412028050340c001007168130000344d607a07100510701d8230f00503c1002010040d844110160094038016140c60040c6a070008200c0807c0c2d101c800b142c05c00070517a66440803541c0d00d080040c01d5640300c2c60060321690a000c55803000520082c000340192030300a0607143e003500c0c0028181e400040800e170040314240010418040700080882d8444030450705054a9038944004903040c4260084065009082c250700041d00c08041d445802041486e043c47d030a41d030580d0040c071095204800303800311150f0000c00000700c1c882c07284015582058503203001064101 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 86114974 1250 86113724 86113739
    0x60d02070c0f06020c0a08061012140a0b0405012003060105070309051206041709130b040b040f1505030102090307050d030c05060405060601030507210209060c07090e1608071806 78
    0x2c001d40c00c00300140e4051050b0300c580f4500508000018000b80008058502c0c2141c00141d248100e481003000d4034810281d45800c00294040510324040600c003103032070613400ba09180c030a900e4156001d64407546013452a0f03000e092581ca40d56030b22412030310180d00d103403294001124550311400b03050702002401d01b07010400742c1e00c074581040556240c1000306070314103190502a81c0c0104003540c0c1c1c500034000700449651740d00c40e02143c640018a003000002d544240c01d010030301418400203801e90041c9450311100c0040e026601000312001640d030142c041e2a00d60050500b00e116030550503900d40e2200b0400c111900d403a16485c06018400d281c4079441000d15504c4916000c4150760803109500318104000346540d0600c14180c0c084800d262040304c0203441c884ca1038480780181a403000068000a0300082034a8031011039002d001c030071046800391543c81b0b00c003500330428400c8003080c3d401005203010520403040318510565040d1000350018515081504225401a400c3c03294031a45580700000c404 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 86116224 1250 86114974 86114999
    0x309150c0711010206011a03041e120207081207020f030a05060405010902191203081b0c03190c05060109091e060509070f060e0105090307030203010207080706050a0209060d02070c 79
    0x5014159600c1d44500d101d01d003032400d00304000c40240c11075211800402c01208205160780300e00381d444090a03625152410840c82c0510708205900080c14032034040e01c100401000048a040407503420b480d0801e448014081e12038200c41816440f41c0c01c180b00c100e0240c585880201c01440000b030131226081080d5848a04154040780c0990b0b040e559000c4150070340c18090004029044580e03565240c2c0340c20000c11340c8041c40c00c004d0144c00c2200d4400061254411070700500c1c500308100b0480d60b220b0060200d1070f17540c0e9100411200d2444650701503880124001c00555503034990110141005070b00300b18180005008070072080e200e14031400e03c135403480c20a1004004600e0b00514000c510f615005042c14a000556409901407107102c05007085000c0e0701813400701b04c00d4070034070b0502c2d0781d10a130800080c5003060b02e400280d450b500c001560030402017904020318040e40700381702c140850340e60001c5000c101d01405a40941212003040003104c00d100c1d9500074500c0d1482519940c205a440e00d80d1042c20 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 86117474 1250 86116224 86116231
    0xb0d051204030b01060503010b0703030905010e19032706180e010b030601030b0d020303090d08040e0a021315090b09120d0503010503160311190305011404060b010810030305030915 79
    0x10306100041c18003d0140555881c1d0241c10329040440c95545880b580000e00d00c10030901a08169a80030000d003008000c0d0000f00000c04281c0c00c80310003079a000f006103065501000c044001c00e2a810300540100e000007200d04043c5c05280d000c03404d0900d010415614008a40c4c0b410814100c0c0e510007041d24441e0301071450280258514039030300d030724100e8000f42c100d0b1030140c00588940850040c150050703500000b10b594503c1e05560b90b101001c41440c010660380a245c009424040c00b0004102081c0b04175800b030504901e192086114480d511010b210800511808180c009005001c05111f081e042d54020b001d0810301809449501c0c82d80c41c181c0d420800004490400684000010070070307458104148250041040070b010301c0c4d1451503a8106c0c0202d0460b28140c010840305103600b07250480c02c6000304c000c0d900400280b200a240050792a14074008480440342c084c0703080d034540044e510518405100740b8843c0784100100e41951004c1c0c17860b4200500300f82c507611840d182c000300c808650086a00 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 86118724 1250 86117474 86117503
    0xb0103122d08010602011802060d020f1605070b040602060106031d0a0c05030d03020c060610030207050f0a12030c05031b1b15061002150903070204050403021e0705030a02040b0d05 79
    0x40c0704039107070000b8107502e01030f840201168181507106d44500d60070044402440d82c11900e40d41c0d5001c2500707041019019511140041318808107075100c2e103e001d400c005a880d0710582c1a501d945d919000d04040c640210b01490300182c0c0104018802c0c42c0c0030354000c0d00030450b544102901901524842c03413500d002c250b002c68080054810400990900308401d0f030520300942015410080343c811304e83e50300c0000030f20ba144a00514000c40464038000d604803a50a9082030a880207054a030340241da445401d6031080754420740e04194004030034840c0c803650070380c1e8425544d81441d58032201c0d0404406101d04a00ba50081c0381003110b440c11030440c3e541e8001154807500584100c0103400c408800d0804014005801110000d900341442c0303030301007144099070040c1d00480005840341c1c601d4038030714043c44400a4100389440e061209040e000690100d0384042400100c541c0780042641c5a01d4550b00d21034180c06a0201c1920b50044c5819002480024000790031103c0d8049a5210a450200347e08031010 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 86119974 1250 86118724 86118797
    0x8030d0b0405070203070816060e03040e070804122105151203040e160323011401020703030207061202120a0e0d090e0703020714070603270b010312 65
    0x802945405108144081107408215901d0407880183d1a0310408000401820000031030a0052030001b1403595001d811102c10000746003d200c40c0c070b560760b2080c012070420412983c00075071200e102d840400e10640c4d102000b5005050f01d030303500341e6414901e000c803030b0604030000d0038812441c102481920311a4440c0400e241084408000b071002d2019101d4441c4401d810401003401110149850340b50840c038140e100980c2e6040c403150480080280107424101c161080131050140c0c0f0780c0140f0305040e0380940011803404220100161384c4c80702c07184001400b503048400b04004450048207545a47ea001c1940580380c42c401c4004240035402c21150255281c0c0c0c0c2d01d000040d041c0c010054a02c40c5125814451000390404426003184203000b05900308050300042c50030200304002080b50700314a01d2008451800707803191b401501800c005890006400d1503441001c440d6014094891801900845410354990075a00d44403c84814240e0980038410584200b04198050440922140c10040c1c40032 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 86121224 1250 86119974 86119987
    0xf050a0503090406050904021f110706020c0901050108160503060114221502071206020706050a1415010c06050603031201060909050c0a080601030b04201201050a030b0412090506040803 81
    0x110032034805422950042e12006c041000584840000c00c00c40014041c50303110080c403c4404680320103101440e5040b07405841c01c005410b5030001010492503004032280141d83c1c0c4c0b12401140e02010131603101c40a510031a17080341f0854001c100460300483e042c500b0304070081640e040b02d0f010341e100c8200300c08042c0041a844141d10081d005c0b0002800d81e00c0c4541c91344440410002755903450a0054140c900c02c9403550f441000702d03580c121481d56074441814480c0d0b240c0302c039541004280242c00c0c0c11034100c0c0400020824410030301003000404058445040c42c0460351a9440100300090040d82c00d480100140c0500d48064181c8500802e95070391950b95041c24a004c0d5000d403400a060342086013414040790202c59086018958000020320300082c2d0380b100348000402419610702000800c0c000002075900800d04207009084d10170b402c0300303a030320f00366a241c083c410f00c20621f1002405030000100401c0010701d1800003031a0b60f03425032a203030b0310f03042c4c58000141042e4000c0c0d0000c0b01d503610000d01c1 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 86122474 1250 86121224 86121229
    0x2010f032c0d02060606031f050a03050c1908030f030c040914150301050402180405012403200d0f081e07060f05040b1614040801021e03220f050a050309 67
    0x1a8480c0c00403c1c4050101c604216000c41c0040c0400352050020400403915140c4604600c0e00280007407400070301d1904426a24281982c032268101546c43c0a2542c140d56140c0c45220311400e2402c44095000951814031400000522604040c220724240401008000340f8558a40115a080072540f50031a800d4186445100076514403001158045e0741003004000241c2c2d40c0c1c101014540c0703100055080c02d40d495140c003500501192201c001c9181182c66620b00c1070009603403c0c8141d92082400007140e0003a6504c5141c1c0c2500440e11962041002811100044168902105040c4a0390410b0b0815040c40b80c80b02c0001241c1c00c00301500710000c030781c600520000e07000d82e84840120030b50810240c245a164440303440c3c0001d0940356a00851100100c03114030031020001c0c8616612819512a0740300d40001340030f940b04400e52010301407842d0105580d00304204c100c030300840c41000345500303000228182140c09006914240e502402c403407502d00108105110442e41184a8006907070340312040b004 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 86123724 1250 86122474 86122483
    0x3010905160e01120803060d052d01050108030d02160606081b04020705070b090d020a03120201110a050a0f090803030f0916050f0d060b10020a05010b0402030603030702010f032c 78
    0x240b80008500010016030481410322001150401c50099980e03441802003520703800301d02c000400900c6074008108240914194992074402203a2103000c15101e1452407d0a9840030300034100c0c80c2d0804c01c600310b5407002540c01440c00781e600d000310030b44030001ca8452108850b420313403114075684c224107005010007402c1c903403046004504139411810304542c0d03202d5541e6401c1134000c100c5050f100048947c103980d1030100c505007040e40108581511501c034585200c412201d003000c840550300303080e201320405040d038007652018955035031803601700380c10b500007103608000c40c0302a2030030b12000701c1d00440c0400c4240000c51007400e440d20965000c2c10303e0300610345428001a0ba0f1504020030302000d01260f5a90320b910300007110700f1180800b103031a403402e02e1002441020340ea646d01c01107082280e040b040d00400d00011301b90040000f0404a6aa0014841a07200032150b0603419081001301c100158019031400b061110740d0f10703000911a5840815194200340a0a50410014800c0310001c2c0001e0800 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 86124974 1250 86123724 86123729
    0x312090d03091e0606260105060402041a0d02040b0d1506030b01050f0903070509190e0105040305030604021b01020d020403110f0f10140a0e01020d08060a09020c0a020301090516 78
    0x80c0800c8a1802c0703440300c0414040c9098010002c60320500202d0612a90380c01c000e014008030b0f4114400607403034840215690602c40c207400101e50031f12000030a0742c5000c1c4282c0301110301c929130001028078518400d0798550300490404440035802e00022802400c0c140191a0203c3e01c00360006000010000c0c509040740c0359840f0004040c1030414165050b640002524180030000c517690b81c851220354002030601c0f0281e0800d80d00b004441082207495000d9400b1003040d640d40780402c100d24030910403c035082c0d4504450140210b02d08001141590600e98000c0020000c0d01d80002e800a60f002003490036030380401c810025082d0007250620034040c00e9a18064959022102c0d030080c1c010601c0800d0201a20300c19592281c107200182184030b6001d500c000080c1e5200d24030440e03945d042814080d06559030b1403400ea0041c45514001840b40e03004074421402208005e103819002031502c02018080d51103041044554080c05203079100584090280d90000b51140c006005007250303211008011401a9 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 86126224 1250 86124974 86124977
    0x101701031a1b0405010e040f1109090f0408040b03070201090b0411010f030e19020d08030a0614010305270a050f0a12050a050901180308030405010515030a05061807080312090d 77
    0x14030b1800824480840741211020b00340b03244001020000139000b840c03400e0b10a03031072030700b01090024036440003002000244d00442e5824003a8480080c80460342604440050070002c08000603c040d00c1054041c1d9844013241c800480c044080341d40b5102c4150381940c0480d03600715900500720740c07985c2190307c40344010064542003080c0e0109020655440b02c04d4111100d4040d10008400150f40711070405450742500300165030b60300d0420982100003000580f25000c01400e617150311000c15031182c0030f094080ca180c214a850040b4500600c7d40d110000c501d5400a54816202140700041050003c0540d6610710360103800c402001c7e00300710f6100301c15940c0311001c1002c10040200c20540180c155903003800c00f03181c42100c0503500a0f840006510940000e841014080202300400c00305402441c400d1580c912004122a5001c06056031444050001044d0f5001140018200101d041d0804130703500d400411148456a40c10141d030550740070343c0181805505200408c21410010007800c1040d40f0507 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 86127474 1250 86126224 86126251
    0xf0a0806040b0315040f060207170d060504020a0c0b060a08070b1308060c040303030c0909050108011a0303250c092a0c02060a12090c08010c0221040302101701031a 72
    0x40700c40034113610500500003441101131640c032900703020403a4156298107034000d500411140c0e00020541440c1c0021400c0d0b0b0240d4140007000ca4603081600a42d50140c15507151020080c1150f591403004c210002d00301608500d108000003a034140070804000246405011680d64020300d000b4400c0c065910341224413180c0c03020b410701c009501c48004075403c480e01403500141c1c4035080038048034001c45983c41517048500b01070011400120641c00005032001c2800b10a0782403005206240d26401021003418411114171604960325803814a5a401e4034802d90f050a12a5210800c8500311400301150b003801125a14100032070129511031803c0381d41e10383c1460710fa00c40403540014010302ca010482410803140d4066050300c1103894104120301980114540c2d110313510b540b000ea00034109040307000014070030515220512840000368a44030040c0524103803900341903809011510f24800d0802c4208800c613014052003484c0641310381e0180d4450404100c00c41c0e86000d9402c081040605480c904244 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 86128724 1250 86127474 86127493
    0x20a06060b07062a2115080607030608030d0b0f030d08090f0309060703030905010b131514030d08070203040e09061504051023031b0109060c17070204020f0a0806040b03 74
    0x19145840c81c2d04aa0300c1c00c44441c0d10146031074000c00b900784610342102c0c6d090580904944900070318480a1390885001c542e010365808500b2070a99415205445072a001040345560b00c40e040c1d00400401c54010300050b818240c0000400c0c5003a0f0320040d2400042c1e000024841882401d1120403907000010b0021414888400009022403060840007000d00d540e1700baa02c02004800c0d0000c80024400a10b205000da4500115101070728130181c025244a1641d0300109164002c20040d81044401900804d9000d00a10040d02c080c0400b91820040d480103101c002410f40c0f0008503d44a803c9200c00b80056060604100311400d4081440c43d22485c208030070010421200780e420b10440300ba20740c1750380d035103810b0b07110001410282d140c03143c2e01405401582030210801582c00304009100b030b640c0c15181a0340b19001c60307107800000001441d00404251820340000c111001d050003900084c001464081410400341041d8001d10303005012442d24003c0042c40e10b400d2142a803640303000d8001e00001d92 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 86129974 1250 86128724 86128781
    0x905060f091603050414010f1a0406030b010306022a010209100c0b062209060518070b03010b030a0612060915020c030d090503091011061e0f07020a06060b0706 70
    0x8a02c500d5410559180001401c0c40b65502c04261100050310003000402400392405002e0500c9a11000007801801044d4400c0e0905210702d80c2165040f545601499003103031b0300c0102030760001c1d00894489214101800c522401072418a004d50300c200d00060355455100e0500042c041c004181c0b400f0300000401c1c45000c5149204510b90205080700c00704184035142c0d201900e0001c120a94404081c41c12180380c08004807070b0300480c09985103c5a44d00603c0320f00e40c040d543e5030210f000380403044200340010070030a600040599044008034002080091300c0e50141e100e240d01c1404180c0b102c0da142c0210fa014000d1800803000001c0380510300f5032410403130044c0c80781e03244a00c40e041d000c02543c4c2c2d40144c0c01d0280c10700644e141200c000300302c006811056107004100c94022403081d00c49004000c0401c0e2214404078940c44d040f04c0c0c0d01500401950744101c4003840700c1c00100b4087c1075028580b40716000920920840700a0180c410300b554895001d82440343c101d030b0340405c601802070343c06840384031000c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 86131224 1250 86129974 86130001
    0x92307090510051212030a0603020f0303040515070f020303071a1005060906071707060219020303040c03020f0d051029061806040e040b01030b0702010c0806010e010512010905060f09 80
    0x3940283c581c4c05114050f80001882d280b1071156082c40c000d800700138003000c0c00803600701500b00c0f4000c8990840b507a02c140101078480c0f040344225030344500030001050f01c141c4024050000140543c64501c02030354140c012a04680c09030a044520003003580c042d00305081d113040000e0704000a912800c684a003042e001c1001c5200e040880781c4164008604401005098984030070403491021406882e4845841c0c0b0030080e40110300c40041d1041504602e403012031001090301c1c42540c1022201c41d08901e150240079200304035944c800e8026030454100d40100d2002c10500181440701a400500c60807400070f00b004642c08601d40400f100038400104585607150821b40303e94808482400030b11945480014546100d0740d4824803240ba440c0d42004140301c1e10840d0b10707040742d00816107e05190750701101203088070f00480e000b0020819840101d4010b510a4203c041540b206050440c500304020000b0480c0d24400d902c001c0041d17403903401704601e5040c580b400000f40c2c007054808669904001c030014a04 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 86132474 1250 86131224 86131229
    0x60301080606150d050702100e011a060d02130311101b08070609050303070f09080c06071b030f0501020c0d03060b0304060504050c1905031219030c03230711031602090a092307090510 80
    0x10b164046010064a0041c2d4100d0781d002483f4070317400141683d07920f0030742c80d048004442c080c401c41405204400e01e60145580d00400400f11a03080030300f400f181e13070749a91604000410f80b0610780d501c000c9000514200700443c001d40482c2c079900c80c0e00380f0012000f402c1c0310741904072000d1034010360b807805400e46840d020380311900d610010204041803420402001c07141168000b50100c0d00e056505003d021065009048100020040d074680051241c0b080d42941c01c94490b07040f5000c0108001004201c80b50b01154000b413080042c0c8400145140c0040c2c03414044010f400105055040100304501d8200115210302c01d010f28801d0a01078001c0c1d950b0040c02d40090044140754458445070401e1740b082e13100d20583c200100302c240880d003208a14944040003100c410002c100300b031003890003d40000082c0c64890707032005074610255029509020015002410580c8000c1d00c5150301d000081c06a00e0f5940c1407140011b110f9460b0810403000d03032800c011a441010000e24040074080d0044403010584203 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 86133724 1250 86132474 86132479
    0x10030e0c060c0f160303020c03010c0905090a0f020c01060906050409020f100c08030106090602190206042123101808030c070b09100b060301080606150d050702100e011a 74
    0x11690001c101503400e001ca032140f60440c42c0030301140011109001c0f040359096078000d5003101e050f1880301050501b01d807901c86805012070241e1208101c680b418a0400350302945840d80070078608054550030051380c200d2004824141d445000511441981c5d01c150802481304640610040000f5004039900540000742940a28100e011303500c00e042c024943c000310107500008087d81c0e503940315401031842030980504c00050080e007130f04148404e081c50403928003074cc00034501403910b03203003180d0f1306562401050501c2500c1e0034000e031500410440001c0c1d00388201c51941d80c1e062007031200e0302181483c01801d221000c46150000002c0c12940040840c28050340c030400c2c060b925125448284668000d1040c0100196119401c10043e0300300411640c14540075101305026003184170b010030159000c24058080315601440000c3c0a520303054032080256001403d25601c0e021180b030000303080c3c1e00211454401741c3d00c0b0001e069210300891250041d00003006000b040640903001c440300b1200c402c18502403 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 86134974 1250 86133724 86133727
    0x15060915171f0312050a08010509060a090c030e01020c061b070506040305030a02270909010c120f02040305030c010212060402040e0f060a120b0f07020c010503011e050a0b070210030e0c06 82
    0x2240c1028109420700550742116801c0000f4104d450014100d60180e9503050000d084c0c28000501420b24003200c9029200040c40d103a0080d040010b4500200102110035082544806104200c41e07002c0c4014107582c19440050002c500e02407003400900b4a1000c0651a4803104000030004698040f5a1540180d85440c0c5223549840e03056001000c0c0c052000010040040081041c136031070090785842044a10070b03140d00d211941c030070401300d00320b4140c0c1c1800c00106400c11850b5114540355401408002d20183c1e005041907141d44807140b0f903402c444480c80d0260743c00682c0301814100e41144a912020032a0700354901030421a100500034030140480042a0b809400720340f050391160708403130180001d40000d0810714007a00301881d04500540b144a0410440300102d070000340f020490b101c4048040c4c450701d1a51340390505142d803010303c000c100c40480e4a1910080303a00c0d5a000390580003001c401c0715554031030007035004001d00000f041203408281032a000e4507464900f0041008140d1100444469 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 86136224 1250 86134974 86135011
    0x105180d1b03020c1c030e01020c06090904020a080102040e071107050a0b0d1b021f05040b040308040f06140601020c0f090109150801020703021608190f061506091517 73
    0x580c074150652100326440b2008175130b1119030700003175034005035642c0c06a540c40445072946001640ca03036194080b82d5420010811405c0c240b400c041c0e040b250070510160a05c0030f0766648024250880c3c0003604080d429540c00c0d41400303241a400122a40d20510380c1c40502012854540020a00d040600c210780b080d4002090315010340c82d80c0c0d841071205151301c403d4003103035003039041e402500c5028524520000400301c10521810307040d5485002e00c982d81c456200b0340c040c0c40d070f0b1301d0985084400810494901d0b040203c4000051081d001c0d0b00c1e107210074249852250305040c0000382c00c00c4a8143c049000d0740c41400d0503145651500b141d0b60444000c07040c00501506103040c150f400448640102860307600001e411000c00d607002444105601c030000c41ca413050364440c80403039160101c1c84404c450b1241a0f9580f00c010840020542c00694401d481c006a0354898501c2003084444c140d1090303001c0362040754100700c0304081400c603c90f100c0107403404107447c13103a03c000030300042d0001e0150304031200c0141c000d = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 86137474 1250 86136224 86136227
    0x30c060f060613140406060309020a05091308070308010f1d0606030a020f0f090f0a060203030601051303060c0f03110406080103080a0e1309020406050a0302010e09070315080105180d1b03 82
    0x480f0303019074409840c40c034001d4898011181314010b0050f242d00031440c0940014030940300c1e10441904503030082103510558504800c2000000001d04507290782201024040300040810b0001d1401a1090f11200710640c501441410741c880c2a9120b002d020340d0701c54450703a100d001c2402c050340c0518100c0310142c99441d0300e264031000b40941c640c0035440840028840781c048075000d014040408007200e4800c0c80d0041081842003458040c4600400341e441400428807960044001e4120100c2a584404505031750b9100d00080c4ca60b400b5003000450445244187d040b07601d030203500d00000d20400704910300b529209005052200512018010a1000c24113511651150301d9a02811100a1240040c0d240d00c21101d402080311590403131245181200c00141401c041c4035120860340c05865441001080100b4010354001c0145188200340d55000603c1c0e600d0004501140648004000040c4a140950b04a0000c07001313000542240d81c014111100b010764851455001c20420005030380030019545070 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 86138724 1250 86137474 86137477
    0x60102060420030703030306050405180d1d0406121a060109050607020a0801021209300c01140a140603010b060415050c03070303020702100c03080c0c03090909010617030c060f0606 79
    0x500d0b0b5410301542c4c50001c00d05606400c81d0040c1e074002c44040016444503c0031300042550349554107626004049a12110381c0a6292080000300e01d11a0908904500000504a501640003481101c845001003410f001d070700c4540d2100360710f001034801c0c024100300c40080e10448440c4507003842042d00042400031900c031004204000c2003550300a540b1610315107190808080201c400740c0c01c900c5200c443e40660f00d079a110341c10b241c1e4055810440064903041038055154000d5454011543d21000000290703440e200c0d50b684150080600001c04407030710481030b0510705014105510a070306040340500700b5560303101140c04070741040319103513540142c002007a1400d00900170900e5860202090ba08185030300350b00140348561003110034158010216100350f41814400d400030380090303041000030745060301e00c03401801c42c85614411682441c3c100800079820795011215100c140e515481c00300281b000c2a03240c80c04250456010354246090022f070340b66034100040c00d40c8180c6e1556004104603448060 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 86139974 1250 86138724 86138783
    0x50f040b04021b070312080708010923090304090b0a030206091207080a050304090501150e06090d02040f0e070e093304030801030b01060306030c1502280201030f050601020604 77
    0x40b08620308080a925280e2034482c0340c070046d42c60f0943c0302c051410700c0d07100382e004511400f020344443c02d5076424102c2c583c009080c1403520741d0f800047e40c0d0000c00380010800e00720f4400e2503000c0066980c0e508012510341aa03c01040c2035002d1900b454050005a5401d401d481650300309854602440c4d51100503d4a41403c03540070042c1406120a01c0050040c04070007001030352044032080c01640da8690503a464400511020000219210f5618207945840401044032402c024003100c0f010301942c0000d4200c80f200192000c1d1981d5881d10449104014050340008100e8504800c031946022501c1540307a01c5411314540300039002031308041804404445000300310740381005114552625140160124030203020555071850341c03c0000900c14807d00400c1c0030349c1d910181c034060252400c5100319451261944080035401541d03600010b011b01d203a4400400302c4686800500700d1312030300001d0100d90012100b8002c460600c820030084e43d800081503900181e0142d8115000382d8414508200344030f484 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 86141224 1250 86139974 86139997
    0x30103021504031202010204080c060405090403080a060902040b0414011103030c091c0305070312050112021e030303131704060e0906040605040f0c140304051509070f060309050d09050f040b0402 85
    0x2c0c811032503d50345c154041d00c2030340c01000031a82c60b10400410004140558414191300290070700000e0000307840b03070345181d4209092010110340c45440350101416078205800440c031000d004681000034001f06c01c44114220801e09240e2600c4070f403020b1540c2c903403200415202e0b107210001500c058540310100c0c40001caa40380c0c1c0041c0030b010007600e0003c0c11640424025800210900450000d000c1c0900c01c440c12a00800b12440041c6010b609108542124a400c0301c07183c0c11012551249031001d0008600c03465603e402c0d0760303034450185040c88820341c0c0300302d0718140002c05000500c681e0380c008034400f0b01d21030300301c8142d2071030b5946200190107043c0c1500601d801508080005810158942011a184429458a070b202485917104003d0074081210b003d82903034440c42400c0170002034101500e42000c080810744010a0302d6585000005c1c456600c40c80c00242d45d02646018000c090101851500f07840c40c00309001481d050000d00d103d07c1c400c0c00d041c41944e0318105420103a6072581185c090320083c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 86142474 1250 86141224 86141243
    0x9090c030207021806010503010909052505130e0d05070f0c0902090f0319060b0315040c0317090307170309040513030e09041208070e130501090f0e0303010302150403 73
    0x88000601941007000102c0c069118524448410b014070b01040c2e110305811b0f5991410b580c40d04000038094041c40e0400c4d20907000324003031140203544c18104101981c0401007841c10003403600e801d1002903105080710b00180d5123403004c1c150007d000440c017081141c4c41ca28009464110900f03207442c20310350054004008060790500000c40000c690081c0c0707206c0700704913a41c1d4120015182456291544075103000351003c0c1c14410640000d903940e002d15000000501250f03800300c850700c0ca0355403100c002e40f800e07640083d03003800400400801d0494040036103888810141003e5640010a6451b010b42c05290103045829038011000ca404100752100803400a109000b942080b80001c06081c800100503400150444044861401c1c0300460380e0146500c100c0c030901482c109801103840e80c001134481d0302000302d20307824110f26981d1924100309031a0200301c0007980d9403401030010120341345503040c000103504100110700601004030649044a4040c0c0e850401c0c2c0e4400d0001700350358800c0d504002c0c55142d1 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 86143724 1250 86142474 86142491
    0x80a06091b0201060b0903030708030c04030b04210e0306190e120c0d02030403030c060c12090813060f0207030611070c12050105010b1c0905420408040b03070909 71
    0x1d00c003190160080035a002041065103e00800c00700d445114501c9030107500030001140068600d000940d44121902d143c24141078480e0744448c03051009a0302500c001080d000c102d032841402c01000c409040550500103003030a03804e0040f035110000109103500c0d0504020a820901c0c001e0b4000c1d0942181000580b60100c20704921000a1b0b04600c62040e65449034030700c44194680000205c0b400e0f6074040d200d103a4040b41c20b03078070b02c005003d81d0325000c410003425291980e031141040c040c072580c0900c502c4016840e0400e119a900e03c0c85a17641c8280200010040380100890700803840c0d8098a03044040030629091b800d10228051203455001841c1c1d03956990b0010754105019070302003800c4d00c070340000d0046998482c0030302d801d4054096007698181e00c0710704a00c000d180383e61005020300d00c540e09440308220943c111038100103c540300c058414410512550180c043e241c071410844d081c0605107001400c06881d03031000c1d801503000c3d01850220000106036100e0088420304010034917114103101010 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 86144974 1250 86143724 86143751
    0x31101090c120b100b03040210180b1b010501030b1815010e0f01080109020a050405071b0506010815090a03140706020c03130b070201080a1e050a0204061e0807080a0609 74
    0xc028169807014040c2e004c56980c0b07607100c19080450303d20083c1142980c1f00c5e9004c010101c500030a0000c140640e1508000407440d50130951402090b62102003602ca801490314503454078112180c0c404203034544001800054601c104094008030703210b4146070300040301920035181c909043c8a02c0c5207106204000985200903c40031845840c1080d03100425903a41d50340c441c00d82d04c0600c3d00030340c003030010102800b039400c05a1000c1d9100000f45031112200380180981c1015100f060025201a0015001842030250400c011108080c07100a074803000d20b000d8104684441d920038008040050610544059000708010b80c4d800310341041045603910403e0311419620750081c0c8000f072900d14500350001d8500c6280d0241c0c0d015940603180d080c510703a98a48044010300301230010300d05e8941102c4102101074403d108080c400c1c2c1c8201e41c016512400c0201c040e210f05180c060190410100d04d654400700365114408580061540c104408691543e42e040d4015109035080201c5c110b20f0040030400c0203 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 86146224 1250 86144974 86144999
    0xf020f0315030a120807120e0c10020d0504030605040302011b020604020307050609031f060b070c09050f04021f170a05070f0237020d031701090216031101090c 70
    0x460107150034400c0341900720103260712032000e0003010f040307030002c2a0780c0910540507910751a8450050315254411810300c2440000320344141c0340d2a41d841c0d0010ba030912440c206880c00340c841c00e099000900c161402840300038182c1c410307400f00410068440d804035003054005d400c54420403443c0c13240c0010121900100130f42e110002c0398241c2c800c2c4903c51000031036050010444102e820003402800340d03200804030b80180719080d6550b0b01c40303482d520440024952800c201400200340b0070300034814900c1c6010440d0702521006000000760950140500006175110b444440c80c9000b0b00b40031105104810b80300351030101001c4940c04521652100f0010601441d03071010340b04e900c564861040c4c18845500c01c99581500300c0c036520901e036142c140d4000d202403210b003000c10390040d600d0720081c004950303021139081c2001c0482140491501c15041c1c0411100340113840c054030017200f0440c100854291800101d00841d0406004d006014043e40e040202c290000503003240c110101c00c2405070355845d041c186 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 86147474 1250 86146224 86146231
    0x2040b030c210f04020d0c03020a06170f010819060b0d082a071e05121e030f070303021c06260102160305090613120c0e07120b040f020f03 61
    0x841029000000c042c1c0ea90400300b8041c5041a4841c11560754660a01940c880040c1003580c090b0001240000141c0e110000c03140640b140381c5c0c45000304046800d20070344d00d000261030085c20801c0c0c50018004c016000440004004056a14020354103441c10400011310071021031582000d51002e50f003060003411070080c440785040c074981441e00b403650000f40b44902c0303d980891046400003541040561031100700c6039900300102d004007401641d10000609a07200002d0760b840680c01c030302451041c800654002c2c02c4004c040e40051860b100080d0050199480f51070001014107a0215007100000400c0340400c42020b6090420416140c81741e6103165038054500741e040386864128072402400106000f80c6980d0100c03c21f81000340c441d50703641652584c104400c4a50003410a1024080f00f004014440c001403020102c070b040c190a040c10050f07100b054a40080c02012a018240403071681d00801490300e241103080002406070303602c40002d010f40002403041004900219028a05010443c0154007 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 86148724 1250 86147474 86147497
    0x8032503090c080d1d04020409020d0608010506060307050d020a0507020409051005130c031712040b04120c03080610031b0504050a1d01090e0106030b07080618060310020c0102040b030c 81
    0x60741e1401035590b5008070384e40450003e40f42000180c030041c4a500008601c3d01c000704050b04060310784001c4001c90700f00b040d400380c1340c80c1c803003c040205003400c0c80346e0354110105036038447c0303507142c0808060807500ca01060040034541c0050b180c00080e02c28000e690440d03500070814401a100c5052451717072103548005020301585413502088562440b10403151140b40c3c000710300c1020520b1603c5450142a1070000711104501c2000709030501485080424801ea1094000b04000d00b000e0030b01080c007241c4503400c50280485c41d4400400710760803c41e00c2e40d210008441540c105c0bd40ba417400c0b8041d010000d0869a460300d084581e020301074000016100741c417000d4031b020b4505076443c0b41181c0030708602c04440d00d803110035074010b01c19201160009070507003100c04000b140103a6640e17248041c801c3c0031200345000a4150040c00481c0c07402e452103802900a41c0306072411410500c0000340c444401c00104007c0607400215004000030039010b0b80c3c010080e1814261b120310704a401142c072036000120009 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 86149974 1250 86148724 86148743
    0x90209160f081e0c09040516080714070209040f0204020a1d040624050c06010f030201120b090711120318070b040f171005070302090f0f0d0803250309 66
    0x1c14400c40c1d0251048a01c594000b108103004112500004005040c1240c04502084000c065072140c0c0100760288034180d5230410400e0501100400207200503003103104111a1844c00044d00300c1d02019501d005404581021541d111803408041d0400e42c03503002904a80081010443c0a4208400d07108100307485025450200700241000201c549074000c802d20003000400500c801410040c401c54100d0b25420107030300d800780d151280351920409a00070350740d01d19040014401c65030b1000d500f0318900c9440c81c050059180c060006010301c0070080652080002d0b5005005000604010500c15403e43c6210741e541d9060800c004036102c4081d8900010710704c0340442c00991040840120b800310340c80400f00007000c3d0b050038440c451510380f801d070100d45407045810405001d01544920f6015280c240c07001652100f035032040c400d0455030752402d2481042c0308040f0f0b9100e900c680441c0381e00e20383d0154502c1d0307403580e481d00d000000c04041d520540380190032100c101c90f6146c040d80302e203010602904428 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 86151080 1106 86149974 86149997
    0x15040b160909020f090a140307060807200f0601080d1b02040608150106030608030a08010905040303140c0403020102060c0c0d12020409020706060f0602070302061b0109020916 77
    0x1046000b4000804041600c6c010584000030541c0c04401030314840b007403000076180c3c10188902c6081c044540006184240b00b140549141010001c91010301203820284e00d41d41c1086050b8400e1510502d000894460800244004002c0703c940c2d4040b0103018150208c0010103110328101d82103910350740040f076030320000d01c25484507000700000c1c1404c5624001004050309c0581d480f85405800820120754902d034002a00c43c1920034100c00480e0548403450124000d0500c06154a110300c02181484252074001c802007088034003d0b42180c5454540070809486440f41c1c1a12031f900e64407485035031000c0d82c020307141c100c1c846901c440010308150340c032100c020585e88100012a48583c0d01c1c0d0083c81182e0324661800d001c3c20151004040240c00c42c1c1c0032030b810b0b114035072140608a145115400010b01d0940211a100c3d6010348041e11500f8281d0f1a41f0781d070840d80e14a100840c0b51050003 = true := by decide +kernel

theorem cover : BRFrame.Cov 85971224 86151080 := by
  have h0 := BRFrame.cov_init 85971224
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85971224 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85971224 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85971224 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85971224 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85971224 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85971224 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85971224 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85971224 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85971224 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85971224 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85971224 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85971224 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85971224 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85971224 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85971224 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85971224 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85971224 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85971224 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85971224 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85971224 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85971224 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85971224 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85971224 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85971224 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85971224 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85971224 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85971224 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85971224 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85971224 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85971224 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85971224 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85971224 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85971224 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85971224 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85971224 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85971224 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85971224 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85971224 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85971224 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85971224 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85971224 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85971224 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85971224 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85971224 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85971224 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85971224 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85971224 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85971224 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85971224 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85971224 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85971224 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85971224 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85971224 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85971224 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85971224 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85971224 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85971224 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85971224 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85971224 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85971224 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85971224 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85971224 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85971224 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85971224 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85971224 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85971224 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85971224 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85971224 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85971224 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85971224 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85971224 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85971224 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85971224 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85971224 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85971224 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85971224 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85971224 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85971224 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85971224 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85971224 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85971224 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85971224 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85971224 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85971224 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85971224 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85971224 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85971224 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85971224 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85971224 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85971224 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85971224 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85971224 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85971224 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85971224 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85971224 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85971224 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85971224 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85971224 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85971224 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85971224 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85971224 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85971224 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85971224 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85971224 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85971224 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85971224 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85971224 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85971224 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85971224 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85971224 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85971224 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85971224 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85971224 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85971224 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85971224 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85971224 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85971224 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85971224 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85971224 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85971224 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85971224 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85971224 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85971224 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85971224 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85971224 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85971224 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85971224 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85971224 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85971224 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85971224 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85971224 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85971224 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85971224 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85971224 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85971224 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85971224 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85971224 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85971224 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85971224 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85971224 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85971224 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85971224 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85971224 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85971224 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 85971224 ≤ n) (h2 : n < 86151080) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
