-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2867
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:58:41.844766+00:00
-- url     : https://prove2.me/submissions/bc978730-55e8-40de-8454-83cf37a9748a

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 515467625 ≤ n < 515647482 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 515468875 1250 515467625 515467633
    0x3071b0317070c12150c03140c030901060f09020d0f05240f060a020c10020d1403070504090204092003060f12030c0607020610050423040f1709040609020c 68
    0x100c144001c2040e00002021145210541c1d40490f4020f0a10100c50403070f403240d64025041c00351681845c040c0c0f0420305440085c142820f0020b1885202031351069801142844c2480e1240d448814040c050003250340b06601901d610300c03003c90a00342940003402801501d0100340050060340d0705010480c5c404031400c1d5140d91104400181c10040c3e611940c50303042d40100903c1c00714585000042583d80402c9001d00540d100b10740c0b01401c1e003040d0002c1800e0141a00190540501c1c03518003a0801c0b010060b454a02e100010000716400d00440546018181c51201103440700c4d00c5280c80b800a0880e11008150070821f0006040f02d5650201103a00c101c00241030400c03080310315070504c0240354080c05510400c0c082841030300d82c103810810105110701410360041006041504070540005800c1d040075009600b005400ca441c907485a03d02030754032207040341c219000d076140d0400d4030001190b100011700501100340c2d260407040800b0040c1807161f008403420044107540758800402c03171003000740600540d04 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 515470125 1250 515468875 515468903
    0x3060e0304050f061b10020d0506030c150304050111030705070308090c0f060708090613030309080102180904020f0301050114010f1107050402130e0403020102071101030b0d08031b030903071b03 85
    0x2000405002c0d0100542403020b030340f000d05c500c05410040c05041d00c41400c3c0c0d010600d44102aa2170040070b030492010b401500300143c511011600c045100c101c0c1e006040750006c040f0702040001d500c1140c14068403441c036501c07401c2904004003564840e035001e0b40014001c0002c2103201e180410707000c4418500404c1c054a4010350018803481b80c010364400c0c0c51040051103030030fa0644401e80100000c14980e140000d0f0b203429890058520700f615001409181c0c8140b10b80c54401920191440c103d6034110344500a41e0303942e100082c07a0384c6688989640550034030300000b62030701c910b40c80c0c101c4902c02602c502e002e02d4681e050407200030b901e0940d901c20399848860100002d040c80d42c02840419640508500000e840e00c02103240501c00b940c08900503940007941000303000c0d001001044415007440c007230008004c2038000401c1041c0e08500588201c1e000004111284440f444d05000c5640080070541c03a0320304450542e403030340c1000c0801d803208a2185840c401c803400a804010640f0b81c40150100c0f118 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 515471375 1250 515470125 515470129
    0xa3b0108061e041a120717060103030801120f082113080d0c02030705030a1107172e0f3213030e0604080606180c0403031110050c0403060e0304050f 65
    0xc91310150400d04c20403890103541c2c070b5403184106081000b002c00000c0841610b846030400034690503c08100c0707940c004800610000364002c801350304507a0701c00c0701d007040d084143c100b8400500414100901d00000000c0302030742c2050301902915400000d4156483d02d90311441c003a280c00e4002440140f1841c0d04014100d580e0829502c00519240ca52044a0800e000756850615503406107000c000402c0e01c0102039080c8610400101c3c028001c20b01400030b050041245c140c2e03036101c002225070350002060758200b2500c15540140344102600c20001c0c4030485140c0c070244024643c030f6140c5103003180c580156080c85000001140c01554252103c50342c4e50380c1c0c44001d080c007103180900483c2000400356901e00700750780346000ba001500d207503070142c0200e0070503108002c81d84098801000004990808108112508405603011a605402c1a4152083c2c420b00207007004801f0300c468504c54940f800380444029104040c000748d906c1510201310590b84845a030703580c2c3c09940300c0c40f03030b200702988030300c5603a4 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 515472625 1250 515471375 515471381
    0xc021201060b071406060a05060d020d0b221112061e04050c040e090d090506070204060e01030b04150510050d14010c1101110306060a3b0108061e04 65
    0x40020540006800703511000300c4105030f8030000f400c1d208440c1900d4480311800041c0566030b00141c0885640f001c051a241c08a01540141e11016000940c081000826a0303ca41c2000c030036078000405101041c0f03101c145080080c410030208003c05032810303d01081c2c900a000845401e030071400300300c01aa80d5100c00f004404d951442040c0300320f991548103406d03c0d071198040c0320300902050094548450800d0207141002000411082443c1c0c0280500e80070180c01c40028000d0354016030744150707079420b1070010402501c4c00350710518000308400000402c2c8114504540c1c09144101c0038a1607008500d00c5d80c9054507010f940e419620000348400700058a490358810880b1707841090304060b1954034201c014211400b01d262440850fa80701c0c2c1d00d0300e00c9003080c81072681d1444428030702825400c00201180b81805003803941418400c144800104980b00c0d8120142c050341041300464003604030682e42c0101165640450307000c151042c0c0414064513120080d05e2413030441542800304544034000300005 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 515473875 1250 515472625 515472649
    0x1021b1005120705070201140a14030604060b1b07230f0103090f060902090901020f1204030c0f0309030303150806040b040201050408070b12250c0c0f0311030706030c0c02 75
    0x180001000b4803144410346240c454441c42561302c605855014500024091200f0082208181c5204010b80800141c10404003107111400003281620f964407880440e000b061a80c10003e1020301c003055520806d00394410a0070b441040500727940711380369560000052080c051039041102c0f0b80140041105060040404d00302c010145400b013901c1c0007985034010306400c14001541c2090302c660360b2106600700311000680001608008614100798207030414458000c04203000e00045400d00800d00b41440f40e40b000c1ca0294004000035001c092602c7d0191880e0100e2200300c02190804a0030700203544140300d040f007100d900502030311f901e40da0780d85c4401040700f0050040707040c00000c3c0008507010a04100490140002c0780d440e594a041c0450405903603c40101460141a040e04185207405446040e0710182101801c040c1c1c8600481d141802c0050030f140c021803481a16000000f050081d213500f41c02c08440d0541c2924130302522900111306654007000607602091424480100500700b120164070 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 515475125 1250 515473875 515473877
    0xc010b040203071b050109021f030c110a06231009060909031b03030e030c0a0b06090402010c0321020d05041506030b13020a03140f100e0d0c110a08100b01021b10 71
    0x680070402d5030004003402d40680c1424905000c01c1d40d41846203805128130400400c8905011403c403050461540e698185914010070842d100e01c0102e000c220000c101c5612801824033f035074018544001c120081880751b1041c07108480c00c00750300260b0702c4c41a208407485150540d0740c02849403010341d060740c2d11054011044080580c1d544c00301c64100020300181c10070705800070160140c0803a500304440c1c1904040c0c0b840d4403c040301400e1000503a000b14059040076854240344c1e144c14800c900042880702590040d84509000089880c82d011090740301a2040f0b1180c03040855581c00700343e84400b10b6969003c000c01d034982c0c8070b01042c40888100e4100b014107200400d00190240c6903991100c2171240c40c01c1c0b0600f1350380002d400c5021000f003802802c1400c2e840d03a408001d612481c01e54542d6911131032600106000e03d121081091201d00000900120740191001280598411b041596280094124180789103400084940d45d0701c04140d0074101a01448203c00c1e00c50203404100b001440114400 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 515476375 1250 515475125 515475131
    0x1b08070e09031c0506040b040b0a050907021c020622030207050618030a0602030406290d020103181101090b0a0203070219230316030b0411040e030706020c010b040203071b0501 77
    0x9000f1000d010480b0701c83c0b000c00d078030118085c281142400300b5910294009413055040900a403615100c030710184c0100c8100300c94805003038403118410307402e14070601d10800d0030550200303440b075841d6000a5000e00500b01015070002410507114800500100381c00001c005801c002001c010b01d240040240101d4040c1201d074100d803660842c0082d1910480c040110b40b50b40d0084100000d11095204084c40c50102e410420790440c0c0c4070f030840100050460180b40700300c1c428244d81e01964400d501907180301c59a8500c0134207501103030815080c80030b02c42c203c440c0054107080c0c000c11007074100015181d041c41c09400541c14a607595003002903124800c15051300c4003007003110014130300c1031308038030405041d0b81c80c481441c10503903581c24941000d40c20700d0340c2e6040310b00e40042000021801504180e01c01c3e00003610303c01d1a207207500003901600c8042d0080c801840080f409905214481d030003000c400004e10001c00c691048902404281d00084410b400420600c4c1ea99500100303200d0a4a01081c0c130401c000 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 515477625 1250 515476375 515476387
    0x305040816060e1219030c0309020a060815241b1203090714151602060307051b0601060c031103040510031a03060f1512010c0c1b08070e0903 62
    0x5901c12001d040800e840043c0c075001c04028010083c08110f0860840030021464169a016680414030f00d048040007055991203600c240c0754800e5121880280e401008861900c7e520480103108400544d050001e480103195a494a840c1002030b2588044240f40a590520804641403140790091078581c005042084141c3c0910706090201e81940740b0640c261640740d040c55900a8074143e510b0708103262492402495090360b50382c00e1680e10458003020340306541d4280356600660300103003c0c2c40c000d4011001205001701c441c1c10034090700b02034010000c00002c0c01028640a0b0341c5a4007072240d000443c0005001c80c3c0404d20a440c01c18003801c8030805c80303240a555401042075402201240b034006603841001450825000c0480d000c8500c0480080015040c0316810115624020b49000000ca2405a40111984130015031076203d64552008118000080d400900081440c02c002c0314454096103032901032415610102064800c142e00a140042c200100c510400b0006800c0c00c031284000d00c0741c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 515478875 1250 515477625 515477647
    0x402130b0118030b01060210050108120a020c1e010e06160803060a1e090507020f1b010c061103091905030a0c060b10030e0613240204030212010b0102060c1903050408 73
    0x10100940c4030311550a061743c540000203003800760703817403e41d0905424400104070300f00c40000e40240f03400003881815656120701c94141d00d0303c101083d020350010800456401e503a0b0080c0c4031407520358001c1e03c941c60700d040c0c180c042110600c00d8404d0801e6a5050101e44400300341ca2402550307202c3c0e009806210f0060316100302500417910f4600b1603084504811040c400e412441c0122a0801203900003030200d000004491620341c04811140c00764400132480c43c82c0c581e0300c107108a900882c2c2166040104084590035491140d00455031140f01d40304050103c480c01000c01c2e00c641400e600540594100880c64074100c50643c904003003030714a070791031b889078038055629030b2240030002c482900e001031845603244045090210003131128004c10050310119002c0b43c0d251141507040c0c0a01c0545400350002407034814001d000c0e50b000a0741024064000b1040c0d5101588003485c060826002c4814580c1c0e402c0081805102d040007000185031426401b2480301d009411080d00f191091800780e0800140b454 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 515480125 1250 515478875 515478917
    0x30c02100b010e0312030a1a03300c070f060f080103140a06050f0906180a0201110715052503120b0a081b0111151f03080f120f0402130b01 61
    0x185ca1140d03207000018468281d060b842100d00c1036854220600004021600284d15101c41c01100c8458100101c4e090a1101c084901007509414065145440701c10100d0070b99034900b00350103041120b62148101181c114012408a00906001d54900b002d030b80c2580e441d06120824010205030512807202c02800049150240d244500386c04060007070302e07140c002ca81c51319000c1d002e460910040c0c01c1107102d5090140204040b01031507020f0a12081e5189106002e918190700b03a400702030044901110440c0d119404001006034074102184404c0509646110a8546070340f001c00401040082c8410540451190003030789440b9802440e0398007070b955815895003880c010003585900303d103030305268442035a0010161444500c652000700641c0c500c0030700503c1a4040500160701803a440c07550f000204500458550145500c60101a01c42414001126254210303002032103e11840e40002140802c0d142d20343c5214940090600300408560030140c0000c00d0107103000c40c1086a1641c4c559110301d0801 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 515481375 1250 515480125 515480143
    0x151902030d05010b0d14070203030c0c0304080601030c05010807022803020a05010c031b020c0d022806020d201b0301090803190b2e0e03010f0b04050601030c02100b010e03 75
    0x80f14035502c0240103040c01c11221209002000d2180728018428240d5000040d89e51002f071944490b07550381025400d0a11b14040c60b4400840c0d0322030328001000304109841244100ca0082e00c0b07080060711108026612182d1074090b4601400b10584449141482c505103040302c14081e0040c1c4006002c641c80d818251036004c10000c01083c4c0310841d2408400c551011000b03106024409403c1c82030403c40050b503054003410001c0d10415800c0c240c88845c1014aa00c0342c0020003810005001950302c1030007a480f00ca1214002011451028401000107000d0030f46840c15050380300900141c10241003101d0559905591050b015135803502c03102c002805001c001c5014140c0c0309007960481d080042540d00741c0380745400142c09008080c4900c880784c40c065141c00c0c110b0310701e0f42442d0007203100c001048840c42440507041c1c0e0706600305500c0c0980c050899100d921680f000740c0d0b05205540d100d800540035640380c0c0e848440140d0010202c0b1244400982c0980c03101c00c4c052410341c000c1034140c8006441e10000c0 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 515482625 1250 515481375 515481389
    0xd03090e070c030e0607050303010e061c0303091e08090409081b100506181602010212040f1103071a0f1b070609121208060d0203030a03060503060105151902030d0501 73
    0x1504038400f4107420110103030b00d0303902c04c4440b90724108056035039549074001071103003035802c1a0000c049042d5580c3d54140711030740700e1401c40030303084544d01d0704004018055240302600c01d0340b038406925003070721030b001024204a038210f24100c0ca81880481808000c00c40d841003610910300901c4103101c1035451807501802c08103404010620403d841030f00108840c030150050380b15406e0745c0d0254040d032900e0b41070580d00c015080d05c25124203040d15001c0c1c1c06481489414503d50140c0001c00c400c101c501c0a400c13a003207000e40801c0480c1c0203040c05140c2d8441040c0a8a50030b950302c40d6484120740c441000522034004403020341401d01c0f4010303440d2180e0300111072500100c3d400c8a2000d00400c1d41c0810218010300e040c25040201d6040b644800d21620444d00144040002c11720000d200c50700d40740c0885002d290301404403a650781d81d11800070700905c014014984280990710000032a460145030541b40200803103103403480c1c90026400108602040070f1110258001401400e100d41100e1181600a117a8 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 515483875 1250 515482625 515482637
    0x6271f110a051f06090c0207030f030c151a01091406390d14120a150e0907050906092805010306020d0b04021303060c0903080309010e12180d03090e07 66
    0xc0d070040c1109603040d60b00410b02c101e02e4415903610300747c3e0002e00c603002c6030340141e4000307021301c21420121200020102c1c09001d04205641c000c004c80c0c00c0fa440213821050500070f030b0000c5125080112005402441001c840b1604122a21550714000e0000e040301c200c6609508810003402980007034180002140f2210460050b21681c120503050004c940c0074616850034011104290a1403030480c080c0070400c6014541d080c001a007002e00f1544041d8007040301800d105001c0c0e82e15144601e0405040300d0303000c46030103040c400207903500340b0031482e0f8002d0700001c2a54955a46031101941c1c031000201d4002801c3c0100071401a8444080c425540a5402510003503035442e8420341801c15110041d2545000340d06c100030000c0744000401040017501d501040200709200041004c4482001035000540000e200000717202c01c04005600c40b010443d010016902e0000000509050342e0140504440241c50341880d0a4010b10300210201002031107402d2003898030b07485940d00205400c0c1110800c010800c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 515485125 1250 515483875 515483923
    0x1f140906040308011a0703030c030b06031005010f26040602090909070e220308060621010503070512030f1c0501142814060906271f110a05 61
    0x240c03000036103001d490340149048012081590a00d0680305d541005410142c0d41e03609c40d1100b600c280c1000c1c1082800510294030707804c0080419241c200c192145901080c015000603030340758025240d07021803544d40b205000c80c07051000d403840e40150004100702c6526070700304600c1e0b00382e9840b0340380c4074000e40100005081d0107042c00c202d07a5038040080c0686980c07261652500a80c8010b0b40748041200341e040ca0006070645401021802030b000311500c1071890742e09041400c403800c0003c11610f04842c021011070305181d5440b003e11001c0c291345524810341d500104600701110160f040142244103150840f200c804607100c4003001140c400782c1040c2070242c551030046199141aa07680c1c603040e400c91160320700d0403050512128010406215103c031640f540d42c00c4607240e544400030b45001c03e50113481c4070fa40e5451030458013802e07180f10a061030b0611030b401d803090031410244160320210503980c041d0325990365040d4094800d400749401e1420584110803203580069820b103c0c10107030a60407504458038003 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 515486375 1250 515485125 515485127
    0xd0905030f0318031206060a17091605060406271a07151a010c0302031b06070f020a0b06060315030106030501020405040f0e0d0c2303030414030307021f1409060403 72
    0xc3c500e000e0344495620601c804452503070381c4440b280c1c2203d403c030764603640c0d2681074000303442c9031041c000c1c41081c03c5080810402d4161002c2071001c0341800401c101544c15031110100800c0303005a018550000e5042164110981202942004400620360049082d20707510b4241c00d2040c00400844000007034003285450800030000c1d00d078040d101040304140712010204000070701003000c1c1401c00d410030041150500506000340100c940b001150520941c91050701d00d5490b81d2034130306503170713240004103000c407480040752000ca4045c00c07096110a0000058450108001d0f06400140201090000010001455640034441c00c0b0081d4403c0002503126443c0504002c110707840008d81c0004942010b001c509413031400700c0c0d50580e04401d400d2980303200d496800c040040c0d0003a00440c090645505920408000c0000081c5200e244620380320070385842c069400c01d031240819922240541d1120f41560702c0300000712240c1c00c007125940c50021700e0504407540c2081100b801da801c00e81e00d802010030300c4141 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 515487625 1250 515486375 515486401
    0x1507051e1606270b070306031406010302310b12010e0601050415080a1712010906050a06090b1902030c030a0c0b01080a03021f0f0921031509020d0905030f03 69
    0x5920700c0243c50031480d0f01e42c1c08901d424900340c802000c00e0b00440c00900071900a6000002454200c4541d0000100d14045075036036180030700060b4420614080340b114801d00c603107858105064541d5800e401d07141601d058502811001c81030359072055001c1005c0303039100824400c000c014a04500204040d500d0030342030008440d142c040c00102d1000032101031003c1000040d0030001103502c800800c1403202d074000302245501402c1c0b401f41d002c00c141000001c040c202500500142c40c821559807041c9551103000381c0b4041114410032407000c0c1c05004000d0b00001c5441c000c1c03406034180c010b8910300440c030900107085030b00010028010540404021050042d11100c140c090002c1c0b60007070002101c2e60310017030742e55400d40018814040c5404980d01c0c20143d41e03042a200c0030304000c02801030100600d0051000c1d1000c041034256031217030411042815103e4000c0864049115014219607410319501001940c080314440340c40355202c4100700002503013040103041a51040c41d58a8403400d224221942d0 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 515488875 1250 515487625 515487641
    0x703030608060606180a0b070c031104230402030c040e01020c07080102211b03010e01030605060f0108060d0206120106031514060d050402030c0a03140f1507051e1606 73
    0x3003035110b4001c115481d240d0b00220303180e10103902840500e1212078030000311514286d401c2008542c030302203524020000c091340c07a901928410311200c5071006141c4180300846001031036402003502c08030000b4242c1c0260707024503a001070024040c0c0e11846250000329082e01c01115503001180c0d40003e0110800009000d1300d0050f142e4100290f2501c122030794250314000f840e010f0442c4079103010b808216090303a0744e140490500400c2040d141c907076035504140110f603c800d1206a450b242814002580c529083c440c1d00c407000030584500d2200c3d00c0d110188455188550401c0344c025104210080c0e031048090203103402010555030218840c4c10505001c2d071184d01561007241441c454a034004100c0d50740209507011005807030303000501c0c0e544d54000a460b04174284005900151031040100502061108481314010700b04100c80e20405480400c42d80d41510201018060704030002155010784258010300d00c1e80341007011403c0e5101680c40307117209a40f00000d01013000c034405034200304200e114026210 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 515490125 1250 515488875 515488889
    0x8041206090b090c1507150506210c04060914010b030703090506011205070b07030e040f0b0418020109050f0307090c03090b010e062106070c17040f17010b03030a0e0f060d0207030306 80
    0x2080409940e1080f1024181400c0c481f04030391140c0024003e512400d44d058049061a00da200161400d105400d4407241e1290031180079604042020a10700454001c04065440022950096a1070888420740c01d4001520840170103807242d030b1010120f8400c2211602030668071600700000700203880c0440c502006a03100c00803c580610005020a400c00604442c0c114151004245080d006004400414650048542c0103181001110003602e1004105420314400e80b42c6084850301c940400c07004010340030f80e1951640c0b141009000c4511150484000000e460801140c40680d990300c8a139101404d802c050b002c000c00e2000c000d45403500400909a58400c05510500340880385120b586440b0000d01f00300030301044009600c200014207110040618007140341a03200c0b0b0b00da04800424045510400140070351080c00c1948080c1d061083c0e0402440050085103007242000050b1850001101540d9202c0b0513502444141d8540400a11004005400050f40c4071280d290180441d54103800c051 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 515491375 1250 515490125 515490127
    0xb09100210060308431b060201380607110402040e04120504150804020a090f09051b01050405010c111017070f02060c0d0e031801170408041206090b090c15 68
    0x85d00d0181c0d02c9003003080f207a07114860706a4610309070401242902d80da9400b41132502da03c08002030034650651100c61205104840200b004852083c156001c0942d0780b10300320700c100744152138081840c4c014002c2071503900c1004c1a210000a0a00050480e0016070201c01c541d0740704020081040400079000c0099059410498109414820502d8480c24030040b841d0034070640c0c0001c541035558071062503009042c0000d05000c1a0102c1170080090001e046084074544140900d2010070703004110700c2042c020040e0360311410140740000450ba00460b0400c1030f00d40398036032003034402d0302d840c1d614045481c00c0890301d8100f104400b0002401c0c0d4504000d0903941004a00011000961f03404280144c02500c403080554640c981c0c023043c01c00502820615030f41c2c84c070001904005003100032582c01c003090805d0701ca12009416a520074450b00c807080701c000303103000800c002c1030203408003604001108500440340000d070340c0c00c3da560303011b125503065440c030b03450364800320b01e107481454007408240800d81520420b0b = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 515492625 1250 515491375 515491447
    0x213030b010909242418020304050c1011060f01180b0a0510050c160306060b040b0403080a030204120b012c0f13051005040302010c05040b09100210060308 68
    0x800303040c41c11301d00e411052a440c494050407001d50740c00100242010003d902685440348940c0d599010700340c440c1185d00305030f254210350003046900c00d481c030840d00030000d8038a0f052030600300600c042c20000c0440078041c2081a080340900f0070804648501d200c0e0b42c10b144154100803c90b517560130100c880d800326508040400100740c40c0c0980c11380403110b0070f4401c1c03000c00031961015507441c0240c0603540c4144c82001e904524000031002e070401100e0003040d081000c5921206898240d20a0b03000380c11581904010400c0002c00c1e940040c125042240b400504040d1109038094008444100948940000b031005102d000d88181c4044942c654143c5891050068509110083c400040c902c03050201c07030314006440400030031207032142d85e80d110044d5a480c040899680c0001c00c1c0a640c1680151b02c1e090040c1c203858069800c5038256102e0400c001d05017807402041143c03900041c1d00c3c0c54110f000700705d90411b0600d0640030b00070140d0701c240341e916107400c1c01158001c1c1c50180c00412a214450031812 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 515493875 1250 515492625 515492633
    0x80609100308120c3a0507020a0f15050108030c10060f17010b060c0307060e0106060509040f060f090e010f0902090f04080c1903030c020d0f0516060213030b010909 72
    0x1181c008049850004500d940c1d010303050000d5009008a170003800030040e004008250b801e200c828141142084107851001c0284032480407940c0850b103401c00750f032050300d40700046089040d158090900c100341603100d5121590080c01594020792144025a0000c03840070001d550030300c0002200c1b102c1100810182d4603000401002040a20991030301c0700309036070940c100c1368080d000607801c1d032005002a40d903100018106c41d5680d000c0d0006540107480c0c00e08000b0311804c10700440d011210079585460404038210b08110041042094001c02141d45080004401d496888200d00401c1ca0300ca0028070b99020703647c1182518082e40440c00074510b4448804010303510a40e403d60444041c2580001079501c0307103086205807040400f807503490320034009801c0d241c04000e443e40c007601c2d00c2991b042c8480000c5980517a0f6424401c2c40c2400800c00d00c0c0075600520748a140941000440302c000075080300795070340303130001240d10049501451112015062040c0141c1500041c014103030341000300315004081d10703 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 515495125 1250 515493875 515493877
    0x30c16050d2d0219140a0809010908061306020c15070f090902090d0807020102120706020d0c0318021e1215070503040f080d02040b030f07090501031104050405130c0303080609100308 80
    0x40581c400655121025017031240f040201c00d500c003410021030344406400e080007051500038042e8070340007480b00040414009008038400d0701422a14a03145061070403561400d02035080410752280303d00c04c0801c041c1e519042c0481a9019401c20b031140f03503640e210071800625007000c0d5080808080d00410032080561a03c4c802c43c86c1c010b80040d06540c030b030200707440102e0420707400c003001c071002c0d100105120f404d0080581c002d00300240319690030000c051000f40107809031980d074007000e40c50a50303100c125000f5062000440441421810003807026000c0f540c001f50500d200940400d603213901c40391141c00060000d071643c40d000a03407810701d90300b076252503980c03184815035810000f054090301107041c21103080f140d01503401a04440030003540b640340003904600c61b45001c844440000c1e00f0784900040b254002d200d00c1c1d11004068400c24a031078202002c2c40007032f010103488000300911000030b0b00040b488408030003000d54821f66480c9001d040045c100b10000501030f2420480c103030800402c00000780018 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 515496375 1250 515495125 515495143
    0x80d09061e0c0803102421020f0a050d1409061b090418050c040b13020310090c0507050c0604050a291c050109020708030c16050d2d02 59
    0x1c9940305088844211880a800c19004003a400040140a42c005030f100c040d1041e10201c0c41e079811564101d403022184002051210004580c50494280604840c0103009007020740c0400f0151800d4908440420189d01c10391156001034800700d11240c11107591f0240c4114058440641e41490a041c1e081c0380c3c80d030300d003e0000319480003031b061030490900400003551581c00d00184100710314109158105101c0300c00450071202da00503a408140c3da40740500c00c150b41c0703104c00344c4401408140003030248020750015100180c22001c043c0c3c0001c1000c141e0242c05126140d40d036030a074881c0380526020b4548074047c20824030807401404140155141c00035124100e54030581940d02c84840545003014142102054039050b8030002548038610300b081d01c8503c2041c0e008017007001240c1e42e42e6110422030040f040000c042002c01c00214440f418010090b203010495214020790010003903560364a01808070703100c40040707411000b10050054100703440c41200544070096403180381d52007000135103d03001c00d = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 515497625 1250 515496375 515496407
    0x3120a1709120306061309050403050408060708150f0f090a020405090a0501061209030c02130509150402030c0609130519050603010c170c0702150d11072f030a0c080d0906 75
    0x100305219200000079200c0d00908201f50308000034209400c0080160b0710a025403801032042e032020882d001d01c2540c105201d4600c10b081c5050b0f000040c410010300e4a02c0014856001d6101c150603d4540e1392070034414051280c04a0041e9598905414003180303020042492148903d044010440c0340e0b0040300b4154051030200001803420942c0c54180c0720002c0100010350800e01440c218644503c0c107600c41405542401704850f40600410181c2c0625042164001c0d0190845040c01301c90741014005048064801801600c2400b01020303a9421244129804408011950207541200119225a5030812400c1c0d0080c04125081080034040b00c4651407540d215080420014489030021815110a10b80c000d00d11003140002807070484850300910108180700e40780030100c0101c43c1e0400c1c102c42600d68480400400e160701084802c22441b1039040214251550a0f02031040f59002d00c07190640c64410000c030703030705103050005071450520407000c28828040c00345011300c40680c1008003440d07400c5078 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 515498875 1250 515497625 515497627
    0x906030902060c01020304240b03031c0b1903020a0501050702014104050406080d0c060c0504030804180f02040f0909020609040c020a1509030807050903120a170912030606 75
    0x6071000ca0058494030b41e200c011035101205000030000104c0310720316004243c0c541d00c2240050300340070364120340002113590340c903520401219007500c1c500814200100c1070300c1340001c1c4546020f0b011511141489004485001034800c0c240110310707003002164041c140070320700300c1c1c10410300f60b001900c480c1c070742e000c41e42c1804c11580e08004558003030468140500048068482c4082040501d20402c3d08903006a600c51818500081003220001035819010000c80d952400c0626564030b800c00200041c00120003082010030020020603090001080180020841403801040e21403031601120310391100c0041c01030040100b0869000c2003c01c0038103a40c0d50000005611442c1e1000a40520613001210381060030209a442040d40101e850818940036050104003018001c400c071040700c00100300103010072401c2e404a0404ca110780090a9404e401074200c8140e803240740595a03072508000801d00018104d01c0034420700c045285201500310071018020100300c692003040c1d41081c000102500d0140344 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 515500125 1250 515498875 515498891
    0x1505010e1c0c0b04090e060402011e0c0b01030b1f0602030927130309060315150c051b040b0613090207020a0f090c0e030607090308031815071e090603 66
    0x245031141d845540301d080c10110550310548144260098400c00b40b080d45080d03900c10409801003940c03440365505031750303000e116140e00900c24819140304900104210099a611000801000000c1c3c080e40c0074100215841c5010b070f5550305000142401c01240500503401004060340010540b0341848046a2143d4125000004524000b444202602081c84000140010317071043c460b000c1401c80c00f03a541c04000548648090701500c001000c246d0841c44410801c01c40c0030b400e00a000110071080ca00044035641030f886843c501f000c103000d00c3c02c152046480c03200651410780f1804200c00c00590300e4501700340b451005644150410321884904c40d40005a0f031003150f40e407600c5400038250100d0108130325512090900000c0000210020200b40061040c118038078001901300c1c1701e052a40c1d24040844c3c210340d910300c0d00d0340026000390107910342e040c0d9005c0c0145041c4400c0030001d13400301411003a131074111401845412880715407136031821403e42103242c1941c445260401e4510038200864808 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 515501375 1250 515500125 515500159
    0x3120519060306061e1409070c1a180a050615061314030601120b16030f0e060f010b030f070c0c0b03090c150f0405090a140108101505010e 61
    0x100e03504100d4904903140070008820095258801d505440b1140402d0100710f80041900e40c0c003400ca0300801c400c0300d2600d41018070620307101c200303950300a546251180741034003240e0352101c01c09054410092a50070315000c12070007000c0c1401d001180c9801c90001c1c1042d01031503d5403901d0300000f820881100d001043c3d6003c2d181c481c1c500719941d41c18452003140c001651001c00f038500c4500151018428001e02c400011000c80803481d0304c490b5500300580c80c4036900d40000301c40039815107410fa00185a100d15245040c80d245100c1c8400d0451501c026141c40d00c0c1070502c0c0c11015070140c009014018090042c000c4806400701100e5100540b403c011040030000d00301514400d429a02801d001040003007000002c80e004980140c1040c0107a91141e1881c080c078502c6801805180d0090001c413005000400c603501d41a0b403c50f81010303040b80d00059680780d400c5008840707a000d8024075003d5000b10840c1c92602524031451b0002c1138941c4641100e03c1c148400240461690b00302d9601c140a0f01312191000 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 515502625 1250 515501375 515501401
    0x30d0f051308030412030311090604050105030403030605040218030f0d09050d030909050124090302010e010c06090b070302090117040209180f0f0c0a050a030b0a05190c0c0b090a031205 81
    0xd80b10880840703403111394502d1800d41c4d4030303000901200041e0a04103201282c00301c0d0f40590b05c0324030004100c030341840d047c400112601d801c0100300358101526804002659281ca10042042042000005204000c040b0500d4034080d80c0103c5065154400c1c09080e103420390000303d0400756401203404401510b814101155400d5a641080c0c03401032410f40002036090902c0303441c2070400102c0c00b0003042011400c1d401d0710300015500c006808559400c04562083d13124112200c555803050200052000c001e480c2c20080510131243d20300482c0d13001410b42101c1d0380011104044100c191607110f4640f51a41c08113060f01340152807400180c50130b81074501c4c0c0c10bc0c1445036910002c2da04080324003a607050701485548840c6144902c0c001c200600000c5101d062544041c4141c98006c0500c0045881c0c1c02e200c03000030b20000304405280c020b0310f00c440081a02038004c011012106640b42410a99a81001c030041e010117003c001881c0d1240390110b002a401080240c035201e03041c44002a150784001040c092 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 515503875 1250 515502625 515502629
    0xc08030c0f0408010c081e0610050c07080307141603150b04020c03030f041707081b01020918010617010e040b070e04110c070e0609041704051518030d0f0513 69
    0x315500384171642140030f5101581c075205180040c89000040710480c4c800d80394100c2a0b035100d8100341c0845240d00d059018200400396070100c01c0c119461603540c0d0000c207046400080c0304907030540e1001c04066200000b00304050f2440031015002c81e0240c656520103120b00d081c1c201143c5540d03200c001004d190340e01c170b40c141c41e05040d001054940e28503020040b05c0002070212011698450a030602c84000268401510300c0a070380003074460302c1c1540d811070092042c50b41c080b40103020f6400300000495512280a00902e5000c02000020954109000501541d0000308110385c4801504010441540c640c8501a00540c010355040c41d5901c40e000e04440c482110003803030ba0400d04080e501a0030300e00900c001e061640580c2e060314549a1200d40c6180941001d80b52564440e40c06008100402c107081c4030300746546030103002c81c4d140a507610702040d0f9490341c05502511119000c19448442c100000c10782004850440243c0b025141000019200715113214843e130030800045a00c1c0702c00400e807800040 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 515505125 1250 515503875 515503889
    0x16030509150a08070302090d030806030c060c07061b030f0e0a0905010b040e090118120519120f050420040f1b0f0305040c03020d05150c190c08030c0f04 67
    0x2411070400305045400780d01000182d40010103200001e440c6520902c2a10302c8054014082c420348000c3d601d0454078880050f200e9a4180506020480142d494000a0440903100c9001c2c081b440c0c40c01201911124026005c0385c0385040030b021880c0000e511000c200c11504442c14801d041c0d403c400049081811650000a4510718040011038107082c0d07000035008030b50580c16242072a0b5110044c0300d00781e075804400100140341d840a0f00d0700254003c540420380c6421890300c607080080c480e070181305640ca0300c2c0e84180881e01e14030489a071050180900340501d88415414029030030640c1d00c0074070002d880c1002e00100084100d41d2030381d039034480c4c108d8030030403044240511504c481541e00c078401e10034820450700410f41d000311074040c403800303401002e2007203405c08070140b0014a95001c3c41240503150104072214003c805c080c0c01c001d15922607242c0250380911309284c44151040c100684158110300d40d40911200074624000501c598040700c0e40004520b10440d1140c5c0801c50b15020b600564120704 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 515506375 1250 515505125 515505139
    0xe0c0c01060603020c0d05040e011703070b01090b0a0b0c0616020c0a0315060e01031e031e0c030f0203090f040e0c0a06030207050105060405041101080403020f0709050f0a0e0316030509 81
    0x180ca03d40c140c018000c4121078105a5029002c040c0c000c1d105485503208003030f0034030300d0300c0010080443d02d41b1040d100c1110348030035a49098425513070300b545540309800410070140d42e1000a0303220300700440401d014006d0010040d00e0320100c8045650340701c10040c054066a80340e000c44002942c400e21000322184409403010b4496516803409030603004a001445880602e0a078000401206e1030940c5d03030403607070099103000b03108400246a06d80041e94540503410300c140e4240c0c0000c10020b1106c3c80c1c0021240d682d420392810054075004080c05124030112007150f00074483caa4442e503440490201d90302d000c80e8001155200e0030703211802d2230b1032006415440002040300054803034050f001801014403c8000308a696142001c10080f20000e43d4007a100050502e030181d0254041c00310315070040e00030b004851005241c2c1b0202c42c5040d42c83d80201302004d07240c90502884980248003079400c10341240060004542803a60203640b402244030b1003101c10311501c104814180108210b820300b4802500007 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 515507625 1250 515506375 515506379
    0x140d0b180a050303091011070609061506050c010b0906032e0c05031807061d0d05011a18060108040837080f0402061903021207110601080f070e0c0c0106 67
    0xe60f00c0e60000c41d10a50103000302d0042841c0780541c0e21400c1017415070a2401e5042004548420000700840c500480b9401e544030380301e54411640d0700790f00c0010085540d44581c0e9a00040e00182510500c805c01402014468240081950b0208400c3c502031400da140c02160210728003410740c0c082c2446010b000c21440c0a40740c0c1c482c0c5a00c9030007144100e8803110f440303050100902d01159261076511506002a1380741018004e000303c8030010700314101c40200920700904060310f44a01b1601500310148180c02064500c1c48070782800d0010000c0440e41150400341c61804c040064891580100000d104540005110000c01944440309907600400c0059100c0d0729036881c409002e60500403101c0c80800c4280300015208800704003800c1c820b541c0900000d0a14140d904a41800f05000c0403402c1410340a0145881c2c680f0b01c000e8031442029540e640b0f90b150081c2803410303070511206800402e0304c0d801402e0600800940091420200da14154640006695100e411003650055030323402c4d00294244440 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 515508875 1250 515507625 515507633
    0x40b0706230708010815060603060d02130506010e060f03070e0310090506040c080318010e12031201031a07080c091c05071505070f0b04020a0314010c09140d0b180a 72
    0x3507511840716500d0308209030b40c07501085681d40100c41042140710310244001081428814042c581110004e801c5040094150740000c4440450440802c0201e030794404016066030302c00380004e40400d0554081d823404005011008042c4002031185003407048050345601c0548041100303210340c41c40c5060030003001040f803038400d4a88000f9603007a10422941c06d004112900040101c40d0400099510880400407900044d114021203002c0ca503070108031860301c2c1202840a2009148002800d1400c203403540c114900703100d8100c901704400043c2c680e101c00b040310319900a010982c0082007006516180c1012a0000e000b0716082802400000e2208074064104640001e082040e610140c81c0c00381544071044044500303024806000c0d01c40c8410070060303c042410701310216000b90005d4440e080d021388030b494158402d1003002240c110760b0356689120f0702d0903500c544414050201d050342a0004c00c2440000303000708540e90400303800f20b90300c00041000c122441c080000c1403418030050380d00c13940785820 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 515510125 1250 515508875 515508941
    0xa080a0503071205121b041802090a06020105060d0605090313030b090c09060a031b050603011707080109030e040c1112041e05031509120708040303020c15040b0706 72
    0x320fa408440003038014807a4003500503a882040050703130301100303642c0c5c2c180403800860540105400d180700810000c110748141030030305031810b001c040000d683d80c0841030038003410b01140d900107811a40b40c0400d10040b0790312a10001c51194102e40c0c0412107489180c0010f007988a941400c091a20300140f000003044140d1002502c144055401d40700c0c070b0041001400890764044650355400212620b050000800842c200781a0441c0e00c04919586a10303803000c179860350f01c2038000e401040d0f0300c0080395980203420030500300540040c2c0001c4c012003090b50f90241a10b580018414404d54441110425045c80b40e1b10508100701c0b144101d8007080b400c0c100c0119107511030300410b0b030042e8500c8a4140c5031051314440300c00710f550150060850a00ca480c0c0fa042e1707241c02a0020086024005d030b19000000184040c1c14010b005440e195901c43c903500c0c0207860301826401580c00360702c4c110702082e152295401503e044842100c00e0720350300c0c0c0e40d0b441c020000703000040426244940a50078410411540c80c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 515511375 1250 515510125 515510137
    0xc040e041a1509190e0706181e030609081c020903010b0406150507050f150708090a11010f03060905010b0403030801050303031003020f3706030605010804060b0a080a0503 75
    0x1e8141050b848080c100b02484207400c5045070400076140c0401c111400c010781c0380e10031804440380060391609400c0c4c450700b00000c0b40d110700c0000319003a21003001e41082c0d0102d40f0007405455116091600b4007a040311400842e0704c80074006640e00e920f01000c1c404a00111aa54100001e00e22030301030110b0494802500144101c3d8025882c01180840310300301440340c84c0c10345000884240e40060243d034200d40c071758060003044035180100306210b00c2d01e5204124100011140d80d461005c1880c00103c010141040200708641c1076118605003004940540243c601d41c500030303e42290307a1004000c00303401804095004000480c03a00c0e00000303a440301d202c05002541e109a13515500d603640ca1301003590300e000c00e8821031590031202c082000107241c4015600d11280c13000c2c160f1114214a0310f000b01c0210300c0d4910503200c0140c1c4070055000c1200646a0002404160908201c1142031000080c50380b20000e00007031400e981c3d1240321001d03981c1c08003900020821241160549111841c6c102d8480d0420 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 515512625 1250 515511375 515511413
    0x1a01060207080a030c020904020616060207020f04090f060510180e010509060f011202030c040f1407050a20011808040617151c051006140406030302030906030c040e04 73
    0x1100011642d0381c804100e00c0d10850301562540c1140c2007036020448000e80190089078403030010001c45003a641c1c2020035003038840c050300005896052600611100e41c01051030203125238a0b11b071a40002030300300702c040345250740c00c0070780014141d460407407512410500b9080701e55003003c86070300c552680d0543d82040c81440301100c0207201d582c8a5140c0c081d0788941c10345002e056aa00070005002e03d81468664180441c0003c0c12650341101c40408a0201d03050031103031608182e201c10312011065942c0c0103107904a0020328041b8501507040d10010318015041c08005e40460030004c82c6006413409400105012452a44c9202000a2458243c440341e01503c00c000c045101002d0141110b80030a00741d6210b1200c503000c180b0115600410021200121800c40b085010149200f03c007162041152a85c03811000c0000941d0508120001040c124608940c500c15805e02c2030903c0000d9011064803030f20390040d02d01c1500c98840d01c0c405162030259401c19904114900100420300c50304a102159610702 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 515513875 1250 515512625 515512633
    0xf151214010506090712060915030b06090105060d02070204060b2a16090b061b0705130e0703060504050f0303040b0106030506010203070c0e07180b041401020703050c010503070c1a010602 82
    0x1445400500ba502d0490b8402c1d805038620700042c642c5070003002c000700e91001c00301d00001e0035074549500c03400b110256084c2200344024842c0601c20004103085242e00240b08440196666150500058003440354407008031180d80c01142c248210740701c54114001408803050741e503844402a80c04a1448861207040d01c0ba141009000142c202c10b000c100204000c600002c0050080d042062500261000521040e081002082076003441c000c00e192035440c8410b501c0103801c0c502c1c0760004000c0e0400507480414140f625014229804203000148201100d038800000b02e8030b80d50300d050240c1814100c0455100701c2c0400000c2104101982300c1c1c0c103059503c144c908001e59261040121303074a00030307000d0007010204082c03014080b144c14030741c0c26940705445140000d110814945480300c0c050b02d940c003c9484210114003840b003500b500248491b00e420030b100600940749035444a40d61100d140b00c4c01410700c540000890560342c858031004600742c1e0883c1c4450a40700420080421240e400d220b18401401 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 515515125 1250 515513875 515513903
    0x3030f0709080703030819090c0f09020a05070f03020a0203030c010f1b050304060b0f0d0305180405161407021f02070b0301263d06180f1512 62
    0x1c080c903194002e6554540040010505613a42502d2102c03001c0c0c0034803000040e1818040d550b02039030080400300e5104940c3c003140e162400c115080c1c04400303a00120f20071801880318030a02c0d6071103405c1d50441c68101104502c95600b5040683c1848520700b000394041c04000399410304c10f4415003009840c3c1e04403240c1040545021005c1c844400320079812000003d00810128010901540040b084400001c1c07001340b2885101d80040c028080c000310841c04200023140d41c00c030b4028541d2404409640994040c07200345010203141c03600b4113420001d070003408529603145d10f800502101703481d40300d9809005241d007003101c50101551402c81c1c0c01c0d0000144a0500041409452501620b04071101e000e40c0110300e03004d0f0200510340c0030440a5140307451082c207099071050056a400f01c800c04032034801310030040080c103007212120005110340c03000752402c105040109a1389204c6095015104550010780741c018020f0701e8018010b515042140c83c4035540d00071030b500c240510702c21892849a600e0000c060 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 515516375 1250 515515125 515515127
    0x60f120f0c0b280801050d2a08100f380d140d110615031006030605160201020c0a1e0609050106181503020f06040b040e330609060f0c03030f07 63
    0x600c0034014550041c15440001d0300203a00c00b80f95010031416042c10134226003180040d49224230305540542a6580304000428103500c05205c0c4218034041020180402701903c051020f12840200c4440c078030211185040c00da442800809808001d401010301c01c201c207290500d0100c100ba0000440e105001f49204482010b004003914200191700740003921803035545202d4481000c5400b580c290309401101901c001c00140751183c02d000d18860740e000111410034500003c514002c811b040d40075603104009401e042c80b400100840d030303164011046c4020310220000da800c4000c81c400700400460820b80854200201900080180d480454039011411720f55003900090340d07000e0103407000035000081d0334405802c1050030342c15141000381c1124900740c0d440d40d00e41035690141d4000e03031654007807806101041010300280d44d14184410075840906106039140480502d800032860f01c070320f000081240c0c4a84a82d01035500e201d1031b0a0820752609106001543c807584211440842050110001b400c4a = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 515517625 1250 515516375 515516387
    0x270c0b070c210c030212010605130e160f0e06280e1e0402060c010209090709030201080609010806190605100309150903050f0a050d060315060f120f0c0b28 68
    0xb0341d81144030445000c1c03854007801121802c40c10507000554070303400085002c0c0c9400d00b010f104091008000181c05280c21102130820929011714107078008054001c101e480c00d284410b80607101c0b40100340034103482c1e41d00010b4000e0009850145160134030005050800b2265140104550415800601d1651418010341205812a035441e850000c81c1c4040b60141c1460400350020301441d43c00186007072100b0001420304032044800300b0006a01a40c28421944e20011068100105440201065051120054641c6402031006421924011401c241c20003a500301c0802008050804005c0740b12482c0f005001e0300603018243c42414044841000301e0b010707407061880080c2c060703480038101140c001c1c803201e00b0390040050078204201070280280c0d4103402c0c4204070096106804240200c031484c0e102c038090b1602984201c040c6880c5110400102200c401c104440580c80407041c6090711040c0350100a03168143c001160200c03000c20100d804c0344d10174003002045111042d0004000380301700c40490300 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 515518875 1250 515517625 515517689
    0x7120303140714161703091605041802011110020a030b040e0a1106180306180d0e1f09031703040507090618020313120206061201270c0b070c 62
    0x140d404104030114070301c400101480c0849102d000c0121030094031102c410811b40084d50300c581c1c0c6403c458070050401c45607408003402001c054800f400715214606212400304103043c0701030305100a02c408072044040c00e00101f10000b24214007151a0102d4020060040014042c00b50159143c031580c81440b103000100f02d00c06980c0300c0c10301d480c1d20080005000d0070b0f0700a8411400010318a0b00310440b190b809000031482510300080402d01040c1a0440a25203929229140103001c0b02c104003480070740300c9100840030020092000e1002d081c61007000c86440240c1d9002a1416500c1281d05a01010960003107005900404c100c070b00e543d440320110b1f000c484140c8196200398201e546090440c01140d0080c41d401034000719010f0b00c0c11196181e000186c1c00310251880107800c140d0070440c0b649050081d03072000e0311a25000700b00784940700c0103924001000000015855161141c00c44c01c00400b540c0000182c07562a44040d200e940e0303803410400c0c06282d0702842c0c0916103a085513500c1c01c5200c902c82d4038 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 515520125 1250 515518875 515518907
    0xc0507060e061605010f0506011707030c0e030a0f1403030c03010e0402011101020c070f0f1a2802060108120307020a02131b090915030201020604080a02071203031407 73
    0x68440e15144041da04030786803000180e0030031001d11a4050b0b0181465802081c0760180f0008074081a604c00c1c03110480e1001050103051050744d01c50000c01111080c05d0a43c060150300740021500000030007038500700324000306694103105110390b0504211300d81e40d0408006220f50007621204d451180c246461340000c84414207004410320040020921514105810900604201a500f691404078900f684e100c3c154080160f44048001c0090f551f81c540740701c006000c009510071500e0b0528070003658480100e24102450f00c004a40c4411240318a5411030611f007403030b1842d003850520a00040d441c0c80c001d104a030064040c1c0041303030390300c0d08400e42124421080c5a0140c002007210b6800c01c054101d14030042a1070590b40c59110120b542c0011080c44142d00c0c584500021b186001c01e07000641d0f851502d0400c0b103030703d10001000180d80000d03d084e04075500c407038030700e03203070910004200d2030683c595120070310007094010088180344e09640002040308080d10250215601d800003038034541c2039403100701 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 515521375 1250 515520125 515520133
    0x212060c03130201140f030709050402040b0406141b0a0b060603101205010905010c02330402270103060b030d0801060503130303110a030608060106020c1806032a010f0c05 75
    0x4102010301d080200c02c01e84141400c40c0115061007a40403a0780001e941000780325000018071800a80001c4104003c02c1c04650a40c80d045c24142080458011486444140702c40b0400c0140031342175041c1038a03080542d00d00080b01c0c12682c01c500c55900c8048020035502c031200b072030104100b401e203034046030b20034411614901d1a2234501390704201100320b8071005656655964621000040007801001c0307040c422035000b08000881ca4444030b03842509a00d1b510104451403c248800e41c614100a03030740581c0464203005000050002412091001c0d0528542140042d00100400006600c10500c044081d8112850001c1c10001600d582c4800c3c018003020450900004040798085500b5001583c03180c90007050030081c01e0346060079900140b1a40c4003290719880b0070b004401041105a0040640b44001c00c2c07001c640e9004a102020381c0a84051000b904070b0000e4402c3d101000144190130f88106a00c1e1403d81e010881c0201d0700d1915001800500c4030b103e60f0095901c1100c05c0c0c46802c3d00103020b0 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 515522625 1250 515521375 515521381
    0x6040b07081c090f11060c070e060307120c09050403170103050304030606090507140a0201020c16050415060530040308060a08030f090f0d170301080709020a170901060506070f0212060c03 82
    0x401d4902e145d502e00c5988030404000e1503903001f2045c042c1e00e00809070f91b0400922420300a08050600e81640c20034041040f114080001203011415001c0481c0c001c0080002c00d9141c0b42021118815041405041060004000002c0140c0040100101c7e4001d02e02009200e440c1d00b04401519025604a00024494140511542507110050100c1d0140380001403926568403c0716081c070581e1040d0b035903000701002c02044103080078000d550000203040c01ea0704505003070580c054060f005001a800840880c1c90311100f0101000810340c8914031980b54035140b500e000d00c0c004006000440e0001e00a07401d400c030000d510000017050ba0b05d1114440301c040d0501c100740003841a0b001c840c042c4140e00c07101d00e00403100840c2100903415500a8010f21290b565030401c030260346040c2d030588c400e4101910402c50104100d80c81031184403021244544e12810740c803100211400740000c1c1e0403140d400580040c000c42000042e1080e513800303500c2943c04200b0b00219150482d03c2c1c000031034421042c20350030000 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 515523875 1250 515522625 515522633
    0x40317092a030c0f010909060303090801110316050a120f1a0f1e03211b0a17070501110d0f110307090509040c03050d0305010905061009090b06040b07081c090f 70
    0x48070f04c0902e418549003408994881c0f00b1411745071564410303408100350040c20f00030503000f8003520300404400c034003652950034803441a003844142114204100320000c1510512074ac07050301c0c048141c049444092010f6020120910018090f03449a20340000c501403000030a400c1c55900062000303001040c0071040070b141c0306100044201d802c0044c0c0d00d801010540e0b590700c11620109040171004115464940011480c0b050210040141049240d0721607100400020886445c1400040140d65115115015864106c0c050642c0c0e503070350003018801140b001700d40c03910b81e4000301810090507428401c14844404540d0725110035103e440001e00754046c24011401d0118415400a20903503484c81559565161581807803580792022000039155001080400703200c1c083c480d00144100c4602d4416124080094000d24441c4250782e440c03900da00003d00c803a61000c059600030054241c4cbc881e9564404d203041c100a80c0300c0d05000039010b02203071440124004071f200d161070056200000c400c0401140c0c41d = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 515525125 1250 515523875 515523889
    0x306010c0c120b01170f0d0302070602120c09180906070f090b03010b0d05181b0307120606080708030304050a02061813060501140a1205040317092a030c 67
    0xa07988441101800038124120300c0b80000443c0c00754401060a505043d0b050400020a000340300030742e405142c1402c91040081380031090b88806003001079131b484c2c0c1441e10002074054801d8101070080c1013402c010114007494018902002c04035503044580110740c00c5550060380c192420801e55020200040207140982910b85086202d03040440790b107070b912458202198801d0704000411000460103c0f0003030510f02a80760030840a60f042a0408400c0040551751404050502040c15861b140000e2070348045c420312000e0302010002803203001243c05c0c480c2c003510462050005921a400c0300188250010042d6809036501c480903206040603034081042035008800154148501480b1619095841c03034804941c80b180200c002c580d40b40380000162101030b00c06402d00c030b64207041100c11480c03a409044484078107504400000c12751a20704040b036449600d0300365031034032000e59824803840540c0022a2070510544c00281c1801c21088003080d16024048901140c0661100c4240200e500c1c14207 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 515526375 1250 515525125 515525147
    0x1151404021207020c1905030c15250b010f0305030f0304210c060f050118020c0307020d030207081902010c24180c0e040f02090406020903100b100f0203030601 70
    0x90001d814962481d4070480c00410544040001d68003000f021006414040a00040d0070003850708020b9651130200400e889500c00c00580b8408c0c4e181d003551580030703c62801038603a44550480c21206201600001c100d0740000b00c6401e481012084000081c00000d008000d41903e920002443c00c041c2140c8404401e5080940f08036040032100c500e00186403d03880704500a80507958075440c2051003824820104c0380c1c1c0e1000c1d50409400d02006005400c4081c1600c1a40080f130030700181d03a460307400c01c5141540220310000794044c0d0341080c0602071607400a0040240d40c0030b070003500c0700103c40303181d00e5404541c8504000d002c42c40c0c00400401080300383e000e54032444207442103a031240c1d6018600104842507551400c420b08040210b4a00340240181d43e94044c12910303a0550003401d01c0d44031801040c00244000307100d400b0301000181040150b405440b04d42e6000340c00c5036521031000a515015240507114036019010300e0381c0900c25148540c0c0c40d1400400c2540145181da203070900111040b880c94 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 515527625 1250 515526375 515526379
    0x10050f0306010b070b040c0e0f1e0c0a05070204320c2503020c0a090e010b01080105180702100609020a0806100903060e031b010510080703030203040b07020a180f050603011514 77
    0x14036000a100369507180d124401d9400740142031071490070ac2900d032103080c020000d0b03000c240300d0701d000c100c400e030751280c111141c0c0080d509140f502c495042c400100030740240403189101183c1e5803010681e410fa001c00b00b0104104184c0d83c0309450307503000c1c0201220f0084130302e030a2410700480c0314904418419100115410f0084c410784684165039008140014601d900410100e0f03507940081d05510703004e12514581a400b4607003100d087d49004c00080302c01c0310800702180381200000105036581e00802004082e00b001000c1441002d070384002c2c40c8025040034860101160a000000b002460721040720903410703110b92030b07a0310b400e0b045880e003000501c040b0040e00041d210400c8514100c1440b0055048414204800840c3e1454561020092540783e40c1c0242c40641c012034007400000c2d0007206803400d40703200c580240d480c0c609a0000901c01e114a601080c20b8100c850340540c0004925004103240801091061220341c03541c0702810b00700d43d9207030040756030b0f2900940180a01815000111428140 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 515528875 1250 515527625 515527643
    0x3030b01081504090623061e01390309080606060a200304080a060f11040501020703110105040302060d0c1d030a150b040516080c13050d0302010603080310050f0306010b070b04 77
    0x403903075006c002d400080c80c2c400c0074582004242c0c40c0442c10708003c03002e1860310f004210140c034006060502039080c800060040d00854109070011581c9031008090007400e40c12400311a070401409236065400394803103d0007a0000a10b10381004d030f04035104445d1b955114654180444200410794048100c40b0701070b80820030001a101904012020007a07001c0e101c0002c14502150b01c500840d516140d03564503a0b8001c0c042007145a8011030004200c0350070080e1010101c0d08040100d84910883d08020350155010483c014042c0c6103178030114103c074480d11016511100c00d00400401c0c01315a0304254982d019907103c0000513020038003620300030407a000104003107040700300042c181c4004441d80c0d5440c811640f0300c41c000c01d44c8039001d160040b2802e81c3c0a03181ca040920311001544640c02654010260342030401c003050301c05d6002c1c000035900a40e40d00d03201d08020700c10706a41c04c4a4482e50340300e10f20918103403034145400300f5507604032440348840034545003499503005920755005005881d01e1003 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 515530125 1250 515528875 515528891
    0x60e011a0d140709020409050610020c0d0c120b0702010b0d02130c0c0602040b090102070905151e091f0b0c07030303050c07050102030705120a0b151b031603030b010815040906 77
    0x100410020014002132840540c444d4185146101140c00080007107210300400755501502507000309020003408010f40d001841d255140c205001800030541c0050442441000030b0010700602d01641402140f05500920075280c443d0f0030048800c410b45800382d440841c000380ca203840b030f007540c0c410710305400c440c10306800c5003205889060490700640c0c0213100b8200005060445503905008607000780420f030100700414140030b8000d4407840080c280c01c03405003c2002e1b401c2d010300d9070b100300b18448101c000c00c031601d50b1038404942c003140c03060150100a0030b02006004034403200030ba0160389a0000c958000e20100b13155442c00c0300602006030461809140401c40c82020030803c0c0011845000943c980603610b0314409680800814014141007640380360410030710095846c81d00d010000c619249009880d00b003441c2d2501060082e901e24050710b84000644d005e4050b1400c5069030302c1c81d0080d01c1c00c00480d20030340d0054406140c101e8001c00b20160410a28400f854250301c0104124044c1d000091804 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 515531375 1250 515530125 515530163
    0x9060a080f100f090c1e0906030521030106080f070e06071202300a0e0d0318090612030e03030c0708010e0c12060721051306050114010e1c05011107060e011a0d 70
    0x230796030350000e90782c0307401a04a5503205040480b030bc80780212910310782441d43d0f2401400404400010f40301180c0d5100050201e500c031486034003d10000c400040140380e880305103140075003400b0306100c901c8025000e194905240f1441e0100c44840c41038004100412400744c2054081440e800080d1a600348510444401c0c1140c1b900c0c2d500a2003036100342c8905074086020b0b1800003448156074042804181000400e1054648803590009420791508001010910480000342180100c0118050501c6095030009413000305402c2214110700041c00d9405c10740c180400e02105a0940c58440c00a90141000c203900a20078404001e8820040500300c10035201a841001640c40550303142450441180e0700c02c0c00c4c0300e007900c1a1070061041ca000b180f002500350300040c0410820041103481000d01140b00340c0c0170050303079038103401099001c8002c1001843d28446690307a500001d0095510078034180041c80f14010510420844d4002000c0c058070b004280d404001c1c2e843c1019504807604030035080c01031085 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 515532625 1250 515531375 515531381
    0x1112130b011e0905010b070818061812011506110304090c120f0605090c0703050c3007031e030e060a0e0d02120909060a080f100f090c1e09 61
    0x280000825803541c1d400c0c15140001d062480d030300721405903803031310004021000851080b82d07800ca9100d41c62607240c201d07941d2540e2100d034805150703681000c0d0004d1600d180201d502807407005a101100c400340400d540d401150300f2100e0004420b0140c01c0b0f00340c400c1c40114018044007070000b80c840c0407289025142c0721a0303c02d8030100c1d014030021403100301030b5075040b28840c010f00d002c1502420007048518034002c005038004da4081d0540d0b4103114001180428544108100e82c5841000421a510603070014901e141d882c2c8045003420010400f100042c040210031000c031080d25405680d40c0e0240c951121107507142421030300300c5070181581c90f50798440074082840110320038190f210002915907500d600082c00c08a54a01150464100140620b58034046c04180c130070404064440d03200941d81e1101145080d61170707800c64602849400800c4801d6800000c12007514080d03007000740400d1000c0b0b1004002d40e8803c180081005000c0701c000c0c0310f540381000ca64000f100c03d090011440564426a920031 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 515533875 1250 515532625 515532629
    0x9120b060f0307120818090f0c090109051906020d0801030503030c18090a06030302060601210c05071401061d0403020a0f03020715050405150903060411010306050a0b1c1112130b01 79
    0x8500000304141842e0a44002590842c8109a445180e0361508e8500c5a0f0001801405070040712404030b03c0e100280d10611044004c5d180140504819040000304604551050f2180714018402d24202205141c4510000c2d8100c80e8270174021030a688403401c00700100d4121b105540000440c40da44d484d065502c15250034001e2000b4140003035110304500700207040000080c040350502500c0f44401d411055032000840084540d100e0002d1680012321040b9110701c523061020344224181102c104090006611020458084d09440420b80150081001c010300d01100c0c09005600400541004a80c07000f82c4070a2103846032054036207068403010807620030502107600341d0003d000401e003400176003804040c4a41c9003031301c020024203060200c03000075a80c51009000034190300d14096075142590280d000030019040080a008545482c3c01840c0d90075080110440030011a9200b00305004034140308100100144c03901c064501441490303440b40e850300240c00c20031024000c11800011400240f11980 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 515535125 1250 515533875 515533883
    0x21906050603070602010209030705010c081201061101420e07020c09060409020307050112060902030a050405010c0c170f0c01090f020306070801080c091905010306060609120b060f030712 82
    0x1141e080c184140b51808001c1d42050b802e5a00c1000b039041c0507600020810100d1303009107400000300341e0f5850240d2540c0180071141001d9a07201002043d6203400082c0f0841e01c191030f41c000c101064841101c084410200810483d407005000d001081c416408500030124407071060b403c01c8110b03980c0071120074540088420300b0041c0c001c44500070142c40d222003810780101c0200c8043c025415140c0003c0c4c3c442069228150600400380740c0b0384070000792500054014026041c00715103c0c40c1541040024007411502101eaa528154050301d08501810070846410b07004207000b0b074682416030504419902610303000d03800302c0c0d007440f0a0116034001d004102c42d4038450a01c8504286c118030500d460114007030300c0c4006011003180140048400081c0125081c60704941c0340743c258803401011070785a03404404090200e42058004414807545810040c122012641e40e880081d1769080000c0d580201510020160012000460450314210002c4013034040f0003406e8079400d540e900c401420710071302d03120215 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 515536375 1250 515535125 515535131
    0x8040305070b0903070525141806030a050d0c110405070210050604021b0a060b0607150f14040c080d1d0409111e09010e090307060e120a0c05010e0106061e021906 71
    0x4468a541120440002c1400c400b065023640307109400075441a1904c0100c071082000306000802a503020081d02c5041c0350840e051f41e86c2003440c810300a0900b0100304c01525003130300154000426050510609204100e15409000441101400c4d000500000b0344031641c81f94080c0014100c80250154140c1e0080b10342008002101d8107107400000d03110300848143c4129014000400807031700c101041766030b16030403150001d220029010100020155890000540d0003c40200702c10402900c0060040e039400030103c2d941c400b0717048030842c0c4130440c2402c1e40d1528403400c1040c151504058101804585c03140001a82d50f000f1580071580c201485158a5411b40032500510510700700401100e0141026a201d41254902804225981c0c400c0b4807004064680d15205100310103000c2c0304104100c0e03040d070103842d80d801410f00018400b840d1807a0580c1c80e9442d0500c4450700c20030500c07418040300c840d0f031940d80603044041720340714005400300e1020301503010340c1c090034070604486104800c00d240700304000 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 515537625 1250 515536375 515536423
    0x18012f07050a051804030806061603030b09060405090a03080405030d050c07031206050a051201140c0901080907030b010501211b3b0307150302031608040305070b09030705 75
    0x81242e00b1668003007805905915036425204035490200d641c81505401d20750029214000420000d2054114011f4501a11000c003010558190819103003e013040710300c50426140e6100b080102e580075512a40d9980c400118000000c2c09040e41c4c0d03900074054001e50342050b640062070000e0768401c44407400348800015510f810903410040c4041c0760900140c00700320040c200004903800c42c400c0c1c06040e11a1412207130b410104207094111510280d8003041e0b030800d07401c140e6848860f582080705001d01003980d0f0000a000c1040003c6c0450031070f43c0100c002c40503640703404010346100082c0080c941d010320100090090181c0346019101e0746140c0880d0f90036031031040d010020b02522400310107081d280c1501d105040c0381901b14034a034400702184550080c120801d50000382c0350404030350151014050b01d502c240c080d107405901940c40380032030b10041c241c0860740200466040308202d8009022500c144400400701e80c44d001180c4d0300800140480e0300e0520140c4601e46444000000d00003510a0000d00b = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 515538875 1250 515537625 515537629
    0x114010309050c03160f090e150c07060e010b04180b0a02070312060305030d050108060601080403030b0406030b1005040c0503040b070e0d05150414030702150307170a0209030601050618012f0705 85
    0x7820010100b8840400c00002005503231a16804145003c1c28080c5d40380c800300b486041582e080b90503056008200304221340b00b100d20786000e061200d515074815480e0a2115010160065058808980c01040c039110f0741d49081040e07000390481b10b000d03403c00c4a05c68103030001070705512074070011318000c40095440302c0149005506a6030140c10844443c0c0084050025a98026001682095050901103246211480454003d007441e45c000303800519400d040c0140c589040d441d00c411b4a030141c4040c0300c500d50b02c000c02d550358401030b1402420018071900048603103105520040e049540100040714030410b0703803140340c0303411001c0f0884503281c2003010038070040082b2007441d2090000c0d0340014505105554001a04036030800792410350603100040003800700b44c4920308080d81031010803600d6104d0b0a11544106c004e41000c80054041d1003004008960f600e040d1055801a001900b4140c1d00300700c00500442d60031483e495081034840c41c4600324490003075101030800c00d80501d0f0004258461410b81 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 515540125 1250 515538875 515538899
    0x1d060a14070f0b0604020406021509010e01021308070b030402011409030106030c0b0c15060105040e190c0c0c05090606090d0f05120d150308030f130215120f0114010309050c0316 78
    0xc580d9201c5e604c100820000240c02280c01c1c1c0e0354084404911055a645005280c00b6003051120f20700294030025000448c01c0800002d6015a004c040c00c0fa8075480c0c4810715440a44005d40700640032410048102140c148901c000700146140a070020992559a540342c000d500102d402c01d81902070080713490010110b0420250903451141260840f260508000181c203900c220301030f0000891940300003070103224042d812540130051428041281c00003038403006020345a408801c4941c0703c8030070ba000a8910308040703502c1c02400010312061400c0d10360b0080009078008040200d0360300c85400c0030840801e906004200d201540e01c103205a44100f00e2019908032804080d0560070170400b880d05002003112141640d43c00f5048010594554444c2d5041c0c810040c91568000d600c040c0c0740c000003601d08007040140c14a110020030340700c6c03103865542050260742005d0007203000c0d00010020304550f96201c0d42051003400d002320217862600003106c02003414080806c00c202c50501045108020803050030f1 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 515541375 1250 515540125 515540131
    0x150406060e060a261507090f080102120703090f1b1e0315020c070305060c0d0c0c020f01120b040203010905010e01060c080a26040309151d060a14070f0b 67
    0x10743c0112a0780c00c10748003002001c003008801003502001072001428180c00c015260341c412140501c0c2d180e604e0004001400130003a0701840f212003103143d600280e1010f050094500da4070701360090546a036101c0702c00310000d024040c02a525440040d1001c4082030350030142c4a904902c048102c20503504001000d4031810540e034021039180d05a40041011072005240c41c203640700c2ca21f0000da5030b00c815203d01d91402440390000f91481c0114010300c40e00a1600c8010414181e80354000d000300382205000359000003407504041d4100d100c021402c00079600c00c1c1d101c040042d07c0a07400207144a40034000c030b8101d80090300002200780c0c1c0d450040c0582e0a0100d800790060400c6d1424280b4400e1580c0c0342c41a600030002010144184844060105112940e803000d680f0720f1450300700c0c110300d42801c00810717808861140791420f00707001d1041c0c41e0442c130590320480382e42d1106000c00e0410001c9014803d8503402024148200000580304a904640c503100074001039000d01a0380340c59400fa41807040504c3c20107 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 515542625 1250 515541375 515541379
    0x30e070803031302120316030207140102060406150803070804031401022d04030b0901020a0806030d090e0a0213060c0c05010305160c021f170f091e150406060e06 71
    0x45020003102034000200d9510041006119207040001d1010507403044000603648503e00010401414044e40710785210003d501079400c8070046540c880c103840700c044010081d980181c1002c1d00007404a249a0090040040b00d45294200b96580750640390554100800889142c0030000d020018815400c550107207890111000b1440c00c0c40c20710141c1003096052200403070a0050a04404071440048250341c000e40e0005c140f010b980ca0900c1086001b9808502018041040d80c80800d00c14180042c0030315407105d00b80c844007252030a214801c1000d00d4000e000902154080003540300030340d400d03204100140078548408162050700d251020a004032500030904051910041000840181e21040300c90700241c113046484001e40e0002c40c40c1c14601c0c9000040250b20302482d0381840d548580d0081800f500380718080d01c1c50b00c07452034400b2040801d84200da901d601240d003042c0a80c6200070200803600c0010105c03420381c1c041c0e40f6035900d550130031a800c4e510542d50300420028101c401d1600ca60100f81 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 515543875 1250 515542625 515542633
    0x140111060709081c090513020720030d090513090606080a0b01080d11030406080703090b0c0c010c17040b0c041a0316020c090703020a12051501020c10080c0702060d050a0b01030e 78
    0x4d800c005000b1006881001c4c407170180d260b0581203800d400d504030745c02c00f45c210035403800d26615456030006903500404400d000380300300c40381c8009452180c807040301600d4000b8030240c00c0f0b420300c09203070300945032814041e107407180da0f13803c0011482410007004841038403420343e021702580340c02a03031810801401d00c10f500340305107503901c001141404411101521040c0c180500380c0d4454001c01c800505030000001c18803103445040c1304117425244040c00b15010340000a101c49880e030f0b501146c44844110200b1a0704d40e020010030002201d00701c0040d4021300390180f0909065481810b501c0c4001c2803459511045400020301194400c102c0d0b110b5032003081c60000f0200c100b009008101c1c1900002d200600b00341d80411a23191640c0316918001c1c2014021074140201e003000c00b041c1703078461180c111300340c003501c91307004d8442d040d00300204803462565090300d9013012503807580e0b6411003660000104a074880030400c00810381601c2c1d0b108850092041c0c40c030000d008005200007400310380b281c800d51a00f0b588 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 515545125 1250 515543875 515543923
    0xb060316032919050703020f130515040e0402060a0e0303030726010b0703080604021c020c0610031a0405190303050f06041a040f0207060216210914011106070908 71
    0x45004903c4410340901c0b50000703075a038440d641200203020f85c65000d01c00740000545000d00c100001800c80a0310710851354600540c0d02d000b8680d41038400ca104194035900c1e001e0020b000351400002500380082c450a110500bc502c00d000079080d5441110700b00041264a24140415680c00b00c0f00100480410490f0590754100f58031121140074120009080001520003d400c81c0c1b1036406075070f0003407034007140c0d182441c603620300801c06500004441010391040b000010004803100c000350084039040142c0000a1464000d8001d036080003c0013640c00d44548403a01010031003062071004035a0090340c00003600d003001b00d0304040940014001a1060f4180390f011404007913004102501d00c00c04950000b0b041c1c1c0348419400203030003440000b8042c00e1021942180c00b41c0102e107550b20f01d600c180c0d944281210181c0c01403404c201900ba882000490b42038060041000c1e040311000c50040504100f8180d0f00000e1400c6e2408800300c83c2c1100240208008101405d4108003992041150105a00d0511 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 515546375 1250 515545125 515545141
    0x16121704021003090b0a0f140c0a140708040b0304050d0c20010c060e0d080c040b07060902060904090809010f0509100804020607120e1e01020a0b0603160329 69
    0x2500241010748100074000500c0072842c003e9019184450f840310302c1012615281100c0e00003803240052220340a0f05140256144224025000d441544d2008140e420506a44402c48951017000e4440e5140d000030000040403503010380187c0300506500741e150344c0e41e2811340340007401c1ca9120785940e4140444101c01000207055140184403104143c1030f040540541c1a004a420481c4150084c1107107140c1349401402640c040b5481d136012141d9261035081340c5454041c0205481a44902c400185050116070b0000350141c1045103400c4c00180180d041030201c100042c1161940f541c00c594540001510038511358002c8000c20303d031401420110308116110002ca951194020210810030154170001821940c2e480c0075a14000d8120081c0000000d2856010b0042070280d10410b200d0000240c641b0061007006568106006040e409030039110704a544a0344502c601802280d4075000c0c0b2180d09407407007100c00070b00b401140540a89411240601084803c5141e24116241c0c80b242c0749080000340c0e = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 515547625 1250 515546375 515546417
    0x13020909010b1c0e010e06060108010b031b0d0c020f251a1903050702100203070e01081911030a05010f030206030f040213060b072a0515040801021612 66
    0x540001e50420394410f0002c0400c031034a03010089219005140090882c3c800505511000c001d001031012035200d03803580c00055400390f0302446070030400c41c0c04200089081c1030b2121129400703032004024a0038011052211019202c842a030480164042d80d40308454500c200076403810350784000841c0002c40680c031340f441502c1c4900d014115416940480e1001070614480840d80305880c01c0c05042c0d10485e8034440100030780300507202100140b1812001408070708451088030b025030400d80310450a4050380300151344078500104907207184103a42a0584056119004903013800c1880c12443c0d47d03914089000c001210410b811110301400100000e10068807018200c030b03000081e1031321043d41d59446100041101c0f0a5820a400c298207121002401c0d10070321000c1d080340352044840b481c56428480200d0354982c00c294210240540340c4a04208605240c0780b1321880ca04070980417450280c40d800340c40e00366806600c0030207902c9042c002c3c200c10b1021707205c005139000b40d280c0360001e55480400007a14034 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 515548875 1250 515547625 515547629
    0x209060a030e030f13030c06020105070e040509070b03100e01080d09030206160f03030203090f012d09120804020111030a0c060b060904090b15030c06070b09030f070602091302090901 80
    0x18036540c1c09605500c4031041080d10104c1c001c07181100e513514806060299403020511040320080508030307011134203500600802d4402c200720303650410400006002c1002070300010306510960700448001045241042c80114032a4039132141040001c0c0c90706641c020042c205074441e403081d80120355100896617006464400300c81e0121038250f1181c0e81c0912510802e007010303c004211075a402e254008050301600518800d41d14081601d4603900448501802d0302c1e0a02d0740858603a495a0311402c003002c2508880c401c01400880000e01d2840641d11a54902c101c800704102255525040000310344e40308058082c0c4070846c10141d030800d54402c0c0050070030706848030010a0700340c0701e8429201a03100c1d4020394818881c0280f041c0001100ea0410064008040e03a0041c61f4034070795161000740d07007400503e0796400301c4060956440e0441c071b929026000000542000c17550301040040458050b0f0103006007103464020080183e81e006900f0402ca1940024651291402c2c018091844595540007107581 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 515550125 1250 515548875 515548877
    0x20a0603020309250e0604020705060f0a0e0a0605161d0607020409050115060e0303040e181903110607080f0a1d0307061401050906060f0a09031a1006030209060a 71
    0xb803207032a80450541400e03800d0340c40704041e03041910005040051101c400702210310811041d5619121b00003030000741c1c0304040e03016219a00000228188109541c00300b82d20a00c40c00c030000796071862616007400d0100d00e0b041030b03030390f40e4686003030000141c07544606002d410420304104003600d410400000780c20220710f00461084d00301240c0c0405548407504200001c9034030900800601c102c00c100c209040e000c40c0607810020b00301e01c100e107406041c00001c0f18144c07294000461074540d03035604003840203c3e4200c658074660284406541411541002c031100c0c203407003510b50f100c5807101811a14039112006003d0f008004001c000e10069442d41c00100382c012983c41000b180611101c0020f042294001849030101d11002038a0303010b10080794800c0881d1800d100d5602c50590307a4200300040c0c0300d426500e0952141040141c0740c4075103860300081c122861903080c1610181c1c0d0305d0312031444611600c0320f0030781401c203003c00300001400d031810800044e02040c18110308040c0c1000210b5280d00034158458 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 515551375 1250 515550125 515550127
    0x1106130920120a0e0c06090402030606070606030c08100501030b0103150e060a0608100b010f0c0f0203010203150324010506070309170a1203020a14070f053403020a060302 75
    0x120007542030390080d001d01800055200d07030316032070392404681100040312034001c03081ca40084c100c1c1c00080402d4103410004020700040c280704060041100030b510107009075a02203010000d0f203001400c140a824003c40c09020340e215040d15014046042030500080d5441c6249072000500015104034507142c1901e402540190906140880140080100da44102840d2190f00200050800b00343c02441c2540e10000c162400c200c10384256009135611765a0242c0071500040030307500d540344100005048a4024140090314101c03d4020901320ba0040c1c0d00d01030814095400d400041c10104400c5d00552058000429007a480700419099554180106445030900103605018140300360140006402510010b0380200205001d00795250001c2c041152010380071000000303040d0007071080d00d0009146407a02201e0080c8104003140036400403500f01d401c0b0041034100b44c040380c0200a04504101003034050440100409012500c18a0310200d60750700c484115000c0c00117840c2e100032034007180c030142809 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 515552625 1250 515551375 515551391
    0xc080106030b0708012601091a0105030d020a050606060a18120b06090601020706080c130e06030f030a0903030f050c06040b040b0907050609060c010b181b03010602031615090f11061309 81
    0x6c40c09012680390261000e03283c1c40900030001d62200c0c1003070498500300c0444107140041c1c4401c1c3c4c0c5446100b00301511503089840000c070b00b400c10301c0003450001654503180702d01801c80c2e1b407414a5207002c0e8205055112503000c1d80c0d0100200d801180d60440804c035000031003460b180000039500c0d41036000c1c0f107041020113004514a10508010384845004a4201103c850f4a84c0c40340c5008010403074406200e8844d000c504040d4001c04411100e40d5003480d40c1d00038407142180c0b0191016002100034800304102081110107580040c8169070040740700d450075131107600b000c1c141102d5005000e4035465164000b40000c115a540350021500a09002d0300d00300d0311041b14850341ca006045500c003407a0400c0c4021a0041d41218510400703100d40c0040354443c8005140c80e07a5900702d40801d0041d1f102590003044880140e03d9251f00222155108043c400c00902c100b02d200d40a40c0d403410b000700d40010040d603d00040010301031590a004d601600c2d20390a080c044040c900801a20b4401d80903e145d8840b80 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 515553875 1250 515552625 515552699
    0x50409051c091a18010822170c06060a08010c20030c03070503070b1b0a0c05100204060903110303070317040501020903120903010c0809070612090c080106030b070801 73
    0x22004080381c107400c094039496544251032541c444404c64031071464203401c3d511658011141301d80500081070000301e203407104080b426000c001080094881400043c040e0700b208107440700034180d404c00e000241426003490824490025426001422140d0503c0b13000c00030154065005070364090480b040c555156001d921150031031040700e03034014141c0400100403003440030000080c01010b110740341103040c517643c805043c00002c2007480c0d941200c040c100282c044040c8161000380d6800d010340255803180144650714400c9a01c250f001c0780102d00000c8040042c802150342407411103c1c1940594541541640c0013004190391070070540d041381087c800308051000950546000c031501408649000c0f065540c030000030380024400c10710960804691032a01ca100d40502c60080000030001c0c8082410017809458040010034200d034055a6450600041050b42a1b204014101c003000050f0003800c40c00c14012041000300044107100c50100100301401c0340e040341090148440841008a12900d01 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 515555125 1250 515553875 515553887
    0x606090a0302040903200115050d02041b120e120304080a0203120f182a0102011e020304051507050403120504030b0a06170109030e09180a050d0801050409051c 70
    0xe5041031900118004040d0451500540c040c2118440402d510706d0043c105e00341c6403881620400004030240401107801c0c454500702c0e02e03502c01800411941c12030b400f4100c60300c010302d0f41080014503021008098044620a90744141d0f901405041407000f90b800e541c1c014031014000812403035001912241152003403080d10181a07a11241c2c80b04c3e42801403c03600308010580340401d00201c0a0300c2c0300601100041c01c800345904c0310700e81d030000703030407140d030701000c3d58408408203065540762022100e00c3c21900c1303009443d40c1c000010041c0c4030b0401c0c0c00d0080c54000395111590540c1094424404865044800e950840c0c0c4e004a8102148040c1c4800315060b0280b54401030010765a0300c280041e074052904048240d5801c082c5c041508908044024241c40d01c0c2c00c0041c0100310390202c1c400d100e0829100310780c0c2c803101041540140507030f4020403030328000e540b81c401d582c070f82c01041d41000c502d580b000e00303940182003c0318140443c1d80140c843e152a40143c41b920a4a075456611002d0b00c2c50082c070b = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 515556375 1250 515555125 515555129
    0x506060d0813080f1204150e03010e0d0305090f0a0302060103060c09050904030c03110d09090e0c0d030804050d02030a1706040f110705060c041a1c0227010c0b0606090a 74
    0x882c000103540d8461042d510050b2410800f00e80c00364074076054106070f541c4207031000c5a400c1041030b600701040c940b094408540600d00c19406540310444d001e81c0720002c02118590300c0c640c1d42c0014213403802e480c419080c0b8285008210480d0070040c8044007180c1c0c00110241500c1d0402800a106050407400b5111045582d01039600010910108010b042d00020303034102d0a0301a880c1c58001c205000310b10754440002080410100717480c400c080c004001280d00006104461200312030b98800c020300011060428024110001100072040004004050212414070203042c00210704000a149000d00f07003940c41c0889404650f40032002460b56a075a802c400c4420b0070b40482040301582000d01002d03d80e10889007680d05104040c04121800c2010049500720348881388140d040d040d0b20440225141c0c0300e600303c2a001c40c004c20096801801a00c0105204c1e81e1400d2070f0013482d2242801d2804e082d4103600164180b211030001038010940341515079900042c121001550343c0e441da40000c00c0100c0c65 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 515557625 1250 515556375 515556397
    0xe09150109030b25080402011709030301091d03040306060815040218041a190e1c08091608030909010806090705100c06020c10060812072904060c0315030506060d08 72
    0x400da0344d15441d030000802d0340038600030f81c4c03203054001090801c06603840b8241c0e5880c8455004000400c07600f90194010101d200b842606060812658902649980c0043d002564940e580c0e24040080c05010098068200c0f480e2900b4962072410390001240e82a854414012504000c000542003001094040601d4800303003455a00c64204007400315640602088011006440c1c04000c00002c8800106115902c19130b1315480c4083d0303000c080071640340030042c0c400e200d14810202d0000c01034079a034909202501580d001183c07901c1611082007502c6074180e000205030380040f010312444a001290b44030540b10141c0d108070720700001540480b50f8108014015103914800308000000c520042050b070300d07408240505101c1a45c50fa0f805540b140c0151407a980c0c44181000288009600c03861070030b800158002c41810450411500c607111103400316030441d4102d654501d040c009607003502c600c21541501c141050815401c56980740d580c1d91010301010f2103138003510003100030051100c007101c01e04105c2e = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 515558875 1250 515557625 515557681
    0x50913020603192306011809110c07060507050c0603040f020d080d0f02030103021e03251a0c10060f0e0c070507080729031302030c0a060e09150109030b 67
    0x5102c3c410201d001084510446190804c0c001c40e185e5803155000b50220301c50503c1c0001e0a074070307005405004119924007011000d0060210040b080404d110700703001004161991035a83c102440d110342402031005107540300d03080034003d1101190500390340583d204c0e81a50920300801003428aa00c02d40540d044204409040940035400d80400750040c60480f4400e1350500c20a61f26500d24000898808600715010350180742094458499036003400319020825444043d41a12030f0b40e400b5195a00742c40d0451100000161b922030a403040081c160192a440f604100e8241403102c10900100a0321a855184050300c020414030740c11002102c0b192035028044074011541d40c0036881c0c84501314403c0064101c41104602a02e500141e4642c030a8100034008516651310041e010300e010300000c02c142d805109001007511580c407050040f130003600e91500c500c502540c0200401c050301c0001084100300000d2807820000300e076000027054041d03c0d4410a0701c407456580440b8000c44c85281604d1510070b5003 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 515560125 1250 515558875 515558891
    0x1c020303240109051c1a0108030307180834060f0e03070b070506100806060906040507022a130b10030209061213110f0a030b07121508010605091302060319 68
    0x317156500e240c0440c80341400300720085907500700c055201001d1040b0f100b560020000104014807a098a511011304c00040201d03054031511054a07110041030700c02ca001e5140641c5803034240d441d6881107050803c0704181d40710103060150080803425695040c81c1400001d55843d07100380e44c1030020102520144a41589840703c6051859440c54160b80101c00844a04804a5442e1010071030034401c110203420701d2520345070181804000c1c00c0003400d02d0210701587d08913600017145031aa414001c46645181a408000c0b030080000303241000001e06005031030928000380540b14202c0c0140001402d040060b200c000c1180410041c0c8541c0c0d07100303140b0500701c80420280301141090714001a004003281500700326000b042c4041c40c3c8413002e0059015980301420400030b182c1d020050f40c44466071405501e41100400300205540700703101d5610403452a0700017480481404d200d05402000110b959070003504021001410400c981c0390041e0007900c1c00000142441c180800c042410526070804100c085 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 515561375 1250 515560125 515560159
    0xd080c0f0c0c1212071e0209071e111c030b03070807090b0d080313030e0415140a0303082a0d0b0f04060f051c0b07021c02030324010905 60
    0x8000240709502c208403d0801c0307803280100160f40540f03014014511454583c254864030311860b0701c03500c3c0c10700d46040d0b141d8410042e200ca290a5005511030b0b00c8040001012802814040d01020b001c402009000d071410340390208002407046441040703840c41c4208080c148001c401500e410004a80c152060741d8001842c1100003c4450458203000360400150300440100720300b845424202400ca5902800490040c00300c0342403143c2039500c83c1c140804038140240c046425100b12644200c907002e50a14200046000c450140040d01ca080320745806503419540d002d031a04c40060552600045161540b0051034403c540c40011300101842242e04ca619403030461024010581000380501c11400c00c62400d810603004e100190341d840d496810300d15003404c090100c40d4000340c80c424885d00d14185d0700c41c013260501c4e0101e03000c1c041650182401f003801801c5000d402d81910400811940200108000450b040d00350282d11661040c60210040d81c4500499003400e41c0e812050f806800014004902 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 515562625 1250 515561375 515561383
    0xc0c03061303081b04030210030f0608010606030b0409030203161b17010e0c0f0409020f04020c010603050f070e19020c0706020105060f010305151215010b070c0e090d080c0f0c 77
    0x1452103035072050120784da1003a0384040e5061100003000320042c14807084c80107103080b403404104110706150000d0050300c1c0d0542ea0064402940c000d2400b0703503450740e0602c200d0b5894003c0070407a246c1030358144007400c2039980c002e6603485180354040b40400c032100d61004104d03045403148403454040134205203036521900380d20307201d5036800346000d0250710307250200e00c4e1103c01040403900104024040303481610850b092001404a4401c101e0780115510416002940c0314030140041440010000845501350700c1c005142002c0010000d2541e881000100580003c0241b0180e1140711151103c0c0d401e003251041c1000703030040c045228818021194045401941580000d1207103d0485804107c08080780c01903045030025280007090150380090302440341008072030002d04030141e4044500c002c0a480f41c1210440c400e8006003110040050705a0a1115421040014010b9042c0090040c20071204041e602c40d40061410300b40445c0000140300d204203070b02079603655904503501e165904040702c0602c1e12 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 515563875 1250 515562625 515562661
    0xc09050a15060c020a2102040905060402010216080604020402070f29280b01050403080c0604231c030213060e120304080d0e060906040915080f0a06020c0c0306 70
    0x4001070031003001542d00d22940500c0e441e00c0e0060074030100f240c2040303800c8001c1c03440c0d108680d0340c0712101000c3c000103031920322035805040d0040d009440f9604280c0300083c10804403110f0314131103d00300101444403c0001c600386030440d9044400681d2032025103000d105011040c1c00191030f18050f484824800300307140031203065002040a151002e6540c1c00c2d00748440c0d40400c0d01081104103007440c5449555010390150501c80340505205040c10342c3d07541c41d007003180d104080b001180c0d0008428042006a0850008400a00c01c809698401a501445a600e41310002c0c4501d01e107103424544003501d4001d07030403036110141c07400074044160f443e00c201501d20003040e070089000d00c401e00c869411606010080e181541c80c904042c10800e04604000c894540544001035401901041844002c0d62010000c03c014180140085611100c0308545080050180d0013219550001030a9425850000c1100e0050070ba002d0401608e450720b402d045032410644140c8140c16100b68130034030003000004001383c85 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 515565125 1250 515563875 515563901
    0x2b0f021c0b0a05070f0c050f0616080a060506070305090409050d051b0106030321060e07091d10051210050108161a090111010209030109210801050d020402070c09050a 73
    0x48070b48507007441c402111021181d060000b21203008400d0103501c11249070010fa07002d0740846841000d2945003a081c02d506a80c00c540080140501030740107030704241c52030381c085e01c0000c0802102d85080701113070040c0b0420000404014002401d1030780c5598070707070080715056040400c42e0200940040c003e40756074011130800600021007011401141014000e2000760303a8190ba40a00d10305501c1c038001d103000d88001403041d041d0340750324020443c01d1021440354840c030b480303a0b1018016850715103480c0131500f106000020060344030341009100009001d00c0c40c09c84000f5601004201e5003098024207081140e0148100c142c02d00000188a0000083c40d520001090854040d07141d80c0b807551400c00c00502d50101d4900c00144000c1e001c1d5030103100c00080140750ba00c0007608d0000c0e4400042c0c00c496144200f01d40d858108e81480544240c15018915458600e0801c645503504180009184482e4100c0081c825070b000a0044200314866807088000d0071703005000d119a017020081040030749140740c1045 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 515566375 1250 515565125 515565143
    0xd060603021e070507030201050a140a0f090e04030f080c0403080f0405040e03070c26060414010f140a0e0a0b01090603050d030b01050d0b120d18052b0f021c 69
    0x2c0c94500702d007022101081d511000504010b4959401035a560300718248034000d0100c1c502c484901d4544410050072041510765405a0703403098110090000100707504034000d007281201c100700c000b0383c00520201100c800c40c101007145039280741803d055407181d80c00040c909800810440c1c08814480d0103002520002c44091008000c07205041c5c1d035034040c4403009014400f49a130704201c4180040044100e81010b100b8400c110149201c48600d051000d417400c541c030680d003c481d040f010000384101070036010381d01d409000d82014030658404061024108045042d078484e80c00c01250001c100341c6c8117640e0f0244a601c00340d03a541348001c00030b000074403094820303000d0100e1061119100b440f400310b10080586990303040020704d048080c02403098401c0290048015200310001e03020030040c0501084441c3e4a0280f46c601d18030485441461a9104600035244056030840159404a0a00540c03281d1000b00d0320364800750411800c0e85104000103900320700306440003c5a080211010242140900164 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 515567625 1250 515566375 515566417
    0x2090406051c081c050c030403080f060a060e032d0c0f13091103070b090307080d091e051c0203012301260d0302040e010b130b0f0d06060302 62
    0x301107000c400102e48090045000d81a00010311480098055070388015a07203819110a500300d0790403680b0658040310300a0001c010001050761181000c2c0d4400d22100100450341008008108080c072079004010601020303040040d81501c0400c50b070f04403100365542c20302d6055514072003c91160803658ac1c104190003045d900c0007441c14092221080c507040606000d07440380d00f0000082c000c200c04a0300302c40322196003640e1001c40e60104034140150500d012110b075100c0342d800405103016101c0d8401c1d0081d81180040740d5110360480218021614805801e10031012802440c4a1000003a040560700602102c0b0a00030745188011042600d07100364020454405610100140082c0c0c43d900307072807140b908500512400b81c00001c04490005445203c2c7c0c214602c50070364034101129001040d00190340400e081103a106100d61a600400e400070742540b0703014014926400d10380c001d0260740380f41c0700f001402c0ca1000c1ca44c8401c60b258074082c00c0c001c002c0743d03841d06802006940014014070300801c2c94045 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 515568875 1250 515567625 515567629
    0x1918060905011b080a08090309040e0619110a0305072c01111c0e010309020301060e0a0606050304030c110d020d0302060411030f030409050a02040f1203031a060a08040813090209040605 81
    0x60ba240a5420002990030999021741c1203c2c0104000c01d481040c1c00148030800c420b441d01e000d0940c0d81ea2440d00940307494070f0040303204003c4100020003201240d08103071100209040e03e000700c3d000d000c004d10b0040b4160380c41c010240d60442c3e08409403040c050000c001840c0c0d8442e00e000d64440e915090b17072112101e0800300c104690362610281500c408840c81218078041034000c2d202c00003400c006040100b40003401e500068211050740d80f000645150004c108600310110b0703c2003c010b0a000d0908504608240c1c500404507c45190002d150f100c2c50701e0391540503601c04580d8485554020112a684140782ca0000c1d20f80000799002c8500340d04040d00e6149902e00480c0000c640340c1702c1c000440c100392501e204030000d800c02621a042c82c560802000c191041101d100070050700c0e107101a4515600a860014100d44a00820803855040c824245160340d803502c0465141d680c907858801040e071a1030400451a2154070141002600700c0400002c0c010303a1a00540440c140c222030801c081c036501d0301 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 515570125 1250 515568875 515568917
    0x31005011b031d01110304090509010b03071d041b06030209090907060e06071403040b0408070602060f01050609031005090703050123040b0c0d020f03010e1506191806090501 76
    0x640200811502a83c0760700e40b51034035030031645041c01454404004280303141c9250542d449500b0030b101203a101c03010014030907400d01030300040e038005a0050412619003108804c104441c1c0007000303c03d00b521b4000c07409010403241a40d6800c18200302c100c8102d507450b4005070095000121041c01940d100c80054a540404202001100c0b16502c40020159260081143c20f178032090089421003030f441c0c8445a820700c10409040580b01e61140b440e030f201e0420100030728050042c0d00003000c5520100402070314008840c1201d0455109880d459200c103030002c0084d04110241c0106074041e880c200400110440c00120841107034000c40c02000100c18940710500c9035003d141e84a118000300070080b900141d40c004001703074806001e581c0c440c142810113035644281d03441f141000b03420f400080010310051005901980d08240d1a0b081200960703161004100140a1400100700320b0803400081e1030140e0007200038660340c0f400091f46512064488a01602c06900d81c0151800140c040f2446d400c03003e1010 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 515571375 1250 515570125 515570177
    0x20109051915051b0d060914010e10051302090102010f2f030915090f031c05010b1e0f1605071403150a0b1809010e0c0402070206040306020f09030303100501 69
    0x540c840308101d115200c50041075110000d01017140e565154002100b402c00d00c55070140b2625161458140d5162507000c104030640980410b075440e92807070080009039207041522003041d034500005a15145a040140e004100c0c5034580342e005420084004c0004010420846d5121400b4510740703409004404901280d020480b20b140c541e40c064000311110324551008103a026840500302c2c0c03038800384e80201a0858001c16480d200c103200a031a1401c00d03140c01d004180c0900035800c9603608004c012211000c00c52240c0300c074904480000541030170712038443c2c0119044a013000348a00d071001c0051034101d035941d030948030710903c4082d1a00000e807603180109403a0142460701200b00d46a44410703030000010105500700c281d008039041400750300902a00026403040150170000120900c0c030380001c1e41850000842a4801ea204000d100010b9071000160340c10703250050001a00c82d104100c081c0c5140c400c001c4010350502c00030081000005c94841508250703002a640c01c5003960b00705c245005511041c1c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 515572625 1250 515571375 515571391
    0x618071815050d270f03080f040f02010f030b150c10110414030102160b18030f0a1206030602040312030c2a020d0b090c03070e09030a0c0302010905191505 68
    0x2c1040c0400108540c014403100c4c4007845840b082000b441c040440c850030400c0c4200c0c2c0301180c031444e00c8180f40e00030b20f00c664071144010740d40c9013910f420390304c14402c004203000090505c0400007400c5940340c82680a80c0608401400c800d0728034941d4402010039401a46244089214850b103c034980442ca0090078440040074944509280c24602da011105800090040d00b540d401c1c054071101e59172104602030300a01407403ca500a05103004c1000c1c1e0340c0d22000141855500c10442003185908440c101c81ea00103181c41d2100312102034500600151003290f02c0582058000f10b004005c1c0104903211081c0c0d55501c1d242000001080e100546a6598440f0050b040c403180406201030804a4046550300a01c010a0266103160540d20b40c0a107000a4624a10b503a02100703698006003003c008080c050120f1070200d40e01464104d004940d2485190202404c020140d00d0441c1014000d411659a240e40141603c0e1602d1900c1100030361840184029500000d4110190102c00d50500c1454007070802 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 515573875 1250 515572625 515572627
    0x1217150a1a09010c05280b060108043203040303020102030106090f0602070b0708070605092a0604031410020c0607030605041b030203100503120406080c041d061807181505 75
    0x260401510f02503054a02500c007401740c401b48142c10480c0e1560000b010810408031598201281401200d42c5002021241403019050a01020545140c2c008820741c1901d94019402803c0321074480d54450f100225140d280b001207404010190190040c41c107841d100d940e140016a0380300302152a41080d8030410001d6040303c40c0078800c034001280100001d60240324224a0204190703162000c46008540e0b40d21907810500313001a00001e001000025120780354084085014608001116807049200082070340100b054a1400d20740d080c82044119050200c00315121441d0540700c64032a4004c032030a80c00245003c00c00b050918052044840b69500c034201078582144d0881706900035030000d00700349035543c541a4006107641d01001034100e9083c003154081d449034617141c00640381c0180502120260007003403200307000140089203007640000744c07408030511648a003c0402c0c610420754451f503021648150030400155041880002d400b0f41010202461603540c1c10800603040344940d81e40b000442c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 515575125 1250 515573875 515573887
    0x2040e0607120c05190207050906030d080a0207030324050405010f060f030b0a05040c0302070506130209360f0d1e08271e191217150a1a 60
    0x1d81c1d0048542019034145140b410803942c050840085d0809a21001079119440500c42030030320809083d0414070a8000b4041c00c00c0c01c5a000c0c111250040103580c410340c2c081502c8081c14400c2d08044d00600d80784600258040003001c10b2000d0602c940100c40c0101d05040c0000380703d0301c52100003c210340c0165079800803600071a00440103400a0701d82542e000105403800b05095546219248102d81c03682c40c0141d0b6600340307180c1681086002001900f40341070701d0a0480c00750702d0f203d180702c3c0c1c0310005941c083c8040188110004105035010300400c10541125402901c81d0000526040303840110b408845449400e80c0c0d00325140501c0001c080c0f80c88108100780782d6000d0056522580080b45458010301c0c40007040b680c20515009450000c61036400700001544051200529980340500341d070107009030803014000180a620305a01c0100b18081c0c000b0180380d454400d10707121020460101500c5036030b0800300610082d0b220140030a0380311b0241a0340000f0001e41448521054000c0000e42d182061 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 515576375 1250 515575125 515575157
    0x50403110126060d08030112050601080f1e03040e0a0b030c09040c060f020708010c41030403110111030601030c0e0d02090414121e130e0a110309030702040e0607 71
    0x900180c942504696071640d04c4002482001c0070710b010f4400500d103003080591030b040c014038054069000300001e40012034003840403000810712400030b000c18110300382c0068800b401c141c82c500c101d9104070300100c400c405011649080790003401d1205c42c201c2c05c4680d81185071080182d846400c3d0b5004044c0036148100308012400341c4255000c885aa00580e1a20303903840c5225401c2d1031102c40743c1306c0010080a20f21600b03a0614400200c50a03482ca07030101c1d036841d40140c124803190140010490820044001404c151250800b6906035520f8002403260380244030980120350410359125001c28101042c84801501c0360280b0121064001c2c500008030405400f481440e403c0940150381902c141c642442042d5810000e2145d00245403070b5044c5d40302120060001d892401518451404104000400213480c0740756052080d034604030781c00070050b22151303056001050760140b04000c54002104005c80481c2c040007a142c668000c0e20b0030301008080034002c1c0e032500c0e01210801d02080302c400901d00b900e = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 515577625 1250 515576375 515576447
    0x8040615050d05070303080705210a0207020301020a0f09060e06040e07031b0f1412071103090307030602130803090d06050a020d060b091f02030a0c0c030c060504031101 74
    0x80d00c804400e11440c16107a20210707410420342001a2002d40c0f000600b0070800d54040010b0fa40800a854502c0c284071040d441054482e02004501480c0142240891403000c4141c5c112854103500400071941c480a005000d81800034443d044408140080400100f403400740741c59903007018004088600c0c1038144040c100c04050043e050404140d5950827610b42540c4d001d1070845e034044542c540c14180b44030380c0750003416204061092a21032031300340502c0070407052100c007054101d1440d0608010001c401c51026207580241741d6a09c0c0e00d032040c10750000a0002c654001d040c002608011000c0c11521600015900d20581d84040e800030728240c9030101248407036020341e4020fa20303c040940b6081c2922074100a540c01c41d0000c1e010040000b840c1c030034514006a81c401c100000142c0c14400c0d000d00f9034080d403240100c3c01c009060000450484007000b0303040d290103000c0c0d0303800724600042c03d0b10b40100810743d4105001c200d42840c092420080b2643c013460040d11622011016241010300c0424240e80c5 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 515578875 1250 515577625 515577641
    0xa0e0d0602070f08030103060b193309080610032f0402040e01060f0e01020c1009180504230721060f15050a031203230702010c0908010b01080406 64
    0x1003a400d1003000d000681c00b0f00650001401264407139145d5040d82401c50895221180c401c0c0b1030140040e0320090302080100c0c0c1011113504014644103490141d404400d0000e0784030340216100301d4680360b60309240c1c00c00049001e90360084101c0741c80795151000740c07003265814080a030080703043d504544188440030200340d000d030410007042098a400c401c041026a0003030f80010501005a90041c0512507200e050350b2211111854800c50a8084500107512030b04400711a901500341450b012082c00d00542c0084020309100c1c030030748100c2240d400d080008000c1664101c0325511400410a9040d02501038ac13036481078204003500f000343c074001000c0440e0411003100c41400ca2507a1010000c40c07828421649400070403000807030020030901d50001107814540105100c4e003ca40c4061010441c9122813800000d040d00b40003800b048583c1d001400b624036281c0c0325180380c07641c02c108482c242e410741244032161a04d071241d131007583c2c0701c11205003a02c00d9200c2e01c40c0043c00f20030000f00401d80030740040b90 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 515580125 1250 515578875 515578883
    0xb09030f010c030b01080a1401051e0d0c32060307030e010e0c01091a070b04141e01060b0a020c0d020103020408031b12032e12061b050a0e0d 62
    0x2008400e9422429a0030710680040466a10710440156580040c0c01c05e0b0711100010040040000750703042000c2461040c0619030191812400d0310307492054050f031800d6500d1008101e00c030710304464038140c4610130841c0602c2c000340c00d0740350702005005070b0741511000300c0245582d17a0300c0410011081c00781c2608000d0205041607107903609110b04c5d03202842100300f0380c00804041d0038544699000900304000d0740c3c1c02695002e0400440d01003140746101661400c035403018001c5601d4445080c02a0068485030841689000340710000c0814030400486850f800c40c618024841d541c2d441d1042c68550058844071f00140e04022a1010245048211030608034070505005040035254054503180d0307000401c4e103803081483e0803031503009240c00b042520310103402c4407045407841c900540d0210650309a94035202008401c04241200c4c8405001004085c0100007083c0c82d02e8000d605007a005000e8510f2444060a05c0040028525103d94100e540282403900d5011070b088040052066401c0000030641d = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 515581375 1250 515580125 515580133
    0x20f031209030702090a0c0305070519080402060c072304090b130606150302090a0902042111060d0b040e0606030d0507080f0406020c09090105040b010311040b121b12070b0903 77
    0xc0185c0e0b0f240190f074003c1e80c0c002000580c0040c140000780480d13202800d540103100c01482190581714400903140d01040741450076040c19203941c0301081c80e03800b4120101000d40148000840c800b690304a030f500d5644220000020004c10050602c8220b82d54854041c000009400005d0b034803101c1400c100300741920990340000c50075561064428112407580d00c03100003d400007003041c200d140050401c40070300b951002c01c5107001d1500c3c1081c005074903025002c0400112170030082e0240944800801948580940516030700c055100d0080014040c20103140c1c45245044400703003100d10001426841a40058020218841e4000d02500e540d0403070302c4201c581c0c00c010441010044240405800180000c0d0000d10b0004d2a075002c10440c280300810104490b89000108400318035104a0700781180e0300610000d40c60405c942c00b182c090700140a042e81c00802111402003200c000103165030b1031502c002807010040302c0100c01c1144c4035031000d4801070540d001e80e805021400f040001480b922000030221 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 515582625 1250 515581375 515581387
    0xb220c0813020a15110d0f0e092a120c030a140412030f0b0d120929131e1e18020d090c060201050403020d0504180504050c150301080706020f03120903 66
    0x10301e2401c03072151710a0001507032001ea003c4084d80c100c0c841850300c240031180f40707203144ac0620100da0809615048418044600c881d000d0180c1900c40441c3ca04410036054101c05150030221085075906c20b0b01c10b00480780c54456048040d000c0900000c0c00ba41d40020403a004005040049001d02403240701c07441000c0e605c000f03840713081e91081440343c01c0c5031142182c50580108540040d10104c00c5034000c2080710404403c070040821b100a50301d071442142c45080f030712101d02c0328820420402075008020061111101d43c09101c44001c2600212403240b2490f81c0000c41c2c1ca5450500c1921b5440303010141d80d0f0480c0200c1e0259400d40180c0b440c05081e480005c2e0750501e41e210320743c4402050f40580e000d40d5440c018001071650520403007076110203e0600c41e2034a4540b01c1c4032140c0308417018810083c0342c0e4600100c0c040100621480e00145401403000d4000b4118803c035210075802889402c8a5204850000030702e14008510712402403900c00c081c40c107003503100c5e080c0c150603c40181441c40718042040700c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 515583875 1250 515582625 515582657
    0x201030e1608010c0503070807110a0c12050d02010e070303030b13020703050c0601050f010807050c07090e0304080c040b01052d12092e0b220c0813020a15 68
    0x4005644071840301e85900c0d00d0000003030b00b1101254900c4040000401c10004101d40041034035421201c103283c841060b4010100741401c08135180001051000318074400100c2010307080c01204040e019505444e0319a45444080c1e0072524404110001508081d80030400b0a009920a03681d0520142941c42e490390804d540c01c040703901003002100442c5d004039201c80c140c542003090310f02400c420384419090f840b0700000a054103400500020800ad0b001642e6401a40180042c3e8014600c00e84103110007134082c1c18003620f0f40c0041c015201144901c028042c01460140952040b03c10f060b1a164507002e01c1d0700c1c0c83c4680f190811175a0320382201da10402d08401000d2402001030012080c0e6003802c5080c4031035054100501c90040104130030002c480a0060404021010019261000001000e0354000f0200e03401c0030650b01000b01041120100e02c000c3e030001d2b04076545000040d61981d41a03a0b0300c0400207440e0138000f80c0650000c070000003d11140394400080d0680c0c00f1039083c081e1503a000004 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 515585125 1250 515583875 515583883
    0x607030903120906050f010f0807031e0f031e020303010e070e0a030506011206050906070e04050901110d060603050709060207060503061809010b040507020d020a06051b130515070305160201030e 85
    0x10442d1416510000c0061804103210f00307e0240040390000140c0d40c1ca80035000b940d03411240400f40c0681e0000444c20000c10a09460045030b9038040301101f1b02007841e041c05000d445915079814445140c05004a074024070120031203068401052002c2c4403900c5d5460101e416850307001400d60032491038403010010541c2000043d0080070640450500840c6518280050b650068803011030366000000340f0031800c2c0c000400d040c00182c00c0d1000a1a6924501043c1c09010002c84282440130000b40c5c4019200050304210107554a40d14280082d1301d80b0704085500108502c40d0200681001000317201140c13155008540101c0300810941005a6004640e030b42d00906a03100c1145039034a2104c0c0c15241083c1c0a07455003c000d500213001c0198002c2e0f0080e48500b98004014802d590310030014100803010703540c0e050051040c2c40c0058131681e0100c51589084a9800f8151042c0c100203074006100138101c00315604103604d071380c8a60070890312900c038038014074100c6002c07410b040e114040c1c540c003854100 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 515586375 1250 515585125 515585141
    0x2403060b030c040603140c0a0e15041404050108160b0d0204091b020706090f17100903051305060306150c12160c0504020915070501021201090c0f11060703090312 71
    0x8009942c551404d0b10160031100800d40c401e00e40e032102030800c51080c18000a4a440310301e40e080c200350b1001c00b00d00140800769081c01009180c9000314000c236440c40d000c080d0301c7c140c12050300c01700441e90322100c40d250384001d00301000e918408100014040781162402420a80305861405820710b81c40d007005030181d48002407000700e2a0036080350010803c4c0e0404c500c00003004142811340055080044100b41085a03018800440304546043c000f00b030000c2101c071005002d15002045140c081e490020011303840341441e081e13900e81001000ca080d24158048a0080c24001e190b80b00030810a01178082d1500001610000c9009685803031a8044400004248040460300d24210912041c0343c064407030a015001540034520520001e0303820344400000d0006515030109980c0c9807401071505a0282c810740b1820344000d03040500020b02d10f03015070001041418203481d420401c01140c2c000b2134070444000c1d044626a4801030104482c140030742e1140f80010f00071328115084d50507086611058074124 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 515587625 1250 515586375 515586391
    0x50f1b07050312010b09131a0105070c03021008040c0f0605191707050406030e060c04090207150e070608012102010f27050306090a03050d0b0f040e0105060306060a2403060b03 77
    0x4121b183c40c944a240c0c0f51a603101d4000070000800f01c0300700620401c0d000181c25060003800104c81c028480181074004c02107a00402001c0c8052401c2c01c0101403e005440407558046012804030304a82400c0c611026144103565481c18580740c2100310318112014a845c5081c0712802204140102e17450325103502c02c54084e00c030f640d5134503c1c09400034100c0b094070080060580010007445005480c0d00f084030115035200401503140c4141c1d09105086550004980715503601d0000e4415180c0404034015040320550786401c2c10350781c3d0f9400b900d041b00e000d000e10036042d20f9250081d01c1c0198000c40604484440c1403800ca90080041d02601d10038070045001d1011041c070403207003006030349010030096034400c002c02c0c080c00c3c030300c3c0b640d85d0040c1c910701402d198808016182c221105454a074258055801000240705016208900d10054000c0c001a42e001d8042d000320300c001005c0f0705044502c2d00480f0050241051400010340040c40c590502042c041d04250f00d88400069050f60701024501811701 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 515588875 1250 515587625 515587627
    0x180118030803130c0801091a040501020903061303080601090b070215090d0c09050915010303142b060e150f04020c1e0c030d0f050a020705150a03050f1b07050312010b 73
    0x2c1c20001303803039040c5500c0401c5503810300760720500041e401d0a00945d00008001e42c00c1050315585081030182c0540001c00341c062255208020ba8810140d00020049003c1d403074030860394880100449106803580900c94502500300070480c01424001d40c3c055082c102224824180045000052a0310281e2881031b0b404100100b400d008070b200e68442c050300116100001e10b0f82c18210030121138244014030000d4180705112959140d4020b000d41190601040341d014003503c000c40013800024a98259451102d50b0314046011582401a100150041500c11403681c44a92040c04000795000074080b4190840c2d02031102c09650700e001c101841203800b41c03103891424808000202440c200d520070f1040c0c400c0d80600002c8650542001b0781c40030030ba03c5450440e590b020061030503481c140c200e5000980190304584100885503561002e85801721060740c0030b01c8652540713201c49141755401c1e100ca000c258021100c25a5005003e0f00800103148140e054900745410f0710203044541c00242c0c0540d40c0400c0c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 515590125 1250 515588875 515588911
    0x40609030b0a0b0306070c03020a02030610090c2d030b04090b0405060c07150515030a0c060f170109021b030304032001090506060f0102010e07080a0314180118030803 73
    0x704500800303500008503181002107200b26400203554060103412541403007052200c5406242c800c0c0100d81025401404036140c1e42051400403001c18403501c554082c03e454145007403030041c031413003403031f1f19003d460f01d4407106141048400c519481d030002101c1c018560b40344d10b0640a602c40d8003900d07898500400002426143c10708000b400d14030000c00c1404070702e05c200800c4001a0444104e8912400d80d404000b40959542451040c00b1001e07411b4154144120500303442040118100d07401650035035076800840c401c041d0b4003910404038290405070030811410041c0306012059014108150b514421102401c0c0c0e4503801505640c0251020350005642ca88800041705a0000e504901c1341400700030000d03426243c0760035407958400740605202d04101c40c000305d160b86c805d4100e0385c451301d2044280d800c0265620005503840003d180110003082c2c2c880d290412061002c0f040c0d40c84003500020401d52051451f0045030320a9540c2040c120620008a000c40030950082c00786104880c5c00e080082c10032 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 515591375 1250 515590125 515590133
    0x2070b032205160b041d04030507060912021603020a1401180602152409190c0c1b0614090a1d06040501080c060f2832090f0a08010204060903 62
    0x101d0340c0d0031884131810208020481e456440142808110b121452a503079611649030459440c4501c107005010b060a0080300c105001c64110803c0300c4c03000540031154040f44200b000121b0707840900c406503102c074210004110314602e01d82a80708206051624a00f005a40901c503480051950040d00050384118661015031210710100c80d00710000c80344c941503e14005144c48564003010940c28016440e80000c2011300c1007030100048850103840d418019940e803a5030080041d00c0c1c0010594481056040c0b10300115102c0000d0000d4401c1a51030388603070441a1340c16846584043c1020303420200100c000601803000310440020913038526a01500c500b01101000b00740c40341a00314400760f03006031400510a56030a400c8031009408441e107075880c1c6059100700001040180f41811440300c82c41407008101d40c0c45100c411000302d681c0c41d13070070000850ba859506419960001c0c040c0307c46041201001d5490300103884c80010030014130204600f40c48008072426600646d11010108074441d030184204 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 515592625 1250 515591375 515591413
    0x1d0619030b03210903070e0903071109040b06090c0f03040b0a0c020c0a1503061212020d03021e071b0608011d041505060a030b0c07150c02070b032205 66
    0x18101c0c01408000e00015030650340000f190361540d441e9100080c0001c182e01c0510068008082c6403018641629010081c40e07101c0c0e020b8a42200c84944990350340060f841c010921900443e0000118043d0b641c90200380b0201281c040c0c4200c122030818403841842c00c824000443c4543c0c410080d010f441c2c207054200d14151910103000c030341034ad000411320f0303506a01d4000d20041203616110001e0f0004190440c02c1d8001c0105800c40d0070340c21003003080202800a10a001849110304c1e901b200d0500034010030032000ca005100c1e101454003036002034803102450100c040d00846000305842503012040144185060201e9402100481d008400401102207024901c46090040f4580b59915240035521101002441e07402c4d040c8580d500c03004222191620b086220180d40d0025696070141403041900031039400901d0f04a03002c0500320a001c3c100744c800e02038080d640c0e040d034006154081c1003000d2030f05a5000109504d85110112203285011540d82404a041d540600003400315240b18003403603410 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 515593875 1250 515592625 515592641
    0xa08070516080c011e110109050312010501140d020f09040203091e0304030503090d0501090b040303090c05060405031b010e0d030e0a060801050105030106140f0a1d030601080d1d061903 81
    0x40b9400903120301850381d800040c0041030100c000c0c410300d25280031410554000c0d086404840940d881c103101c440030840008010700c1d4000e40240f490b60700742e0f600e1004462007180314402140b511400e0107003076400401c03900504103800b000d4802505003820740000c50300302d03001103440c01c449920410000b030007103070341848607416980c45070055807400303085440d01e6a0324403a113111703940510100300341030090203400c0d845400781d682e100000d42981c0c107143c00d0040141c04000c00681d00603080e02000a078510380401181c0481d18054080c0c240c0102520428141c3c080501d20709051148541e40c000242e61843c40c01c81d511446500c881516010784000c1c42400826600514280044200144030742d82e000b00c281d0341121158908010421866091802640600c090b01d021840b004251411010703040100c0c059800e090f6484800c540300c140c0101a41e450081c070030701c042d540000000840991142251039400741b800c1c15a650b2a03210240891480d038003400003000c03140c20542d500e10302c06030706001d00780c1 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 515595125 1250 515593875 515593889
    0x70605130606060e1c11030706120c0c0209010302131506051806090d0f03020a0c090606030e010501320d0302030901020f0604030e01030504260406030e01110702120a08070516 77
    0x3a164203158049030a1001c030f0001742040d85002815542044084041d000079204003a080c0c600c1c581c2c6c1c0c0d00f8080c1c0310f4084125480c03101820300241c50500c0780318464200200303800501c1111603900e5a0240914944108007850002c0c4d100c0403081050b040f42c400740c000408071551181d50ba10f64052070402c1d03080c040d40b038440c40380310104001340b076641d140100d028419412842c0890010224034081c6d240482c80b100083c00c0d0703048401c00144c400310a50051084604c0ba071428000c4060b4040b80c0383c01c0792070034004d40392682c51000840c0a142ea10501f49100040f14035051069413500600160510041190440c0181e10000d004181c65a05002d1070515584400003000ca6050543c0e020300b0b8040d480300300c90304042e80c40700003406000d05150b000300811494221000e0351031303203d0b407410355a6006005020219017842c10810800405104403000941c2c80440107081c08115407c10084400c41a180c40143c81081c20020214000c00c00a02000748030700010305001565454511311442942c0c4042 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 515596375 1250 515595125 515595137
    0x5060309030304080f071a010e06040207150b06092d1008040609080702100c12021b040e0a080a0e042003150301111b01140606070303050a0207060513060606 69
    0x11403600c001055a800a030700c1880c1030303141c0c0f000700c0e4103a1030350044807005403048040d0078201401002820705103060352107a200048003580c91409000aa1088820081030242c0c21144064544400d0f400041d03e02c00c0104100e01c0e012820002900075803000c0c0c088529510406403806003071000e442000b140c520283c5806030700801011014040340c3c0d000300007400007074981d1020b1080050000480d16955801044003210a0600c2c10050800d11202800c451300d20801c1c00d0560758600001d468800300842a58060a0040290501c8042c060080700304469109410105c40003900c0b20028109100c2140c1d03886070003112590401041d90300942c480070f0030a0307017120016003042400040320f038401e0141d01514209150705020900602d05030008001c000c0000c02c20082c03421301d94007200300d03c2c001c41d0002d1104074595500314a4200003955101d5100204002200001e8001d400a40d4031403200c030f03801404c2440701e48515042c1d8000b201e954a205c440300341154200802840350b140645503516200c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 515597625 1250 515596375 515596381
    0x100c02010e060901060b341a0f01050a17070f121a0601170439080f0601060c0501060806150301140103080d1109060c010203010302030f0f120d090c0b0d06050603 71
    0x82c00c0580300ba0030380d81280601040f51f03c070400403040c0c1d05041d980c0d03c0c403242940d00401c1c2c4c00d040b154101a060016034503012180412202161311a0f4141690381c000c0800c44070a10b44140101d466140c0742d5000d1140c0242c0e040040c03200c0204107200002e056001d45e030178045106107040030b900c00002141c0310740b0702c25010034020545d920002146200704510741d000703201c0e2682d04284a1400114401d41080d1a42d9a044d240d5070b000000a440c2c0e400d03000e01200002600d5440460700d5203402c00359200e840c2c0c4614010400c0c540b08001d10310041c1e0241000141c504c3d124140c00381424000c9540390420003161031701d0301130350809100b4001010b2035201098000e504507a104126485040480c5030002c2d04c48200c1100325040c941220610140100103d503113403c12640140070b0341092206078840e0003012080d1040100105071030072044840300c068903034004807008004981e04414851422035a0f035a9003540001e0b861900c00e405014201c54450311040e1200340340d0240d07003450700850b00441007032084c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 515598875 1250 515597625 515597639
    0x90a020a08070f0c171305030303061804020105041e1d07080403032d0504170717071e0c030b010f1202060f0702091503100b0f0d0203100c02010e06090106 68
    0x1c19040b00252400301600300c0300e0035049070701900800c00030700f61405030608481621a002d0003411254540400c10b02196900e404250b164081200c90a4101e0140c01105c1500503802c042664402c0c4141000c500380303a00c035407940302510303440000541c480c81c2050080c414034855042002a501291161200da4500100010a440c102800080506d515076015208216403040402e00240e000f1502c2041180c1d40c040780d001500c001e0f142650710700c07420f00c94001140555400c4a000d180c020540c030406000032010540b20b54001c0c0e0040c0da142d000c50030007400301c4005540c1103030801c2c042d1a00c0c0c02a54114146903180000690040500c150186c1040002c10a01104e41d0802601101c1d9107407115480c00c000801480341d01d034000e50000b00641000301803415111460382c100800c0d402c031101450028040c504481c03901c0521640000900701d003403828509a14090b01092006d01a5200d0801200c50607050301c10080795500981d46a2140096144040019541c07081000c0003d02c203071403518130 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 515600125 1250 515598875 515598887
    0x14040f0218010f031b12180807080d0f020c1e16120510060f08010e030306090103020f03100203070906141207081f1508062b020f060d0b090a020a 64
    0x1d8550520241c0662600042d0007540319620007880b15030751103450701e8541da00800c2c02c1141d24840c00010f242090b0752450105441c080880141c0c03109080e0b241403050346174160540c02c2008102c6039551900141c0e495990140083d010008201006180c054203d20001410380d00040c044002940714980c1060350540880d501000c4403001d0708040001e080310700703040e4204081da00148420500b84080000d58800070410441150b4045008101c200300f150081622840152013656001c0c02600051000d46050726217154140d000801715246c225615000c00d050360001c68804010400d200c40401c221600000e18000700002d90301042c0c54000c0390b5000c1103001c2c10280ca06c4007001b40e14400180c8543c15030140311403180c4251021f4540079640d02400038040d1f054240f090005540c0d0f00460981c1c149102d2600000c401c2080740b0301540d06d220a0081a0f2000b220240c1c0d01c00710100c0c2c284a02d454600007806510103004000c607601042d2000e01c00d99440151031042582c0c4104000c100b5268404 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 515601375 1250 515600125 515600167
    0x3120c08071107050a0b120907080a030f02010e010f02180405090a0f05070b0c01061d041101030b0d1a2502060609280e100c0203160c030c14040f02 65
    0x70425050300e10100b00c07120702d081103070f800864101d003900001194950301c0c8805012059a07045220382c8503500e54800e940c482c44540700782400c0354005444400028090741e0803000d2880c45100014144601c80215821740300d80b10481074580c0e078000790003865441010010054190140c8040c4240d04000089a0382d8002c1000003900b106084062013040010601004000740400681291100c2c00b10380594001d085510519211800c0c40e103202c1010b844c0f049460784540e40140480010000d901e0054000d0a03105d0f024a92000d130b113031084000981c2c19001e04841442200300c1d200c4c3c07840e020fa284403082090024007108800702c00755141c605540060495401641070b03a20a000f03884e4610030b8a030712440401c0520001103042101589030815502580c2e9894188080310341541740544184103d80000e0324280060700100805000c1c0c2101031103e29410f03101c0e00352005101c0d40e0b81c5581000c1952074001002240b400040b408140c5007900850b003510700085011880d05100c00580e1000a0400c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 515602625 1250 515601375 515601377
    0x109060504090b0a030f290402011b050c0a09020c0d30110a0e0108450f0d081f051c1e0308100e06010804050a05010c030903120c0807 59
    0x1d0311840381130f445410181c1c0042d5070000d84503061038458980009001d42402c07008130848984d0180e000d11000170080c00d4051501a11100381c1c10b18424031090041d807000805492500c6404281101503d034621810002c1c103030840c00503100c2c49440700260401e408003580c00f04000907005599031003c0c0e404000764010b84032100c901c03d10b510010584000c4d02d030410b85158022004280750307080d103402c140018501c600036600c03009503a03142200e0440d1480c0240c00701030b00c1490700380406500ca021640c03030f014546c0c0101420141444515502d0320b010b0820035000301607082410f221070060380040110360005254102044100000350542036220300d5032048920900748002c001010007030103034000003095040380f680303808800300301c9524004100045040340040c050100183d215285030443c101170b1030004030039031300c00c2d04ca24004655610014005661900030000346100056003445101002d12541e100800d0704441c034103016000b071400c800c00c02000ba0818034036400702c03540b089450b039000800d = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 515603875 1250 515602625 515602631
    0x200309090c0d0e060705071b030308061905150403031205070212300105130203040f0609051e071505090307180204050d0b0a0e190f0609050303160e010906050409 71
    0x210a070740c0640b81002d01c20550703005032400c2c85113190b4818007d05500e4011107403117000c0440503502250001581c400680014041000b00354149041407582103068000c9001035042922400001d45000f1301180d01d001c0d201001600304201608280c40c48500c40701107208011a24004e40c0207501c03031005140d03540007240001241e030311480c40c1c0515291080e80780040c521a0701c0ca088140c01c0c10380c00a0103590f22850b1020030410051110b4002c691180e0760021052000c09a039507200f4029044000e4100c3d414058208140007440b1290722404115034050010582c5610306452031050500c80b45541003041402c100d0300603030b0b8a0001e003032000c582c1c119410601103030034013801c030009005642101c0d900c03403100c000e03c00501c100070f43d20b0307400390440480801184000c0c1350070341c1c2d0302c40001242d40030300340080c016800440c08100d19922028054400810a0b40711503984d10f003103a108440c0300d607000c00c01d0000c146400341d2201042d0040d000a091030031101e403c4c40006410342c0107a209201081d0b403 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 515605125 1250 515603875 515603887
    0xa171504050303270f0703030305090a02060f031b0c01020406090f080a030f09150306050f04051303030f0209120a051204230613060210111305100e10200309090c 71
    0x1030444c84c20090011582591900c1e50040c00c01900c07500c2c284030030380001c0d0401d408150042008039403004450780c000c094500d4000ba49407c4950740d08014110303000c40c0c0804211316601c0b04000000c2018641c03003000160b58504003100507041e484180c1154043d640346810034441444c0005000481e42d4250400b03e0205001e000102c84003c020b400014844080111040708260507402120658034211513802000104009010444e030080311200815105880c1880c00b107406070b031050f40da066a01b94054079280c40040803035081b901e050b503421415400070b600c0c5824041e0a1200c842454103221070f05140c03034900140340040300380c84d000f000038203840e02004001340c0e50341d001206e034001c0380d000d41e8100c1c132541d80d036001e500c44c0410300d008540c1d982400070b180c508816840441c7e00821060b40000c416500340f8092000f205840c81001c0d05018a280c3c070421550b03904031001486d843c03070307a0f24600100442d825019a05120000042c1181d01c18041c0381c11310b0380c0c1c42c03a0003648050019400d07a201c0b0 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 515606375 1250 515605125 515605171
    0x909070c02150f0714030903150a0603020d0f02120a0506010501260f1006020d020706050306040b03100507020c19140d060c05090109120f0809030a020a171504050303 73
    0x810100e0a003000d1000080c010480ca9a0f0101500c1800c0c090008100368084440700c50751a8803401c007000d82d0540014081441541e00b0000d015001076045600040305501d9a02140300304021a05c1616004482c1001c082180340840310040c0040000c000340c8550545941c6003075a85206001c0c40d410300008400c0c0f002101b1040d80d8a440b44201120303800001e007480420082407038401e807015181008030794404203c280c000191a8010f00e800c2c1c0c003c010301490b000048031203801c05402c956010b625150055140e0750100140c1c80c03074444000300015942000030019103401040b000b2039004054201c1c00c00c002642c020f07400c00444050582101060b6040340014540c1280362000802880c80e2030300141200d07900c00041d000308582a01c80d2840d907911105200340403043c9190052110140598007400505c42d01c014012004001d011140802000c0e80007075001c40b160341122444500c1d00340c150344a501c04102000d0b814144400c071450504058031016281d100007480701c0700e13140e42d90031501c802c1 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 515607625 1250 515606375 515606389
    0x8100c0c2d0203060f09010b060f0d02090a0801091203180b060907050705030c0609210912030d0908031b03160c0f0606170d05030c0423040903050304060f020909070c02 74
    0x7803035004060712202d10f051295012443d0041e10781141541c0f03050b4040b6450f080c800102d4100032440100a07040c8a16541080040e42c0982c1403150884030b011800110007070b00f401001e00c0c0500c501c1c4484000700c03011200038101c03880a6407441c0111362000318507000c511444641c5402000035601c2404941d0740013020f54045c031078100018414400058200c14106001c0703111402840c120b01500c080c0704000c42d00b0221200711034003032071502d07008010b640e00750301d000944841c40207030302d400342c9003016040300c1c1040450750003500c03e80b030b003c10001c03c02407200800b0a00c140000128814070b41141002c00384401415085482e0500b4006030804140030720480118004856601c410b040c04281d031075400c40a400c00800809001620850740c1c0100c07400c0c00380040d2407168009044060a151500c000a883c2031500c00034041101c1d151855499103480b180224241c0314000d4070f5141e601e003803500d400790484504030000c000c0d440c4140725040f80c50342e40c481035a03000280e03483c1400c00d00c0418000150b803 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 515608875 1250 515607625 515607713
    0x5030901090c0e04030306060c0b13050f06190516020303060910030c3b16050c010f020403050d02160302012001060303110c040b090109050405030d020408100c0c 71
    0x4448125000104020203c0c0003500c294800d940a01419a80c1c1405584883c07075204000c08007000c440004d545003543d00132802215005000319a680703c400c1e95418100b810507202e485201c3d404184082e02c0f0700350b0303019098016404e801d2401600c0200d083c000d40724040039000d54841c03a824004140c4030f134510802c1901940d001495459000e0750340721940c16192001e00810b00c800401441040c0d940100c040300c1013403117000312141d22240e8850f485685000c004183c0003040c040d040c06a09000a02403043c0c1d9002c00fa4408010703902c0303003941061490000070480ba80300f150b0000c0f50b03814a1b01e00b0000b9507c1225428248800c0d810b41c3e0341001100d84008902e06070040d0310302900001855030050361101503042540565100c903d0107410301c0180c0301e4480c42c2c2600b00a1100c0104040510769102d1a4024003400c00c0d613092404040003101641c3c442d901c40c00c400c1d03220624501101ea1284100010050f180c207088c102d900642d5204800c24621420445c1000c0b114010400c41103030802018403 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 515610125 1250 515608875 515608883
    0xd06150312020304060314090604060506030109050a120801050307060f03020d021903050a050c1305090408070c0608070212030910090c091805010605032802030a1401090b0f070f0503090109 83
    0xc03040c01c044000a640c1d030003d100c0c000000b0304005014950000c050758850082e403185018092640e034170b85914024200c09846135070599664004000030a400b4481082418130401c0d00359081c049441c0000e04558068004030312035045a581046415000312281d100641d0b6400d003d6114000181c0769070081c0101d443c521140d1020411074000c160b410340c803543c4221107200d41048180c98801803501240070701252a512a1544041441349280c10101c03076030310500c5142450b1818015550396801440f40758490b00224004000784600743e5018840d0303000d85101008054114946210136560361800d140c808861940c6c1d49c0400b006101c112103885000e070019030814401603074034001031040c810301107605461551910702d0120b41c0c0c0c0750100e40120b0841214040803100030f40e081d501d0341310b00322001c0d0480e4184030388203929002941486c0d803181c0c0c81d0080c01c0001101c00c0070b41083d00340d0100042910120759240700402c44021341012480c91005103a180c4251a9503952007003500400b59540060 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 515611375 1250 515610125 515610143
    0x80c1917041a010609060504030209060d0501020a051c150b1323040b0303070c05090c1603120b222309160b070c030809030114090115080c0d061503 65
    0x620030100000c800d081c1100b600c1d4401680d81d50300c01c442c00fa9060084000242d0b0402c01000075141c520401b54105800408854040c2c20503651542241d1100c481040442c1000c281c010b0310b22058043c404c0c0e134800c10002404080c40003660340d110a4180d01a00b5079018011a20600c0140c8016640c0080c10a41c420340100304905680d1000032a4012042845a418078580ca080c03402c0100941e0000c0d644080d107440304a00700001c2000d030380d20082111070203400c01d001c03540368144034058544071b2501075160842c1281d860271116055525440c0254040c84015034150400d0070f48a038031030300392200d00c03c0000e608180c200352010450b40c00c104c002525418103080c000481c902040131014801810006807040b552101d80080b2030160034409810460b00321001c0021941d07100092000d240010700004081458004a000040f810740310120076039074031106121141e82007000030025000c000001d18404102c0310009950f40100d1400070060740d1110b90207003100015508a07005036901c52648 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 515612625 1250 515611375 515611381
    0xc0d0b09010f05191a090105160303061d09060103080c0f060108030301052d0411040b070312050c0403080304080904060e07020105070801050d0f06050603120d0b0f01080c1917 77
    0x242c424a400341c040d076032003000000e21024400c2007908580b0100c8081c51701c101002c00c00b550025001c0c1d0401c200035414004c0801c09610107600c80035070b0742c071240c0c800c1d10000b4055013001c003032203450b52400c01c5420640089906201c030b605000504207044940c80788500e542c80350580070080c1405001d5421aa003031203640b002090f25007020000e075050720401d5a44101d2542c48100103034a10a03586207181695032484106541c40c14250000340030082070801080c03034503542c1c0c00c2200712a40040710603030004100d00034803090501e04e030081d40c2e004001c09030200d090a04540340c41c00c0511028000405442d00006c1103185c949860300010001d10000d5121016840d103c94068041c040846010000902000c00420700e442c254548104103600021011040340c441da45080003808017418140d858803c010007054662000c500400242e140544045075072070f052403e105000c4142d41d01d071418020303260108560210030030162405101a80c9486030700403403030b08007501d131030340e8460701942003140311810 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 515613875 1250 515612625 515612639
    0x3031e0302090a080307150b100804020604030b0c07050c0901151b050d1d030d0804140f1006062303040f14030a0305070e0a050a0603020a030605130504170408060c0d0b0901 76
    0x20301a61070081051a110f40c1c1d0102c40784e02250300b2392a120341c2c440d040c11084c10045104980b103a51080c4050181b030310b010340302d8a82d06074100040f5a80c094a01000441d6002c000341403044400050050b1400030030b6504004200b0381c091051401001003040041c064009010a0702c01d0341061500030042d100d9180c52418014a01c221141002c080c81c0703800000711089003000201d082000d080d41e980c105040e2602d6651a20010007003010030140d21990700803c030620740034000b080c038040d03e203040083c4e02e522f0500050102e0701c640c0c40c030706030195000d41015901c001200450350300c19804900303c584960a451300003442c070050640c038086484089980c0919a405620031802003882e03407511040110081e08000f06201680203c41c3c0142c00c841c130402031540650041c100e0100c0c41e00f404108507888501040341c048040c407190602980300c6060100f0b202d00c68120358100304d04958843d1409060220360780c2d82c1c8402a100240b802c80008006800544c0340c2d203d038402d9031005104174400c0d650f59003 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 515615125 1250 515613875 515613877
    0x815010513121707050c100c0204060602100c02070f0303200703030e0f030a2d32030a050f130929121914030d020a1803031e0302090a0803 61
    0x40403680f40c103003095000351109903401502d5030940e11200811110041030203000c22001d08207030384010b100d07103d000e10b40103a03101d002d98000f401d9268020406000c8031103820007581e008810110964004070411702005140b2761506051301c1d0141001ca20600044600866034661024966654050040301208040e4000074030240c0040450760301800d8410b034020152507544840000300030900b00100300703000c3c441146001401c051183e0460386000300787d445001c4040b942c800c201c0c900a511141c1d0886d045c40c00e4a0200c0b2880040c402181080e0008a010f000c0b44164000f0105505000c90304460002c0e00760003075005440060002d0205c41114480c0540710b82d0a440071214030844800504c0c1c0a041441e44408200440c0005083d40c0f201e9890401c220115040282c546500d503c0d80c9140c0f901c2e01708010f000321a450f42d030042e610701d014000140b0306003040100d00b003500300f000300800c0441d13807290a0402c009802d00241581c084140e1094000f481840726840e00814031003c001019079001c4 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 515616375 1250 515615125 515615159
    0x1407030512150a0b0c0c1302090402040b030a1503020a03241b030b04110409180b131a0705040308090d020a0b09030c04060f0b0a02010906020d0c1e0815010513 70
    0x16070f03012041034680c0c608122500480f0280c11940e0301800201c401e0f49003000e6a00c840144c05c007401464581524041000e0b68807603000b0b06107003e0000140407407100e0b02c1c0b0a110301614160a03400020b419903000941c0341486120103405240c110441e0301c00c402c03032000a4400450345c403800300912564200145160b08080c6020000f09180007032012290420740107412035210103501e4249054101443c283c01084404d240c8121310040c60b68010006010340103080c019061414030001c118603524041c1c00c00040d400000d1a02200e40c0c040c00b03075494002003940e050b40d038400400e80c2c0320703c40c8801088000104000103580440007080c00210074280000424803035000342c003510307a034103d6581400309072081c901c03030320f0950100181c007004810142000340100b000d0f90310005c02c512076584c4641050342c11868440c60b9076130341d03841d91025443e040851818020302205003031590b01d444220181240314018202e41c0601340c1180c4045442e80310b84100d85081d91107607044003a8940380e0007070480d101c1c806 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 515617625 1250 515616375 515616379
    0x6090102120307020f1902121c03020706060503060709030c060504031a040f05061006122a021005011d07020c010909050912030f070f1403190608010c030b01030b040c140703051215 79
    0x54050100308101c0410303080142002c5040d802700040d0f0322281100254000743e0140c0d102d50b550100428a0f13541032041d98060038081d41d401d140e5504604240c00801d640f0390202080c000d003000104005000f020038455000c0660112500d2a51241000204807040c048000c0142c02aa401c11040400364031303151042c0d4000384e0f200041110708009100848040d54003018018015050790041400524800f520014803031040c1c0d07042c141220f012801313842003a0000414039540803807180600524005181c3d001149100030301c180000040041c204640600500e920940c4440c0011840700042018000c050013060225a41c0c0c90000c13014101c0c6481682c075400094810012104110f00c100c1110b1411107000e1485440d54885c00d101810008400880200760b540355040012020420310405451144a4801141003908440014204c1c1c1c1e40c400d02611642c509004a0131060340850004d02200c150043c26545402d50304082d229030141180201140340d600301000740309540762480b10446881 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 515618875 1250 515617625 515617639
    0x40b13020d0e16080a02060f0903060a0605030105070302040b160804050d080904110403051f0f02070b090105071803111302030103241b030504030306051f080606090102120307020f1902 81
    0x10f0020601995000c2c1c4035181e1180e018107001005490700c24000e110300b05c9a00440c9150440e2100441e0500004842c3c1c0c0c4155a91000c0402040c18280600c03a849166807404500d0b1a08240110100d4003030004035021a1600300c040d0030030400104120340103048010100c0142c1c0f4610314180a0310380c481a81e842c00380d802c1c00c210461182541d801c0c0c030300350b03070340300001e402c1c5015183c00c0348545042c2403170394080d80c3d034071000c658030300040c244028a50b1030b001b000c400340f1a240c0250850b00352680905000300b007050031080050140341503070085061343e80c0a4201c0c410b00b01c81c0c034000f0780b0024800c250445417900c00000001006a13104180f000300c42e0a145801c01148400080c50442e0fa400c401e4130340001c50751100c0c0c0e50311fa21960015030301c07a129040015034135845da00071598054100302d80b03208642c4c2c4100700070030060700944001c0d03016008031500b500c0e180c03100740002d449404200e070050b64410084003050b5114000d00088089031000c20484411088071840d800c091071090000b6030040304 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 515620125 1250 515618875 515618893
    0xb030c041806030f0209071403040b01080d09060e120a08130602060f25020307051f0b271009050405010b09060108070e010810030b0f07090602030403030c02040b13020d0e 75
    0x18090107200b040300e0300022603030300169003502844000c0500920301c10170440b0310140800b0410916018501440c09200460702a6040054031490032000f49124400e200c0015400c20050760701c8001410115000e40d012240000c3c0c600b0ba003407410001110050017000c01113940d80d0540c41c0007072040126005e6600302d443d01e455481c0c0c0c2228814042d50442d610500740300d5141c03066400340800703800942c003902c1107a242c01c050342c0b5501e0805486040c020817000c0c05200c59204009240520400d19100300e44d24607a50011404202c40344e40d80240c0706002c030140c9000581403402c5d0340c040600403c090760082c0007a15262030010300820308220541e1142500303401051907540b04250a921a186944034004402c00c4c3c2030055483c008000d00d4418004d42424002c40020304a90000740a1014420500f00d9030400610142ca0035015030008411544180410000320750700c0103841d480141c05440009001740800d0101d10304049084005205500016050700d000041c0d91050140145002c140e1b10655 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 515621375 1250 515620125 515620169
    0x3141e0606041404020f0c0a0c150513090b0613081006060c02061e310503030705031c021306020a020109090b100518100f02060703020a08041b0b030c04 67
    0x406140a6500c540d049001103e515040540c02840725014801c446401c207440225183d140659483c8101c070210701c03180040003100080f000107466412141810ba00308a00060a2025a40719100790818140c0b5400d181c01107480c0d00741100e80c0005484075443d14513498501c820341d1a51070211080b1800d2a0030380c0001d10b18865051811a43e074001c1031140341805068107549002c0c803182c422580481c0c104000380d00143c1614100c0084240703000003100c901102e5420240301840d5502160107500b04024410008001004171144000310f04481c6800c9004031400384001e00440507080e81c41c403076030303040800d02c5a0002890403d09100341d8405040da91603840d41019184240380c41a00440000112404940641d014240c0f00890001c81002d02c02c0f00000981d100518600c0ea01c04201c0f0741d00b540306217940c14819140d110419090640c81c16043c001c006101a0300204040c184120a8544000548100c450b800003000e090092544908050080c41070f207070301500c600c1d2880307410010582002 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 515622625 1250 515621375 515621377
    0xf0619020c0a060c03050a090b0417070914162c040b010e0609100c080703030e06090106080a0f022d10170a230f060a14130c03141e0606 60
    0x140350b4940c0e0b11044c0e01380e156416242504080d9155091101034000400c030914450042c2000b011a414600d54020904820364280f030b646810032141a8200014000066100141250002c03000f86038813070301218487c401c9507412600502041c0c81d486020410311380c500368607010409401c0c01c4a040044041050066651075850041160000014000c0410320f00d0b0505403003814074200d0802101e0481c141d5100c0d1110380c42080100d02282d0342c0c921031244550104949507110540c1402040b07890b04201041b981c3c0d05e181d0a00400e6031400381e0010b4119100c203600440d4181d034041c0c03420100030001c240d1440003241500d00d113009000c4001c001040c64400c030240e080e031002091901109881b0455108040c150544580540541078000b8040d1400c68400141c030a851401c500107840c02c20760704104088100b6401800c00200c420342d410f1841d9100134610007100e4182c48001281522460168080c00303000f41c1c13009a400c031140400201c030304109150701030012240449a1981da4640801c502c0b = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 515623875 1250 515622625 515622629
    0x18080f071407031a07021f020c01090c030303050c030103080403061e05040c060f180e060117040602040f0f05061b070f030302030909090607021b0f0d1515081005060f0619020c0a 78
    0x16403000d511015080103041c0c51f030020b502280005480d00c1c1941e01364070309591303400c80700319850030100d00c0c20400e01d40d0500c9042d822030340a0150700c3c5554950780302c6059501031070101910b066903400c0c0207281c50b9014040a040340c00c02c044140814a8641030440c5d001e0440d100d1440801d04464642e40814440c00d08201ca418013100094081410441606d000100c0241080c3c1884064880745441d80690500503111710320840300540c3e1281081e0b001c83c00c0c1c042651110312840b451400c10320443c1c0c0c078941610061045607020400074aa4800e88511380089540003070b9551301c1c000e4002c414198044020300c4142d4082d80c09168985420f1003141d603462045503e94016045018143c3c1d40c450410701c004910140145081314070f4503580000382c400300800c60121400e040e0748101c030810f0441e41c021480c2e0100390020341d041e0286051002911200740e9080010070729171f0381c40000c501d5668030004012000d40174284a80b03c022500290703000040020b00f0901520a081d4804407a02d0b0405070541 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 515625125 1250 515623875 515623877
    0xb030f01021c110d051009110405010c0b151e0f09040203060408070f061118030c030c040905011103041b1e050d051009030302091318080f071407031a07 67
    0x41c0310180010400289070030030043c26203400030000c00070f02daaa01d000c0c080c02070105802560b035040c9061540740c12201d40e00341801d22108180020003945e030300715040140094010a107050603544070003620180c06d9590041c0ea03480040002594040c149003000c80c001c8001c00d85460110000d920304221540070201e0b0002d500d46d00a800080000d43c04001810415104000e0001000c1a070f5607088141d5600130303da00351104011900702441c0c8400e48040c0703550007058000d032007004200d201183e01d42101c440d41600075138585540d9020010300b50710850751051640c10058581c00c00e45010208503003561b20f092000005d002002c0744c4607880c0010b440d20f410f17441410f20095850b140501c03024001c10081a510350080600310f561030f070024050403403898402d940044e41c0c5c0d42028204000322551200101286107080b50781709054055034002c0b926541c11032000c41c1c03200207035039409041c1d11030b904000b81052a04007004c0d041c0c40340000d048050742d110360601e0030343e01108489c6014540080703030094 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 515626375 1250 515625125 515625157
    0x30c01112404022d01210929010b0301051306051c05070b120105040b03070f090e0d08060609012f06190c020a0615180b030f0102 57
    0x4041580186031030811251020309542451014107208481e01c01001101c0c1c20303900c0340c1010407003107203071500002d0b01054019515400d410300303041c941c2080c111251440c03411303c00c804e0801040d0030748880300749080b8001c940c0c040c00012914500038071128007503001819115003603400403044200b0407908034162005c090403642035a280c0800c02100000c142108054296648004540c9131603820316079000d5000d50102c540180202c1c43c1891034100981e0143ca1401801e0007003402e10200c4243c000d0441d035086901003032800c80070380000c5c2400019400380444000910b00003c400d21180c12490407400e0b20002d0300d040d04e00b0502d040e13403c0751088a9050b0301080402004000e90f004100c1e111803002d400d428102951991348151803403048111801289512000402c440891124446090a2001032017030224210001c0c2c007039952454014000c0c000f545540031000b0500070019220b0040143c1c0c2c1d100042d5900a002d0351001301311020281d030290195581c100c450243c14000c03150001d04102d01c1c5 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 515627625 1250 515626375 515626393
    0x30c1a0a140d1d0f0d030513020d0203010e1912030c12021b010608100b1009030b090309031209040e06010f0b0c0c100806032401171608010c14070203 66
    0x281c0c100d030301038036605040d5540c03440c181c986007014402851552103008001d000404e54540c20510b0300c14140303a0081014100350802c481c00a0380c94080340080c0c0d0541d00b50382d150004d8400280982202400b882d4140700720411001c9001032540106507060103500c01405440002d002207040e44c5019880c5004500841c401c00c07046542076000703041c2103100080500500d80803100481c2541c0c010350003001e8540c040381c950041c1c00c0c01c1e071090000b8040d0031550b6044419519034040c1c41c03944e2601c4042c25050107000021480d641c1481150081c500c001c068a004a0b100054101c0a40080344554001d80c50b0110407a0301c6000000c1e02170513595907040e095080391421050700250703800155290381500519403124101c0c0c07145d188050600065231a0070741d051034140e05040c07401e60040310407071300b4042403803010720b10301440c801c01419109102030318034200024000092500e620207040394458a803a0000103941d076810b40c400e41c441c02d0650b0310014110300640002c00d0b140240310010f980364022083c8 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 515628875 1250 515627625 515627657
    0x1905040b0f04080c072304050907060f090e010b04061d090a1107080403061d0a080f0a031b080a06050a030819030605060c010501031505040b1302030313030c1a0a 71
    0x1181e41d00c1403068104624000d002c100741400e01c545a8403010800160104d05852a044009500001013060303408108501e071141400750303681305a00c100030a204108941c0316407907120300e41c01c6000d051041ba015100b96911005e009280d481841501d000454102811031418410034110080c000001c102d00055140c00340c0d03200c020a810300b0402500c0c0800c1080700000b031035070320140c03000703500888000800d0521400d0568680c4001c00300343c0c40d150003070301283d40042c8445069400300412000032a844d404558401e0b0b000b003542045a052040182c00351100c116030001006205000b802c00a00c8036981d110705200c840c80706800010111082480300a00b0282071219030355001d070151901040050f500c0d00852034607402001004016512075006100b800740450110402c070300c40718002c100fa0301e001d80320a0b41c10600909000fd506003241504c8007955410419510b8065901c0e007c417194541e2440c0001200800c0c0c42001309101d40901c0c10000244048151480058141c580b54a50700d00303c03003 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 515630125 1250 515628875 515628901
    0x10516030f180e09010e0102040f090b19181a0112111201030f03170408040e070c060e071a040305030301031b1203050c06130c120201021002121905040b 67
    0x700c0c41c10441104012140c2c0c4622036440c00c0105208030212207a810522822425600254242a4245c0c0100801c002d00b054100c248030488502e664000758110381c40e000141000082c030304040041200702c1c400304052401124a040c06c25013003004200c100041200700c240012148086400b14608603c00030021441e60030640740100e4030a00c0c0c0d0b181170462032150f0101e8400382c0003030302c81c0c2081d05011800c141e04580c5028103c2d100b4800d11001c0d1034039540d0f0503901c1c820340c051170040c401d402020a40c0a4042d981070b1341c84650184042c0070300003111943e5030b034551080c4144140b004104080040c00c840790740849050302d410101443c039503130035a204d0040b00600b1508a4410340071807500014101d0750103024104e154420750340c030b42c1c1c1e070041101000d00e4248094074500920031120051b1001170248240503007241e034101c5a843c040100360005030b0620040d461180c0703c250002079000008041740314401d10411a042c80b21b61200729007498141268130441c1e000b010115068003141c0f0701132010b0 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 515631375 1250 515630125 515630147
    0x1401091d071205070e100807060305061011011814100b0303070204150b04030b100504051306200d05040506161b0f050312061e0108040210030b120601050f01051603 72
    0x1021510265a0340b2601784407020105c41524421140d0041481040818400c81008100f40c0c0741c2404523052020001e0001c00d003144610040c4000c2080024180700c087d04032450141e08202241564109420021048080780710100498052010119012040e912803a4643c0d01c004c0c00440c00c0020941c2030100414409080394203408040c140040d8002031403006102561044120054906090408040e849182e80246108a040404010050040004012940340c104502060340c40001020002055410803403907c508400503145d41d001103140c01041c0201d00c12811204030307680320300182700c08204c0003511000203144590300d183c40145603070b120f921a902038006508404e489948a03855a4050801050100311072000c001c02481c0508200740c80800100702030491580d202c00092691400800080c03143d01e6040e10940183e103e0f0780080343c103070005080e00c140c200f4183c0d010b0750389074024403aa070f200b44682440074549520913002d56101c101d2071000d0504060a80e5400d60b500d100c10 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 515632625 1250 515631375 515631383
    0x1110c120903122b0b06070f080906040602030715200c07090515030106050a080307080c0703240c03110904021e27030601032301020d1401091d0712 65
    0x8803c810003081043c40100f811546050400b264020310400c21102a5000d400100c90146481030340e03182e540f141003c44920355071000c4042600125890a441c050117607a008940016010402040c010703000801481110700600d04c1c4170030b03a00d20707031821815541017030007000c50000c0302080c1c14020850744018144004030581544c001da9110b080c03a000300c0341c0454024000c0c0760840d10f24695402d0a03c1034030081d0000340e901060301402e00c400141d8030b1085002c0104452400218038034549420f01c030307403c040e6900511101c040554a0703501d04207200c0d883c0c0b00456052034000c008044500912501d4001c1143c00080c43c00c11000c074041200a4010300c0d40030400c003100c92400500304035044000d20764030322010b03252602241da29100b05008509031341041e02940c002001400412240d50100c04030b007484007550690004020f010030302a0049609034030b00203043c900c580903507034250300006041e01c9164804210014640030070416001c01e0700c030b0100030b035004868140b00720040064440009801 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 515633875 1250 515632625 515632633
    0x1050d020d24140702010c1d220203042001090b0702061201090c0f0c08070215040306020a020706110a0f0b1e0108010209100f020c090a060b0a0e0301110c120903 71
    0x104010440e4403003070342d00c2c0821001d60f10385040310031218501e603458011566100802400e500c04101a01c1e031290b484c1d82251751107500c44070741104d588044504441280e0300a22454192045400001940081e10700301e40ca60780d4800c03041c1c0c3e00c4031850701550384403105a561629051404600b4180c0303038040d880598004404000c000348a85034125810300030300c85c4110003c0c86120455004040300581c4c0b91210070064031301c000c0d40208101c05c0549041c50303012596001e150f060344007000c02501c00d903840144001d0010840c40300641e000315a0f43c0c120340464641e0f4210b0418440c1868850b03800c60801400759100844c5680840e0554030526408407604590746041071200070600c5100d8026403050400f6034000420510b00d060004852a900710203081c61003540350f60650194849101c14041400380e0f22801c005018440c45800144c018110820341640c0c480085400a01c110180f405c20f501942c01d1070507031154014008101d4110211a90181031141c030b4001d003840107584020b8185905200e = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 515635125 1250 515633875 515633903
    0x20c040f180c060f03140f0c04050d050f010b0a05030d08370b150f03070203091003050f1b0f0c01020405062d0703090306050a09051c02120301050d020d 67
    0x281e20160485050081050700c0566140030002491841003680c403608040c1003800001d49401079480c001e4000a000d000300a451b918003110303602d20701650b03109035403228020b4500303c1408030100309040c50070740b8040280a051380c0f43e03080c07200081d4103202d0300d038040e40100882c0c000e00c0d106a0710113070420400051180040081401c0300702800001c9108070028041c11507605801344c3c1c80c4a100480141031706c2182d140380704210070303507154007652041002c1000000006000b20784244221030510358010495407081d043c1e07090040050500f200c0c0c240300008441301007846048684000745a400d0419025441c240052000001e01d070404000044950b400b407002041968440d800303400b5034403100784480d2501d0b00940902194000d020300b000b000c04d40401c900030100754481060010380303802100c0819280c4074171903007600a11015802401c00d0103242c9007640c030068502c200200036011b5500700e40c46090442c6565801e8032081c4600d41c0c0c400c84005012006051010100880f1409244e8030a0100 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 515636375 1250 515635125 515635151
    0x7060806060d2406090f090c05071e080d091406060f1e0301020a02010b2e0c140708030a02011128140d020406031a09010b130305010f2a020c040f 64
    0x506550885000719044c0903044c41b0030500c184684001b090340001c01d20818809039005801d0784282c100c090b054900414131700c1d8410809100c00210580e100851302d9407062044c1e41c0d140100609039007203030300c1b045408024001d55000a41140a5440189000316002181003002800d0b44809840c0c07038100c40c1c041c48050b0380c1e5001e2001d001d803c3e001c1e400104120312120104248d200e0038840c44030b44940b510900500591040c09000c40c03490722070429100d400070f141401c030302c0d40300000d001081a03c81c0c07401c045102d10020005d881008502d800912001c100500d1440950140b0707141c41500e0031700d40303807401031054040c1c41901703c1d810b140c10003881918122141070010b034024046030315143e4002408200480d8507200c0c940c01480041e1078102d0340091031000900d94003042c031a081c41400e000c10b907441c00ad04030804800080d41e012008001495410303059401900545058074032446010003030034041d541d0b0f2042c2c142540150360180890381008000c1100415101c038402e5105a03030742d02220510 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 515637625 1250 515636375 515636441
    0xb01030e0f0a1e030801141f030c0e0d08090405040f0b0406140a0614042a0216080304050d030f0318080c0721030c1515030507060806060d 61
    0x101e10409442c11001500741040c2040a90044566003003041d5042004030b98800d08840c191030341603800d09468421400040c0f40d181c40003824400e0305005d40c00d450f05580c1c05900c0b0b00280029a1264200920320a0130030106048044016103102c1080018458920300380e4091540300b48241d100c0400c484240e01c0704080100304450480754141c0d13a01e91071102d1814a84020760105060800b4091030b8100301004280c8250418054003940c3c5405441804944441010628002940c0138414143d40710f00300941d1a02c11449903820101c40641c0490002c00220884082d103030045d0140b04800e070a5681118034070030815000f803c02d0342e0782e540007203681c0b0b80040200106014200d555100c0014105580c01c245682e80802001c1d54403892a1000c000010410301103182c141c14420201c2d190350420020004042d600541214a00303041d01303e0408038030081c00142c5e4010811200340a031540d82c1540c4c204020307521568003000c00e0228202141845e040400f000c0741e04450002d28021348940c1800b0 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 515638875 1250 515637625 515637643
    0x130206090d08120106080a0504020a0e070e040507050406032016080d02030c07060b030c01090612151e060c0f0816061409011808040302010f1b210c02130b01030e 71
    0x303a040f0410040010940c01031450b074000340c44410400242c24a0b43c00a146002284614203103403a40000007003c2c903009041d00c1c1c0c3c0c500000b42c018082c0313107040b1500612507801405084040303841e1040d5030b2000c100e1007a500b448904100806440c040000d451b6161820b4802021202d03000200a640240360311400514092890641c2c61911050301f45422015100700081c83c50182e44620180b4480d0380c0d000c003c5908a52140c14030b0f00300b41008107100ea000e441c403200300c40310355540e030b03c0d0001e0941c18140c406208101800f40e0306100c0c3d0f890700e50840d05880907a8018000d0008800d0500104001000a26686c015000b9015068010340d6624050740c4448841c1a40104903d0030440e4a8070b082c01250340d5150303542c2860740c032400296641d0100307001d02c0c00003034100800d101c40d1490b9207014101c1c01d0401c1103541c003042040760302c0d450581c40f02e8054030483e0f2000d04104510a040e6030048100d03021a0b5402005c91480d00015102d283c02081c03550310590401d41c4075655500c0c2181c050141b801 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 515640125 1250 515638875 515638897
    0x31e0c031201030b0703090f060b060f03040c0518011d13050607020a0b1005030a0f06060f030c091505060d0f1b1106070f0c1101141c0e06130206090d08 67
    0x4002c2d80755003402d204681000f004802450306014140700042c5206410b402146e900920020703a90808101051090082d006500e205070307800020301090203500c0c505201110b408940781c0071769252681c4039400b0b4501c284285108000d0121003100100c080030300385680300c1c99811408031400c4040e00c1c0c07a450150180c07801c00242e04038030703044400c0c8442e0f03400f01ca51001032481007240c0c0600e0320004c65076800c4140c2c0064000c500b01c15502d404c1160302c5c1c00c00d400400501c040c0304196500d82c10600c0442c00c040c4100003400e032a00d500c0705601040d100c24a422200000c0c0003500307050602e0404070180c074041c005242c200365107c04000e420031000d5400001080155584440744030a00010381c940302e00680040148005042403844580d072001d10b00b00c0c04d03a4043c0a0301141c40c0c40d4801a159110501456410301c400890104d0658800e6009105404025007051104030181c102c21512150140c030f91400c19001402c2c44c8025092000050441c8a8007801d11388560300c0d541c0782c032000e58106495100b = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 515641375 1250 515640125 515640157
    0xe0603011401141c090618140f0616110a06020c0a060608070b07082101030303020309010515030d1422030b0919021002100e010c20031e0c03 62
    0x700031943c1c032180c00404078180b215010300c1d054000c0744900c54500180030010180d620b03121341e00b081000c0c0350880201f50640c1135456800140c0381c60200380d41c601884c082c44c171f648503d180c501c0150b0300006966008521604000c885140050411544180004d08030349880c03052204000001e4041e1000704207a50a100c00740c410903840d0b28291041c0d400b10f5101440e950303c8040d017808004c01001c1203911003548841c0385035a42141d0442c4020313134012804d2400066003040000414107405800451080c4c8a82008125580d00c0585030110107001441c65901948102a044009405181d100002c841020203041c10550802281082107544051900d6640b41c014410401c001ca810b030000e400c540144040c0484886030600414030000c0104064412202041601b10550091040c0c3e84403407134101080c04290746c050029406802030151403000111400307203203070005000100d690800b00c80840074616000051007072010186100b09101021401005080c010200400c018081032402c1481070b = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 515642625 1250 515641375 515641409
    0x70f1706090a152301360b0c0105011403030a080601030b012d03050702060c0910031103041a010b0408060f040507080708060a0b011e12060518061c02010c060c0e060301 74
    0x1001e44101c60040c2031305010881d0484a07603c8881603401002d01003804850400340145c000001c02d00e130050f8401d000e0701f44e0024505500e450190032190607038440d4110542d51000c0e220601d40d40c0e12440000000098248010038410740c400d82080f00809014504961511031112008801c0700500d151881d5070842e849082d400385405001d9558451918000380c02d15141c0005903c0440c4501c1048610490440c0c6018017808d002c0d41c000706e440031950300c0003600c0e4581446d0502504100c9111661070821510001038101e0310310003160152a22000a040142c84030941d009840d080500300f280c450142c90f101007080d0104125000c010001480140b0982c00c4c040c01c40000c031140c1001c198100034081101d0b44040300300350400700c196205e91800b41001c261586c001d0009003000d400c135540c040c0241c080320325030620202075070b030080e04100d414051407004040c40914403900c9500090210b0070074250203000c10080da01c180c0e03260005003003402d1641c1204000981c594026001003000002248007 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 515643875 1250 515642625 515642669
    0x9130f020c0c03241501031104080f011103070e012a050d0f140301031506050306090c0307090b0a05091e040c06110a05120c07031208070f1706090a15 66
    0x10560889009802d01040080d0221613403503c440c0c014411101080740c18407071011648268003200b4485000140544c13100c0c0c03208801a01d0b0410b0b2400200c0d07541c24089500741200018007242c0c0184529203650007200c41e900015540140c0035500c100a00405003200318070342803091100c800c0c1c5842500600b02c42c124000b405003035a02200600c40c10096020071000140c1715143c1101d040d250401d042d00d0007401103402c8080034200d02e07081203415004803028054030640c005214a243c0700210186c84a041c0c883d080c800841e540d11a04c55401b800c1c9503010482d40c140185215004214001d81400d5541d020381180d070034043c252001c50b01c1815004c002c200300c550000c8885a1440410040c1c0718a04460310341c140d07102420841136203007207030008210405410400440d4004e5620604c070f040048040f0701c014100040441d1f1080101d8485000450314a119800040864188c036071050551303101c1209001d28130f00b008182d07030390659903615803d0300c406441034104000d09210003031008a8a400c0301d = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 515645125 1250 515643875 515643883
    0x6030b13020403050c0d02040e2d0f071518060903110915040e160b0703020601060f0215042f01020c06070b1302150309100501050d020609130f020c0c03 67
    0x9a8a40d02441403000340009203020646100e50f45084aa0078210f80c443c2c0005401008a10b0f103003005482101002001102c0034145107141000601c5040007110920721415240c0c6281419903130725400100c82800861503030001c072069140d151a0201c0e4089070130b020b50301240210380124000c5005403900f0820000d0807000c42c541030740c1c140e130b0001d103e08000c2751807601d022181d030071648295110400001c40707090401000c0515400e40440110407961200e080d5034a0340211000c0d40140140c600120b0f0642c0201400580810720b41e00600580c02c040400ca08042c1d00544100c500d1820145420001071120304104020b501c004c000c0450f8240c54400a86040d1050a1103400350005000040c0401c03c514401a4071062150300709600d64503034800a40e11003103170a0500c1040b800801400700c09540041c2c0d456038401d41c000304101daa6203400402c0f1040200b018003d600c104100800072040c00c1c05844140c8903100036201180214013414294103a0700541408a00f070380c0001c810200d01c1c82c0400c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 515646375 1250 515645125 515645149
    0xa050705060a0c03111f050f01060c02060d0c14030a0c021c0512090106030b1905091f020a0e0a06020102090112111b0309060313020907021501060c060e0706030b 71
    0x1984180ba00100080182800e61078000250a01c0f2001c0b149242410051100b10446042030b182194040d06095000004140641d20409086140c0300007185050041ca0315119664006020711704041d4805600307070142507400041c608001e4003107240014a000d8401640c050044100003040c500103140c00240340541403015007940b80c0b81c61000d0601c080c0c201046980f100c840300d040ca4081e81d0360190181c090b04541d1f000510007080038003008484000002d40c0164007401010501240c0c981d420740b25500d00d4522400222074030801d2a4140b000d8165004102034590b50401e40c18030603440b00020200c05484d48001c2c0541d4000444c90360070360780154101c24109003032004101010b008888511503002d4240040e040c0c1c000000c03411141941001664000b043c0101119036074a000b8a070429803c0c280030089004d04030300c80c0460010360000c40c00d1004105110640f001c580e1070400c049401c08100b000c29912903031303201e0002d142180f050098402074079550310046055244001070001c040c17005 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 515647482 1107 515646375 515646379
    0x23150607080307080108070f08060a0507170709090c0c050a030e0a0e041a070302090117060f0406090b0a050a030c03060f140f0103120906320307020a050705 69
    0x105100a050300d081b1400e075145140d8400081d40641540d0088102940101e8001849440307a81d001a511044a1600da100c4000c1c24094018841c815a01c5200086a01c00c0612400301c05000e000b12a900034a051004150707552101c036192440346400404010104825120035990b1900c00d1019001c0394001c54101e041c1031811000700c1c91218000d00e40d40313450742d0000304154003900c06d590007800181c4074540e10903102d000e42000a4001012564442e4007403e6801c0c1e180c80354426400900f04094000a81608110400401100c241d01251288090003024000290b200c01c09900710f036807140000c01c45240f400d140a01030511220984405c0d904a4200046c541d03020300214102c900a03c462407603c140204102c0b00c0500d01c0c080c02d00840c1003282c120100481061236a18a04011500c0e081417849600c2c02148580c81036668900590107003003010140281844000000c03d01 = true := by decide +kernel

theorem cover : BRFrame.Cov 515467625 515647482 := by
  have h0 := BRFrame.cov_init 515467625
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515467625 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515467625 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515467625 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515467625 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515467625 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515467625 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515467625 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515467625 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515467625 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515467625 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515467625 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515467625 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515467625 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515467625 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515467625 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515467625 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515467625 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515467625 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515467625 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515467625 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515467625 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515467625 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515467625 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515467625 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515467625 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515467625 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515467625 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515467625 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515467625 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515467625 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515467625 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515467625 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515467625 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515467625 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515467625 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515467625 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515467625 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515467625 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515467625 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515467625 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515467625 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515467625 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515467625 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515467625 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515467625 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515467625 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515467625 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515467625 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515467625 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515467625 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515467625 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515467625 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515467625 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515467625 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515467625 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515467625 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515467625 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515467625 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515467625 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515467625 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515467625 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515467625 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515467625 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515467625 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515467625 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515467625 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515467625 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515467625 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515467625 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515467625 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515467625 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515467625 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515467625 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515467625 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515467625 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515467625 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515467625 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515467625 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515467625 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515467625 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515467625 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515467625 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515467625 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515467625 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515467625 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515467625 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515467625 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515467625 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515467625 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515467625 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515467625 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515467625 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515467625 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515467625 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515467625 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515467625 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515467625 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515467625 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515467625 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515467625 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515467625 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515467625 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515467625 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515467625 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515467625 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515467625 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515467625 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515467625 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515467625 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515467625 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515467625 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515467625 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515467625 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515467625 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515467625 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515467625 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515467625 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515467625 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515467625 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515467625 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515467625 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515467625 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515467625 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515467625 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515467625 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515467625 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515467625 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515467625 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515467625 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515467625 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515467625 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515467625 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515467625 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515467625 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515467625 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515467625 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515467625 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515467625 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515467625 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515467625 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515467625 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515467625 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515467625 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515467625 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 515467625 ≤ n) (h2 : n < 515647482) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
