-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1267
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T02:04:45.3616+00:00
-- url     : https://prove2.me/submissions/8bdd6bac-f055-4eaf-b260-9030f047f28d

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 227697841 ≤ n < 227877697 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 227699091 1250 227697841 227697863
    0x21e0a1412010905030306010906050f03010b0c160602030a03150b031503120a0c02090108011a0402030c0c12030402090906150d02060909090c100306050630010902030a140708040f 79
    0x8407003401114000c0c0c1c003030005550340c0c0c1001e000141144003998001000c0c01018881d018004901100750380c1150041809a50384114010f036103410504003500040c82480402c2020540b50703170000152148010944042010500d60629a0f965501610564010003410800214140c0014042c001822000303011100400200c2c0412486908100c03c002d0014200c9101d00040d0703e043c0444900422a40c8020043c0daa140c0d0002c0014201c644861401a0b8002003c03034015620700c1c0480c0e08400319601034490941e09074200b20301b180c0c01640c00742c0c0b02d6060742012800e04180810940e02420000c00250b01a000c02c10078040070700c0700e500c02a41d01a6040c051120303e40c595001c0188a09181c101030900b400c1780b1381c00c2000c030b1195010404105841c0c01003e000039102c1d078046440400c450740e60b08194041d04000084400700c2143c07141580d48401e80005035204440c1c016501410345d10200b03010400409071103400e10701e8100c0b2410700240d5007074042004907030070840366000c0600903004462 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 227700341 1250 227699091 227699119
    0xc0216032616121409060304030e030f1204080111040807090903051605060402040e0c0d08030c0403241404030504050f03161203080907050f0907030e100207021e0a14 73
    0x2000042c00c14054030552100e4411060300d991228101c0e07440e4080600440c01d103800100801e025000007400207040c014000c2c2641081e580c20000081074100300030031030b400d248408440c00d0840d04948104002c41d03003410240c0d401115104240c500707440804004001d014540b04000015140214064060200400048180034003080d11a5500360241c0d0051000381400c2c8180411140400d0040041e5040803241d0078081c6d561500241c10590496050390303c81d01c1e0303200300700b144e03210310f42c0300034849820030365102078003200f4031114581003050341010040d0391200d00ca40001c3c04021a00100020400c00c000d101610701000c80035602c3c20301808560040300d84469503015038025030881894094158041020180c0c884011a40050701c00050322100d8500350104100c43c0c00000d02c1403203000301c0400218518400e602000841000c54101d48400084080c408000d50110106900890303011090880c00b92001c1010003c00d00060440c02d4181d262034940c1c0f6816840407189540500f0b22219a0 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 227701591 1250 227700341 227700367
    0x30207081306080f04050c060c0c0409050607021501080304090c120504030306141909021c1a100f0c1118040c140d080316090302130c02160326 63
    0x1485040003001079042906000300600014002044981c1e41d8070190204070000f140801c0c0704070294000e07108180c907520160421403c0421070f1030010b4110b45001e4109044c40340004010b4010380440d02a117440300e1040080c01c072803000c01d008440ca2580100403c1100302c0c1950f1240a8668052500e14051040301990000b600c1c02990305134000b81d1034040034001d84203400e008214400d401c490702c00c03020f6440b80705924501c03101c1c03041034999580401d1000200840250b400c40380094140200302c66050000e081f442842140d1006006100c0341c2d0944030100c3c0505030021180c02d190700c41285001e441c2c0d841d0703030300c081075a001e0030741010301d0003000720514200000c0c0d28059072140300d044a080c0c0c10085034901807080b45480600ca1056800c00030007080d031410803030b90042050040b0030340c51201c00303030140c03004401e69000a41100a00c0c0c0c1c00c21410499602c5161440010f070f01350790405040303c02003031a21155001c080e102500c02099260301480b008101003640c050008900d0034214a50411 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 227702841 1250 227701591 227701597
    0x130210020106080105010b070209010e2205010f1b080612071a09030f0601180906060b030a0218242523010c0503010308090301060b0a03060f3303020708 67
    0x1400241c1e459100a2040709005e001301c902504102d030410341412107540000d840c001041c41110900c1c0fa4010102c0c0c1510761018030258800058000c10801e090149003550003070003200c46040c0c0795171808001c0c54a450014150510290a661b1001c126480b07900802c0030850080c2801100c1d44250b40c0c00081e0300d442d1403400a44005811741054665104805141c1840d078003402018094102c00010b0214015541000446032542040024408070354038010004281c1c64001d04103200020081020301d40b4990020f201401c404420209009a0f0f2402d000501d6404442520301c00349040d02c142c140b0301c0d1a006004880700c1240f07141c400006c08081c421300051542416945400c02142d00148034a0b0a10b0700400d10340c1c104000c102e0014829001041408180001088410001000c030980e40c0c007500300a000e8405480910b0380e0703408a00001c0c0080605109000c248000c1c0c10340011100d034200600895415004215483e0729528005185e4210b541c1c0202c0040c9a03090211038041200c01c009 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 227704091 1250 227702841 227702869
    0xa03060209180907030308060a030819110604060506011211040513090b010312020706050301050a0902162a051e0103020c160b0a030605042003070509060f120c070302070e1302 77
    0x84e201150460500038070902005200a00440c1c10800810010352000c040b0345250038003001000550900d035200b2540b03805004410507541c42020300748400d00c410350703014178000c0000741ca44590f1a03029902182c242d4002d810b103507940031401c0c02304001d2818584240c051021450800003080210b40c9e0322505004420f800640d42030700145400c1d1b030030350f404000242c0684183d080643c21985001e00060510b20503001d200302803500442c070404201c0035841484c010b503602c0014a243c03903a011104903040121000c20718400701e40c03450001490308040c2c200c5800c0025001c180020a040a401940650301441000005124a0b48942001c0c0c03002000c40c0098401060055076507622850000e0684000d50000c5114526202100c0302d444520303d1412035050800b0002622541d40c0041681c0034001d840c83e140c0c0280e400075400c02c0b604075207801031025442d03150000d4140d0301d640c04009100c1c0a0500c00601603404014240a903e1036403255a520003e900c1200d09415040d9001c210980b4070005 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 227705341 1250 227704091 227704093
    0x80d0207060b01050403050c0112020403051e011d060606090a030f1a0601030501060e22020a0909150518040501110f0a030c0e0114090a03020a0b1909050a030602091809 74
    0x4000007080018000c0160440c000d180c940e003805e096031112034603000040c0790342e814403c1c1301c04005840c14454040e01e0045030444140c0705c0181004103012118400c0381d56400203540707420078955403906884607140a0a03807400051040e0b55a134420b00c8000c1c0d20494000d40c5c406100c0340000001a81080c03100c44880c030401e16201c201d40020031880e40100d010380754505041c01c01006020b202d80c0040b240300280c00403a000540340080c00c0000c2c2060340d64596844415000103802066030742c00001000c1100c581e4141081080c144200803048001c89020740e0398444c1e1440102d101c100404ca840c0c54016008000005000803501c126560030b82c00720011218000012907a0b8905075094802c003618848542802000307443c41d840000e000a40801201500328804240e5420540f070301810305020f1640500106015910b4000b41407054000e058101d51340b40d03039a80510180c920a401c008200c90010f0204404d036810f42e034882c07000e50000c03145d013600880315603000303075040c691035001c68019802d40e4 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 227706591 1250 227705341 227705347
    0xe03030c0604081b07060c02090a1b0504080f060105060406050703110114090607090e07031a0d050303040516080a030507151a120c1f0203040b030702011b0c150c0507080d02 76
    0x5504044c20001111342d0440303901040215000400000080d83c1115160055034508092600421000481e501c51408142022241710f40081c010015142403208a4941ca1660000315641c2c0800f401000d80014060008020035802000501101403180c20708062083c0c0e201251421100308107100c41e002c180010a006203104240500e54000406192900036103080003020304a424002d8254410559182201800080c010325140c00602c0024403242403907181f414101d03030b650400e40d000e071024000c15040e01c080c0e40c0841d500e2021201900050950300c0350715203065945030030200f0141d4000c8100c051466281c907041c814558100440c41c8260310010800c02801b00b504501640f440040c0e100c3e866140301d41c1d590116103004454841d11f070818100340000103e056018503400010003c0c4084140559503806401c29071481980308a040407400300500e045030054480003024103002b46c0300200161526081c0c202c0c000003092030408928209041ea00c0c1c050a0340171502d40c024255000c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 227707841 1250 227706591 227706607
    0x6040309050906091f030218071106221e120206010b043005060403020a02040b09010e070809031b0a050c0402270f0904030f080108010213060e03030c060408 69
    0x44030655026103819682000c50b89444008581d075054003600c44010b10301405101c044c0315000940c210040c55000c0d10901090208100450404d1826154080850420030503800c1211000414038494081c0603240c02101003002c0300155140074485040d1012000306580c41008440310546481161198040c400e0224410400034100f000680103600301280801c0104861080e2000144042010b0250014907113403c540b000e00c0640c1d0b41000a0403400342d00100003c0c15001b01d00b00618600940d024000c10121800300521a00309002e58125500a04c0c04900c0c1c00340b01d82d007007642c4a0bc81740b00712440e228980d401c454600440f0341c008030107540103554032420008103106090a4080581d01941040b010840100c103102510007032102030a84042142d00e255141c0c54000500c080281c0680381d203090500b0002c00260200b400b03c40403c40b01c000001e0041414800c5402c1d188d4003050a006150900d50100d442000003c2050390500c803d010400c5040c0c018422a401603200c2c00740c050b595121 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 227709091 1250 227707841 227707847
    0x1030621021008010f030212070305062d01150f020a0503043003171306110c061e0a0902010e090f07110c15032703030711030304170715020c060403 65
    0x3001c1030b20301001100f1004014a60f0341c400d4000580760304441c0c510341058440050351a00382c041e4005800c5112752018403400466408906140b4a40c0c15440310a00d04654503200d08000c00b845469121101107815052151041c0b00841c11b0300706905c103413008040d007501c889103541c100d6009060f801c4a0b07038440b51100c3c0c4000e103500780701c420300c550f07841009911514060036013400c0c44030394101c00315000c0c0040c8007128080b0300c0c4000123902140070001c05030760840f042c190f83c2040680880600c152404124000c0e041004a40c140c0c80e120a105401d07955003800401508100004906000044204001a03540c141000f849148600c0c8241084e00c5c11010062108500280031245a0010001c0d0052602c0383c0b1102002c281c0c0b880c0c0c9e03084d541c0c1c46000c5c144841045d1034184076442c0d800010000c2c403070b450201c0114011003203135030385850045000f180c01c0d031070384401d540041910342da00e000d9008081444d0040d102c40b601600000344c0e80580a0440d105903440a10800300036000b203c200b200305a0 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 227710341 1250 227709091 227709109
    0x11040b040605060f0309100e03070c080a0b0a0c05070b13031b0c030b10120606030c2304050c07050a0605060112090525090f050a0605060a080103030e0103062102 71
    0x40844007801003a250101007800c0380700b40703400500314090010005144000400038000c5104c05100300700460140c440c1905c1c0c9035001000d00b202c0102012000183d0020000340b8241c603140c10420000458030780c45c00c0600107001024180003800320500040703011500c0180c407280b2481105d400c0b44074101d5685001804600c4001c04102202071260240d000300d800d0590420036039901c04145a602e40742c201080782d415010360300403c1d100d45940410700800c00720350003441c1100d204800e000071603500e039824814440300700b00400c18040c04810001119162035001190080c0d0202c0601e032900c800742d2039281c28252005070a495040c0c03a4014420296803220a0201c01070402d803041156041550305c01d51642102301030b000c800d006844c40300352702c0d840300e078000802480f2000307080188161040820014200c01c58614510310318040b40010182085030858000710b01d40d95a0301d29903821903a096903000c183c0e040d4a810540e03201404102004c00034107140c0e050120001c3d04079800560310401000c00 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 227711591 1250 227710341 227710361
    0x1009032001020c36100b0f0313030c140322150e0a050405010b1803030a0813050c060c010b0f03010b1008040c03020901090902030f010c0914030a050d093003050d020c0601031104 78
    0x408100032111950008000380c0b90496254032705040205107500701220b410306400320150003864000b1039415103d800100038404000c400309451110084041ca50000202d10310a1071a0904010141c1094600c500f2070041605002070032013010b59110320201d42150001d800c40d01001800242d143c40c0d4a100da5141509103804074004c3d4604003600c80d00a00e4560050002c0c0c00d0107440007040401c00c0001d0000c2d000080f00903040c252103281c0c804075203000e4420b044800380240008180c03c00e290606000710b82c5200c10190038269001c88010301203943c10300050040d100414207100220041c0d60707a03001d040c0284194040890103214034010035040201501d1300303003090ba150002181009401000340422250040e20034100e0700403482c017090400c180f0b24001040d40c0110840000d8903034001c0460800d643c1348011003520f5910081004818203401380c1c82c00d2010040040250000f44610000d02d41c440d1001c0e0050f08081c5500e03400da103081020303001281c071180300000115460829228038ac46d05 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 227712841 1250 227711591 227711609
    0x4050c150a090e0c0706050405250506040e070c14011a0603090a03050307020307060207120801120c150903020d0f060f09030806040f0b1009032001020c3610 69
    0x1114030741c1c0c0050540309a502c25007900244950004d040b0484c8441503030981500071308144150b14182c075060340c9030b03100b14515035012100e4010f07c00303124000180c010b05644029150520b0b09051588000209030000d0030b9008004000610900044990018010011040001141c103803254000300d840c0c5880412030703d024a40c2801002100a000036045150b1905810326698079141c1d6031f012805c1d0b20803c0c6010700b10900000322034003080120001d51110301c0b9183e4450790180d1b225940600b19046880c2d021705182d45e6004240283c503221030420f11007208505210008130340d41da006c02c550340c0c015403003614210001001302d421b11035240a00c1c0b16044110508000600f01d0381e40107850020068a500d000c1c540c0e5000302c501602c01c4d58052131400d0b400038500d4100c0047e6410042c040c0000d400100c42c0603040c104201848a003e6003c203100040c142c000e805103610748010310041590200280c2c1004034041110301c01d905201280351000300340d811400d100740c5800072940703803131002950098020b = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 227714091 1250 227712841 227712847
    0xb180405190206071101180b030a0c03050420030309130b09060f0a030b0a0e16030512091e010c06020d060f05150405091306050f040302010c09050a05240304050c15 72
    0x60f81c410046403d0300380d015164082e08a40c4500480d802c1c4203108518002d0403481401080821091000d18402e200c020003d0003040d134143e41c22001e903101a01c0c0281500100f4101c0c028841c68101d0700054080080c04481c00d0885150016107002c40001000ea902c0742c0e515003982060402039011648814243c0d00c03420f40c02d10142c003103410341e449480090041304059010445040c40d64108511405600003120318400300083c8002c06c032010351004440034410800303220b114a84110a9484240005040307032174201711904100010003941e800741c1e041044620781400000d0301c41c03001d0600025420703400116903047c01d20072400d4200ca90002c0744210502c0b491003640010741c000f200d0690f103090710440b1441e1a030300e0400c0040d00880100034036890511040003010b505940000d4030841c000e500a00600744071000c00d584070081801550f401c40c103921800d00680c2811704100740103100855034038030320f55202501d040e0f440d00180d40458841e00800d03041c000c207180001c001200c242d040d4012900d = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 227715341 1250 227714091 227714093
    0xd0e01020d0f020a020a0305060709060e060304020f0d0204050a06060f03020309030a1809020427022a0c0411040302190803030106300b1912080d0b18040519 69
    0x55100c2040001e24200110441c1201e140c030b10030b00c625002941c0c05003000000d192246005d43c0c5030039044030072030009042100009440c41c401d40c0d14501343c2d9000b5260b02d02e0750710342d80c0a010780324880c62070381600b12041500403070041c0c8aa2090501c00d01d9880342c002880b40c2841c1000b00208038000215003007500504c10311211341404805c4030180145410700e291107a405100444440c5040e501009510b88082030001d85400001804080711424046147c45007075600d850808074007944111003218003484451010411000141101c2046884211141c0d0b42c0d01e04c0c001002d403900c4002040341414042401c10850030003210707502e404245802003020300350070110481d5a82c001442040204a028038080d104128404a01f0300303c2d43c40240c84400c0364480e071030703200080e122289031103000f00c5400e2000c40850b48106407110646a00e104000c03140c5560b0f072500d45a58002c0c040d400c441a0341c7e030700703c50b5166450501c103030717000344100c001c034080d91a00341003041c24000c4189c0000c00740240740e16680 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 227716591 1250 227715341 227715343
    0x10c0e0f0904050a080706060e060109030f06150f0303110c011b08130b0408060618150409080d0c020d09120305040621050a02121509040221010212010501020d0e0102 73
    0x11554110507195031807603682c0d500302145010b0044402804040c4001820000c1c010b41d0303009031042d5155903404085a48800f030045a01c07010754403020700040348031154000042c0241e0031084d1030b00c094041c0d01c0011521400c0030f086e41c800e80e52003100480c1403a0602031110101f880b202043d0302003402c1490008190307150707250b01fa81200c507004007404030005000c0c9205640300a00e4010b400007070f88054447d92103c000d00d6a40009582c035070b100b40041801c200007000c80240041c401e60a0345001c280f014109130a100c041d10189800721aa01e400b405007941062403480340c41944c002d150b005124121554501510003020b80d0400b0005100700f218030f0f00460341003811101241d030980303071000803151000a24628100f9034020805030b40c2c10f08061000021b85900a0107588140e541c2c0f5550b03585400c0010301c02000000c480c02d030004030107000038000d442d212629038004500b074110248500d800d19940c60032030340115080a40da61402005000a507810064003111000c1810078a0501851000203 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 227717841 1250 227716591 227716609
    0x11030106080a1514181b0a0e131e050907030803040614010b0d11041208071401020d020d0e01141611100f050705071505071b0b0108010c0e 61
    0x810034841500c011a6a004007907100f07040c90b44a50b403d40b58510385070100340c0001c491100f40c440c850089950003148450100b002c0600071125940075211160000c10201d166400c096092006e00c1010607520180e91944081c0e00074072001d1301c4001400114010034014140c0c003180d01e00d9180e52401c020001c14520001710303d401c1d40d0b000b4144d10744030355032803400350007a15151900e01303141c682d50800003405400c100094012003001c0e19080c460241ea4030311581890040e8400c4198800381c1c42d860501040c548001030030703014001d02d00d443c601d241d106201400c2e60f0003c0d840b9412980c0c0015184503080140c443d00804d0404034000344000c00c05006200e800075009001c410320a2000002100d0a0b400345000c0307c6500449029030b1592400300000000810642d0b1040141302c2c01c220010b10618440c000b142c8480d0350020601362001704074400300c2c008020040411051101400d100030483c5100c0112802c90b512414840c4200d41c1000d45c107500b9540c180f000d02c824410108500200b0f69902504 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 227719091 1250 227717841 227717849
    0x5090304030f06110d02130311042c0a0b010f150509010203030a0b040e0106030f020910031e110a081f05060a0e040c03120c0302010606020a02100e0a15030b040f110301 74
    0x20203d40401104c284584034819200940c80003840002c00c01d840b0380c10f41802a040b603004182801050042c6030911042ea80070f80a48035100c40e5541300c03a1030902401d8158413018041d041110408050340d5102c080c02502a003200b151100d2805082100580c2030003144901b11080c0780a901b880c04450000c0c0d0b40e8007025200d80b07410390b21104000700544460b4021254039460900a0204990b00d0900c1a400c0840c05416400340703840d000000c00d40c000b0001141c0c11294408100300304081032040e6a904003043c08002c80b41d000c40030409200580c0d0704142c500242540e1701c040c2285800d10240e0b610070f44120384603800501d0400c1c0c100700050f9103144900c82211001030410304150343d030380713040c40c501010740c6c20080c450030001c290307000f510303501248424401c3d204e43c0081141d140c070b40070306036076441c001d610003584142c0c00c40d140d22200380702d0b4a1130038408038041c10040180d9100c2d500d05085100c2c1080038400070f0750301c0b01075a0003450140514080e03110a032204020f03124440020680324801402 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 227720341 1250 227719091 227719103
    0x7020102070c2d0902121008070314070e180f0706080a24060c140f0c04020d09050618011805030d0b03030d051f060f09140f0306011805090304030f 65
    0x4440e4503e0040602d000010318104030b20840c00a48901400c0b0094020303104810039081814001078803240c6040d130036015074001c17a008101561070b5507241d07a0481c031540c410310914000c1c1c060000702c1341c41c0d1904440c002c290b40e40708515080c541e4202140b52058003021a0010744c80000c00708211504400440c1e001464901e0101e01085100292081c4044054815000010342c10f0001012544422810310786803190750345038040212031040c2c5030364090501c02d0300415040302d048680c561900390300a20481c840c003207020070140502c1c2c44107400d1460481704102c00d4000c02c151401507031000c0c0314001d400c031143d001d91400405151101c0340e50b80101c00000410955492040e42e403594200152000c449000006100d20300d8044000e0f680022808001ea040030b07a01a408902c01d401400741c00c0708589555030340701c0320b1890650301c0083c1e2480040515088481d0320384481058809011840c040c002101d894503817000080302c508120703000100b0954990b0401c1c401032001038074100e0b040d02600d030066 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 227721591 1250 227720341 227720369
    0x1309020f1507080c010605040e16060e18040506090613030203040902030403030605060a0306150503070c0605070908010f02030906010b03091b040221150405010506041a2a0607020102070c 82
    0x1101405110b0038902070210340001c5403640740f502c1e05410241c10ba5034180d400740319042412101958841d0785041c2004082035400040c45258811980c0b03100100004202034070660084001ea20403650680342940c250300308000b0040d0b4814100591600180601d041520307482003034500035102d0040d0702503100c4103070300040410140f604c070342c01c05806040011700b4555611900c50b4050010306c3c881c480c80d081d40a1261402507468000c8040d0b81c418030070b640702d101100c80181d40314030003403070f00810050170311401d0350300802c06820920807908101007000c1c0040c1e4908102c0d031090f14050059010482010042080151000c4089000000200084410101240380d03000103006805812480302800c1c000b1008540c404d0071506020313010b0500c0348c040741c0720440400103000541d8401d01849400c90b0b0200400c01c0302c0d40c4142854407100407905003403030805010a0300e81400c41500c440d1500c0c01c6c40203400282041c04140a0150040c1f243c0c0007c51404505584100d0002d0043c410702d1041c0c1c8083d = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 227722841 1250 227721591 227721619
    0x170108070509100e011e0801020436050a0902120601081903020f0303100e10052404030804080601051e0f15070606060201050106030b03011401141203181309020f 71
    0x2803100d0300070b05030701d0118512640c0c49906e5010b81002c8561040400004c03071000186407170062003280c003a503412032002c2c5001a6800100c008440444031650101c014070b03440c0f030140841d18811140225449000032510780080e00420520035031201e2080c0703090304200b0040201910015980400402d01d011110f800707030741402c0c1a0305103501108075450074040001001044154400000306850403941805156118109070708084d0069010769030704440031020300c0c1021005643d050045505402000d45001e490350354400e550707040341d407102c034136a400000103201ca440c2018140c501000c0181050f90f808644500150401d0420400c141c09840111070100400c0480344c00c817031805800603010301c142d50b901c0b40d00074000e1500b4803401001915080e0030840e24503040c001d00f40349504000c400849070b401e001468240c50050504254071200c1c0ba007290036150700910140c43c00210040c440b894510003c010b1003007201b6886c04a5220626052900006940f11055620004410b82e602500880d01c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 227724091 1250 227722841 227722861
    0x90e03070804030f1a070207030822090e010b1c06050a0902040e060103051603030c0602090a0305100515010c02060a0c02060d0e06090d090f0603020903030405150307170108070509 79
    0x894038050001480024040280508074070b0102c0c61501ca140641c8404440c003500c140d0342c21007958111b0058000c0c500070408140c4440c05041c51640001021150340b89100007816680e4030b0394840034076181c03a01c0d45100500c0d820300c254100c0840030f5a0800b4520195200700f20011000100181003e96900118181480c59409200c91170743c040c0007040241d03c0c906002c1c0c0e45a030248030845123071203a80e101248586100b8101401c07247e040c0c81d800d00c980150750341ca1010f50091030081d84c000c49004000800b2800420004080c10300342c1900086900784a880c03280e002c0c284113419814844c8000e40c000062300e03000c089513100681468001600c40c040e10014059100d20511020400d00300980c0c2c440d181c01c0415050b0290121104541988504a4082c1d5131000340d4400e40b0348100749803404010582c02900100503410005003036030320303140d1202c0c00034a031522119010030040d4004401c0201040d0040994070007000c1564001342158074000005542d4501400391500400524010448800d4 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 227725341 1250 227724091 227724097
    0x907150201110f0705010b3c0303040308130609050109030602031e1006030614030303010515070506040b0906090f03160c050607030509180402010f0c050f060a0f0f15090e03 76
    0x2d0300d42c0c2690341c0b00e1100340214140c00c014805c0d903095282c1100b0021514246804211b255150340440312000d00d400300518981403028007404a090546c0103191903551b0a01c020405188640e015a494861020f030b00a1103c0098004809000b2000c5041c4001c1c4c0e08919008101d076803124015942c0e0b07554604007403081903000808041700310700f10280000b40c002816000c00342c500659040041654400030b04e8244480414080c0e0103410400040c426800c00050b04c100301003961900e5403420304a666450700e800c03000c40b01074444861610a10045040600c105500051081c0050180e88103843c0d00c15142e204240c210807420400c1c202d43e8040200b081c0607200142030040003507483d040c4909000d03205c1d0b40529061480342000203815803041c03080e00030179030041d80c040c0e448a000000c1f00c20242c542c0d1031881001d940310300c60f113400482090410042144125a410300100d011003287c1a50710076503031003d608003055810400c0c040c5142202c1c4050204507601000003044005148006904501c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 227726591 1250 227725341 227725361
    0x1204050c12010b0111030f030f09070315090b130b15150f0403030e090c03060d03050f070f05060610020c091b0304050a021c150e070f08060405150907150201 69
    0x2101d09a4004100d1006510241d03c0541c01c1c5c0315041030400596440d0348911440900052526091004c220480300c65103c5503030082c003200407903007015120b0707e5140c0d2a0100d0641d50108030b032070b103001c481002404c11441c2d0b0060b825100080c07040502d030b07480c0e03900345800410501b100080b920f481c00f6039035100c10380441c00d0750480340a1691414520400c91340c2c1d81c481d000c10303004030f070364400d65810070b041100010b8840c505035580241103840f05030402c0140062160700380d080080c1404080d0400740030350001e28105229104a200c030b982c462034a1420650f0003450071388214400c64040c02c6480d00420507000c0308104036511169030359a24900c0341254409178051021400101c20001007120014111a5140c000c0794541d5802002d8000400c03005000c082c01041841141002c03503d0703800941102001e800b4000603110310742d8a41c2550302c001121035000400d154401c0e4240f206100e01440084034800300a02d0500851622080c5035a035031542d40f0845a5400c100c05442030302030f100b075004403a11 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 227727841 1250 227726591 227726599
    0x20c101b0b09010b1504140103021c15061e0305040c0f080303010915140d020a03290a02070c03151515020d08010810020d0204030f2f061204050c 64
    0xa40024200014644800c0319502655071a140580b5030313600c2c02d04c021001040c02c02404619042c18814058509000c0c0c40c09141816000e005c40d00010a2140c95151074406c0e94800140c1131549542000d003040712346c0e12080a0010700e08100c2100c90504d501020240401e04001c00e080c0c5952030700341181c2100d54080c1c4040c40007150b001c80c04071000300081d8120342c0c400b60244022020304126501d0001ea40c0b08821503001840310061040c00e02d200782d800c15a00003020504d100382d80340c8440b00c414400c1d52a18503202c0b21840664600b00f107008202e0741103440c900003142040c100d5078420b0a40d80786400050710710f024214107000404055001000940740089031034500540c1c0c0c200c0c181421f0102c4050002500070840741c1d550940c031680c0024120386580c00102405000811707c14001c0d0b00105450050940800000c804280c85019170100b441c031940c141125a6900358805840c042111001031580c558000740d681c0560b01e043c00c1e40d0b100064660b1598803921649031040c50a0081c40140c1d0700 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 227729091 1250 227727841 227727887
    0x14070f06020307050307090608070903060b031c03020307120b1305060607050d09030b07020105190b010c080403110109080d080c0a05040e040b0403030606030e03070f050c0604230907020c10 83
    0x79a6510001a40c01b03122180c1310001c8144e110941610380c60f50850301a40040c0c6003020070404100d054210318001e80c0098192070005103101035000c3e004142c10703048000300345c0000600001952000011086016249042207035491314000200c0200302d05c1924201141c132040481d142d6690441125a4154080d081b42d0000e42c2294000e00100a00d1205807901c20300d080000b1009401030161a115050b80c070011080181105000c03070080c00b46401207810054080c5a500000c1c03409401000514040ca42c607810312040480010800602500015030b1500183c00f03c0f8003241c0c20903e004d8000760081d80082d00c424001c04210381e030b40a5540102c0104a2050500003032000d00050903000764003a0303038180201c84c0c80303000580c2030381d90809045081d07034020000d4502142d02c510000042d507200300144c0d40740310301d040000340840d001a0401c02501f030310600000340030b9105494141c44061706843d032039243d02d03241c103000c0c0d201d20986280301e014510f0310000000303040c0300d08421900800c4284010384 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 227730341 1250 227729091 227729101
    0x50904060509101a04090c050a0618060f0c11040b04060611010509160b0f22090b0406030c0e1003081b190803060d03050909191b14070f060203 63
    0x8090079099441490a00441886506900041c02681095140700c07680c82c111011001c2844000c0454003016180c0c00614400414140c0c0e03140b50480c02030500d5600d40c003440c00720150700c1c580100294801400e0162040d02007044a802000800b1383e15040161141000810700125000d0700a054826034003620304030001c11050742282011410801d0302d00200102c0c1e40f0320319895075603200a400082000d01d0000108045003500700200000c1d0310084030542045500204100000f010b1241d481e0091040c1c00c042c0b26028040c402c400040c20b044405008183ca103850340d010240180c007560b41e04500d5940024540040c0130411001143c0c8203002507912500a400d07280b2a0425515010050259246013490b2050102d611045550010724840c41c5407644400c01040081c81c00048091140501140c0c02540c0c40f80002c500c02c1203040150020f401c420518402280e17401120503000019100035014816070001d00e103d081c40d90300810954451041c06c02c00917040c41984024103460000013002 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 227731591 1250 227730341 227730353
    0x31b05060f0705011401030b06040207111903020910030809060a0c02030706020d23030105040506030a120903030807050a020d0509062208010e0d0f0f03090f050124120b070207050904 80
    0x2c40480c1c0108001c20000090440f004000c05003840080d1125602802041e1146042d03030003014600e105600c0c4079441042c550200306002c400e1034075882c00701020942007080d800c0401a6680c004030b5560565803e82c1550340e1030111340140c4515030300079200880c22102c2203000302110300341140c00404403621999075420007175035455445104c2000400310140110f0a040c0e12448803519415144200d00750ba027080140310080900401d520b03414401c01003144040342c0000001d14041003103541c0e2160003421418013801d034070800f41c0403608002c0d0400444248940c003040c0c0d1340f009015850129520003240340051110b0113a90120300b000c40402e402d540d4400d080c0e500c100110390100e8028071003036003454191b46d110120400c0d50b078040303080c003c20304c0030f10740c46000b40d4030110001303040010f40710f2981d0310340d8201c4507040442114280c0d501c0f10010306800c02c1c080201444121903180e00744103030910b044180b0090301420004d00c103012081c0403032030450090010070b001c0d00c001340c904511450117007088 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 227732841 1250 227731591 227731597
    0x19180503030c0c0f010c02010c02040f020403080307020601030b070504120f023d03020301030209012c04030f0201060e0108030a081824060d020f0d1412250c031b05060f 74
    0x21031041d10701482c0390825500400381b00740560b8058440421202075a0240000307008035040451007194200700100015108502a5000b424954000d00d40f0350b04500d0843d81b042c4015085100340300042c8000c10030300c0c20303200a081d90290300c80c08403400083c3c1840410075804003154070740c4c2d0406c503010030066001c0302008203140c2640d620b6030496412910740002c0d0200d1000303000282d0040b052000506c02c03901d020f284d5513620405d544c002541103071106100b5406940039070b8110002100c45884e503107015424066071019124003464440254900047c0170b96900c1094003002c00d10031344c400015819590038054500c9250040143d4400c00c410030305100304418000d92a101c00e00702400400e446042484400141300c1d13020b826103070302205400411040c200c400c60300f160740c0302d0b0b80042c05451504c01c1c0290b141c44030610380840c3d140d0524422480b0484040207460084402410b22440031a0140b56083c0449810410110500f00061058030401e54a41c203d59048900090024001c400403001 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 227734091 1250 227732841 227732863
    0x12011e090b0604051501050c0703021305042603061005161a0a02040609061d0a06080910270c030f08030403031b020706050a0203130e0106020c0619180503030c 70
    0x240071841d50b245010070040711425215403070241902616440c0950181005048280d039040841342074a44e20342c0011080780700300e484428425100c0090000304a5000c00420b21504070842d10456513002c0c0220303800500004110a101c4ea420202d0383c5400c6010300c00b215607111541d8501c143c441454208000c00c07070220040900d414000800088002250348241ca0030f0303e499a4411201c1c41c5000030031510380c40c3ea1912038903a0008040c0b500010350f1201000c0c001450642c0340d0422914207107800d1810b06094190484050341030540c0c48082507005241081d590003112a604a0782900341024404034047e03420007003c4285040040d014031061802441c41039101741d80c14402d1706000c1c210707800c1c00a840802080540c4c01020f040c8645406100981684402881101d003404e80c443c2074040c40b0b040c6544440c0c1d104c850703c0010f11090360b041c4100220114251031807843c01c451098566001d19800780c1603c100300041c072801c1074401d08102041c0003030400404482d203602c8901c0040d03071260200c0c51707 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 227735341 1250 227734091 227734103
    0x16091e05060402041a031f0320061207080601031a011709150103030e031b09060111010f090807060c0302042102010219030807030b091006120204120c0303080604020708040512011e09 80
    0xa03100b00e61441c4251f00a072a4071850f06082c0c82003501191540c05584100039500000030320036881e140a003840c11502c55035043d03440b03640e41d04000d0700150845000c46105020004024140c03030325640c1056038851002078091048441c0d07502e043c030306401d0458401481407900341c42070001050580c000c11110203030f1b0003201500d240c0f00b003151080c20100c121601e081d401408203c0001c040358080c094110042c1580310010424840c401040404c131110302c181200c04210214440044c000507100710001010282021842c2c0742c02d01c201c0126280300114070850300d00740c5030f04500469100744070083d212000e0010150419419180180222a00f2070f9444006482d0261400141c0361204160b030141c0d80c12120b44401505219084900414420744002c54a4003080000340002c60b00300100560b03130082d48071403101411460b00030a23095029024034455401031115030007080d5400222030441e6003c03a00c9106e540301c5101c0701400f400c60f4141001600310b900b42e2200300c408242d005a420903220301 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 227736591 1250 227735341 227735371
    0x7030605030102040e040b07030b040e1e0f060c07080903030a200a021f1407080310080616030e01180c052707030c090b040816091e05060402041a03 65
    0x2061508070300481c401c10941700b9800011401003005225180d0300520280707000305c0d050480c44042010740d18002c0c1d44a0a503802400c41109500c0912004415060302c0b902a100b204070381540181da8900243c0300c0c403031043c0001082010800e1110840f107640c031005d410342e0b450718800e80b006800306042c84502005105c02c00c8202040f10320100e501404117500600402c16500d00d0b81c400d40100070041182410701c0044840380764804a40805000d40610450065543c1e107080134914511003c55030044045a00c01420b201c0150440883c105034844c00d4680003450060603202c04c0e001d401d1a0702480c0280c461003d040301030044010049040c0d420070b40d40c00544200c500c0030030305000952088820150f0544d80454003c52082d005459480060325025050325111760030344040c5c0d0f02ca5402401030758013070103450100c0e2003504d68500050034400010402c0e80500080100324607032000b0b800460030360322000500150342d00c0c0c0c1902d0140084101041c456013400c4180f5071641d0060300da81b68514105 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 227737841 1250 227736591 227736599
    0x51e0a0c06031d0a0b1504110d0506030d020a1718040e010f0c0c0c090203070c050609071a0304030507030f030f0e060604200409180206030403020d0e24210f070306 72
    0x221140120340c480342d06400380e45c4101b101e1114904040d0642e9005480307802c8500700500e108081c0c00078040761100081c5500389101014a0941d50208140640d00540700030808540d6800304c0c2c00000da00c02410030f41c0c44c003401345111843d00381e491050f035000780340000448215005500c4103030480058181001f24404c0090305544400400301e0090200006040502061a964010f141c101c08541020064920030f07a58007810544c00b214038107115031042d05d0401204c207030b603201000d002100c520b50300d00d5800e281e140200030744502d00c805800d020700ca610760000c541c46540101a101c0044208001c403d44c032040050f00c80d4026900d581c412410040350f014a152092031004030740b615480d8032490545007503403d101510b8001100c042c04980c01c0040005038844500841c881c51196000e004420300420015100c8000c01a0041c0103103142c08030801030001c500c0e4191120800b100390541c8480c4850548050745a00703410700306650020609014000340c1c001450b40c0510700a031810320445442e = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 227739091 1250 227737841 227737843
    0xc03030e1305130f060f111206040b0117060f030d020d090e100315020906030a05042a1a0c030403081e07050307030e060c0f06070f080103051e0a0c06031d 68
    0x1d880d80c96100f40d850b020400000c0b070b100c00034070300345115140108000022502c00000c0b0360b407007160070342066000207403468001c640304c0850342d20580403030301040a4180000000e0010038070034140500d00c122440880c0607950b4044140c500342500400710f0b00c14580f05540251030740c8001d017600d008144481400304103503e07a020820304c10710340204a008102d1440d2102c00d03118070003c4c040503a00b0707401c03c02c040302c07038440e1002540f080e0f410010224541c10180303052003040100411049101d034903001d14544160103101c0500440b201140b0310310240580c001c14051520803851000700714840082c0000030000d62002801c2c1d00344090b0300c14016405281381c2c000c101e00c00d0180003405c1d50010800d5400290041104074001000034248a042941c0d0b255124a0a8040482000320b988030004012816078000182081d8840303070700e84031070103500d1541c8203030781d84d8000118511111030903039240c1e81c281c008112117507450350001d1180d14a07959a0388060018240301b4a1f80d0b01c400035080c01004d081d90 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 227740341 1250 227739091 227739101
    0xa0b031c0e040b100309140a20010c210909020c010603060b0603040c03061e0c03140c0702030601050f04020705150702070605042402030f0409060e06030d1409010302070c03030e13 79
    0xd0192144a1390310408100300d0051107089012146550030402110103c1810400c0c05101403061480c40c80c046501040c88200f040207445840c104441900782d080081e052101e84c441d4003e15044940d462040d00d41c085c1da04038000d0300070090080c8085010758141038150007100c101c2e1b0055400f04440180c1c035003445441e00c4102e80142240702c6500c0100000f41e046d42c480365000d91440c0101c51603059881750700b81076030451404880082e464264990203000031031241a00a031042c0041480c2c80141e5022a40b940414412240f0039480803400b11040e40703da03011500c0e103650100990701c2c4035118103141e10301c41e0307400e0342d4240041c070840802243c21070090040320240d5815031903281203078501b02c1c10940040c45c110101c0045010511403a030f54042d00d074003d000a490110300c00300701181800c00314484801d0082c486846030340144400220503030403d02034205a0382e00c0000740d41d81e007500c000603000307441a84401000d2001600c1c00006150f801803554040c400701f1156650f45032044640311080c1c032 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 227741591 1250 227740341 227740361
    0x301231f17070c020d0b090a080d09031806091e0306050f010609050108070813020121060816050f1e0d030f031805190309030b070c050f060106050f030a0b031c0e04 72
    0x9040c080803080403c84501002da8400302800460341a6001e598400710305400c0904ad4000550301c906105080603003002501c805078203031018641c0c074a45030030b10003440d550b240c1c42000a007200c0d600c003410707104008140e40e1000c1d54100405100d58100010107145000d401d00c0b0342d200003030200001040b10340c0709100c25030080d203d0350b489161548403141c0780d814a0b05008012030501400a065410000000c1d4521042d18403064002075503c0c682501e081c04c100305110411010b4585603801d004035071310031101d80c2c0d54560039140500c3c406002d103844100c0e2884415840da21210700c120074020943e102c04407041110403550140400404460140134107060000d00a04e140c0182042501070302e00d4188000a050091400d0110b9a40e05d469106600d00280c83d8900000d050b20f00c141c0c148031040008c443e0000d1440e00134030a5624051307000f000c0380140c10203d0311a2600001041a40e0540d800c1025104401826502c7c040f807042c18001914600d0b0b018035001c81c02d24500008240381a1003150526 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 227742841 1250 227741591 227741599
    0x6090501091509170c03161502060606040e1902161106030402150d150f080d02030c0601060e060702100c02010318020f06130317070203060109020301231f17070c02 72
    0x80c5007490301646011115401c1c0300920b100e0041408840d40d000c01c0300c40001e0b11f45030a81415282481c800300e10b000ba401d100442503610400c28808103883d0081180c0c00c5030412588007600f520740110405c0410010551041641e001140c0d60011008205c5013103404d6100700210003e80c5050001c1c045e441c04110ba000c2c2d8040803020302001058481c6004008a500201c00041d100d28070282038802e1929170f81140e04c03c44025007081c0300e0041304000034210402140000c5040c030341d000c032880c2e50703900c0140581010402015107101d03da48480c0140c3c0c98055000f0324025802418810040c040750b22103100740d002030b040480910f40102080700180f611600a446100d5050040085c0b00c07440c3d1050302c212022440c1c40b040040801c85030901d0b00d0880c980211100d41c2d80d071060040524100c010f800c8029524410801000309070f144840e0a04080201d1101d801c40c00b2030300340001d4401d801c5c094040011040500000005030307001b1201900c0c041808900c001c2c0340c54400b001c07160700003030803802500 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 227744091 1250 227742841 227742857
    0x40606020318010e0a03080705010b030a120c030e0a0b030f1602030d050c0c06131203060e0412020f060c040303030e0102040807050904050102070204090b040210140d0207060204050a060905010915 86
    0xb222880e00c01501400d041070510b210804220008501709511640c03040d01c0c5404040740038010010700b8001c408a0040841c02450051003980303500c02c00c420f0341c8031f180c010b00010100c00301c1054000c04549100d854020b04c0004a02e07903c0340d594440340d100322000316024a4410015a04801161106030150789540c0110f051141030000703040180030141690341c0381e0758144014192050200407152180c4580c15150b001000d10f803038040e00c4d4004800c0d905041c0341c20060207011010b108280264030680143c445a0383e02d15114043c1e080a10540900c000380c05003104002c02860382a0040040320f102e0b0ba010040f440d00d51000c1c038201d003e24099155507801c0502d027001a442c10301583c0c1e4005008030300040c40d01c0302071f500040464540003422150b69079900b0820080d80303007582071003c1c10030950400c2100030020350010000752040c0080c00750303242d0340464980103000385541503a0140802070020034031a40c813020060300604261061034006031000c6401310b0485100781092051520035118451 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 227745341 1250 227744091 227744107
    0x510030c090209011b0804062c0913020d03030b01090602071404051803070b10120f03050307050403050f3003010308090609030102070c0e011d150406052d0406060203 73
    0x181d8070441c00c3d41d041010025507402c0b1151080010b500d21841142d400d5030312450b0085c042c044c000e080d680c2003200001d50045103c0d01226003000300d6040d004442c92490b41d6594400c4a04610752080065001a000c610f50800c140e0194010303460980240ca40100329a0380b41004c0340d0781e02d06405003455480703956a0306030701c41c140b0303400694200c1842c2c4040e60090000e4291945950000b600a0342e00102034400d010000002000050141020061000b41444103444414504807a0344000b07040000000000c1c49a51085060f00d003e0755000301550f00f440c10203010140d8402c0c020303040e9030710f40e000c81822201c20306451444101000c02c10386041d056a10b55165000e07182c2241c40041c0e04002c1c1003000703c0340d5a600b0310081005c18451541c8858890a21101030109641604148051400f21f0801603002c000c0001040d4818400f1840c00004101c1e030f80803034003400a030340c410ba802001c04041d0503104100500d440c5c411a00c403030b41c00130400748064208130070b85045100e90070150b001009050 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 227746591 1250 227745341 227745359
    0xb09070f090e0c0d020105120709090c0f1b110a06020c0f06070b0f09010603060203070c1412090d020312040b07060b010c0c05090405011113030501050f0c040b0a0918050a0510030c 79
    0x4542170050404505240c1600783d00710110604071a03070030004080c000d00780500b00151042c0038000c0e030a4038040340041c0311100060100041104081c4146010000d0001044581c405040c5030079000707070080310516039900d00695074151418036140302c0c6005200040040c20000151841241c00038000d0040b9203481031a14039401020304500d95039502c411010001c110305000a49c050481c0ea6075031040402641081c030050b031841c1e4014607482e0400100e103030a020f07501c81502e0702011708a0740d0a09000052000230310300020501c03542d03c0300070301240c005805e00098010b80b14860050400340140225200119132420701410b00804c2c06011042c28011414615070051303119110f1800010300c08100000400755401643c0c5c070317411034903014a0a004101081c05100c2e0002008281c0e07108034104070092130340038040c2d80a00c0403180740102d4880c0501e40716001007401060400038041f48a6000b050348406400d0890781088a1401c02e40444e800103510500d40c82200d80180844002c682030181074 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 227747841 1250 227746591 227746609
    0xb04180206030103032105071d01030c0509060d06030501051620192f010909020c0c040b031005010e04020f0303270102010b060f03011d04080d0b04090b09070f090e0c 73
    0x20b2042440ca900c400c0040c40f805104041c0250752380c3d04e40c2c2c901c0b18030b0300038900e070340b2a081c0340014100340c201280d40d019103800005440403007404950045e140c07410006100c0007010560301c054041d41c2000305000b03a00d00303401c1002c8006901917030707a10200707040000c9a01e0380b1301000740c84130260b03807285400c6110f070080044449600e41c450344035804040003440f030a140004a400c10803602c1341e80078044501d2581c2080d0302c3c1c0d009100d0400158200300800740b50f0b5450b2132501104034050364551001c03841555060011249003c4050810056541c68a805018030760046504074021641c42204060515000061714150503401d1280d000d01c21098000055050250750014190b640b03640c1c184c8442e41c1da41c1c01030441d07007005075801522585000201c5444440d041e18401d10340704c0c51340500c000308101701c0032038a01515444c400b040c0c001040c80410000c10b541c0b08094940c901c01c00900100c101c002c00c0031011078100c500d024a4150f1a0040102281c00650240000d680440403050060400100f4 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 227749091 1250 227747841 227747867
    0x180f04021f0905041b021b030715050306010f030207020d020f1309050a11040c120c02030f0d140a05130b04020406120c0e010b190516060608010b0418020603010303 72
    0x146115451035184410010000c00c107016010a40c1c41009200c42e0a061062000c5005608080c02803400030010207074071000f02011034540482c0d454411185a1010411500142440300040b82c514901c800c00400942003695081e0000780d6889103801c10302e120b402641c00c00c5400070b01507440d0000725400c0010401c1a0200d0f00e13048002c100841d80c0c0340c4164410044901d0007940a400010460320300604c10504640507540701e60710307019a03c214036a2061030610091216880010000001c5000703901c2d6004805002040d89000561b42c00089001c0e080701c0d0082d209509403114136141c0c04240800d43e40121450307078004030300301d0b82240800e03c041c0455420a0015000180150301c13000070225008446209807441c01d000b44042004940c10724105006040d4640b5540c208264540003103207141c200101c003000c20101050400004500c0c4000da03154940c00802008499600e0b00d0b0031380602030001c0154442ca29140c0c02c284849201c03c0c1d038095850303000f8101d40c0b6580c00c44d50162500400d80c48 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 227750341 1250 227749091 227749099
    0x108040303061e050114030c030c030405012c1c0807030b0103090209040303140c0a141809070914060408120a050f0705150c09010e1507050106150806180f0402 70
    0x4640354460076644000015040b0204528200340000d802140740240406d84c1020420400c4500b0361003c044c1d90b041a1034503000d5940f0b84450410902508000f40d00c441560448400011001a068001c000729400c280c00e0300c2600c1400301c07001c1144010281540045502c00c40056a918400d074402a0004814100010154807640200380080011a01280829034421704418552642014550704c0308032184003070720305044464001c11b2013200c100040e90442c3c0216944041a07000c00403040070460241a030400392814600040038400d8030710550400c07015101100c401c904092045030309580380c080c0149038804d443c008041309980030420110400800340004840304a030741d4000d003a09070107200100000c20020340b00041c0c090006c0c1c01c030307030403400c04004100382660000c80f0408585011508458254040c1030411000e109010005145501c0d00d0001708003064000095000440155030344084c0b0303928041448a20399000e0303c020861425000002d4054907502c017503d03031061000e4 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 227751591 1250 227750341 227750351
    0x1401050906010c050102030901150b030103110913020301020d090605010503010c1e031b020307152c01180c030c08060103080d0f1119031103150411090a060816030c08060108040303 79
    0x1440310b50072a00240c23080071060351100c407000042c200701152800640700715010503103154515568502280c10b0100001c1c0110f04090000381c80301c0600c000b1a20894000d802503564200e54180c050042c07500403002c4940074641030010600c0d00b814880c035550b94500b5100d0050010441d82c000e80b0041c40c00740e80c90200b40e1105006248001e11a030303490a00006078005503114074107460a101856101c5c02007508a500c1c2400d010300b0140d10110098519028040c500141c0d40001506400360a08c2c0d0070684a09100340d6a04082150404d002e0007224001da120f151a50b0716210003c2d1120400c1c40080c2c0400300500401e0303070b1090554811b4490b0300c404403000a561380d203030301458400c0e0812101100340d6401f10010414268043c06010050102032038454914600001c00868200c1d000c41d90031302075a5140c600f1848030a4040840b0184030005004080180c0d80c0c5400400d8003404907105103000100741d011514076400780c003491150324240d44a804241d07840100468007103034010810350400d5228 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 227752841 1250 227751591 227751593
    0x140c19051912091a09010e0d051b0405060402030408221a1902061b0d020904091407060c050604060b03030d11180a0e0c07080c0609070302131401050906010c 69
    0x10720005080d0700c950004900c2000b40c2038082c11401183d400080074444805880315034100e507504480b07034814242003070f003401e090728000300e85001e190b41c030002c10900c00d8a112100075419400b049001440032502440943d8801003400243d0106403801018024140201120b40950000104e18514000c01155070b0690700c0c00c0e01c00f9070a0090304d01068403c0c000460303448652160300c24071141080ca00080400d030618600c0d84c242081111b0740034004503030200d030303031000e2508540403035240040007441800311004904112828450f542e2455000d0b22450100080e4039016052081545400c4409892241d90759102d80010740719914280b68540010070200580140c103108000308402e1000b106901c13082914a01e01c2c0c08180c882c02c80307220b075403d45420080302c900b03020709031751103072540c41c1c61522000b5605d400d02c1035010310396024155008100420042002c0040c00004a90007207c005030343c51b030702105101c2219802c85c0c1c811720326200800140014240b40c0c0c925034011806260031306c1d9080113 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 227754091 1250 227752841 227752873
    0x307080d020a0305010e151002011e0209190b0f03040611070501152702090a12060b011704020306060f01020f01020d0905060601020706170601020c040f020307140c1905 74
    0x300a42039540441e1210201c1d81c035115450240404c00098402030605001400c00b18405c3e8040e1481559002c0c01038260364404c0d0030034410070041e01006100c80c100390300c669029400161001c1d003e409080d04800c60081000b041ea001ca0f03c0f8841800e16046521641c14816072004000b81ca106480c1c002c0034800f005410020a400c500910002070000300004c1c6200e21540c65901c01540600b8007180e100a101c0c4404605000c000c1d443c400603075400c0b032000400c0c4000c00c0c40d4005015560350030032100602920790481401010700340d030b40c403071840060000656007107000c0c1c0d00650981d00001c0050490700f0300659180140b20140111115090130000490a80e88241c0710700042c0c9032105140c04c2003003020084e030b03600f00000340003414849041900c001c055036a140c115039020f043c0c200c04a2842c0e4000d1104602c030490213030042c0003a5508039588c40c0a54010b81c0c1d0b010004440174140e507030003020041038074280b20010000e0501d006141c2c05103054046002c0301a1241c1c0030340d14144c5c4000907 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 227755341 1250 227754091 227754097
    0x7080609070f090f2702040503100b0a08070e0f09030f12040201031508010b0306060f031504080415030605012304060c03110601080601030b0f040506040305070501091a0a0e0304080c01030e030708 86
    0x1c000003505101c4d04110203921200c5400c05c522a001c036005000601c420307500440e00844030744494a000828011080003d81341001c0d65100c860700e8051f2803008900302d4040ea60a40c031600707204c4510005a200d065070941e9900c6500e4929113109000d200c0d03c50843d041c2440d25802c0b0b4014523010a0060990240c1c1c041c0d407010b5071001c4800e030341d5407400541d1414203020207940040100c40613003030642c0d84030100e43c481c04400d42c88003070618030000160400c250742c000d1b20081c0440324850089074094035005030080c00680119800708540301d40c2c0c030440c4042e000100340554a00f103070040c201840d05000391800d000c0c0740030440034011041c10102800f501046418020444c01006084039451818200c201603005003003000b58810725010040801c0740001c520f070b00300d03a00d46441c3e85c0d42e1841c2d05102d80100f4001d00024544078869400602009002c9a1180190800c2004020720010031013541da80b4400c1d4840d11320981c120b40400c40305580244d2000341d0303103450039054a04c2c001d0503a031a0315140e8 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 227756591 1250 227755341 227755349
    0x4050f0105160f02031206061b0a150b0306040c06050a0e030a06020307030606090305031806071202010b031e190204020424260a0c050d0908070b07080609070f090f 72
    0x900341481c00b44030715880f200602100149002035490000403500590310a440140f5040c0910000115441c2d03081503420000300407038104055030312503007441c07a0090300c5428000404c08601e09010101d115440c0c041540d50140e0ba20040300700c14240340400642d0a500142c6402c024014800d03004d94498406001603a01580300301401030f6203107041d00014049912980041041040d80841480018400401c0b110306040c4404c18031503002154000a06a00c0f5081d40108581620000c41e44243d405412a14001c4070440c103035401d9000240880e100c861011800600540c0405011401f0034800303d0b48010a9002500c09480e0035101c14401d41d940c3c0111840b600c000c0c0c50800c005502507405090340e8044400500c2c81e000e1001c0305900e050800c0d002034160342e82c0035543e02c0c1034250b640c020002c44400621a02e03050101809a0810b42d410360007012060307803846c3d507110010340c12501c03070a500c4e0302c03a000092160100351109982241c08401d005204801d00010709070200b100600300c41440020 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 227757841 1250 227756591 227756611
    0x7260109050a0e031b01020708220b0913110712120506030c090c0904060e0106020109050622030c03031514030d031a0f030703020402031e100b1204050f0105 69
    0x1540342809420403648020403451055161800550504502008a46403d10a9040e20b0820050714883d0341c024450500010201400051240c13041400013481403c00b800d102d104141e40c80c1ea42c4840c1440c0d00c03c1100040e405440ea82c07480c100010700b80d1000721450700c801802414200c1c0d5a4501280c041d404546401040b4491400b407019112406104d81c0000107801502070102044041400d40c030303000d0540f4142a4020031b1008041d10386902c040300414140340252001d59681ca80640284070080058503280641c400141c865281c10306a82518400d0b040c4140200c8aa524202d45450105904804040e101c460340c564070140c0c060700e400540740408030b900010828038100b620741380c50400369009141c1081424440c05003a180c8403107200c0011395610f11003140c460300003030400860740c0000390b03c18408001d000351504030f0381d5401c034110b8141d10301c0d0f482a11117602d6120103442620580c0c3d002c4008106090a401030204850b4209209104442c1187c41d4032484c2c82c00d4580440d410000 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 227759091 1250 227757841 227757917
    0x300f1504050f0a0201050409050903070c300c0e0c070b090c1f0f0e12030408010504020a0509010f09020f040302100e040f020c0601051009030516050901051f0807 71
    0x107001c1c0a101542c0480c2c440001072900002d40d0740040d215004034421201126030f218001100c20505000301d032952039000340e11110f000d0320307030240c0a051041a41480e118000040c4e24070b1a1000d20102c0c6c1401c00e4028224504031460040d688403c888010160084510240194800209a04411402143c2100161051400300c1c0b051007050b11243e4111404180c004000b190420340107500d411189500f4030303081001002038804a824100c03a054a20114480018001917400041d40603d00551007203a05900c002c1d510001c1280e8400f0038040d1b10400042c0c0d800401214041c1d5004003078818004115906050f0b982e0001150003a24640d03c501141ca00094189107182070701c20032070541800e0b00700b1401e0000250800e83e8404050003200c0c006e0041d50803216040c0d00811002004662080c00c0f81c4154030082081030300e4000603c1864041d95070400081164586452503104048000b500341900500f49202181c003260050b00e8501407168030224034050720740354503810040150803958070791 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 227760341 1250 227759091 227759093
    0xd030c02190602010b040515100e0a03081e090907030207030c060e031209010213060e03121605010605010309030e1e04060b071407030305030c0d062111300f1504 71
    0x2c255605d050510b845186400108009080508190400303a1000d41b00540244510001038a1404e458080203600020014000082015400003046000090a2110b8960030550003651050080c0b92103141d1214201c4006085148a41d0182100601a03c1d128140b03248648800c800c45143e04000c54071030300005203000401011041d10364000c4000b800851500010b0345014900f24650b002d0a41000000c2d071444c08150b400304101007455820070a81a510f9520b1010040d80c42c00540048449500f0208001000d40c000c1c031410403010340546410001d11241c40820845079951070015024420081844a41e070b151403085901038540f21060560718026800c1c403550f0202d40f14091216a40404000e00010b079104040d40c0d000701c5400f07030490b1a48420041040a0442600001014035900d4428102c081004001388507043c0248140805080c07041d040c01744001181003e1000346550260840300845a0400b540100c1c00038015154003500303484041e4141100980028586050141400 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 227761591 1250 227760341 227760343
    0x41b030b10021c4503080a050901050706050114130e03040b0949080a0e1206090303060111160506090d060f091716110a0b030403020a050d0509010504050d030c02190602 74
    0xc01c00e458640c484c00a2a10b196a0032900d40b041440420810402050000c9070f42d000f0401e4950882d070012081c0030300e684070351800e444841c9282d5160310610345d514101c40700d20380d9442140c241102c0c00018624150508040d0003c550200a201d44c0041d12b440280314110110451550419805142c000648681050004082c0c041003152008151b01c90090000210036004075294901b60741404514460003a00007000c5611100d1700c0c50080c0503c40c20409407030f47c040003c600c80c4009803608000c6c428240c14459036005840d40142d0b1502103414140f15030702d0804041d003070303c01000340305d480e058805680d001c003690340e551034540209458108444c1040b2440200c0f08a02c41c9a00301d0340d003041c52910000c0200c60328800c5c0a0328010b008040c061058462001c0d84020301240c8000070798078205880c0003903441c8000b180640725409094544103010703116004548a04405a42c1c243c1401c0c00c1c20304002d0f01c0030100404406000e294000c0b0304c0181c030f03540740850f04048601d0052444e03a140c00006 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 227762841 1250 227761591 227761697
    0x4090c120c051e13050c0426190210080a0f060612060902030c0409020309010612030807090e0105030a141525090b18040b041b030b10021c 61
    0x4100c40b000c00942061498456039450340c070581450340d002c01d05446d60b00000c2c51900c101c0d0081c140214040c12004c010303000ca00260b03001c0c40346840440e428218020085200c0314580d03076009500c5003044214214082c03040418582001c4c4110000a000710410711b810122001c41d401200866003c450075403024100e032007400c0040140c0030040d8918075000c0003d4100d4410390055800b1030790701201203408000250b10001c090020513a4207aa5000181070240c5070b8442181c1884c0000d86525022982d500101308950403510007074002d01d000d200c0c550300c066403c526105103101c41d10a490b04194252810440d003809046000040c4480350440542d00018490714a20481448554002000102d080408450f9028004e86900b510188501c0008002d4075000d1042c6900c03a00b02882e44034040d00044e604100344010b510100100c4005030300303001120b0915410f040c05a041550b075508030395200c803180400581249000c51844200314420042e4040406100c21512850f00655052184210302c0d = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 227764091 1250 227762841 227762869
    0x7030b01110a170f071a04020405180c01030902030c030105040b1e090d0f0c05100605030f07050f010807020f0709020301060806030102130510021504050f0c010c03050904090c120c05 80
    0x3909090b51152640d143e01c2959024181c551080000e42c0500d804000c0d0a40d80e44550044401d85805503003c101d00103c00c2c142c4040c1e11943c505408118486240001031040214020161149820820040d002080203070300590309030007003140300c00282d6000c3c4542c0d40328900c56004407815007408000f011511300004181308070449a6030034801e1010b80050b040140e040c039494000084c207021442220318540c0d241d03005040c1d2288001c0406201c10b5900a60103480064084504a00c8803115a5640d15590303c1020b41000109080100300e500c60410b040c1d00914500460700c00309a200300c0186042c030203a201b2000d15901000510503150312103d0395410400c101c0007541014218105a0380300c074214407500e80300c5c101a41500200500902c0010804036500c0101c84280c038180c20015102c01c2c1c951040d0a0a016114285501b907000d800c28400c0190940d403010708050000c001d101c010007240005940035907084100207988040a5544230300f44d0b11a4082c010100e10b0002884100d90320031030 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 227765341 1250 227764091 227764093
    0x11100306090e0d0e0910050d080c0d0206180a0201050f0304020a1d061914010f0e030322120b0406050402040603060c0203091008011a0f091906140310181407030b0111 73
    0xc241b0180c2c0700549480c40958104541844003400c007032030403401a10502d030015210f8000c0044800111b40c010a02611824010644c078020807521001e49440e00d10141c2c000b408038105001c2d001d01243c243c4d000c0c59200b8070103840202c1c5242c0349c40311680100e40e40805680d4140c1c81c981000880d040c4241c2400161010b0701d03107000d4117401e00c2d154403441c1e42c0300b00e4503504101c0d070003904400340c611507000c100342c1440160950b640c5440e000720300342ca801c407101c0500025540c2900300103a00700c0403007052001c1381c0c1c00191030750040d162951780401610003c0c0c410303688140c5a2030080041031640c450750201480039001140e44a44c180144410030201c010084240101403004211704580343c00c4640800c4680076982d0758500001d18a0b104034090400d156401414498068a5980780c0361000401d9443da82c462800f902400c080c0442c19100481c1e55260120814200f0854a031212450343c80d8050400800314503407640d802c1004c41e40b0000c840400001703403240d00a08055070802d40000300540550 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 227766591 1250 227765341 227765359
    0x6110105040c030b090a0b0717010f151202071721060f060d11030c120115020a0609020301090f0c0914040b0103020d0f0506041a060d11100306090e0d0e 67
    0x62503403007008800c1d1102070305040711840054980c06007401b03441c012951048044090307080114000f0300d010050004041c48480031000843d4161014580d002218003401000080d064507400445041c0700d02d190004030b441d002c3c85400001121100d81480c0d01e00100e10040e02d84040074422002c805590300c1424451507040d0920010f82c0b5865085d01900fa0291011a903800c004d1254200904198040c2001408080140301c91503e042c401001c401c0000340c4980800d036241d0000d500e071000e88040d92409644814040400584a90404250940010000644520a034845428070301900c0d0048450445440003030040014910400380e1905030b042d088852868176503100c100495040c000039204446004824081200c0f41400e502110380c460250750041c201441d00e00741d06004800701c082c01030260350010300582490a407400000390443c500c51710000291003800380110012003200308240c1c44500110300090140150320b1001010001401c1c0f42c00b400317000a102e01d40d049880d6100c2d5080c0 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 227767841 1250 227766591 227766593
    0x3140307060b300309090901090506010602060c04050907120f090501050108010c09030204020f09030307050f1912030b06270901050402130b0a0c0614091020031f0305070611010504 79
    0x9580b022070f80b10501c4460036442801c0d504210b296001712048142d0113000c80c010454a20760642058207400d11a03003c43d00203988600003641c44d54011035041e0a2010244010001440c000400b00e400c00f500c0e0822050356503140a001054603140142c1d00034160f00e0344500d8081100900c605401000490002c05c800c80f1039900081c4a400140300c0a4802c5070041a00924a50b200f421a84001e40007000c40e035650f4031500d006a250508400c070301c1d00a0048000c01e03c0b110070844c50403003203240c1c00301048044a8000340190b0040445504140c0c0206040c00001d00b0f800541604400000c603804140030343c5078083c070400004550581142e8011401807002d442c5010150510000780e89540c95121f0711648620802c4a401d03170081400b420260401414412101c048224180200c1d4202c080d81ca18100b80703e2017a0584014078010002000b1002035519040310b41c070041c40c1c1000754400144458580c100300c260007150709800030f0300d803a000307070808000c4c954101d40032410703460141d4000e20540c42c0c5 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 227769091 1250 227767841 227767879
    0x504050109030204201216030507050d0207060b060a0908160b09060f0706090807140c01091203020a0c0807081603031e0509150c12130b0c0703140307060b 68
    0x81e840028001d41d20b6084200b04480d031102c081014200b0748a078144c81e0341a050802d21078100c250303060391101001400e070a00303451183c05031600c202016200d50313160007180c98250009521402c0241c0c4c3c1d00742c0e203110f0082ca6940309002080040241d5852041580c18445c2d440e0406040d145080e00310401d807601041581401810b40d9100340c2d080b00c1c2c1646036459002e650780351380319520004044034607104e1454200314100c00640109406811036820900e60740c80f0705070382c51840005050109015840c104404001043e410b10500e03ca841540c2d450350003942ca84506414136080380da8560031203c010300207500104481a54540940844c000b010714548014210141c0c55a010b6201c03804000d40780d1905c0e00401c03c44a802001034888540d13203121610b210305a40000074041d0050248a0940500d441000203a0b401440700c22100090189061900315081c0c0c00812030f100e8078064800000082031315408400000d1041c80003955452001e86051822118204500703482030b52001c4184001403a = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 227770341 1250 227769091 227769107
    0x1030b010305150103020c0f1009030e040902090a0f110c0703020f0a0e0c0d1806050f0711030f0d091401090209070804032c130609051501020d18050405131205040501 73
    0x300317080040e41c4a00e030400007410b011601400e00c403d882040034900403040140e0210947c940030341c2e1201c541d0350070f5804200c02d4603941c5070042e520403c00000319441d01c8180d404212009071502001070300502108a0b00710541101c850061250000c000030015400c2c6144020459902102c44155250500301c01184240e00a0240081c2c0c8501107014644619035a10032100340291114034a007880062518130302030081140c1e03078403c0310030783c00100b80342c50301900c03d0509008500b0050f501301a20342c8280600c0307400c8403984450180e1654080c002265510300c0190f00041000000300c0e441d10076005104241700060669810400ca0408000c0440c1d030002c80a03541e55100382d100ca800da0702c02c01003100f0780403045500682c05030200d0038460410724640e010104803a003403d0b0070300c015658049101c108090300340010340540c200108900f02640f040c10034095501c4c40038a8400050344400201301117400407603c40c025426904111400c0c0034007480541d00750440c0d171410b00c2c1380034245000200b000d0 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 227771591 1250 227770341 227770381
    0x2060405100213030803091e060709181107050a030e0609060d05091f0c0e040603020d02090a111314031b0111030c01050901060617070801171603080901030b010305 72
    0xd42d01248050411040040b503000464229101540364109200394a88450412410818031070002950f0074607004003049080c0b01b02c0058480070781071850034008484520b1006081c140702d0782d840cac00d1440c643c400035000d055490301840c0101209007203454040c02e50031148807024440c410901140503250381d036401722102d14280c003002113165121b80c8005840c00400c0b25042c21500d0105e9565100d07014144e000481e540140d036502e005200d05401440304480c4103003c0079402144c00d50496000d41840c1304400c1c4c000f4622400090740c1e08010400e0140c0e034001e0100c4020f88501c491003080400c00c04100521041400c40c05008150341d455141c0c0c0740f111258a4960500126a2320003032020340038810b40304007501c00e0000340f000340703000d0300c1c0036008110500030750f008200c0180b401220b40800040307062158000d5101d4083d141d0030700b501084094541c66092003688500c8200f102e003080740b8042c0000451140803400d071128000c0f40090103858070030540da410503192108001204406a07105280c070303 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 227772841 1250 227771591 227771623
    0x1002091509010e1e01020c010903020901030809060d020c0304030201121a12010207050106170d0929070503070b0a050606091c051509070905010902091f0504150306051002060405 78
    0x203219110300681c0c002805030f003c0760340005508034081071a5004003244100d40000d900b41c495810569005584071f400500010790130051040040c8001080c0c000100303501c5e43c000302598201848011400f09903405590280003940010070200210350704500c03c001c0d0703811140300a0022184510304045c1010b864071001d0311a407850b0102c08900748003941140c86443e040703230003408a291a5001000406040d40fa1007400b0b124139070b60080118450620101561102c029034032505c0340b90445120054a4040032070510030041120200080c800c0008200341031044801c4501da1034101081d1007150401003040c3d005c7c503020040c28640750342e28000c041014802c00401101030001d070406c43d02d00080c0b404d042c0a424455024424594000101c00080340c0b50040b017405140c0c0c1701c0054805034002c10324115004030504244104240c24204071041407000d42c034241d81041d545040c00480489449180d0b404031303644010502c158105040c10380c800c5a0075000030062424181d580e982c1c0c0d000c0b02c0c0c0140030b076 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 227774091 1250 227772841 227772847
    0x110703030911060f090a05090c0a0f0e0916030e030c0c0105030406090c062106050d12171611060106051b0a0b010605180109060509060c07090c030209010210020915 72
    0x420041400c00ea0381c0ba20041e21203070f200c20950141400a601c0b1650482c4034550722036000030503203407164039144681550059a0f04249500c0e5007502c8c0600880502018071205e40400034aa450307102004e880b54003130000440e81107481ca00c02030b007103800d1701d400d0510580080003880303641c0000060b410701c1d054080c80c040323a4130394840c20990010801e0f440000e001450a010015106a00800c6444000c001c00f02e4010f80d000e1108080085032058441d640d04005141104004142c0c84a103d040e070040e5070802d04000c85126551f50090302e01155400c1c172600100b0304500c0322541c041800d8641c222044001c10155041a401520601030a0000c0320b89122840c0c80c0d0a4a02c010b10480f1910303980508080344a5071640e001408580000a038009901071602c55a00198803d80c1e220080302c0c1c7e141c40d6a460006584140006a44030408030483c9100d030345030005a00d2820b00c203262840c6416600140c851040c0400241803042041405206034014003503d400b540d45c00c07400244003891070000da03079 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 227775341 1250 227774091 227774093
    0x32006040b0c06040512040f05010e01110a140f1f0c05040f03061e02031614090d080c06010b041410140a03060905060604180e0a0203060405030c101107030309 70
    0x94903200399040140c49407070108003000e80240000d40c0e140981c4c071903800d40f640e01801c481c0002c0c4900951280102d8141c014030100865401350345041c4d685c10061511140d03580c4002d80d518035096007060111160390840c948000e8900050052207001074880015100328045101104068000c0b200c600010641d10520300c08c800e80220b00712401003e01d044402c003c5076030381c20300c85d00070001031220b0450002400c01008400350315100b200e10900c3d01901a0b00480d640e4541140c14450b600d1848080e03030f004100e452865035490340250354442c0b03e4600d4a50f5140310050103030030003606900118214405100900007501c90b82c0581540017420349a514000c1c006480031242c508401d044142590000a01045201c0d459045041900d910003c00c2c0045d440d0402441400c4c07040c5d2090441181e19181a0403210440e82c00071018950702c54212040681580c0000741403450544088619034800036494000c800113100d40740048105484c00c004174816400c0040c004c0c4a04040142095070b907010400c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 227776591 1250 227775341 227775349
    0xc150603030c150601120b06030412030b0d05010219030902030a0b100320030c060f16080f0c0a1b15030c02010608010f06030b0a181203090204051003060c090320 71
    0x7003241d81c40b81c04032082000303040d00d000341e070800541c1c0c01800901c0d04542e581020b000b80c02403a140c814080c141c24034642d55a01e4410761010711140020803d61651011012556101040b00c0941d0045000581e61580102c1c004040000c0003442010b0504140700600942d40200b18000c030241c2001d5480e0449d82e43c42400d10303203911650001840c240d80e44001c0040b241d008100c0d0004140d0603030032122140d0448041000d1402101c0c6107055844003040340504202c141c0410306085c85c403135940706040c1903915080c40c10031740002c625040c450388002441000d010726400c8510980c51008841c044060402c1102d410f801e50780c131400010b050f00c840080114034801d5104c00c00500b001c0d4000c000e02d040c1c02c1d40c0300303019040ca403100b0b503050300051780440c0394900a40703d820401c002e030344240300d8030641e00eaa03403c1d011030034110710005260341d848480307026855a004031841142100d06083c0c0341030661800000304c0354046041d404100400800340700150149460a0796144150070202d11906800001 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 227777841 1250 227776591 227776597
    0x90105240307050d0c110f2a0307150c1a09101d0706020c040e0303100911040f0603050a0501060e030c040203060d15051005030d0e040203150414010503070603020c15060303 76
    0x42e003071141c80e2005501043e5440101c95906c04168400c6e5071034003500c00c0301c260395017440440166000b600204c0e41014902d50428240c00544058152480284c1d2032031107102002e1078040d0070340402c000c059511704100d510030b4155601040096050094200082141d07501c0c1c02100c0e00b600d1069480942c3c0c41120415030304101c0000c41001200c5004c0d80380d880c0251264600011070b401340b41882c011440c80e02011050302c0c80b50903640e8907050202e00c3c040c100c0d0040c001200c0c6603031048404000c049041207040303005034060102d513103020070076080c84d091700021900145c0c04482008030100c40755085030703004501d014210038100c0300035803640c44400004801c1503590000804280160224036800d0100d80c111030310075071451400c0c031040c95079842490b8071540450b6160002070780f211200c0340c051501d41d01664020446000c80c58130030060380045021680c21500b00e241d11010740004010906d400c001c5100604a18901075042c4842018407681d9218a403030b44109914000000511a48081040d = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 227779091 1250 227777841 227777857
    0x60d020f04051305010e0a030c020d0c0e0a0501080d0c0b131b0303030e0705010e0306011206020f04090915020901140313120c06110f0703030e010e010e03040509010524030705 77
    0x30400243c03e00321140001444400c20880e165400d0030144c02d1071110200d55410055010f845542c0300844540c00c210304207401c0c0c0300440300255848004118604440040340c411002090700003079550502d004c651405d101ea14180c0c0410508810b00400030b150356000d540c02a400802818a1240c10703c3c2441c0c5000101481c0800602003c1c2c00100380755150b0030a0307425203040015620440c0d00c400044422103104a140b64060380070750010028217640b02c091040589c0111001404d0940e0703c00f801180354442c3d8020000c89840c0c001410900000109049801c540c0307071411403500d03580700d0000c1c1c0250202441c055200702c2c04000200b18002603201c09a80d1644802c8402c0054525203016100c49420303e42550b506e031070311015242c02440320085610303250307000f4011420028a81c1d0200c0181c020107110210030354840c0b04844c004c40d024003407848100e1440c00950b4640e030a1200340300e0107440c141d010700e21a151080343d4a00a440d400b038403095407058401c41c6aa03031f5490500c1030352203102c1e00103 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 227780341 1250 227779091 227779099
    0x3040201020f120405040609020c0a0f1a01150f0810060c0515180f0307020d290103030201020301080f032503090308040315050a0207050607030c020c04090803010f050d0b060d020f 79
    0x52003e0001070a08014000d684040f0b60800009803120038034402c90049070014420344d0b100c0241100800d0346880038105c00f0b44100022001451010800d41c00b0180030383c881802c0d10040103503541d8854104400540101ca07a140c104c42900d851035580c21000c02ca84585000d000c10324005c4028040700340003c030070080010381c6d400664140403075103089511043c50520b034140248199448000d9001c800c454605070000e26001e0851016140d02c100c00d01100c48400102c60a00d400c24241d400c50200f59000b18004d400050b200d41c0b40c5860700d420110001c50300b458580081080c0c080d0911140109000f401440401180c40d402da440d05844540941d000035000840108001080006018a100c5403c44540003484152564810035050b4000c482005043d0f0f0401c2c00080e150921981c0030941c1d0030010300c110748003c8511030100f000c4508071101903071006030000042c09140900000c0c0c6000381000c9c1d8081c00824038030785801401c10301c0649154410b0b0000d1040d1811b540e6403103035500c17014030020 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 227781591 1250 227780341 227780353
    0xc1b0201140d1109030708030a0c0201030f021603030903080604090f080d060b0c0102071a01060512040503090415081c093305090a0902040f031412130609121703040201020f 76
    0x70701508004d07081007840f5440ba10543d10003081c0c401012058030404209074460b0802c4110715801074001e4500510180030281c0d09104800d000d0308402021589240a920002000381541c1802080c00c0320050903c0c0c011400c2214240c000303042418581440d9800c41c180640b5140c1925920000c2d00603030b1301035144844045418009580b0660003800101c1c4140c0c01101318180c0c84600060404091103260b0100d0f0080c002004000011844142d02c10f00c10001d880c5000002d50015049409609440d851030303418450501c0f210a04002c0b140549091480b201e200350403502004200d4032188c007070300607942e0728000c0d0b11078a1510404032124400c4440c03c02d02040c14403002c010081d805c4030640600c101c0002c40001414016442224180e4160140000041e421a180c1400f0106441004921849051180c040005001000c0e04100c8040b035001d41c115881c155006020b11142d8000741d10b440c07181c80946002400c0b620081800d60008131942e03443e0344c0c0d80e0005070705060440040c0350540c000c0b8 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 227782841 1250 227781591 227781611
    0x201050d0e012c06010b030a021b100e060604090f0f050a050a03120506010309020a0902070302070b13030201080703110703200f01060906060e0306071407150606030c1b0201140d 78
    0xc941212010f01000d040c1d80e1021041d2880c140c3d02c490a01c00c011058074200041080c501d1180c00500012107a095100300500700e105004c1d191185107980c1801c041e985941e100c0c80c4070028040b480d0080f5003107505100e50742c060303299802e400340e02650062400034608164402c00c0701c00d01200455a800206840032010541406071004150800011f1454a0000082d103598020f1051900302900606000e60700345c100b0220000070744c4199410740a6210704140010841103110050950001228800484905c0c0d40b0000d442c880d4041c0c01e01c0141402c040000b18030a281c1425560070f0341c0c2510306050700c00c02c1da14071040320306002c03050729243e80106500002c06003015000340d002c480d5004410450a541c0d40d00440c0c071142c01051155050f00301c10302041c03d4901c10b41317008903446041880346250458643d9041d80f10940401d50383e03159500c854040191640500c205144142142070003d0441c0b40d1141001c806400b070f0500070b040c05240c00c4008469209001074652000709102c04114071545 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 227784091 1250 227782841 227782871
    0x1050f1306090c0e041509050c0c030417070f030803041101110604050105011a36030304060e01120b032a0a12212003071a0411030c06070201050d0e01 66
    0x601d807119003c650030b0004c0d0481800d261080030403120707040c9803034020701d030a00041c50701402c00074000f441c5a41040c0700103100400107000070802046048a10507281d04101c8002c1c1c03c0003144d030b000242011a5200c00c00103e00c01e442101e074029800a94880c02c0d003688801600c60ee800e070210f000c2c1324441c1c0c001304401c21005610450603500c100c00c0004044c0900640b028481c4150707a01101c03070002e52080e401104401300010200340780c050156455188130070010902e507401035804000050403000d540000c550b00700784409a2406505400d102c513205040200307030f56294100d0900e9851002c150041711040c03001c18481c00a5038001c000802060f40c03845c45100c01415680b043c3c0e40a80c2120f8055a001e4140c002d00d050b81c500c54485440580480312140a0b4000324503424901e408104642d01c00100c600705c0d02c040102e550b102d8034200c1d08041c28014940c0c1e5502c00d41c14081c2e84401c003000305a03035a01d0151000d5941c2468802d48d102044650720b00900b2030340800d00e540b90f00345400c4204143c2 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 227785341 1250 227784091 227784101
    0x7061404230f06031506181002070f050306010501090e04020103150801200313021c080703051c0603080409151d01170102091e2103090a170601050f130609 68
    0x404541d01420b02a100c4200002444243c0b82d8561075107120200c0d20b40c4e410110040d10812250003003448540200001007401d0007040030001d40183c1002401f800071111144003040a080c064006109941c144000a040c00c030780d40c02140b0f4099100c80006045a100b90441043c0c181e202000e6100c20355100c45060103480075100482101c403507100860211001c40e010381c1e1149030300c0c0d0403904245110b6001d20a1030300d034010041402004d5001440c0204013400c006083d00761090341c031103a45207400a00802e12840071070744005000d00f4800c041005c1a0040e00b81d50988101c40350000701420100140c0c4105002903100450700a0013541c5180503102c00c11102d41202c1086070386056010142c01c3c0d19080348280c5131181d600038010b00404003444004603181184c15000381c40003041c0e0074070f0b0b020307007008840c01d81e81c040d070541c00055002c034941400701c0008000d00a080ea64110840000b11080d21520b05004050086915003a442e140ea0b440c5203407009a24148501001291b4440c0c481070050b00d = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 227786591 1250 227785341 227785409
    0x307050c0c041b030e0309090a050402010c06050405031216120c020a021207030302060c19031a04050a0b010e03010e0309040207030507020d0302030901140a08070c020a050a1701140907061404 84
    0x80d11782114102a5075003c0121021484000c0040d103a627901c04040314000c0c0400b9100b6810000f10b001440d0004902e8030407140036a000310000d588503050004034603040c0c60020241c401c4c84c5401600c120010760080ea403074040c0d4003d51004140e42c1d8074003034101c0c6407001100d00650320915542104007400c0340400c404069901075400d6580300d641d03040440907a440360500040b52040300c03400305401c3c1c3e44a82d000da240c2510500091000c420400001000c0d40e409903031200704036984444598256070880c9207090098000ea00a00280414140f01c54503030040b002d1882c01241c0018584040620540032107502c15402094801b140003c2d04000303550f41c00c80410346021445040718010110740748001d0341d82460483d1b0f12060310f0342d50030b4800c0310340302e004d003c04036081109140d003c546640c42580c000058505011b440301540850030b002802d460010b07910040c4030301514113100c5040e501203462025903801c0c0c240390300c8255038210b500d403c91095903c04103082140040350300b42448d041407070b10040 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 227787841 1250 227786591 227786597
    0x3110106050301110a030e120c0f06010501030506030703020f060c070605191403040f0c0302150a030f0c090b07240203060f09010b0d180c0803090102100603080307050c0c041b 77
    0xa951a0000d00d800c07100d12403411034011a040c0300c1600c101b031087d00f0514041401d4070130b44044070354010a0302525000100010301642101404a081010802081380180170901c0d003803000d41040004a600c8400324000a80152100c80e80d2079a43c0e152803085507000ba0310300d000c48003c10b5844200030032540000403901424441c0d034091000883c860140749903510003480071189141c0f540d58800c601005d8040f01242d440e201002c0004c050703a41e6800c0040c0b081c1c924500141e4039008850020308076400685e4035201c00e40b50014248220398400d8915040e520206c4401d9540c5040d0700b04441c503100c9500c54118001040140001c1880b095000f9501440040e80c0c1a42e11022400030000504024000d4142003803045c04054000d149c103410070f0040039851310303000707012140c1ca4580d0110300d00d40e40c000c00f280343d0002498040b1035034104205500408a800100b240c10305581c2c80c01882d100c007178044810804085031041003407400340f014550652000340308001755000000d154900180b418000c8001c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 227789091 1250 227787841 227787851
    0x206030a1512050304140301090c0303080a060626060121090201141c0c03140405070611030a080c030c04090905072c0c0f070f0b01140109050d030822031101 69
    0x1105800c1c02c0900040d40d4040081c5081c5402d250f42c200c0c1784580b400d1201d03030546d00c8440040114000e50300c1c44000e1802561901d15515000d40c03010142d540340c2c0d02480402c01c0c200320103410000d02d40c4488201c40003690720401035803100c10040740c060040745012070306045200c4240e00d542c00e05a11481c0704074401e032101c1c0031414021010512602540c401428003c1c0c0702c0b03291603c0b880c62503121545140240c200026804600a11201c0115045030200c40c29400608113104035074015052790b03220070804e00114500309410703400418801014021150004003c0042000c540100094070040d04442c1c400f040619040d040c40c40d515500c900c85d16400000b00f41c0e00d0090b55080d1040002c0c038296a41c2100402e450754040d000040e403029029038541e07202809a00001079202d11821400350003800446410350501030007414090b40840c0c0b503414092500c004004a0315258100c0380080c3d00350421210742d030f0b2010a0505079113220710107545042c03c5107458800301900701d014100c484120f81d00802c4 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 227790341 1250 227789091 227789099
    0x30b09160f0507020f1002070b070b010918020d1b09050c03070305090601051c06020d1407030b01090e0f060301090501020a050d1404021807020316061a0f06030a0e01090206030a15 79
    0x500ca03c6040c20181d005030179030703084540e6820a41c108117021052841152075056075000700034415002403908840d91907c6e18010440030b0024004c9c1d503071400da000c909003142c4800f98005a41c02c0021940103190501c004c840a50104541c1660802000540f400b03000034507121a12401380c0d482245d180022920301004901800e0b4001102d506a500180841c110f10b050103d08140302d002420085030b065800700b01d0f00035200140e002e081c2c80f94100c00000b21490030440000741c10384018899443c1004110030080005640522000390005030355100a042e6450302c0021a01402400348013810640c0006540090164000c0003851642c0340540308200c1104110002600c4d0641510041c0d44072401815800c40f00c10409060354108003c1d0044a01c0c0440c02c000d0000280522001a1400740c3c1d80d19111880400788184500e90910496841040c0c8da0300000184d21804003a00f1088101e9603801c5990b0080c17000d5011509040d002800d868580c501081c0c02005091060302d80e4034001f81c0640006 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 227791591 1250 227790341 227790347
    0x9250513270b0127020c010b010801060c05100209010201291e06120c040305011404060c05090901031205070611041a160b100b0c0a0b01060903030203090d0201030b09160f 75
    0x50462644007488080b240d1a0814030501214030b01400001549000c051004ca12803601c02001c02c04104000405c000300c40d5800917142c200f0580c045d03002d105110b203198001600c041204140b080900400580720040000102d00410900d240c1c1c2c00c0003031500348002d450055106081e20030f0402203c0b80785144001858140c030300c040000c981078000c03030300344024400c1819200301765602c185040b203104d042541d2510b8890940311f88181030b6004c542c01000340710502281d4000d817a000c007254100b1750300d4001594040346005905110280101d07032000549600e1074855000c59001a401a0060004101a0075060310983c014443c2c8004400c01d1a4180b0191030340a040e5056060702002032480e0f02c44e070391240703007a10074028000807402c0d02c1010049203000110010b0032660000e00000c0c0851a6207280c6296800c8045c0c0145051194003407040000036800002c0340c402060644540006020341d100603030217048140700032580110b014040108408044038030111071102c69807007982d0151847c1c019 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 227792841 1250 227791591 227791661
    0x110403050109111f0203032406070308040b06060705060610030e03120108070501031806020f0f0d020a020d0e0a03020103020f16030f030f060e04060218030d030c020601050909250513 80
    0xc0980c04c180300041481004800b84a150716400c00018a1223003080002100c5900c001d108601140124080c0800d200f003464607a40d0161050300c07550b00d00301d01e0b5100c41c1e03a034a00003030845104040301e81071a0402031007500040660b041100c11280c865000d000a18011842401401450320421000085540c464003c20314050300310f800e6610450316640380c1c20003940c407140c02c1c859102401c02260b488213242d100200b96500d004100140c5440101400038140201101c80d64108504060354440c2030b900c03d401c0c00212582404c00580c5d8401815000c07045000e90320921300c2c030b407480e0314003242859042031044803030728016501040756038100021202120401c1c0600c070061140d00d170024001500ca0760050036120300040c03c08404250020003c0e1500c0350364009000025105d00c994084250104121409440c08645004039407074a16841d41d82c0d1200a04005400d425800050220390030405210f405081c02a09004512405095841c040c01d40c00400d01c010a80c2d0f4038801420409013403035 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 227794091 1250 227792841 227792899
    0x405010905030a020f162d031e15060501050d0e01090c060804021504150c020607020a0902220b0f090a0305070e16020615040b04060b1303061d07060311040305010911 73
    0x2d00e9a02108010380e500000034240e0111104940315400440402c41040f5600114401042510b10007026860200032b0784000000c00d060f01da013010028032041c1c1e0000195903005108040020fa0701041c01000340c0035000003000500100e0034441d0214005a100080d184030304d001395503005051043d101d03004a60301c03c501c103100c109041c10303000b428910f208030f2003004c4e41030004000d1814120142c0000c0c03100c080d04c0d032205261503400940482c840e402c1c109078010780042c007001045101e00d01640040c02e8424400c03100790703c03100090103202507079608004101842e0450121100b00e922a130392090791803015680751140a00340c50500b803036640f00240b8284039070b803c0da18890012207a00203020103031a842e00c42560140d207541001c80c42034411406000ca41040c4415807503801d156042601c01c0340d524940130051000480c854035005107001403041c0480d080717403400080c5600d908041c030f4100d004581004085508204043c0207005041418540c030741c1c01280c40d10f0501100b1142507401506c2805 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 227795341 1250 227794091 227794109
    0x25140f07060521160f0201090201080a0b040612050604060614012007150c0b011208030c070c12061514010906110a0f080301090507170f0405010905030a020f16 70
    0x2030140001da21520280c07202c1d0381d001d907207038040704404080440142c404950700203403050780e41c441c03060550740b101500e0301d0751105000802c0892400c2c0c0000304515401080011029210301c0d00038040d4445500ca40c000304a00d0340100c00800d644e1400640b079403001d82d02a11b12a00f402c80110740c40318105e0f84032494900c16103541a8406d203a907920060324031081d8600425011302600002c1d01d1034403a08081101e001a80c500392803400c05c0c41d000030a00d8043e00440024542166100001219201101e03000044018465202d40c214a007120f050030325904500c4518104281103030420040c0e802c42092110104014070b12161100c215090b04c81114480364009102c0721001c0100c24004c0501450030341102040c0e030b00205550f00e604060141124049070700d08000001000000307114803900b0713000317489854035041e803880348004803d11000140c010030703075004104046410051300354050309071f169201040d240c9880004402944900000706600020300489400c0d45030340303103c100410b05503403101c1 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 227796591 1250 227795341 227795353
    0x103150b0603180f010c051b0c0a12080c03040f090b0306251b0c03050d050a090905060112050901020901020c060c0703031416060f0b040216060b0625140f 68
    0xb40c460b403d803048504481c00c40c040e8042c5a01c070250280074500100c025515031070380d0ba05c046800d032003100860343c189030784580000711131201e9941d401e41840c089420300070300040500b10714180450148112080000c1502c00020b00003280440c4244150072107160507400c000e410241d40605850748401c035129143c7d0909601d0965045540794604180c2d5010740c60a102d020740ca40704210100000488152007415500004108105040140e0180868207142040c05e10754550f0740548030040d00c2c05991407a07600c610005106920808516000144001d814811400e001003418002e6000440007070050096142114440c24050121111221030740010220365282da1000c50340c614100f0405500d05200300245081d101c650740341e000d0010b000b070200003595040042d660084481d12500d2078020b50050100012140800e01e51080701c50f04200701190803818003001403801e02ca80c0b0400041000012042281644412041a1424441c9003000118401c0c000010b0341c60a00ea032415a042d84a5 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 227797841 1250 227796591 227796601
    0x3151009061203020c190b0f0d0b0a06170c0c1e010e01020405010905060a09170d0e010905032109060d05040b0708040503041502030904020307021b0a15031503020402030f0103150b0603 81
    0x31401c0e804005007010804440750307c503164540307150311035241d0030100b14010820940400c10345c4a046030555007194420b441c10318002d0007400042040c02e0240d0190300d0742c00000e181d040281c04482d0750b03103004030680d14055503c9504254100c3e4503107023032101390b10b01200700d040d20105108440542c0d205840c1c0d0301c00c19180c001000b5a56000d0714240040004404001458507600c1e03076001050401500540901c0141001c000c00d40030301e141900b410444250b81c10000c0e80c42c0410038400891040b608004610000080388006204904411343c00c000001040c45c040740461707002901403031082c540030190b5142c0c03201c1200c440505550281c05038000b0001048411003903040f03022307140098015241003808200000f0101d80040360070b680940c0090882c1050a03502021400d0495012161301c00100d01340401d4a074141503082018041c581d40c2d82c10040d09c0d11050002c1c00095900030025074ac1c91405000c0d900c6039100c00e00c01280c00303114905405408000a016900d020800502038070f040d5641c03 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 227799091 1250 227797841 227797849
    0xd0f050c0d05031b122a121902030a050a03020c070302100512060d02030d0c05070f0f03020f011701290307020312071403040f08090a09021c0b03060f0603151009061203020c 76
    0x281c1e24a1006c45c040b007800000e5412024040181d00c4800e40f8a00e0791108805849006030065000c040320440d08108142c2d400240c01034150341c0850700900d170068941700c82c110840d2034444940c101950018182022041403980600149822041d4901010075600e0f003c00303000c00c40e6540d8200942c035400803418101900d11400c82410300d503010381c1c00c031014199111140e40f20a803090b004081c01c010a4181402503041c0f007011041c481c00280303001000003406120310016a1410300400032804020500c203000d42c50f0302c0716402141d0702014142d0342e4a041c0310b00c01950f40d62041c4d0642c0a03000308079000bc0c100034007843c0820389a0032451080b034a1a82c95540b03000031124413000481720f103002807100605c151a000700360070281c0b03100140141e956024000b1a60340d041081ca984610a00702124240580c501155130f98010f90b403070010340b0b4103498820019007040750070b50980302c42000300c000f04030691010060460481300940300070003400740c4070b0050000c2c2d580e1004010380560711101d00000f182c10 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 227800341 1250 227799091 227799127
    0x804050a0b07090b0a03020a0311070b06040b0102070513060602071a0703181805010504064703130c0605190e011101020c060604050906060d0f050c0d05031b12 70
    0x424540f0801040e1503404070304042d00300c440c0c40c40009a01190001490382c1500c203800500381c1c00300806050004503640c070505000c0040109002b0b644a40380004164002c2102801501e4000c0600e0381c0d005c52580000000d121503c204801032242c110006102645600713007071208001080e03002e1801d0a55103042e1200c221102c2d0050700d12480c440b000604580701409110f0041c251180441e965141508010581c0d0141c0c000e8250102c40710709410b000c00c144070380071043c182c01e07103941905890700c040d0307005c41a09030740740c41d108111000080000310841034a207141c0140c0f0641000050b692a140304840d00d000f84148500888041c5506100441c058040b1041d80881454032001902030000c1140c2641c00020382d02c05c081c1e200d00d050015600d014001e080d40040350340000c0c94607140c041d000544a12100e4000341455400d0385c0d400c2c042c0700301400b90446070003014054190341c454500c1c00507030380e500200500c1c1c200c222030340521032121340204a0008010400e00d0b1035051104003602203260003 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 227801591 1250 227800341 227800351
    0x705031603020c06041d0a0506010f12061d0a050903030402060d0b0f0406181802010503060607080c1504110907140a0c210906030902100c02060c0105090d0306060804050a0b 76
    0x4400d40c2c2040301256030313840050015040c80c2c180d0390b00e84c0e1220001c0c4100c402001c2c180d10f0749581070508002c036590740013550741a00e4000385404032003001c10500780c0340101040d400002c0e003524010004100d420810240500426618404000341c4d91602a015100d02058400a42c46a0208040000b0283d10340220900d00001841c04500d42d80d45000135040701d00c00d6008800303088440c81d0315441c1050504ca00308002501000c02500e45a041e4002449031100402c4144980404502e20080c080300105403103103001c00b04d04840e00c554100c840d0000310313801201c0c201d51440c068420760f042420011100d034001c0406458500c4800148040b200c0290000b40c014801c02c0300482c0d10314046003680c03240c40302140000030511501005648000c03c0c01c0724540224040c1400c1400400050700d4900100281031240c0c5000e6962504070f2001403218070440c81961020340c00d00040c0301044a01107080102810345480402080d0344e074090a4450f003404840142181e00300d00c07132802c046a81c2d004419406 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 227802841 1250 227801591 227801593
    0x30c0b0702060411210607080117031e0c03070807150507053f01030b01051f0206070507080909100501110c0904060507020a0b010b031f05091602011b051c02070503160302 75
    0x440e1a05c101c0c0d81c07404608039656000540b400d80104107890501e410094805c818001440c0b07010140d406403500d202d80c1c84911600c0d20701c0000e8101101000303105540115510074041981c8403d08e040c20036944940447e00c0c901c0e285003030003107078403c1e00610446007008204402c50b000c407100380c0803030146100d41409181c0300c100c007a44017003110949410001d010354480e03900200b071941040103004428600801c00a280417030380700c2d10300300300d40c0001e00300d9801101c51801070f994400514050005000f88440590031134442c0003800141e036100054070040d140281d8400c8031800c40c460703490390f803400310200c1c10343c0240340b60000c02e000c51a2038001a900c82c0341030049030340148484c3e460102c5148241d100b400c9041c0c010052101350b01c030b40c076120401c0d51940010000340d0380c10000000c80110000c1c1021601c0050b40b101c16000d80c1c004c4d0402d0142800c0e4180101021710040005007441e40071a004641810140c140c9201520313981c4280e82442c2d0304000190300704240004140410340307140b00c0903025 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 227804091 1250 227802841 227802889
    0x3020f040e01020d0f0204030c0504090804030b07091205100b0a1206110903030301180b010e0a0b0702041407020a0204180305040b0c0304050603010314010f0c020c190e0103030c0b0702060411 84
    0x4021117800340d03150300642400c0050390380d80b41d424100d9801070702d90800d5206d5414003507540b0200d240308064606480c0c000305a0032554845210580d45580d0760b0b44803c61035450b880000342031000c0400c0969401003940d00a00c00407540c90100243c43e0460300405c2e00030084010114041002030f4460303168240c0302d910803850048aa00001d2031504264420341c21100d0078040a140c00300980200c1074107440c282050304103414800000b03000203055008910b803030400480c000e8107555441d04540b000c201070000d100260300741040001e4540101c00002c0e4010347c200250f4a610366078480d400c0c241e85400d42e0380c0c0c1703007490b04114920101d0303401000601414442030102042d16512600114029031188070305402030a4181101d50a44201100301c0104030b141030480003480d500891300f008a023000710340b01c00300319043e4009600403049503007241019070800c500120416401c4208190740714007844c0d06164035501c40f002207943d400100c40082500d0302c4541c61009500703101181d0a807110810720380e13840c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 227805341 1250 227804091 227804107
    0xe030d050f0c1e1005040503030105090405010b0406080f070608010b0a0c0f08120402150901090302090703060801180c0b030c0406050a03060306230106020d0206061011070312030f020403020f040e0102 88
    0x215220000382d070f00c100c029007030040882c0c0c568100050911078505200074003003440c181d1240d035200e010500c51503020b501480c000400b045001c1d4003003040c08000600412046032241c0005039140c50034426801700e0f10a03c0008542d49000b4110700b8100d55034600f00741c1c50302400340d00840e40300711501401c446600c0d02d40c2000002031001d1010340f00e58280d20410140741d10f054010800f8802c049042e035440d0200801104141e80d030700079101c0b4181ca4055400f03c40507116184110300400885d8070410380d951030b029442050900350105408040c3c0a1002c1c0706c281902c03405441141d10003590b410310100070410040007c1c50046008d05003003485810300041681d03513522120143c802542c0a004c0c0c0c61004c40d0b1070201500c800b81601c0c0941010300c020130302d01500b94406545c1d0440034081e40e124051050500078110321810b9a404c0f01c2c4007407001d9408813a038038a000d00d105d509100700d100c003107030801c071600300b001460b482540d08503500282601001c00e100001c0c04000c050181000c0035035502007065107 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 227806591 1250 227805341 227805343
    0x720060f03010311030c010e010206060405040201140c2a01200a1202060a06080613030c020a051203030414060f0708090c10020c0f03011104051c0f0b0402030d0e030d050f0c 76
    0x6000f107002d220500414900c050425040c5904001d220f0b043c88860441d1920b566070000303200c2c1c0d002806990004468807180016529408103039496503103e140020011044000840c5014101c2c500e020300089004808180800c0504c10407452800515592094644104805c5000c00394840304070590301c110f0000e4840010352040c810326000940d000109212003900bc61007520001c2022201420b42030818010105032140d45403c090301300801c10380810705555925200c02c00074070005050703c00d810036001c2c185850ba0402c07142503494140d000102d01200c2004604144a40342c0001d00c0c0f030060b44c131850b0541d5404006010321445100d00e4110703210035143c5040304a0500500e80091540441d00d500b044100314114040a0290741080000c08070602900260341c140c40c8200c400076090f55142c101495201c8a12030007070030000c84044020117200c0580c0302d01d030043d4020740030b641c860040920103407211100e0010780c036059442030345a40c400c244a017015091011744d12815600d4101c0500d509 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 227807841 1250 227806591 227806597
    0x30717280e0406050406211707121107030c1503141f1707032306090303060a08070b030a02211302090601030c0f030b0d050601080d08090d0f050706090618050609030720060f 76
    0x407160354003c2b0066400141d04442c02c0707144200c050000b4131100b030443d0f0301c40361001064490701c15481024a800c114950003a00003e42040b540c5190001d00e01d400c000140400e000d01c90102c440400b028404100ba142255408440110301002840748903d596a0404006c00c5142c810b03003000360707a110700c46181c0307014003001e4040c944d02341c0250703140c1c1409002c2002c1c0030000e030b1041010b6030001030100241030719403056a42c061400080140c80f81e644442014483c51900f00f83c240c0c40410f5810000c1002030f56540041c134034000d680301259903448200650444280001c400007142255011142c224842e40040e810f03e40c01a103500070084442c0e545501e03000d002c1c0c0001e48583c2003241c02000311a0f005030004e0740b001519004292260110001400c000d10f039607103c0042003000201c880c02e00156400000f00268068030400000319041540000280c0d02001103806014a901055441030000161041c0c10b81054a0454600403012a1902c0c1401f0500064000500b4491007034814159805 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 227809091 1250 227807841 227807843
    0x507060e06040524010e1305070e0a06060314040f060609023610121503050a020901080303070e09060f15130503030717280e0406050406211707 63
    0x38000c504007494403134203040f40354141031100c000d0107040300c4a400d045001039046614a050310035454440340701e002c0c10261a131502074040c0c410408005001c00007030440910400d40c88d10b0410405440354022400c0e20030045c0d019805140500108000c03a034403d01c0001e566101e0000011281d585488107000d0740c02401080d060300da00c2c1080b500d420081c001c2c1c0d04240c0c0d140e0042408200056200040e050700204490008115400201c510000c00981c0b10000429448000b082d07455035903c1e210340c1d00d25680300d040340500741d07500c000580c406001050702d014090546540716207254240510005442c000d080903403012000c4062185a102d8000075034448444031040c640d21043d400f0700481402041c1e01ca14080e40c4108001700118103800f911044c440803c1030000d83d41c00032052804030924202c3c01c1030646403028404a032102c1e801c0f0b0302d00d100b070746000c1d00c1c107122241d902d00c204021a00e01e031160303400301150700004400b0805c00300581d111451241c03002d1005502c404807400065042104 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 227810341 1250 227809091 227809093
    0x30b090102122415250507031203140f01170721030c0206040603061712190e0a0602030a030e010908040b030403021923011b110a021305060108180703020609010507060e 74
    0x1403100e1724078096039894000000c00c2126207002c00482c3d80340c545e110514400941001d80006034803017803e210350802c0080211113400c40d2001d042284061a10400c28445c80c1726400b01c4110240782d011740890303040105c400880c80c400704480c5540361186d0329102d514080f03081059003080d00c0010303600e500150000e08880c3c2d600244c82c0c0d042840103c500c11021030111082c0c0c5c4612203c07420841e24000301c1d0001c403d505110390207400414002d66056104100c0c0a600130801c12000c0b8100380c0c000f01502c034907112558240030f4280e10103041e6007203554080001d071444404000c2031041107818030081d600310703102c1d2044030550030012150754032880f120841151000d103001c82000303d103c40d00c0c04251101081c403008100340305000590401255000300500c00f40b2040342102181044140540422550080d000d00d0283c1c04003001c0d24010700080b9582c0d404503500174041030100c0c0c042007039181d403004808000d10b042d0381150200492900642003007030412004101520004039540200c0e4604944c0344 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 227811591 1250 227810341 227810347
    0x5010e01030c0e160e12030705010b0405011a091e13020a020c010f0806090405010b0d050c0406080a1a150a06020a1a090a08070204150f030b090102122415 68
    0xca0b1820031442140c1c800140600300d80d09001120865003900d259010341801e0417103118441001240341e00c80013141c0044c06000c0030a02c40180441034110b080c0e403180440b810040341e030301e803100b0504043c030b0004241c0311500f05025484443c1450080b460260200030003042c4e0110300c030400100c00b010f1000f920a04a0b80120316052000d40400130000000c80c01d00307002d001e10440300001080c2e2480240500d1081071028085030500100303500404807940041c100142284007428002d6a44112558090149150850000301d0034000b1440c801820b42c00a22541c0390300d101a07000700c00040103041803880d400d016100c102c0503910312091100a101035009800c034010380d03040c503401285508000802c203a2460040000300307800807840400a50f8031440c00b980b1000329002182c000c1c6640401d9035200d0305040408900e20740341c0039801c0c0440c7d10400b008920742d6181c0d20114240c0c05080194158507034070501082c3e100c0c0615a999926190f6103030805207013a070280000b04a00d00080541d56a14000 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 227812841 1250 227811591 227811593
    0xf130618140906010e0d051b1e0105031815040c0801050609090709020c011e060806090c030c09060f09040b16030e03031b040909060606320c070905010e0103 69
    0xa00c00c58014400c1c00844515900c0c0700c404038810000091980b810403018203c581403c1d540c544800401c0c6400400f1550502e0300e612544603d004501c0c0700c0c078407500d51b035600a1821034900100199520045e50b9581c2561184401032041818480e580a40c03400b07501e950300c0c1210f910181e828469405810340401c203900e0b00c510340c4e003141d0000d08101c1c0290258010407034900303400101002142d02440d00182d4403800505000d00500c13217400031f00350040416060341075070304107604141e054841040955540d520741c152020340d00c1c51408040c0c0d405802c829180840c506d0042c148a41c0b200020345403c0c0c080c1c1d1000700103042c844007110100e4411807920203002c2c840f54204155001c0b0314007420100881072140c56025600e000007800f12a400c0180c0e02c40441124000041d46c004100040b0305010b2044203191440180089000303c1000482c44c0014403a2120300486e902c40c2940b000030303241618215006000100d40c84684031081500c10580001004442c42c8147d900a0042c02012400755040d = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 227814091 1250 227812841 227812877
    0x81c051008210a0207091a040c020721020402040504020c060720060114030c0a0b030a05060a050607060b0301020f07050106030b0a05041e110406060309030305160507080f1306 77
    0x1041d0450358460703004640c031020030044110000d424502041c420754580b840c58000324600341040d08400416030a1940000c031000800050000c0c06c14122401d00c0302c003405001c2282c0c0e90f42c16200e1403060203609403005481d0520786c0804046c050001d400540303001c2e19000442c0c00c0e80c0c0460141c01c0740b0b50180041107022980010703006841c4824280703100c036042c005039031a542c1c0c9030180105542c0031400c0c450b1140755130f4100000d8500e03101c06007411f48544d03a10b020510054004450a002c203130305000c0058001d01c0c20401071800d8480003400b590809005844000040440941c0c0d1501503508118000a0102104c007401c1e0741d1307203d0000412b00b203042d8130b00000045009812507000ea420718080c0800940714000c918a807550000040380e50409a0420b51000f8030040c078602e401034074001c00851001e90540050940d20302903102400940c43d1000304452061100d9002e01c001102400600c002980d001c000b8081d044041262905103002010b00300440c070402c1d4000404510011048600049 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 227815341 1250 227814091 227814121
    0x60403110a0f06020c1e0a03080c010b0409120309030905120a020f3a02060a03270c090b04020d0203070c021512070c05030c060a0c0e0303091804081c05 67
    0x140d407101d1251a0741c030f0500042d41d24190400000d102c1c0d1010042069140249034004803444002415403050070350728107201c550707540442d00d000055420008000039034201402001115075212480010201c580d01d8101c0062042030022020482c81c00e000003020b03940c1000242c0b804084c2400b5080e00d900c0e9104212001540007125802425064528030551880343c41c96881703d58144040c4c81c141781c0c119844041c8080103480290310001c00304583c41c849900d6408024441c1401000c00402c3d4a1445200c0c0c03c8202000c1c02400b00c0751080051082c08226003120130099400b80c030250402d40e046c80301c0c0050380c1007202d114000a02816028081d89440034081e8008000b8105082ca4041c2c140405c40c0c0030407004240200b40088400080c0403c90304000302c034100100101030f5002410404500409041070401c030f1000182035021b66412441e010048541240b001043e040c4900d0b246e003803034140c1c0780c00104240c0e90460213001e441c10000e01440800a2819401c00010341c3d480c2481541442c88 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 227816591 1250 227815341 227815349
    0x318010306031104021c09030c030801050111070b0a0201180501020310120c120f050d090509010504020a05030f070c080408060106030609050105010219020a150c050d08090319030209060403110a 85
    0x40c10400e00b007012490066036120141c100f03940c00350b500c00d011030350040040254681900003507d171660950625a1000310300401c40e210381c0c0c900c03500b0f036650f0004590248201c61800c002d900010030030440c07404190300810320070503d40000305203400c03900c08010b2030f20f8440c80d00399126500002000f09070880907617420080d00d03c41c0311000a09800f510789060080e07807405101d4070a42002c0b403030f80038001000c2e5801341d059404030407501110b0320005d00400092482c4035484c012200f401c0003140d10300e03140c0283c0c1c403007419503503500d8103503950003058002300b0f407002d0710001c11300800309084000310307049000910180000000511b129490719200500301d414507801507403190301d80001441180c1e4045084841c1005002135010103078861700009002c851181e22042c1e1400c800c000e00710340650031034440740015000d00f0a41e0846c0c20300c440250b5103203004a03042846900100116605c07a022101c4421507022145801130408240b04046580d07648141c2081da002110741d90b030502c2a14090305440090 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 227817841 1250 227816591 227816597
    0x50303040f150311120403090b070f02040c02030c0c010815060304140f0d0f050a031b0c11060c0601151205010b0c160e0c070f0f080309100e030a030c0e0909031801 72
    0x40604c0300486518040c4028400759040c074100402d0515104688100c082c000c04400d007a5070700410314015422403040001240101d0421105008090000c8150382203041d03610064000030101e0300c01144e004070001c0c8030071039024068010b84c80a4940101441c49603100d140200c4191221000540c03a28442074034610701d0364007090082441c1980310724010041c0c13000d4101b0b140c03a00c409000079405001c400340420311144502c041c00c022541c0c02031052a0107809250001c0140c0c0150701804500c2c4900103e0501c070340d00260041080000c40030012100c048186001013641d0305509220701034800070303031126102410106050080410038410f40a60680c00c1c40300f102030900e0020041c0c00070400600040002c0310200b182c006107c0c040008820b01c60384204004480fa81902d4501350700e1300300303031018032741481415145011041c5520540b00143c100303030011400c00d100d142c4220080c05074240d1503001c100d005124908140c48854202d401a2054001b86031545c4542c1d00011098407408005810 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 227819091 1250 227817841 227817851
    0x90708031c18050d080a0b04060e0f1902040f030b0f0f060405090c04020f070303060b030403020616030b120d120209010507061a03060a0e0c09010b030a0b030106050303040f1503 78
    0x110758400840e60442586141c002c615007180d40d44209100845101c080c04a0095899801819034030510003442021801d00c2000002500e0701800304030303003080c060030b80341e4084070011847c60100e800509034440a030317040301c07400c810500c50104141c1c2c00940c49180d400d60200800e00c10818200a4145d028500400f00b9030240303000c4012604000c0b01400320760055580300041080001d081c4042050080e0142c000d41d03a03400c01e80091051541b2032030342600001c1c54001d000c110701000504482c040ca41550003006551a40401c2803042c44c00c0c40c1020b01496581d1010a1003601d8488400001c0d11011002c1c2c003400000c030002610100311442d43c201a1841080010440d80c2c0010540f000c0c1600035200061205100f45281155128400400d9161140204000001c40c0a8000007940c0c011401a58058680761040c005010300a001b02c00000d80c091000889440076540142c0707810350b00400104009035100b001c6400c45e4003641010700b001c0d00130a41400403048680c0741050050080c0390803c0 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 227820341 1250 227819091 227819107
    0xf0f051c050c0d02030f0f031b010e0a03050d09060c0503040308060f01090b0306030703140717060c0d02071b120605010e0906070c0c05060d020d0c09030201140904090807060509070803 81
    0x20302d5a4034107070001d1142212854a1096480800c2000c0503090417004840000302d480312001d036690404070302e0001100d01c1070b1022504040c1800b8018000ca0755500a0150f00b826940c2a505500075101c0f003100180c5ea4414a80843c2040c040d0f038000c0055519515968100307420006c210460040a060142006140145260340c0c024404022290314840ea5a02c0361220310001c0d080651a03030001c0e203d480c0300d800e48966103202244c0e440032a5210403107043c00c0349180d84c0c0c1d540c69110441d404203512100b48400c2224400540003401e015105181c4401c0907403a951000740101d40c1074220300c1c080480e00c1000c03810442c01c1d1007260701401040d04520140d01e0140d80c0350f5513501004242104000003000031780100417a00401c00c0142000500322a190203101d040b600094200c070018801040c1443e0b0382c01904c6d80100004020340381c040e540c030942610402c00e012125070014007204e4215540b00d0f20003001c1075048010b044c019106690110b80c3d41492100c852404029402c0300f1456042044030740 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 227821591 1250 227820341 227820343
    0x20f040612060e1b070f061407020601150e06160309050f0303070c05060a17040305121510050a050d090f060b030f0a0b1302060a090305210702040504020a0f0f051c05 73
    0x7a8410300084c400c4006001444080d00300b400348081c002c051855014100c810802d60760000384a981d403d5100404c0b958035071000720707582c1000b880b82d040c0d00d285543d1081031162103280015031f0090041c00e11072401c110104545e4102c01400c805400089280800703101502c7c00380e42d400c040300001c400440c00d04500303860f0004a0300d040c2c4102da10074040060300da910b060150000d822100520200c240b500c0c9058180070b052680240081d038a0405403000044400c2c0340b403031503040b00d4078020f44020148003010400f42e40560010a141c03050100511005c1802c003168018003004e030703201341c50b5811800000d10300320302610710071800b10b4440c3d000701141d8401e4410014520390480d03044680c1070b0442c2c480b044180d48000c0407020181d001840054440509600300e41c540c03088910440490340c1c0c4402c846540b04103a0900b04802029900412aa60151802c0c2e00b2164105000a200b0b0701c08a60702d503454440505590300103191300101c014100a00d1905142111101e907903000da040f074a15055070b9007 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 227822841 1250 227821591 227821619
    0xe011506080c090a0b04060203030f0f070e09040615090603060e0a02060a0c060219021e0c030312100506160314070b0a0f11030903180f0102030304030807030f020f04061206 76
    0x164110400208144040c0d6032640702c003d00401070320004035961b82d1074010007500e0381d0044912030121180c0d040850444000c2491007441250142d80b260211507410082105d150340141c0103a60090f1030744141e100074007500002c00001e14401c8400150b00b455407600780d040e01c00403100480035030460422200540c40b00c3e021555030f52984d107441d0303201c140076140c080000d00526a10025a040d00080807004940000d40b00d030100700411600ca1011841c096400e60380c1400d6120740303805070414050440e15043c409a8a508078445064445078a81c60741c1c041001c0c4e0308086c00486200008980c00d0042c1a0000d65181020340c0c9601d4042c41c08100740c480c081c42d000042c0140c421581d440c0504a40001c02d41e0160145030500680c5640c0c90514144860383c85d0071580e005060050245034586140c5004040010b120b8010780146003940d907149c500f43d410800081440c801e15840b480b000001444504c01000302d280d03040020b0342c07243d040900042990b009600d20928240c900041444511214401c07 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 227824091 1250 227822841 227822851
    0xb0301140d05030c160611010504030f030e0a060e0309011404080d05071a010b0c07170c041508030c0a140609070915051302030103020f010c03170c07020d060e01150608 74
    0x74244000d1003860107514500c18480c0780300ca40d0140b410701072209020307100c9003030480d040d5680c0c6d0344412046020301801ca91066074028045031040709501441402038110420b5080030b4400e4550000c0103850349800c0d00c0d500b11140c1c07000d800004c1c1d060308035a00300b0f10300d4000002030300040b420b1601f030816107070341c03281d04402e03840500101040d203d082107403403103034090007041001c001101541d49070744010158024010741b81280c00f40c0500401c2e084480380403803854071301f614010491a040391003400010001e50002c40d42e400034004000c1910f01c0100001c144208922009014441c06400c00b1401460049004c41d41a0481001e11105510010f40c040a0b03500a002c001a010040d111036034402506510542c3c00641090342044441030982c09103040380d000341c81d0035201e007140000446d600d400b071020003400f0420514490404281030340341107500c01d2004101a14048103600000d0001c8000701c6e0071105191562154246220701303003e0b03415800115100c2d5255079080ca0405020741c040245 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 227825341 1250 227824091 227824099
    0x60c03070f0825080105010e030111180a0528050108060d1b1203020c040b060f0403140c04020f070303150f090b04330b0301260109060c02070806010b030114 69
    0xc007154078102a01582e1a0a4903403240e40583c3c0601d4203030180580809100b994082010300c140c2c02d0240c201070003002000f001c4411403510b00a01000d03a21500c1d03910805582d008845407001181985840d8420716440c100c0034015000c0c0302c004190440980b40e20307003003641000070300340611140d40c0350304002a0708903034000100c40c01c51581c034246414011300f540c40501c6501715680b02ca003d00d50003050b80540040c00f50380c18410304003c20b080c007500e40b045460242c031060041004001003070780840e5034403804040f0000d8030551102140014213076000440c05160200d40060b08108041d01403255491404101300021801c0345080000010301c003052142c8044a6110b1115101c1030342c4960000354030100d0381103c0030344045450808040d1600b4001501110760f0064808a00201c806d01940d0486180b00c5e20710058206c84e0502e030751007101d08400c0000c035640b5040d81c0310000c1c0d150300407042e5610b03c50340104642840c1c902880e2501e034041c0c0c8900d907203c0c001c00041c09100d11008214101c914261 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 227826591 1250 227825341 227825357
    0x3060603060d0b0c0903060c090d12020111070b15030706120911090403020d1814010f051e0306011b0807030e0a0f03110a080f0703021e03070e09060c03070f 69
    0x341c08103a24100015000700001007250400014411603000703842c01c100190f003202d03400e907aa41101150b5200700c40b61182c0c000030340c0c40340e5030000d00108402a0041131501c000724a405d0541c00a00482e00700c01e004465610089003040031a101c82014002d0a001c2200284121854060040c04081740580300060f9941c45914903000d124990003481d0008074003601401c1c00b490b00703050094585105d21040d03400070b850503558401d00e0740340c0e00910041c1c4003c0010115102580b50041d03a003103141801c0401440418450941407060303588006d9180001c84000030340d00d03c1c204000510f2100b00c800203030406e00c03c4c607104002182d15141034440855150030100c0c0ba075a92140024000c864541c00f00041000ca10004810404800d824070f811000a1300c1810f40c09031640c4901d0348583c1c0c641481c04480e030103aa070400144c500400200d861078030250b0598501503500e4040303810005280c100e00190800c050034400e0100003081071a6210080518a80c150b06000b00700800440c483c20b481d00420000b0 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 227827841 1250 227826591 227826601
    0x191406180c070b04060518070308090409031101020a020109060b030102070327051207031709061c02040b070812060a0b03160203160f1506150507150501030305131a03060603 76
    0x711000580c01c0f01d1141000d150910700b40f00a0030341140c4208a000503002182814000081d41070207985d4040400341c10079041c40240b000034200441c09070704110030700c815032102140a100070196205d940e4004941c4422900b008410703035010030380e02406a03104024020109900050410890308041c03207070b901410440034034507006080c5403c29903014441203082540e070000020041c007201e2062074250200701c0b03040c017084c10310b00a24030782c250082020494030385a2040c00b800701c8001007031f6180c0103040940381d02c481c07100f40d0802001100d10302000100c0c01d640240c980c4881c0e9012408546044a035418400e08803401e0002801c00d1000100d003400c1c081c4083c2c02402a18010300d1090450080900703c2e0a00ba00c0584900030709403000c8802c0107031b2000001c002c0c041c1c80140c61101046880c0040212000c0b12198000c2c601a40c00c0c0b060841403201c0a44907000c1c0302d00841c002d50310140c032188461400300011036180d00c108001c035001d0012106040c140410b490f4080411550640c60b42c0da0 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 227829091 1250 227827841 227827861
    0x41821141614010203070504030c0608040f0b040c1e0603060b2b0f090f03030b010e100c0201270609140108010e04060906060e0106030b0405090a0f0201021519140618 73
    0x200c8402c0e001d1940084104140c19a115004d001100e006003241460965504000d031507a2105440c0074060030403030214000409c140080c0d4580203803007250300b1b0381142c0c0d54148407203000c180d1141d1401e403411900d404002c0b81e5814001c0402920320840010302d0301c034109038000714008580303081142c46202c02c54400f4403294036034003407900b07204000e00c00d108084243c41c01c0e60042000303140440221f442c042c1c0314a255442110b492181010141491054900c00c2100f652201d04c00c01c0c0480c10031070342141401c5100004220000a12000c0b07801254035414a4006480310b42641c01c94000286808484036240c2e034019070450464250741e05250301901d4070304207207025260599000d840c90741410030014400c103000d15003904131030b160b075420400807020408000655a064400e43c81680c0a4207001e408103411540c8803504a20500403580d40c29107003d840c0d04204412036025654845280e0703088070905560103074101915a24a03450b083c0d02d4414001030440c50700c010f040e041d482c1c103500051100ca407 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 227830341 1250 227829091 227829113
    0x110a0804030215010f0306060603090f0213110f09030d02121c0f1d011d100507030b130c09050604031a040611070510180812060418211416 61
    0x203e1030054529581c403a1490712690f8002c0c40300721003051a18030002440ca10034410f0100c0d80340d019690b07030703500c6c03002e60200400b1118452009403c01d82e0b40700700420940b140001000101240c4c100715440700001d60405007001c0c1d80d280500c0554100110f40340c1e032001c40400b10b81001345401c411700e0003c0c0b400305002c80103003600928400c80a25010100900c0310700903034402c038000c120350002d01440f0501a15051025041400144650f010700c11010301c0c01c0352500a6607210784a840d001940b240701d4000180c20407142e00c0d8018006550fa00750301c4005074485040406080165002482c00e80740d541c90340900c4d000107000c07100030120040070808024a51b00203040c041d458000705902e8070380c0c0341081c1d500d4030f02c8901082c01c00c074509050b4040003102580712a0045070090b41c82c82c100114940300501246000305443d52056407108410007054203c1100d07070074140070f202c510300c0348001d01004032100e20040b10900c0502c00005219256291038800b00e8016400c1e0103900c14180c0740501d01204119 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 227831591 1250 227830341 227830363
    0x302060a1107181407020c0114160b161e080610020c0301021308010509070e070c080408010507410c010f050c03040c090209030309012601140f010201110a08040302 72
    0x1601c50b40402c000c803076000903c4101c0300c4c0d4100c440c0c41c0c4414800340d03a90040501080d0201c2e0404031301c603600b100c894015100d205e00c10003002c4030600d0709650f400c01c905400c8519001000d40300c803840849990020325050386602040c00b0007540d00030070344050552040100060302c50140b11029021082c82400070956400c030103000bc1d52245072464080c10480c081c0d00800c5c10541c603000005015500c001000d004451040d141740c40d4507103c0f1041241d2602500c1015520302104020010381c51109104040c42014a581c0d04114180d08800704c0c0d400c2d085842c0103164641503824107020302c2201d01d6242c0d02c035001d15100c2c03580c2e0b40c00c04181c450140100c1e003040d00710249840e0400203c000381d031004612551146003081006610383d03814100300c0c05183c91094069000384002c0d000c0b9401250411004020315104028440c14510240c105240076040311200368030131590074909041c9031628840701c003000d000030b00c124020240b10804600829028404000486e004103040c11f0081c00b008001c3c0e = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 227832841 1250 227831591 227831609
    0x150102011e1a09060d0303020a020a120f03140f0a0509010905010905070305120f27130f151206020702040213171b030a11031f090b0c040302060a1107 66
    0x140010806030000d0981c1c000608008034207100b41c41d640d260071201c0764480c00d0001c00b601e030700c11155241100290440800d607410b40c441d141120001c43e04810104035855429501c1c2c0f20240c0c3d00400043c180e03041c00c0001340421410f030341803000c022413200c070300c960000c06100c00258699850190501400d100c603009070003075103000d0124090001c041413190603607024030112812010b00e038040e119039204030380c0d9402030140d091008520790384c4200d1620794120201c05810145803000c0000903500504958040f803030726a12100e20250004c14002c580f05460711403c0d0070822840c040c00c1c410524004c0314020586035000032100115580d50341600e42c40c98424000c104200e4444016903440c07001c103265510a403160102000c400281840012300340000076024165960851b519110300c200d042040e550715014204420036001c1514010030310b1140c030f01034042040c1e00c2605003481c121001501c207407590740c800c00c03044c009620740c0000ca40d80780d000c1d480d0540a00900300c0d4010300302002a0040b20078 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 227834091 1250 227832841 227832881
    0x2120414090106020604051504022710091803050702060f070317130f020f0109030b0a0f06050603100302090c07060504140c030c010806010309170307020f0d140315010201 75
    0x25000ea04106400840320541e001c924598032548140e030b032a50211401089030703000c1d032203600154518440c800c0d0000e10191002100071506c20a07042e00c00c0c581206001422581401c0083c0e11082c1d43c440001005100d000700007220240204c900d5011049130b010701803100000c0c4480440d180c2d035088405030110910b01c0c9403075901a140080121000b080142014280c440214502001e018640244594011000104030400b030b802e000c1104243c032002d9060008024000002c9250b000d14144940200a80029440f46800e01c0e8011a80d07a600403038003c5034140200302060000940b40390650740c04483c014171940d0360110071407080c40b5031400100640e00344030a0004001101d60900e102201900c140d4048072441818950740d4404000f80900040c04603011403030a5019030b01004050380658141c404900a000c80740107264001c3d50100c005a0007814079441c0300c20240032100c0800014548a02a8502c82c0c1a8252900003d0410080156044010b0f07010b68000d5001a040000030302c80d040c0 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 227835341 1250 227834091 227834099
    0x90b0f0609011509120303061a0405130507020309030a0b0615071a09100f140114090a0f200703140a080103060213030f03090504050603030c0613021c06020304300f021204 75
    0x8081d003068400c0400275074501500070340010f5950141c0d000c2d02d4005d0800501110804103c40207044050004410b50004201c080483d880610048581c1409106103280606000b010702c008c0400005188201e034400f880300800040302d0003441825508840300a54180d120034a034a81444115041d2160451070b213500201449529008541c4088204d0003402150380d0740c80c0e881d019580181a603a0b8404031039000111902c1c0e243d400b040c05109218800200c01b500d0250788070942010812041da0301001284107810103900c207c2c000e0700ea21000c0300550a100800c80301920400040c00005c0c100b036008560b14044803280e030000801160003600003041011030f800c2c080c10114541c018075001d14102030018026090000441d4810368072540240910703074031409101050080c90074226402044001c5d9407a11a01c281100d4140300e000b8800143c0c0d07801e040c0f9103a440c0600110400840001d403116100b00340484803501c1801111301c0c10080100c030b00046049080000120703820b03000d400c021601123 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 227836591 1250 227835341 227835347
    0x1403040b06030d050a170c040f2405040f12170d020a0e0a1503090807080318012403060c09050a090b09011d130c050d0303090b0f06090115091203 64
    0xd0040c40142c00340d40390444084011071310745c460041e007603021070102ca084034049090350303d071181d00c01030b506160f900302629904081e610022070307400301d103001405d8210030090502507007500303542c030265041240c68603282c6640c05500074101d11514101801c0320380300740d007808080022981c5a05042c08560399803040c0501081c000e400ca1814a40000c00302c161f64440c0342804e208400a694a10305050b00c0300c411441c048010f446143c0045840481c103104e40030000311008013541c050520781e521540c040596a5081d402c40ba4032240700300305890011074003205090f9100104099075084500890035031910402a104006964040d54000701502400500080282d00000b90418103c5000002e80d0344c400741e250030790958650401d01700d0081c0c0049070103036400001c442078091007a680c0c41392a80e510f00c00201503048124041c1e0110b41c5032144003081258201d0b40c0340c0c1c8072902502c0c891880c02c1010110345240750501803d03d1850030740031194030041c0a421a08001e142540400340e808030207140c01 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 227837841 1250 227836591 227836613
    0x111209091f03023a11030d02120d021303050303040317011511030702090907080706031b050903070f03030833010807031107050a06050c0c1009020d02131b020d0e0907140304 76
    0x341c80541c0840c2e41e88210340340c040307990400a03209500404c1684401c0341c274019664005039480c15019420000801d00170680018100214082e00c00b4503264074141c14050202e440040090810414880050040f03011643d0074002c048030358034004000741007200c0114035510507694040d50004008040244103000094689c041c1c80558050340d004a55905081c1c00f900c1844207120289200c03040d11a16091081c0058034950f82d0060445840e035650310011001c1c080740790410380005050b0001c10004644246121288605401d51420080506083d514089070901201810080e0103008141e0042c0303c2c3d046085107451009030130742e0b00c0500e841d0055480e02c1e10345080b0740e55410300b000960441d0600c015910045041005405c00781c0344540c0348402071a03000e4080381c0c425010f00400300582c0320201030b40d81d1241c4010b00000c0100780004030902c40711092400c001154402c0007030480603a84903065889401050303174050740680300c210741550000144c00c0461380100000c000c10051160303103191 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 227839091 1250 227837841 227837843
    0x615030f091b0a1406040317070c060504120f020f030304120506061210051e090f1506010903020f03120708040e070503070f050a111209091f03023a 65
    0x1120081100c01818408404a031100d1560000c802c0700d0030443c40341c80c02c0305403515404c002d150340d1502c2d4503555090100c4a480003418184100441c07610100401781124001814083c2411800c1520b01540b074581030300c41100003000c20b0140742c000e80842d110342c800d00071039860007015603032155201e2080440c00b0050300c1d41a17403288101d802040306400d1120201c80c00040503c0500000e030303c20b0081a000d0000901104400c2c0a8000d00740c4c8540800f010950186040c00043c1c20038542407800c0c14607051402c0b041c481103111a0040c032030780c0c2e0307040040e00003125416506401206042c0001038180319071800814408203001580d0020040c3c10300040c4255181390b101240c0d191600d01d03007107d250004070f03040000f080384440503294803800f48000d13004840452a00c2410b019074156001d0621030042e00d00b01d01d042010400716254a07080d580e1580c0000c24454004072001c920449201000d400d100190003403031a00309105c1d2000e2051180b00800040f00200030036454150000c848159100c0d02c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 227840341 1250 227839091 227839093
    0x4051c0c060221030408030c0a0912030f031b02060604090303091707020a080109080a301d0303060a14130509060105040b04050609040308100302030a050c09100b0708030615030f09 79
    0x1507840300c4080c603d01920b001d150011155811940d55204641c4560b1100121200b4403000301d8002440010100c40703030700002d22075510401007403804030028054a140e4030b5100c03607601d480340c142d005442c0d0000341ca65204008540100706200035080940041a2405001e005003425901c1c03010710115100003021586d1080c2c6055504940e1000001c2c200c0d403c120004015080c00c001700c2000c18403e84101c41c001c0316010500000301450b007803211032000010000b221039600c400d003002d980c40c14404074284034248500030f9031552409400007a00d400c0c060041c04250001c0c09400c00c40d40d00e07902e80342d2105600b001e40800c494200729000c0d55541d2024851540f00b07a0800c0460115400c0034041e140c040c40c1d000c2c0c00b043e802e1b110341e607094030b0444005240c18407001c40640000301503501042208800c500950251070600b541c4018030091010060a00880c058580000c001e03008086084034100354001504903200c0e1500c40020399428007141480310700346004410b00030700081c8400c0c56401140848 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 227841591 1250 227840341 227840383
    0x230301140102121804061203030b040c090506070624030f050c0a0308070f030e0316030c0b0702130c1e0509030d0e06040509041a0403020f0c090c04051c0c0602 70
    0xe030049940e8a0071101000c5901010301a150341010380c0c0e404a00d2142d0300400104400d074684008484001e4004401e40000b41c882c9481c50140c10303d4451800c07540701510700b00141c0e50400d0045150fa00c9002002415140d850003551424900d82e074903090058209541c8041c1e142d96070600b02d461440c1e5000503600d9014145468019140c0b0b0004981200d45c0603980e181400b60035150081c40841050f000d50a11495140d140003940e814411200b41c00080e511103540141903082804000e80560004024030504020080159880701d8000340516540240414501600c0d8807c4410305071002c1038011001c1c500320b100380000d030003034090403040b0410b0301207071380c0b04504003000c58940c111035100d1504480104002e000300c3c1400041d0307a40c414040e03983d443d030380d40110702d0030074010104032016801a0480200260554400d1089100805080b11000e01a0030f00c031244046c9031089102d07080c8541c5016541c049011a0b41d400510031a030454007000e41c9541d140300c0603444806800b80005122029 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 227842841 1250 227841591 227841629
    0xc0d0c06060608070f1b02030303130506010902070503070b09150103060614041a1201020f0309061621051305060a02030703270b070908030d06061209050d0e01230301 73
    0xe00103444c0301c2c0700307540c1c2d42c84600407483e00c05544481c44450440521089440c035800540c0381000118041c110003103409408200a060150601f0b80603007200314040c0c0104401c00101c0c1c0c00000f602c1e220b5030400c901401343c0d1211441c0300c1ca000c0f000329030141a4180c18000005000c02680f100003201d00300a007558190132440c0410045452707965104e0036074550802c2c080748500b080d2480e00390310040394000514164468014007041c2d08100d030084c1d0103900030740401103000d2884841da03412900ca400c102e003101d4000074400d0002510070b404040450b81d60f8000421b0b1491003900c1340c403000e03040000d954007420484406000796204403a0031001c41e06141d43c44084044040c8048003019500700020a00ca89960f1050461240036210340b0800c0240800032903031007002d10042104c2c03511708800003555860715001034400704003046148030451500300100c01080c004556103c1001140c41d00181902e07100c801030380d65800320250160048440300304d806888100000a5060b10402c0c8149440d250782 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 227844091 1250 227842841 227842847
    0x6120a03080408030c0405030a06060321082d070906031a030318010203041703121e0402040903110123010905041e0602040306091a01050a080c010c06020c0d0c060606 73
    0x110a000400094248001801182000b4050354011900b0300011385001d80d50b9000a242814805050720302a03581c01c400c00422031010000b800d001e030075405103007051000540250580100625031000f25000b074015082c00c403801981ca003085040714400050740c2c1094030000708405901d0040303102080c600703c56041550010b90101d426510002c000b90b2406a101c10104074480c8541203541c1941f00c20302011031044401d0400c6521928060000e40c2c03a03c820400e000300d0b640001c0c01c8811612007480f0402c6140d01c44420041d40150150f41c04a00140d4070315086848d26520140c3c643c4651801c0d03030034030498202881e50b45080001810901040e625a50f030a0101d80b01a1402801c043e00500504c00b00c0059400e90400d05008890060405a82e62195425246803030422a41e00403e020700c7c070f504001560009024203416202288a60700304a08140e844c5000725105060100114038607040000740d40417904c10300c0216041c0c644400381002c02a00c140c541007400c68500341481d101242040c4 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 227845341 1250 227844091 227844103
    0x613050108030a030b031c022b0507080903150c130b0909060108100308030c1b120904090618050105010e0a02030f06060705011d21070503040302062d030612 69
    0xe010002d98600351107541c06500034a90a101c094042c0920448548000d9010159010300c0d0040e401509160080f0120b84081d80c104451607050100e10011540805600c4010307182000e9001c107141d41d44402400000349400b003031034182c3d40414001c10800c9443d0044101620400803072401110826480d081408800e01641240507000b1340500300040d5958030030f511454000c0c2c12003925940503501c0303850780c642503482101c00c0000d08000003000c2190007030b11107060034202c15180117013003000500d41140300b5070722600709594821a2100c041806004050b44600120001002c40d41c1250701c040c0303440387c00b82100340304030300c503110a000000d0b6094a8900072684540011072281d0f0050b500ca01c10050305801840d4180c885640e18400c100b0043c1000c00070043c000c4208006107203a80301441078001406a0818110140308207120328030000d100041501c09896040b900070780c8421112420142c801a1520105800c80007070768100882d10414000b5401000c0c1640c3c80c0d16a896210060b5603100e07 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 227846591 1250 227845341 227845349
    0x10306050c0c10060501020f15040206070f050d020c01091509060806030c0a090507090518070807050906030a1505010c17070204110d0c0e0901060e0d1b060e042a1211040b0306130501 80
    0xa10140001d2b005241000041400604c125031600d51044e494543c1480c00c8050280c09002da8002c0b0012079040da00810440e0040c44001c0c403400600d03901100c000c1c6245a00d01c03038030082c041100301140c3e0a0b6018030030450f030f46c08003800050711180c0d0b4000306001b4020680c0c400c004a680e0141c0032600c2c1c208820101c07020303145040c40280648500741c0841d5450390040035041001810300c0300b40d0399640c8030b0f0011030084147c2003000c500640304016000894a8507404503051008000306c0d803000501140703824902c0400450304940320130050000c500509101d10403920070b0003000401140314541503000414900030742e65090340a12080080c070445000a0040720046100c004240341030386003004030555124070130010800039403070300005010380030302c42e401540c0420300715031412400d030a00744981d44011380100c01303503030a05494001d01d080c0c4c1e0b41e40b20b15200030080301c030b41ca050002049401160001c0400c9207259622a5201074200103904103840b90303071250b91900552894151140502416071b = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 227847841 1250 227846591 227846623
    0xf15060530030c122b05070e090907030f020f0604081c05120105061303080301060e040f1a01110a05072303010e0607110f01050106030c0f080f010306050c0c10060501020f 75
    0x40031881c0400c041d0010785081c9050781c82c3c150b42801445144e0705c10000c2600e884808102414220700141045210200c0d260007464228100302425400046840440e900f010308809007015038004500c4854030008190b07000200050005602c4000148120500300010040e281c159942201280c10307100d01e03000d2028181001005024524064000707007a00c01c01c41411034500d03a0380355281d141c40e400c2681720902043c1540489142801c04d4004c0c81c2070003035900e80400030483c1552903039110282602d6683c1c10040c1300702c0180269203042100b410450740160440d80055a100a0758000c003031012058400c54240c240800d24a06050040503c4002c0c3c5202030074465451000c211500c07a101d483c142400d20401003540c800245c02e01c07810740600019900410703035944049000e80841d40000b42d90701089000d104124036036042001c06c50560b0341c0190080f030300781c480c1da40000d0140540b181620160084e980c080440c00b080380d0001003100c40c02c0c0c007515044030f500f00d401600c8440039500301d500 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 227849091 1250 227847841 227847853
    0x90612011a0415110109020a03060e120f1e120108060103140607080c1602060c01062103020d03110c010c08010602062212090b18031501030f15060530030c 68
    0x41d01132641c50b6554100900002003500650f00024030041150b4001c0d52920750f180d000e41a1040140300d2a0a1410f80b0903c40f49001c84880c1a6441e905c2030980b04807045081482d00030151004500312280046000305030707150303546c5031603d02c0e4407280c0c28401200c00c00c1c00d84140d4200711201140c445c1c452041ea0301c0380740c02c3d5036400c800392655030700490f204101c011280c1140d800598410018100180c64000000b41080c244404400f82d4442e10402209440c01d0707241350310010303600182d020001c00803458041000e103401d501c2030b56503010b071040c0c412255003045240c5480d9a40100b900d4125100d603421941d041c1c45054130f401000102405484040d0b00310800003001c2940e0640c00800b0004a242c850146c60740d0301400c503815004915101a81135411039403034078a02d400c10400184500f07a091803102c6503d90380d5410301c0200f0a40c0001c1841c0302c0b51108120585255220030000c0c10090300e54140402d1040140c5500740200207200c99000503002502c29416001060310301c003120410042407 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 227850341 1250 227849091 227849129
    0x2803020d0c080c01020d02040f050a030b0a090602040312050a030c03020c0d0c32010b01031406221109030114040302030a1d271f1a090612011a04 64
    0x20307071010300704426140b0003001c010010400c0c1d024402840030b1360038090010385480c02c0030310241c0d001c1084d5110f107200e201000424000710300350302030403900076048100000e1005518a044000303401176a00c080c00c1e403401d4a0885030a203401100400b010300141e80e04100801c20203034154124001e0000015232343c0c1c400c41200d850907008049154505015400703440c2d14901304c4d8007090712804007110103410703101c0b04026500c60f1102401140442c003800d080c144441c41c180319010b0342800c00107010724446c0082c03170f440c0d58851540c40e52240322442c0d101d13030074041289040c5142c500d81e0304c05042c0718003a40c43c00c1850182c0481c81d00009020b80d41c582e0186140501041b000c40320405001000307a2021604444043e49a5902a15504180c1d100400b61108140300d5002401128020242612004016050403805540e0343c00d14040c0c0d0309002c0c4140d021a5500031149041c0034070b185041e008100012074445114045424074100c6030201c4421444072003000f4540e605020700c3c0b00e03400c0f04102c0b5501c0701d4 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 227851591 1250 227850341 227850347
    0x601050a02010b040213052e0507021305010b130b070b040204051806100303030e0c09071b06090b040209090d05030c030a23100f0605070f020a03020603092803020d 72
    0x4100c0080c988004a501008a030004040f0380c0201028140c2c4c2ea0614020491801d00350780d980e480721114407400000340a0f001c40000c4040c0c072078030510108031000074a0000c554541c0300aa02880070a54108402e6842d04218503003a842804100c5001c11040c00c009410924903044070f91040e4024110135194490f80d0a010103410040d0100941031840044500c2041080201600c503da152a030091175034650f0a015044901c0d4003c8100650044204030070309032112030600d070b000107041c509044450a10070733a080c150403c070b030402011a07003425070740814050100b032154000d900841e05840c01da100d20b22041d64070300e202031450303000c243d0510000e110b100003000a986d002042e990041103e44e40a400802031074001242101c083d103c0000344078ad0b0320380156091010340010006214075030300744030000c1d1840c018884018075001d0103500040464544012081c001e40d805000703a41c0300e0a200600b80e031100c45c15003252407180350052010249100c2c40d07800a01c042d8154000d4110140014021 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 227852841 1250 227851591 227851597
    0xc180812070f0506090307061103061f0908030a020303090118050a030302250b0f0601030506010c020405041e080d0c0201060303120b040e0610031406071e090909030e190806060105 79
    0x25a0807400001460b000300c2c0007408041d10811002c0082d42d030b01c10341454440219144c010a00e4103a010a104210858640104d8071100300c807a41d24041980c2d01260044802d504950000c0009010201c1c0140700d258001025500503039000c0020301c180f02000307185504080803404040e040d07601c83c601403c04217001f64001c060114403011405510010915009800303984d103070007100c641c9a4101048464819000c415070409000d190074055402c0440009101c1c2260107406407040e541c6074081401c104424000c2c07407030702050400e110240207840c20102c080d03820628500110b00c0c140040e40982c544103100320b00c00c0e41d600d0b4541c0100150f409900b41d0040a00100c03140d0000d41d5034003165200c01e000c00c241380c440c42d0741e160250340c242c1c1107140c00424150050110a969402002485020b50300715442908044040fa5030090100c00e95008441c40c5045a02070b481d62460044020241a8850082e5002103015907412000131310030704280c01400601d111b0035043d900711b600451725075840b513002 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 227854091 1250 227852841 227852843
    0xa0e0705042903070801031a010312110c1002030403020a0603060e04030309050c0d0c05030706081e040f080309011a01050712140715060501020c190e040201050c100c18081207 77
    0x18900c0c8a911540c2c072201541c01920280d000c110750300b00410030000d0b082c1c0400441185991418041d514503504c1c40701418420005230188042403014503258070b001c000810940c4e138020714281d9072032145c0c0406500d030381c005d000982c0a40d9904502084072802030144804407189121203031401e594036103041340280021381c5c081720316004006034641c1590303880c1c007000d808034003400c0380d2003459107414105450b203586544403034103001c0e03000c0c00c004909211100c23001142400000102095560f440c0515030001d08400091000c100401405000343c015480700411401404801c030305100640d00568842c000c22400810404001540400440c4955540c1c1c40c1d4030f8084040f5410400155651a00c80a07158540b0307a44030707900e5608118942e0b04101078000e0407020341d2090a200c00391b00c2c01c0906a0014014410034507106404102164400c0e02100c400311104000c1c3da1412a07280c0a803800b44c4006024900007568407000c91013102d880c4000001110581c100034548424050215405a041820 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 227855341 1250 227854091 227854139
    0x604030f122405031b011704020d1a07030f0e0309130b1c0605070e15030403090512030306150309100509010b0301020c0f060109050103080d0e010b03010f0b0a0e070504 74
    0x10340d10020b004280401c0c0070008481401035070b0076050005062820300c1034000440c440352600c056800c2a41c04c2a421040085019040516503172180046030001c030103c400140700100e42c061020021540e000718a02070020303660188404001c51480300c040d90450204440b49400800010350304e498002d0340c0d54000c1e41c9060f00810301074000c1002039554003054074803e0300c0b9056920184108103030b9104036984800c043c00c00308005000440410041b0350000302e00440d00314004003050a15014010b4080207201c01086034a420810500860301c80d0002c1c2c458038040d45c401e14030904c1e03c01403403042d81d00c41d200c880014042c0340403108640d40179040140828100d07568881d40c0309a280c40038002091030f4045000140300c0250f40d01ca2103854484149d1044248a103024010300008002c501140c001060394040031030139031010780840340181003040a9941c50741c80c00d0100c4510400d0354000e6014804201c4204074902d9548500101d1910200c54143c0024410041805243c00202101440e002451 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 227856591 1250 227855341 227855351
    0x1030915050c040801051609031401090602041d130201050f0702010309050d08010e07052d09041409010e031213051006090506041d0a1203140c040e07020604030f12 72
    0x220603141190810382d0001400040002c0c2400b00d22000d00071950010401c0294241444a10500905160090000501540c6042c0401e0000d403001d4004a201e9a00b00c0c40442d940d650b2014002569860302946502a944e140006080c9031700700440b007000c694040c0c4515140801c100a204242d6001e980100c0c1030541d201d01c8903001c11002c21014600b440a0344802041d54140601480503c0000f030442c0104981048941089101200c14800034203400f0030041c80b00500034200007250280f02c01568202e494491b40c0300305419540b04840c090000b8030020892000e0019010744c491041c42d900a01c44030760035000c00d400060045118035a0381c004e8041d9681c040d059004034003600c2d80c61340b0a043c1d081e242c03400d01619181500c2402c2060303c0c1a540c0611442654081e00d840e00c4007075102030300d0a01305c90241140a402504414000c080425045103245450740c99100150081c0c0030f03803800c03114085c00090380c07240000780c1c290103950991281d07550300d0000035003212101603000b44400034036150 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 227857841 1250 227856591 227856623
    0xe0a031b080c010b0901170c04150e1006180303080118060b0304050a0c0f08100f021b1c091a0306030c0d0b040b0615090d05030c0303010e15090106050405010309 71
    0x1480603100503042c0c003001080d041541320802070302160680200d10f201e90200d000c41d4440c034000400c7c1e010701400303840200b6000c1d0000c0d0724150f0101a03034886511420a07400304455140d1040d07095066500a4840031600440c0050140b941d009500004000c034055178014800010b03c0d9100452036400c840001c601c50782c0b02c00b007162464000355001c442c55408405d8a008029048450401410444001c106101d203445805540d038a205410192403695074181a41100400e804907003900403200c1d04000458240c04070b0540c2c8e88d010403280240f561035055501c1c1d5051081d545001161107403d0001a44046007110355a16403015192550600c122500150741d92180d501c100c2d40303140103100e00d41c407900e003a06009030380ca0b600070b00c1680300da00d0320f2000c0f40682044030700ba02c06000d020384540c0ba03d1003a078034280d807443c4900c80001489100c040000254040b48a000c3d03441007281040c2049611002d4081c800460801e00540000c510300b8001030000d94480d6000044045c0500c0ca040986184 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 227859091 1250 227857841 227857853
    0x90f06070503131814160e0a0b0c100203010311090c04030609080901080f091e0a0209042406050603060907030b0d03030203150a0503063c0414010e0a031b 68
    0x20004032020040d140709010003c0c035090a03645043c802c00d0800c107009106002000e541d021710002c21000503414400c0c40070110750b1203a03102080140018054008560700e036150321803640c001e400a03980710310800419400c20462802524100e0b58085003000780b943c0304004010542c2001040c500300c3c044280800804180c603406142e0460780601002940c0b4968040010020000205500035540d695018084005000908035130b1224a0b070f01b038203101444101c181c03070800b0541c01000c0d42c08051401408240195030350059200444d80b050048030316918840e03401550060b01c01d155210006000084280c140421060360040c41d505e000200090700d00d0005a040d2100c0038251f000030b42c0802048a219004108501381083c201d40b070007642440c1200103507032004001c04007080071422390441c00c00c2c5001000900a13032503070121400500040c403480350a8a200868003695042c1c0710035040c14141d0010b00c6210010b080b810040c007240c00b61a1070640d90710711800c060511103007089007854013141c4 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 227860341 1250 227859091 227859097
    0x1e0309080c01061d09011a040b0a120501051006090608070818010f090c091416020c030706030c090b0c030318030c120301170f0346030c020111090f06070503 69
    0x8840140c00704e10101040030090000d80c000d00c0c1c41e03241da24003410346100a544034007002108108440102d4540c512801144035030185510407607082c00c812400c9400c008041d00a00d11070190b003402d40d4403140c0d440000700e400c0503152141101045800c008501051301c80e01403c0da001480c102443c0035038003070070703051803c40b11481896003000740d45510940800c0108051070004242e4110300388010b021444051040d40c90203004046c407101004150110b041c0248400e483d58400241070302c45641e40d0705405005003600c4010800014800100400c03480c000000b41c0d02d03100300300380c002c50841da603030441407110009110310340e44148130500070071003401420400004103070180c0c04d48a84035490300c01d4488ad250400e01e10140e042d0030005100c50b0208000065aa103c20703090200050304940602950304036050810400014071558001c3c41e02d083c40103443d507002d07403581c4e0b010001d02c0003802c030803400c0310052100604e01c8001000f40b48240c0c94900e0a403046508020440c5103404200e60303d180c910740c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 227861591 1250 227860341 227860349
    0xb0301031b0803043204060806010e0604020a050403060b010903020303040807090f06060f210504030f0e01090509070f03020d1d0d0306050904030c05010902032a011e0309080c0106 79
    0x10400309030300340c5801c0c5585080040141c88000c5080c2414090301c1d190000c41c4a85c04884145810110700e100fa003640c1000b03e1004014004011250720740700d485440c2c05c824065003510200d07001c0460050706141c42211100705850340e840e814141143e88001c040c080a421290401c00d08010220260350148000c1000308a100010840c80d0301d881e5141d8142c41d50503980f000300c24070301501005200e82044000804110703e18003003c1c01d0700c06034100c1f030b902d821494800307020ba860300b03080000301900310307880c05c021080c40e44982102403100001110318050303900035560064108408119090701811504031030721420304015090019803c00c030300c1240c072581e840c00341c0744e0658007ca1640400a0004800e000030702e01c2c00340141c03030405011440d900005400241041602d0001c40c040c00020f40c0001045503005083c0c85c118611a91244c41d18203ca600c080102c0440744848565036028100841c840c06100445c14003424013401c0a030006c10846009503070504c030400601c0600302c1c0c20712442c4050 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 227862841 1250 227861591 227861603
    0x409060e010b030f15070509060c010204030b0f331206132108010e0403030207020306070e040513030c0b090c030d02030a081506030a0c210615032c070b030103 70
    0x2da20040c08143c0f800c10f142541e00d200d0b8000e283e20131a00001400380b50f0740603010b418090f6407400060007250382da100b00d43d4070b0703007140d40b0128011040103400e580c181c5c01441038103204245a1243c3d01d4081039414003200c4821500c900707034004002680d000703400303034030b458401440c2c0400c100c1c680c60a039052000c01c8030308600c020886c401c1101003003002110f024601415401040c41d1901d0794101404808045c041c1040350000400050301b050b1003a0121401154090207a54103400c1a110240030700007802041c034071a50a1000180c01c000340702403903003456a010381d03c0900c0202c554540c80001e60340a010301c1094041c050f203c00c1c99840800410030701c5031045d030046a9548852070010584980544840760b13000c0d40801f6200140c0c1c031030040d2a0002c008110004072000284e005403001c0c000340401e44000700e040509440c0801e1030b0f0f070042c1c01711090703d4600e0311082202c0c2c504604450320350380d1140c2003501e4040050800f2414154071030004c0306d03210072900450348034024102c07150026841103600f = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 227864091 1250 227862841 227862851
    0x917010e06010b0702010c11030c061902060702161e0e04051e06040b0727170705060a0503070503040c0506040b0316020604050d0f020c09130209070e0604050d020409060e01 76
    0x2109108000c07240c0103011980046043c196240e00082940c0c4140101400252007506c40d011155804e10011040140c003e140c142e5641c0f8562000c208042e0f840441009406800c2c0001e01d030500119407000620110130080340f0507814440d008644a070628100d225968800c440810301c200092220b5000d9402100200f0b281c5948020080034440740181c41d5065030044030512000410003512590403c4035070a0402c2000c503803030004c00211345108060346d6402c0e0700034000503c01500c3c400303010b400e071740101c1600c0a00e82c899080c00310900c82d0f21343c0034000483c1040042c460728824005540c000d40700d00200715401d5940d40004050380c01c0360308924049800001030202400244c000404200b42d00d001801013071800d5250300d502c54400c0e1680c802444514041034155a2003030010111148009041c0445400c00214414205116038000c90084034400b000c03d407018041d145500075080000c006900c0c1c0b074180720030301406905650b1700b05d0b0041c0c0c0365010800001c00c14051341004104403400003074 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 227865341 1250 227864091 227864111
    0x20d0605030709020702130e150412020c01230703050c07151106091b2b0311070f06120605030618010b040e190f0f030207081006081b01091701 63
    0x700b018003070750000b04098070400c030300e20042c5c480011281d4a1018801e000a640c91051803160400da2a1803401c02c01049180c00c11080151010303605030301894960846194004c000c0040d1011100d02d04c1074200043c42d8040070826105040003401d020f44245003160402844034080c07071074446990490320400c407801c01d01b13007030417030b44442c0040e09034443e17100900da00d05104422a4840c0d00228001c0c0d070540078801d030311000d41c079403001c0050044071941000303000815000102217032694075a82140001c0b10003030b840148a2000418800b541d10b0110318454140c40d040c41a698180e4a02420f240c00b80c48507800980c5039028400303248500301d9a880e541d52121000b030940e0846441920540c42076203881c5901d582003100240c51000210082c0340c5030b10030192402c1080c1500b070000d00c018014000110090205a800b180b404221141c0f84200c1e15502918200e20003918824015000c083c0d0000c2c03034810892401102a044c0b01c1307018100b00041daa11500c0106d10084241c0407010607a4554403101 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 227866591 1250 227865341 227865343
    0x31f0203071404060e0906190f090c02030c1c02100606030c09150504030b0c0c070b120709050607020103050a1427071a0706140f22080f0a090801020d060503 69
    0x80e0710005040c10300c2c250800b04068140d4080f03030b4069005000c9000047d1950f19111122110601307007501100220380d450181d0b5581c500c0c03e029507007205080500e003150030b40c0000150b8840782520405400440c2003a88149a01c0c2031501c070000c2144154011040d00d08560f109c0c042c041d140560f00411070f10840032004d004071400b54008080644c00c50f08501c3c2c0c183d4090f06072015240e005080b0398850f101c1561108040c010410000c5c803c1c05482c200140b07414880c001042c044031502c1070305038a41d9174110b040d111740710f43d4401c0c01d070411800c00c6000015842603200e00d40c023610354580094050030350848000c81c040d084402c44158580ca1100d01150230403d03526180100122004128007814405102038411050b507111465007008905001081074a40012114a02480c3d80c5455440d1801001740c62200c10786002041d84245180c00c400b0107001c01103008a207800142e981d180c50713070078080079075994001103000e02000380301d0102140940007800185504021190007040c028184001c00d = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 227867841 1250 227866591 227866607
    0x5030702063712020901110d030903110606090a090203030c0601060801060311030628080a1a07050703080610020111070c1a0711010f203004030b0402031f020307 71
    0xe11005a086801e020b003465001010903603d40000f1405a10b401d10b450042e1190054a0074080c00d43c00790f030316109600d80e803603401080814041c2d070316032070091240d00610740c4601046d40c45a4003d10002c000070403da101e50071182072148003070308070b07481e054110b00b00b1814003000381c01000020f0482c10040080c26458000c2c00410091120710364690704045000640212920320903031224910340e920101c43c5200e00428800901020f42038aa07410040d141c111240c141103988407410116940100b0503051141c4252015141c0c180c46030b040b2520f840080025044000303403568110364a8214040070b802a04004c3e1030580d1180080d011036608011000707903031941d0702c01041d08100c4240295130216040c0f01e400580d540c8d0a090107a11910507000460f01c9003090741106140710b8a502010344204000110b0082e4019641504c2921030075002c20f0b2120700180c2c10342c10411020a2106001103112556000d802034802001c542113003404250210741d01c0260301d070030308009a0120400c5022078000b07003d = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 227869091 1250 227867841 227867917
    0x8090a0f030f1e06021209060c0405010903020d14070b0403120509090a0f0b06120603100b060714011d03090103060e0c0405060c011b08010303030507080c180a081c0e0a1406070503070206 82
    0x240ae090504100008105091a10000e40b00c0c03620100c1e0f140511075021310b50300da01a00c02043e01c0d28a0345524410b56650300911045401c21840703800d40844c103124070140c03079032107030b005090b214542c40f100304207406400510004440c1c19034541100d191660783c000202043c60840b41040200d2401400301400c003000301c84482d182904000401c030041d0707a444102c070010341d0301094000000b142410351701c1c0148558040c4440c10305000360005250100003001e40440c2c8005d82c0e041c007200d51a1090304100203030541d03c54500a0050100340454500203000c1c0c81c0400031000001440d02e00c1c0b0000310f080180140090f408a02690018010326030316004040e4015060b003003014a0341408200b0009034800e081c0207050501207103803828025034407030030024024142d15044454a103010100e017481d81094441d03550115000710021240d90074250107040c1141c034800540074550348190140616a848000c0c00c80d020301081180500507a00c1c0805003440340c26500502080c4400c03a6500da0401450802d = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 227870341 1250 227869091 227869111
    0x121e060303110d230d060e01031401060602060c0d020f07060605030610080c210d0f090501080c0708210a090c060c050a1407030f08090a0f030f1e0602120906 69
    0x110910311900401100b1001d2130800c007581c4042c00c65000f9040354003820444030030160810b54006000003040460714140c9000da4842c241d14130781c100e00e15080301e54a104043c0542c200000041c2c00f011000302400c41c2c070304c0d01d842c0035141c0b50507400d0b0308038582d11161003103030f0b1647d81d0b0209008900741080300d50ba1003100540312000c02802c01f6050b694039441014540c0c443e4640d181c1c1c1e420340c1601010a030301d2800d42101142d0b08541b41c04c8028000100748000100040c000d248002070300c3d07101d12400780c0560840c01320750303180402c66140d0750000c0d8071103450403682c911901100503000c045d400f400b9103d1a0382c00e4000401007001d00e41450078446551242d000c1001290305038000c21000704481075183d030300105031044041e02c114440d040c0010307544050224500f491000003030001900c014201e0032030841e020220551103440f1804501c40f1408040c1c08000002d00401c000b90002c8004120002000e00554441c02c1c0c42d41c921040e640700200d00c12a90f08182c043c0911a10101700107600240404 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 227871591 1250 227870341 227870353
    0x310170601080705060d0605100e040b030c0112021803070611060114090a05150310020904050903210a0f0e1501050603060d0f110301050f0106260601121e06030311 72
    0xd4070300c1e07595101c0d0b000b881c0c031075100046c900030584c2d45544040018080580802c0000b04500e4020b040100100b080c14041d6060064281a0740760205008240d408140c4400d949070304103035078580094021003006101c285d01d0784e000c0c0c880d9a030200441e40041c9100d80e10f500da1390040480607410500181e100c403015030f08024102003103580f2031b21850f0384447d14840005590352800c6e440c18113010302e41a03554044c01400013a601004554000f800d8121080e03e050001d5150404501d44d04e205071781c001c180910140c2080349c0048181803619400c4200c01d20302081c950030750003004040f0b40e581142070441368000e58401045500c036041035401004116041801c52a0690120756010004000140b000f194003440d1003c000f5424400d101549010340204035a10340203608659516080c058040400e0b800030b43c1801043c040d4007409881d4070b0703206018603a80c5880c0015150403914040d41038200ea2500d10a442e2081100c0100c1030034444604013051141c51401d001c0c281c4400002c101900d1f400c40 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 227872841 1250 227871591 227871599
    0x9070e0c0306011b080a180f2706081f1a03190302030421020111060415050c071703180f0613020a030501050106080114030c010801060e03070305030310170601 70
    0x24405072503201c9800c2c01c2400040f102c4c070b29015201c00960000600b004008200308a005a0010310081d860b000359040111964880f101d40380a00712620450801251060040b907004442c815001c040d040c100001044c12515a1b0405081c0010a160003108018840006510514a0050400b018007001c2030090360340003040401c5c2c40c4c0c5680b5100038015103840d08088101072081044170f0040031141c14130340c44242141000c05e132045030302c942680000c2d0340050840c004440420703050b0040d0b40c04000d100e181a0660184c0001c3c10b0000c0c11a0a600b50901c03540f00824111144541075101581000e9600e141c60f0700200b0368041480d4500d40c0682c840d203d5038602c03100c000350321600403d20003610200c55009100003410019103420040071542450000079000740c000c0400e506070380001940540c019011421b060392180181c81480c0003c4110740100000b41c007a64140102000180548041c0ca8607900c42c54034603402076498466a80040900700228000280b5038001601c055002c0d201c25450 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 227874091 1250 227872841 227872861
    0xb04051006051b1c09050603150d080c060a0f15030f060b0406150206040201080c3a0e070e0a06060f05130f0303170a1e050603010b0a0e09070e 63
    0x501400c0248500090002200c118410050143c041c8010803201e005000658a50b5000d11145440f0040341c40d115021544c0d180c0802903030300c140111070004071424107010410004035218074095070192801c000002800405024444c480c0854200104071410002091400c488010b000411005050102800003803000c013200c3c521103400c41004520074409400280003030009500014180d051161b40c500f01d9034000c580c1034030960007601c44045c80c0d034800d004148184240c103052081d0308080c2984020301c0300c0401e0088aa0000c61044404041d8941507940407220309140d01c440651205500b00b0580c0f500c08891917222040c148240701c05860810050001030030402c42c402400710204036809050100e00400e0000c014105164410983c2c0b414042c11000e102c072001a0740d14020300000300d0740c0100b0b01481100c18000100100405403c5079144010f0201514103a403654031644001041c2c0d80344400c003006805002000080342c00c2030302d05289000c5841d400880c0032102c040c1003084840c1 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 227875341 1250 227874091 227874121
    0x11e06030c050a030914150f0a020717030910020409020d05150303040e09030c060a0f0c020a02011e0c020307032405010302030d050309032b0605010e030a020d150603030f030b0405 79
    0x150b64240802e105c501843c000083c0040e003c2042440d1140a000310b800c4412a038100e40500101010f01d001904d80d980a0020780c815048003501c200d4030960603105141900c0011036100140a0a41d003249422012200c2603a119900c44204c1c150040384c803403103501c960f100d9690410503400c240001050000d012070b80341d000c0c0d4801d0a0404510324005804040184203c802074034515003518850716082c2e64050040103012516245907103405c0e2455202400004c241000640503103a6401021a6552001d403040000d25400100300c07035410100c2c01a18100704000c040d5100d42208a050120007003000541c1c9040200d84000d941040010405a10080784840c068421840c02d03c1d5039943d06003c80e8514403801c40c4030080311241d44400758403110f640c0c1d00403042040c00c4005022880d03a40c0011140d003041821001d07819003004200400501d070048554030154442c40e003e000342000b00000703204558042d4002d17004550108980c00d0480e5140c41520340ca4142200c0410450900d0926462802 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 227876591 1250 227875341 227875357
    0x1080f01030813080109060c03060b03040c1401020703061407021603081602061611010905010203070c09050717040f030314090a0609081e091203160303020a1403011e06030c05 77
    0x2100045203441c000859412802400d85100284151b107524a0410014910307103e543c8000792821070040f5400e83d8103412030340100d80141d03256512a00384548603468206d02e405190661188400000000e005405a100403070090440c000c10f1b450310f190060300304032600e0440c0c03450102c1d180040c000604a41c1c10b446540641c1d40b00941c00300114030104bc1d191240c403d03803100d216100c903124002c0106910644241520070703071740c404415542e1001680c5d2400780042c020f242701c0a0120134000c61403685e10040e0301041603d010141030507042240544640306690a441000d40303215014140f60b0140a001c0007901c484440d1040ca10300700c113581c0e44500464070024442c40c1c41c2c002c03c40078040740c0c5007a60b04200b00b109583c080640200c8800d210b0360f004040d03050040b40d8125030680c00807004002d54071324076490180d441840c0c80a540842c001d6104101d19010b100d043c601090285e0b60001c088c5000c0c1c543d88941040c1d00380d42c040112401900790f40110105410b1820049030a9840700070b07034444c2 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 227877697 1106 227876591 227876603
    0xb0c0706060e070e0d0203030f040b04090b1801150e090a020705121e032509090b04060303050f1b030c060403080108061303050705030c0d02010209030c01080f0103 72
    0x854001c80d91500131a0101e150341381107003008a45035051701d20090070f50307242825114074046d080d04581c01c9103508010204050245c1d071018404c0e0344c0001c0003221362581000c03080040b5840d2507414095841c04c441c1080034000000d0045010842c4800000c1c44042e103071a110000c84000d4100c5441a51684502d00a91755000340780c008490f00f0a48c040510701c040380d8210f0316441540d201811054449548039800038103101d104018104200d001d65036043c03034624288099043d6031700f0081c0d02d807156242104c00c0001030b03041003c544141100b620480e40300d243c46103130358070700ad048100d5410740342c040010002148140811020320952080e140c12480f640c9841041c2d64603082100d01d440110800d401d510003080c01180544804c601c030310126450a2180c1d91100e040106604282025030740200340d01c00d01c0d18040c802d0b890030301800c1c07030100010314001501c1000c09a041c8009400 = true := by decide +kernel

theorem cover : BRFrame.Cov 227697841 227877697 := by
  have h0 := BRFrame.cov_init 227697841
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227697841 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227697841 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227697841 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227697841 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227697841 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227697841 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227697841 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227697841 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227697841 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227697841 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227697841 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227697841 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227697841 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227697841 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227697841 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227697841 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227697841 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227697841 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227697841 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227697841 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227697841 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227697841 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227697841 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227697841 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227697841 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227697841 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227697841 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227697841 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227697841 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227697841 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227697841 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227697841 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227697841 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227697841 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227697841 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227697841 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227697841 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227697841 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227697841 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227697841 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227697841 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227697841 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227697841 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227697841 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227697841 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227697841 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227697841 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227697841 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227697841 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227697841 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227697841 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227697841 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227697841 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227697841 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227697841 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227697841 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227697841 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227697841 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227697841 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227697841 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227697841 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227697841 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227697841 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227697841 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227697841 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227697841 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227697841 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227697841 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227697841 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227697841 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227697841 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227697841 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227697841 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227697841 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227697841 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227697841 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227697841 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227697841 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227697841 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227697841 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227697841 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227697841 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227697841 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227697841 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227697841 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227697841 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227697841 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227697841 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227697841 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227697841 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227697841 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227697841 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227697841 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227697841 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227697841 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227697841 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227697841 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227697841 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227697841 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227697841 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227697841 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227697841 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227697841 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227697841 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227697841 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227697841 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227697841 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227697841 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227697841 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227697841 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227697841 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227697841 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227697841 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227697841 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227697841 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227697841 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227697841 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227697841 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227697841 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227697841 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227697841 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227697841 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227697841 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227697841 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227697841 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227697841 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227697841 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227697841 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227697841 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227697841 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227697841 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227697841 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227697841 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227697841 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227697841 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227697841 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227697841 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227697841 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227697841 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227697841 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227697841 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227697841 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227697841 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227697841 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 227697841 ≤ n) (h2 : n < 227877697) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
