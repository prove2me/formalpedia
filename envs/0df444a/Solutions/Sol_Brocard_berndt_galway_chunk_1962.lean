-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1962
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:18:48.58434+00:00
-- url     : https://prove2.me/submissions/e5b7c225-c14a-44b4-8fa7-ea9af92fc951

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 352697841 ≤ n < 352877697 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 352699091 1250 352697841 352697843
    0x612010b030304090c0315060f181e05041803090303110c100201050708060303090a030305090a0e01060c1b03030e090403090f0803040305120414090411031f15051c 72
    0xc00c1038420000003905540140d044004456619080d0024165143c01282c03400704103816055212418034030020480c42c05100c44400b440381e00307401c0342c0d115403050060f04000d04101441d038010a1112240040349600f81c4591407150381044071801030046110f596041055047c2c60341c180c81031940c0d405591208500600ca040f5008449640d80365443c3d424070150080070700d0b800014189000c03034014058440c0138183e54040c0e801070111858544070544640140ea801d030030b190b6284d003028000a00c0a4943d6040252020038504c000940c0b1500b240343c40c0286031080103002d042802c1003160790b500c0380c4240b002900140d09008429111705055407280e400c2800b07880d0113550a501d449800d18918090340c8035078041d5000140402c28803d0500c0105651000d0104e50f034035180c90a06000004100d802102d80301e8082c02c1d0200e41001960605088880805400d45000e4108200465aa030680d507054410050034580003045078220b90320b4003030540314014410800b585c10665454540401c03080 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 352700341 1250 352699091 352699093
    0xc040f0312030e01050f040506100803030106110a0f03090614190509120a2405190c021504081c2306040e0115080d08010e13020402090402130504180b0612 68
    0x649411030700c1c070a0040b5807044001d491b00c0c01c41d6041c6407a1003498031000a1440307c040380203002c01d001d0f01034040100c9046429038540b0125560443e4011810054a103000801c2861203400034020560400c0c088011240240c503007010704400d0a6406141c5d1141001c0c41c9030f941808800181428020b1000d01900040606105441c4a0300450319141045503a015070346000e01d81b48035084000c1c0d404803496083c14014080c086030a001c2c5400c81c421440040103d402500d5845c05841c0e188204030b14000001c1004410f0000d00740b9040c61a01503001c00b003200702c8032110040c1c0c41e14000da00c0c0130b400341a203100004c0c0d4500d84207140c255201010301504c00b650003500d8004081c400482401010b040c1080340d030b029545103240c00c415610749a801d410f01001e011401c0010050b4442030b020850f80002c161360f5045c1101070750700c002002403140c50f54859010348040340014020001c10496030503503034140c40400040900804852000704081801044a08441d0000c0c00906010240909203180c0c00 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 352701591 1250 352700341 352700351
    0x501140a1b060207060b100c0807290106030b100306050112091115030a0c030b09132303070302011a2101061a070c050411030402060c1609060e0c040f031203 69
    0x80d4642c0180d07800394009079411601c40e030680c1403514043c074a0810f040180d042142c070210f15640d0f1415117008200001c0c0840990801040141c041c030140014030400400c1c104049685450016008120900100380241100440840703002d019100c0e0009444051f11a80c903000c01d181c084102030085400d04444051254104d1801c07034450752469440c80f003040c0210750322441c003429298211036051160388105418015981c1d074644a80b9041608014000031a010711111400c14510100c0d400c1d03110704811429002e0782c403541c040803002e0200c50307200e5402032003900d010000d003401c0200f1041c0b440c0d9000401c070b060300e01500070301c40f40d1650150b1540008104181d50348495640c04100e002460b641c2e41d0005206820030482250705070160900f12802c010208111142141c5070000a000a00420000a020404100400030030880e908105888900c56494101d81000350210348922101d1620031030208017001c1070101510142d40351320010120091640c1c60381312031211403a644c01d0a2540d00c0d = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 352702841 1250 352701591 352701593
    0xb040e01030b15060d0b09340201020c030d060302091609060302220602010212130b18030702281a0910050d0f05061e010c060c0323040c0501140a1b 65
    0x101e009085c0301c04d14901d00107842c0d5000828003940850040c41098035100f892640c011401d074882c024a03800a0f000840c0c61a08040301c0c0a030b0080c0308140d10800584000300301c2030700d80c001c1c503049041980c0c42610204800e0700c40c0d00c211349500100b04a82000700300070704400c0c89028800d5004c0c0024411440c20203180008006040060280f50341180340103075000110409106d41c00a4000d4001d411030401c54140032943c0c40d000d4040d00c0150104802e0703522a120900303840410015146400d800400c840410482c070407070411520720107160401103010707041e400600448200c0180900e00010642e05140c20844030030406484803120250007800000c3c00000098000c500c1400f020151043c1300050f141041c034100403541500b42260018000c5c403000004050b41d00ca1040c1800e90761000012030320b1a11102d00390007074213064a1071706034102e00700b40700c2c0d509122080ca0349010350300901189005944407401100c03140401d0880644542081183d2a0814402d501c0c00340319050081225170f544010b = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 352704091 1250 352702841 352702849
    0x5120a0c09020c010516050301031b0302030607080a0e0f0615010c140a020f090106020d030e030c0a1a06040506030a0b04060f0c05180603070c0206030406060803030f0a060b040e01030b15 82
    0x1a006541d240d0790108040c941c0000921800d80c1065481c411300c8009001c03110300400307500c41400b00810180d4111181c0702c12a0309a000000510340c01130a8030401d292404004052001c121040440c050030300507480780188010981c2000c01302e41c000078004139951700010788807004241d00110704205c040d402041c0814907910540c07681005110280080071136a004202c004e90190702c07420300ca0488140104000da03000900f0043c00102405c000c83c50984007035000341036014010401d1042d0007030a000030700700240c482e0181c18840c54180c10040c50785440c01440202c034001c84000340c241c0e01001e2820003064086680716030140c854071011544400700300f0408141ca00b03c03800900031400100c2c00f00c03084115401c03e61b01c1c541c0d0a4640d18110f02c1d00f0f02c0024020544010040e02521000010034140f1856803c140c000e015280201c0ea0380e41050029003089280480701001c0c900d00d0b00c02c0100b00c0116860880d000c55000310001c2400e80d09580310000c03103140c0134107007040403083d10b8600d44c69511 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 352705341 1250 352704091 352704113
    0x15100c020607020613030b0f0c04180e03030903090405180d051b070605070b0901050f0c0904180b010f06080702031209011d0714010309080d020f0d0e0c040c080402030705120a 77
    0x31706401c180d2021461440d002d03c00c450050050403441c0007004c2000845844402524119048150208807640d0100d001e80000c3c03444c6c49642c4507900002080150030743c4008000d00740038070140d60400503030707035507a60262513000300701c10001080d00145000c894041c402e001034071400034408400403082c1415003089180003403c2d0b004c81f000c03c0300400d00c0d6003070100d00450030340e0000316000240410324000312140f10810000306021002200441d122810b5101c503441022901e040003000011204c850910007140320013481090108101e255002c82c0051003051200d000d99202d030001e41c101541c4440c004400e40000f440700d80650350303500400c07842d280108c1c9400301c40d26504000e01031050505021702100e4040008081c149424a41005e000450b094120307015403404501c01a00c584006100c190b1620800b0990f030045824258080c20507900810f101403290000c40d02040f030a03881c0e80342600c4c1c0100c11034001e98190004a4100420b0402480c6024044a20f0003601c041c001150707a149186a = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 352706591 1250 352705341 352705357
    0x1306210207200105090108040b0703240911070308040204021c02070b041104150e071808030904050a052802091203030f0124110304030816030815100c0206070206 71
    0x80700c000742207040d40c1d89400000e00c2c400001c1c40c3c02841c101c60b12001a000001c06030000b08521011b50000301c00510940c00710101e10650034103214200014140d5000d481010701810f4052072070040c500e030068450740c04440d4000e90584800f83d007940c4d86d408100003508000b601034600440800e0041c45a01c041c40100744d031a1180b50003004508160900223042030303420f01c0041c06149490740b00000351403100c080b1808c840c02e040583d817159440001c00c03075200160301080050b41d8880000030821179004000b4202d80703401900d080144e46d447c4152803040e07030426181024011f0b00342e926022040d030f440020700d100000302500545000c45110111794100603c41d0655940d402c08014044412180a52070f0300500e10034410314501d00b0040d0000c1c40c0c0781c00c0c4a031040b06026000d24450061001402514001c68010402d944c55501c110205140f00c020804120006811400000e1701c01c12079007159848a14050a844580a00305406a8041e00310885c03c3c1c0c0c2c00801400f003580140d4901c401841c42c4 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 352707841 1250 352706591 352706603
    0xa18050406110408010c11070b07060b1f050c010f0b0d020f0a0e070905190803090d050703021003020d0c02010c2007030b010f170321061206070f0e061306210207 71
    0x3401d1000c000300140f0302e10141f0201c94000802c104201d0b900d00058a030742e141c0080c1c0000b020b502c10382c001540f0864001c00040d1500b01e01e400b0640310358204c1c002d0440c414040009020541100d038100d07040b02d80e403509865108107030341410380141c1040300200c1586030025003100fa145440d0002030307101c003400b00d5014000450030002405a414611080c00f248054065924072981c107005095031640030b0340107068092300c0703030302d5406003404010003181c0001c6070064821a40100712540050281d8442c42a40a030182801401104c040c07051281c562400c0940d0b46a04c1d503035002c1c0c026a4a000900380e002080c5200381480440071441c81e4059a008101403841c0c022124038010003d07141103400380032032005070020b210714000e000c601c840000c90500078258070b01ca80d540b07050015400c10804041019140300340e0042017803040d008440c40d54951b49a4503200c1d4140040d8007080210301c68026003007110b0b81030200400c01c083c0a07141c40d0740d880a0540c40d8005c81440126444e0403030300040010390340 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 352709091 1250 352707841 352707851
    0x312140a0c0f02010603020f15040306020a0503160e090610030b040629071119030b15030105010807051e12100f0c03050609180c030a0b040b060a1805040611040801 72
    0x41d103a0480544415045640000d00050b499900002e42c02c10001c00164025070074040c844000c20060b01c2110061503109c4800c5440b40150b52005110341c100303c60b044413404407e114441c0d841e028200011000c4c50007443c0c03030155515042401060317001c03903001e00c042c507460b060b90144982e07a50040502804c492801e0500d10f42000e44d580390852454400001c0890b01000074030013280301070840034401d00381500c480194465590b03a01c1c2c0303d02e0321544080c128580b2481480150004d08034100b002d240100d0080c0110790700c4050007511901b8a124841d03210504540360420401c40344110194908003c0030740c107502c0004007000e03003407100c8034898040040d61944044180506446000002581403804000d28904840826aa548003900f003120150b1000d01c140c1640204028603000c905001d03090310036200079403a050309081c000ba202120028420380000f5078038200704502000716017031610003030340c07550115004200508014100741c46641d00e40e00d450080c240a0402040108804800014 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 352710341 1250 352709091 352709111
    0x2060d1404120f0504060e031005041506061d0906121207031101020403030504060302030624130801020c0a0f0809040501030c150c080307032c0715090e01030312140a 73
    0x3441807010400d107030512103400d03008400f03958040f060f0b034251601410310740a0785020b040041e2809000101c01c041a90800040200b0030440240100c10203119180a001f0346450304000c0e90004060080242c402032075006030040b91805041e003030b4210f00c0180c1541d40301c6c50607950050401d40740150400d40b19100143d01c20405500c41d98250781052810300031801c05003541c1c1d000b4043d20582c421300c81003680101c0070501540d940102c000784401990302c0d41244403040c085c654108c2e04400d1100d11000b402178000619040b060086903405e07250103002e071540c07a0156031442184c410740f03503059030800b80501aa0000352240d01c20b813406036001d110600183c6162100020504650407000400c0050b1601d5250000e031043e4143c030b400c4001400c000c200901c1505c807143d000d9003040307900d05106254400759a014900400c030f040a0701c82010480c1c030302644a03002640e0090b034170300c00c100140b10000010000b0030300c0350070005080c0320094000300b19a403a030f181c0100364100c1a0385111500750b40d006415 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 352711591 1250 352710341 352710353
    0x512030304052406041e092102060f0103020613150815030307020102060a0f020702030a080306010e0604031a060d02040c0207050a08070e270d0801050a090908090d02060d1404 77
    0x102056407040602191541e8024503000020f802038200b90007a030b12032480306d000c00d2581519058004050318100850031007400c1ca01448446041d10310b052144901100500c3c3d4400300307401d48100403052412150740d1869007031005c3c5512042d51000a83d0304440d0101c1c1c12801c654400b564560283e1300c1d01518102004014101812a00424800c3d4410448840143d030040350407648800c02d0000003034800322100305038000e8469420000e40c5405800d41c44000c01c00c4900c0614061402a41e0f808080c41e41c100601845100714000506111180c10070040e440414080c40c41c0e1102c0c0207410000c0382910b80d80030500b035813040802c010160b00105028040e504000400c8030040607003d00824055180035443c100c1a0409011400310b1030801d0034039034408207550415010380e0b010b00111185060600c000070701c0c1c1c40081c02280e101d00114480012044154004c2c60101501311031101d16050f80d103020009850580c940498001100740400180104035100e085c0700f541c074a03480040c251410389480 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 352712841 1250 352711591 352711603
    0x301090b0d050c040f1805010501140406060914031204081b040c050a08130c060f02100b0a2106050703090302010b2b03181502010b0312090415051203030405 69
    0x4502801c41001d0700c1c00459800552010221802c3d540055024098035001000d040341c206c803090700398a00903c410401c00c1c1540280c0c100d50700c00b0750300b00200202038204800d6480350b1080a00091104400784200404024100f651400017022a80c50a100c21041c00b45500541d0013401c1d240c02c5103011130800080403141c1d006819048904004848591307030040c02501428041c07400308000c104c00900c0c1c442d245e803402201c01d41c101881801080ea5020002c22504441c1810001030040580e030305041c0015001e03200744601e00521403201c40381450351011100e400702cae449c0016403020941c0324012403200e11402d40140b405560204120109040107402d41d401c8010041c02070060f01c003001c405e489c070100040714840c101081d880ca622010705044030f84a00d4021844a100d840b0240080e01e51040b403002e49421308140c000b80101d90005007090f8686040201c42d60802c00c0c2000280c80602e000d81c0501c0e940e5014100085070b02d500d039400b06444190088100409920000901060200812503 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 352714091 1250 352712841 352712861
    0x13060f0b0f040f0929011d0303040e1305071a0403030e011b0303020c0d0c051509030c030301080a0b0a1401090c0212040e0609160c0303020313020d0b1807080606060d140c030109 78
    0xf105d1000b0b030b0a000001c0c43c111584210241007041c1c2c41141d1051303a418012a0018420b5050000340c030b0130061304003a41c4400d03448044810703108440e00010103461030f483d50720120714003a00301400d10f80786031030a540303103040911158100b0219040c5180805581e00000481601a42d00142c0310101c022810386004c08407002398042c480240600720000b0f200042c112600c1e4070090148180342c0343c95081610307502816003404503a01000c000800d201000003880560203016108000f200d89600c9a03c0c000c480d401c10350340c504100e00138010701156400d50420352581d2520300c1103d52a0803860141c1031950003940200d03074a04005414041d66141000023190040d2031a01c4510031114507440260600c0a8114001c06154011001400341c038100042c0c2400107801030001711400109103081c0c404800700302c6940110351510786c900c0091500024030b03542540c058400401d1151500002c004080e0031241d02002600d440303101071120030210400f0b0701c0c0644525501d01d0344030b50500d4582000e803400c2c588 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 352715341 1250 352714091 352714151
    0x30f030c03021e0a0203090a080d0f0c1a061306180606090b0a1809050f09121813110a020a15020f0f0310031e0213060f0b0f040f09 58
    0x2141d42e420400041001c451501030b0620707035904913001c003d9013140607600c05503502c0910004001400c9201140e401c0c68016507075030341d4440814403c4142e0f11094208006030200514211040002881c1140c603500201e0042c58805101c0f95603002400781c0d0400e40005242200c002801c1880c0f9002e80114000b4110504007091120300700164050039000f0915004100420f180340f088a02500a404001500340d441d0140840d00d403515210302540002e64880b004d0b031060704020a020440d400560340c2ca0b00300000b135640c0310000b60b8100034811028103400941503907513216001c1d11a1060b801800c4440254001d864081014249080401c5190101480c2e50b4010051820145240c00841d00c50307125041c40c240d125281c82c07100c41c240c03403003681000742001176030f0b481c22803100a0f060550b0040d603c09c44242e40c10024502e0f444042c0c4805210310b8a1004251405004a20365480644450300382040050300305035842c114010550030545c40301c00ca03c0e80d41d0760518504000213a0100200303640d89 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 352716591 1250 352715341 352715347
    0x10233090616050f091809061003080912031204140f06010305070605030705071505010f120803070309030c0b0106080109060803120c16021509030d14030402040f090b04030f030c0302 80
    0x2250384425001d442d10341008100c80054010131800601d002d40d45500c8010b81182003982081481c81c84011090b242c40ca580c2c8030304000a1030802c0c9109030001526171000c4d06c1e500b041c0003442030050f19034191413046807a000600c803201d5401c0d511701040780b045002d141041580d8141d080440e04022000c0d0000700c0700d0b044100140702203440020742c1c004542513854040e42e01d03075846000321441d0050341c00c000d1090041c60700b5100714880c1074110f54140c0388441e184e00301e25a95801030b50307841c060104c0028000c42c810300008a400e40a0352201c00d2683c024144002c20001c00d9a4132010b80800340c101401007244400107110303a8403584200800380c0384103001180340041c1c0c0100500c000380001d00f208041c0e0000503566113411924810590349940c00fa202000030903100d0b0011007a80c106038800c5000f03128030074040b0344803031043c0e107400300e82c040350012145152603680a001c090690042c81c00c0b0080e80b62203459001a00038514a403080e070080e80c504001c8000010000d0549180d601c3c04001c050040c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 352717841 1250 352716591 352716601
    0x406090b0c0f12060f0d140c01030b01080a0902190b12070504290f0a0914090f18010b0d030305090105090705131e0204060c030905011d0402090102330906 68
    0x41000ca880304140d0210000700fa503074800c0055001010507103429080311854840340100191208041c00319080751054402802100004404440231000d01034006183c81003c10300c2100e13260700002c44180050240c0040c01414038000001b05540e40c025a04645c0c00200c950101c0d00400420ba00082c452038110300e000e15082814020446200088490f1069030f080790485000800c2201d200208103454962a40b485442c0901081414411000a201805444030551a01c1c03103c1501c250030208489d509030700c0b18840000c0381c0b960311205c03519666940a0300d540300c1d03548140844046100c6da901042780d14110034207609544010344204a0703544503c2042c044e0b0354425258824040e00e0110028081c20030480d078504215586c2c8009010520010780810303170a6102c01d007204001d0003a00c6414400c0d94505c01182c00003e802414084010035074030f403051030714264000f08038192051040310940c2042c0c1100e000341000c105c0d5002d075802c400030b4046034000711a04c80c5540c81039080c4050880c5140c4 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 352719091 1250 352717841 352717867
    0x604060e0105091806180f03120c0c0a0506010b090f0405060108150301020d150f0e1b070f020907110d08090309040b0a030b0a020d05180d0f0201090b0406090b0c 71
    0x1040c041d440c80f4034030010000303070801c8105282100c40b0f12040c1c1240c405040c42c070789410b00502c0514107107000380115641c420100200208448000750088040382072955200046000c5401a00d0000d9441c022510240b001c07440821206002e45503904a2590755a072540400411112a1100301c1c043c6050108110341e80e80c100c0d42a643c005480c007229002c508040d4002402407003281c8034282605d151401c94001d1000004c103e00c01e403800740c011003852a865014180c03407210100d92052001c00c00411404840568001801e501407143d0301d98111900aa400189050411641c840c0051510f0481e40c00c020410032402c29481d0141c2080402801c280b40c60540768440c0c001c04e00d00450300c8000404c1d4548071419200000c50300420440414103102070302e00040e6000000244401c0c3c145000f2580c0d6013803c02e0383c140403d140e00010300711b9041c110002d47e8003d07070001e80c02055559400c2c140c3c0c041900d510405110314454140050300d1004d51821314901c000c09820074003001028080c801c82d4040c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 352720341 1250 352719091 352719119
    0x60f0a0c0c081602130b030c0303161b0e241002060402120703150209011e020a02010c0302010b0d0507030b011202060d0203040512070803100b131701090204140906060406 75
    0x60040c0c0b03416a00c40328403022451410f401d00d0000c0d007002d1006544a640141503111513800c04d070440962307101c4109081015502d024000b11800c01c1400105080009048403446e14850264800400c800759034031100c0900140c0e00304d84203c40084031504410345a125107031446250001100c0e680c00105042c68003e544d440c0080c00203000d041d01a041c0c51138010100541d200656000140c00407040074508014013941041072942d001c20607110400a03d03646c0c1807038801c1d074210f040d402000d41d100305030011036211151000076015556140362100c01912007860300c2c01010701403402400300b6482c600d050851044140c1c08244100050003940005903035040c01c440800e00188009a103d0703d03a402c00f103041001e00c0090704a5481c0000b5200b0400511344040d62040c5c444488500b01555290804240c0384100e900c0c059990481041c14485100036034003800d1402600d50000a080e5615404038048412802408450241c1d082c10880284810400d40d903006a0079107090000c580307060b400f210f046c5 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 352721591 1250 352720341 352720343
    0x102070f0b0c03040e0c1b03031e04020415060c0c090209010e010c06060e0703050402030d0801080d0c1a0a29150706020909010e2d01030314130602060f0a0c0c 70
    0x160700001d5280614408100341c40160140710196145810b0051001d0040d40c03120b20258403000b406c1c81c07041c01300c490202c180c9200708078000039914618881000e0400059004200f01da00903610950300c0000180050171300b0281010703031100003c407011801c110300700d00b14640c0b00004071801089808103599011560040410083c02d0185048650345000000351030720750070280e1814018810044002d6040c0c0000e030046001781e080d110b05c041502d23011102034409005400440d130051081000c1705100c0c031032144007140200444480402d030fa038400d540f001025501703a1005130311742442c9086c0b001c006903262440c01d0701a401e01540d00c80c01000c42c60101c50440d0549050704041901e00900c0010b4040311410600100203065540e101c00700e648003102c040e0740d450304440015407590740d100d0800c007284402c161809669006c1e0707807860b6000c84181c2810003000411100501455402c84610280c0f18060609a0040c1c502c82c44c11600e91070003800c0040040d05176504190500905c00e0700002e12440701 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 352722841 1250 352721591 352721609
    0x9041817090307150201020310080307030206061e0a1e05031c1d0d050d0306081b06160f0f02270a0b1f0c0b150918100e0d0e0102070f 59
    0x244030300740009042c0340c15544111040044c20000d0300019a0650081d44100030650071007040350b0b1115205a03880c01340c0400203000d80d00072004100f80307143c84898213a102a068010b811001600408113180c0c80e0641e00100c1038906c100600c1441c050240020400f03884290010545540d0088218503150780018540c0d09000315103013603c0c5c8818080c0d00c011101c020203010710901012510301566191400800c0c000003034604100070070740742000b01d1416000e04100e450306802c181164104841548482e001c000c10b0202180c401d800109010f904043e039070302406002810f00311500511510581600c0040e0003030203200381d00c0091003a1402c003c0c0e041200c0400004850100c2c0002c0f51081241c005000003583c8920010100c0543c000d62100e44513108140e021081d86510741d2510b450a2840b0346d441d40316401400044d03131580c0c3d81c0b00100a65480000b00d03100d1070300c1c1c3c0c5c0040382140c500b0214010303650864a21401c10f9034002d40b4000680c0f60a1005000207844c2c5584a00200c10900844110b = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 352724091 1250 352722841 352722847
    0xf060f020d0606020a05060f0c0901030b0d05010903050319050601050d0f1413060f0204080307020603072a110d210c0221101b0813060603030509041817 67
    0x14200090341a1862810701c5907041200c0da440e140b019640b036040840c100d8442c4a4000003c44035005640d50381e0085026081c00c5080540840042d805000a90f01480c0c004201c048800c010403000d001d00c0c0c52143c002e48651744d5a0411600c0444149000700d0f500310301504102c10701070540d03440400c980c01d18410b0b1a001400540490944016007600c4080e4041d1010450500c1901d2401940c2d01e02490703c11030003040180318407043d0384180c0c0110f200e00400e54200f4000d800240c1480d030003c651102003450001040003100c8403019089440000c9604c1d502c507880710950812503004e000c0c501c0c2c1c14003119a0b01c44290f1550b03892a003441c000340069404040f540000b6000c0f4040c21503c0c2c03010390700a1102d50302030045a0002c01640b0386124100940c0f08000326540d841680b4031034030104075a44113a07411007410341002603032080070181c040724104400c1c4222a000c0345003407103800055880f81c3d6845540d40204420441034403020680740c101d007118031910303800007081544030144000c6480340d4036803 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 352725341 1250 352724091 352724111
    0x30f140706180b071e032f251104021615060503060a090309170607030b012c0108010b0f04030f0302010e06040c08120315090c0c030414130203040f06 66
    0x3104640008003c054100c08418000c00c65005207160910040c2150045200003110004905031100f0005c081c0000d0144050542a140241982030b11481d0b490304c00d910308007000502100020015908220f070100340b103107400c208440c0220f41e5012103421101541852800180000a003940882c010b104111000c5040d100d110070750032a000401008058900710319180410740c020300302080d000c40028000c0c1c90003003a0003401451006c0742c0840319005101c265600740054001b00441c480542c180031611003412140385032040550000c05094070044d50540c10310f000500008030603081441c0b01c2a05119040d810040070041c1c40440e0f400101403860b00a0905041e801048403488444541c00b0303203010401404910b200c2101112000421a13a044031403403003c81301804203841c2e01941c191000f0b208113440c5440d903900c41e000b1300d5120070185002c08201c8464610341c0031740c2c030845007019041c004410328945a062420840c8001d0300c2946103280982d20050540304054000305260f070340b04c9e0b0607c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 352726591 1250 352725341 352725371
    0x403081f150c060b030a0c260a0b070c020a0b0c1006080309060304080f070c06111501060f17070f0305060d240603050109060504020f0d050c06071b0b0403030f140706 73
    0x8a041a1301034140c0e04480b03500d080203522415540261154450f00009946c40719607600f54407010404184094092202e039655003122141000d4480000c0011101c00700d0096510824924020300ea019440c55a60040c6042c036411b15483c480d000307030610301d451003c100d82d580100440c0ca1049044402d50759940d00d6151411031070240714031510a0120101e00340c4208102900094181c808544500e680f450080010b01c1daa841f02c05452080307045484d0040124600820030280b40d450281400e500e0405003540c82c9041000807504c0100281910400340740042e05482440e40000068940024400581d10b860103110032555043c1e84c034841c40312042c2c1e242e1070240c0c000806940c0c0000240990010350600703130003401099a059120b030014a980309040e00d000795002c041e85501001030402d21491004201c0e29410181c82541c2c4613480d000c07080102d600044400c8042d0010140854580e425410002d00c41da020300c80240030710040303207080b60400000354141d85000c1e601c2034022401e01c01d030800c09 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 352727841 1250 352726591 352726601
    0x31503072105010f05040606061101060b090906010e120127080406050c161215020c070b0903010b040905071502070f0e1b030403030507260406020318060403081f150c06 74
    0x103020b5017072614043c00100911030304680200e4945540d402400710b05504554226441e03441104001541004000003500300080050343c005014102400302c04504000300c0c0e0f103200c207210501a940d542d800340f003104288282001090000b400142040080c135981d0390b000c3d600c17640c0140c00501801185007d8480000c010521034200d1650f042d5503043d030348010050750740c1844e01e003c540107044002d0500e0120010320a5541194245004004aa00c0c05005603043e0f403007004e9950300b554840d1840034080d1544c0c007850a46900c908018802c052600206012a0f01002000300440d00000340070804510000b403440d06690054a200c485925501c1004004042041507801080030105c00c000a040d00f60340290f10a282c01e0300c2e452600a61030f4680088801d81c1840741040c41c0b07510b000b140128000754059944002404d0b4035054a1122422191034010120340c00c4001841c082c08000c0c1c500007003401d2401480b20b140300602840d040000c803007010b08035880340100b00a100d00460050041981003 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 352729091 1250 352727841 352727861
    0x501230319140f0114010605030c07031805060f0d05060102011407030507170702010b040b01021603170f131d040c05010807031407111b0f190f0b03150307210501 71
    0x494643c4400320060b01d000c0c003400c41c1c0c03800b07083d0351400000400b18083e004030f80c80368030640701c1c1c3c43c42c1100d5541d040e9043c074010310710030903660310410000c02e031074845031300a064a007410f02c5d05a441e1240c0300000c2043d0389005100070b0459040040030004c210002c0f1005402264504010401c0c0e954000100c4e064051600000c0c0d0b00e5103c10140300307240e9019803101240d110159028811828031500590b950825a510b40920616850b01000403d0714a4500c1040c160301a216526104004131a403a440c0c121480144681040c00001c1240c0001800400c085c00f2141c01d4805441c40d0686a13a10100c06e248a140d050003014400078038900e120f507006401c502e20150f2a6101c03030821480050200303100c0c5502c90307a00e20501d0160541e22513941c0c3d0800c08054001c001581d5040c022080c4103031181560002580990884808180d030079400e124a4054120400e083d601c91401402028032806002c80c510301a0b00110024045074084060400c0c40c818804100c0d034a8600da440e00600510544107 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 352730341 1250 352729091 352729093
    0x9020604152705030d0e061e16050705100c081903090b010306051b120a0c120509010c300203090304120f120503010806070c0321050123031914 63
    0x110301c41c00c0000302e01078141070340c3c1d064040b10040701c480201510480703003c0048560002c2c083c0b00d0101d1042221200710f02c8440c9401095003014401003800d1704405590004a4854000d00d0040c0040d04082500c100010b94a2610751a0550745403100042c80c81401c1c007422a20200318100c4503094001d402c05580c40d035004065491a40c5c0d0380c24114020f0070165150403a054040c044014400c3d46103060390302d5031101d01660107031130310341001c948000d09444d00e80e1428000c821100d40c0107442c66208191256034201c002043c0380f0341030f9000610400070b1a0242c03408031000c04480b000715a6440d0792040c0f520b085032006035a42c40d0b0852051540c01243d0100310788008040a0f042089034000e0003017030180c811b20071584603540c0400c007a50039000034003030340c130b01030340400e0004040c42c1c4140c03220441503000c0c1c100303007040503600128100c0d609461720a0440003900d40c0e0041141d241601440c44114118513800c500d42ca41040010392914456020701e440e000c0c3c0000c0e00d0081c010242221000045a40 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 352731591 1250 352730341 352730387
    0x51f0f2c090a030306060c0b06040b031e0718020f160309050a03050f0f0f0d18090f0b0f04050603150c0409020403030f0201150e04121404060504030b01090902060415 73
    0x410341c00d0707075100c1001c41100003038100440081c50034011900b580007507030311921881e21680e80809100007000e04108040c2d041c03190002c000c0c4240360a400d0351521003003481c040c050b01070400c01e00c4000d0002c1005c0b1850003a2040144815038003c89054032800b081402e034a4925803080d00b0101c034510040d40099a2000700a0000420000c00240c1810304014040c20344117082e0b01c001030313581c40d207844100d0340c0c246410460092400500c5036610309840300480400c990402c3e00c5407000c0b011038103421201c0100558520840e242d910b000320701d042400780c08a405100914050313003c2a190341c03498081c01401650200858504001002030724007519902008544075552814001c1944000518510241d440c00510301d41241c10420810196030300421560700c01e071a16a1000e800d543c4000710302c0304100c031140e88013851115960050005004e1a0b0750079854a0550809044030103041e800702d10450b19021780440180c031040240c8040302c81641240707000c1902820195404020007901600d011a44 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 352732841 1250 352731591 352731601
    0x90106090608010f05060d0203030714030f03160809120406180e07051c0207020d080c0a23100b090a0c111005040b4c0306051f0f2c 58
    0x154013280d2111114881800039841e107805004080399403000194154004008400104c0d50580042c0441444001100e03d41080c031103038030742c0d0350300141c6d41507403803d117009031030040c03542c0c45140503403c6030b0040060550440b10913004145842603104840500250181c0030307a9a25030702c1c0f030550040c07111844403071481c505214000d00c00d0b40015240c1400c50020300602102214600c00da40d2160350160030380d8400c50454841d0b81c2b0540000038020b01d00d1246c11040c00c0002c0039555255000c1d940301d004600901500d07a1b01c603062800311001c034480307a4170300802d0715110340d00d4411b000d8000340e41e5800003802c0008184215400003800080503030b24450b091140b8900d44003a40000c1c860340c0108851011a00d901000b14140600751180e1f00d42c032802080e0100d40c20685003901c0b1155a01140c007a9503800404003407004008456006868071940c070020800c0e260280c800b00810040744808808020f800d10035004484082801407402784149982c440341b010015002da001800c7c02d240c2c0c3c680441c030301 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 352734091 1250 352732841 352732843
    0xe0a120605093003040f05100e01181e020409081224090411030f0d0201090501050a0b01051918030f02011128050118030f0201050702190b090106090608 67
    0x4180c4940246100c0c00d94045403400c103003591280d018102c41d0f500c900c1020100800b40703ca80014000740c0d214500c109800307001401c00c200407080d9090780346001c00c82c0c00003401071508642d02002d03070801c500c001c401c0940015560b02034407604081e2101e4844020406400420700a28100e80028a5074000291081790a008440d00d180700740c2801c41d10454109484c0035440b0b440c0381d400355240c3c000541c0000301d00040c100740c9001c0c400440c041c0844000c0c402130034800785441d071069041409070350342d650311600307000081c011154403c04e100c00c1444a2071280c8002000d0f4428503907090319020303880e0460900144511400074101303d1030644550b40030748900b00100604e0f029070b801c03408100c0c03200084c0c40c0c006010032903034011141100c10854811103401c407000d10081c103003001c0f0344e2075684001400c03103440a030243c441c03140c0c0260765401d0600c000400190850300080c1c80902558030080e000e200c080b454141006000347e01861102d044d483e07140c4014050202a0404041103060040100304024 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 352735341 1250 352734091 352734101
    0xc0901080a020f1b123a060b090a2114030903060114040f050f010b070206070c0e0f01081203040f140a030f020c1504050f06070b010e07030c03020c0d0e0a1206 70
    0x13881d41030340e00c0210804000c69041c844ca03100c00150320094924401c0390041440c90354500c030740040c40300480b0488490110101c5d44c1d26003200f4055000803c1c90040c40c144050002c0c00b500711030481400302508825008045000c80e90010001030340480c203590804014400d9800114018045500c2561202815079408403600781a40c00707141b900088008800c100d000b03581c040c20007003810b08510f90a10301017000c681d101c1102a600300ca001c11003000050404800d100c001c01c1c9000006009003008010318903d5003040c0d0180e921907100180d02d808a10b9041d080b250072581c8640c0d002c0d032244542c5460300303004000ba000104203004007014031050541100c42c00c0c0c2803000b41d034252410310349072500b0402c03450704904900c0322201c000c1c0302c10302140c00c000c480b250300280010801401c040703181e9a4024010300903002040c10132010400c1c07040c043d4041c01007034002c0c11541400d6060841c40d0100b666a103138121041002c00c180000c0c250340f1600c2e0441840c01030495100e0b8006000c4c043e0400d038003e40 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 352736591 1250 352735341 352735387
    0x307020304060f020109031d0111100609061205122b0507030e07030305120405012415080103021c11030a050c031b03030703110118140c06030c0901080a020f 69
    0x3400400080303185134418821031701403540c1510341c9034035507044101042d020101032012605114001a4041c07441500b00001132120300550000314030a4200000342003660f01540c4101105c00c4004124800114007248080405c009100400e0300c82d0511804015041c1c035540c03c94004007940d85807488042c8064002d2442054191001d201c0c0d80d0b414860b15588488a110240000d5010f01150100c00942580d00360400d020b1000401d611000e0040707221105000c0611010045c040c40c01008141110b072680101840d503820040519803541c0c012940c0410b45601c15200420307110f00703050803c0b901918401991101504030750703002d62180382180d550b1240d040464800e105082c2032021414440c09015640140903010314184550381e60241c580703000f0045040c100f5500c40034800c19680ca8042031140035801500100c0380b000248072014108074824400d24020101081000241c0700301d0411201a03a40c03e2030f1114450765103124810090056400d84000b01600082a0345800301d00c0c440c00b8954 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 352737841 1250 352736591 352736597
    0x2a0a03030c02012706050d090506070c20010801050f150f09040b040e030a080a0b06030705040e09060c04060c03090302122a1f17010f06181404020a090308030702030406 74
    0x14018200b4240c1306410b083d8040d04004046240910001d48684e0160070290806900494409aa65100c0d402d0003000c031800d10000e80ba40640c0c070240030700010308080040781d800e100f12484002400090800c9070500819000b0000f0158894a945075080d03110703824482e0f14142d2782c0703420342c0c80c6420701c40b544062020f0b031241e4140580c1e40070601e031500c0b41c6a4094070010095191100040051351040402000505015500c0e88070f028591a150b00461040140b990b64a540380e0130300c0c1450289403405003170b2407110350180c0c0030089050007800071503007941c802c1d045c00716081c584e80c030f0110780042c1c2681009411908845c40d00208007070019618107030400b0010060a214403008242401070b45903040b903a8000540e0b440c407114480380803040085c8042e680760103911305400b007403036440c103410031303480b50360f0000034003604020140e1300890300305520440c54000040c4d41d1803ca0304c502c81101c4464001d1107158002403c1d51014003602818000b580d100790a5900d03803612a50280d00c0c0c1d00240710318404 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 352739091 1250 352737841 352737857
    0x23060709090b090a18050d180602190615050301090c0602070819060218031b0a050d150203130f05010c03050708221401060305010e0c030f2a0a03030c0201 68
    0x940c84a500030840b0400010300000003603a40c1150000103041c00403061080039081042110101e40140908014800c0ca504c5660344011414000c002440e03540d40041e0440d0884100e030510740a1a0190140c0e580e00103c01180f040b90800c050240e1404552107150316600c0c0400940c200060b483c52038089a001c1e070252640d06580f44110754841c030740c2c0d5144141090032001540c0001e80780740e01502ca9110400c03844000505010046460140b5005650040940000c0000d10500d0108083d4016200c199403482e164400d995a560410418003488920141c001c0005030541801030001c03002c06070042011400060750b401c0c501e00900512a807100000d0501000505503030044148030b024a204424900c08010707041004809903945a0040f241d50b05800d900303401002c800d0042d04e0107180038400004d508030080140500d0a94044800d5000b40c03c88011b26a003a180401c020308100007564880f458215040040e160900c4111702d941d52024140c0004400e240d800307141030310807601c04c1e00c544a0b = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 352740341 1250 352739091 352739099
    0x815040c0b0a0906120b1806090603030405011b02030f03120f01050307030f030c030c080d020c010e010b0622050415080c0a0b0a0c03031d0a0b0c0306031923060709 72
    0x710502c29045001c01103120608208a064071880000c5801c0d0341a1400046294552000070f4004122545030080655000c050010914002d1107060f00980203c0040d0b01d0240b03400c0000e800400185440b26101100c5c440c203105545041c44089002e0b00c440060340e80e035054203005080e8464060b2031011000b0501c200104150070b0004640007681c0d00210301e10340c295003941e000c82d01040078220072410400e90406000002e0f03a007402412108c2856a005a00c80c0700f140ca4072421905441e484c0250341c1e04002071280c1c00d44074a0f044501410b20f032542e030000098120301051894009610640e0850324001c0802140e103091011042a200030300e040e2041ca0f80b07075038100083c0080702c2c0200c44604008111032040d030390040300c400800511904010416420b068039071880100305003056105600b0a003004810041d00300d240c3c941c440c5c0c451905508504007500071980d546400340b5036201080b84800c01c3e005121b20000000b074100403045148020706017828055485070003e0ba54100407409102c0046 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 352741591 1250 352740341 352740359
    0xc0f06091b15070816140123060f0315040302030a0e090915100b07060203010306050705040f050d0819030608071203021209150406051206060705190c0815040c 70
    0x60740440d401400d00100340c024101c0e0355001c3d40030507001c4801c80010403440b00d584e400012114a000c0c0a641421503425200c400d007801d6030321605605101b0712900c0030b003071203400c00310f140b484d0804130658104e010001d86001092621040034000307000c10183c2d904100c20964000f0003480e1f203c0d0690365042c03400f1801300030301040308025242d0800796001f1300c0b0800e0b06118030114441e84022032030b80710980a80e6425056085074404001a658290000014018040349001d13894000f042f92801c180b13094580100c080e4517000d140600c0f8807170380b00c09150700188100802074600003803010083c14001c1041c81c0b409001408903118440003401a082d00003100000c1c50039000410f900354001d084041c00c8080240c1c2c460303005902041e803055512480c5110040b524000d0805041c071a242e4550306d00700084282001c00b002094280700d0541007200000144000c0750321100250210010002c03022140f07404920302142d500100e00501c9201c202d10340d1011000d8130f460142c0e0040c180004203d072122258 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 352742841 1250 352741591 352741633
    0x20a02150d0605040509030a030c020712060e12030402030706050d0b0a0e060f040219030b210d02190f060f0e060a09150b090f0c0408190201030f1505040207080c0f0609 74
    0x4407000c1d04103201c144000c274003c4d001042d0444461055610003030f201d0480c0149031a0300c51050365059a20008042c880f0070400440d019008442c5040e41140741c15400260380d05203a0103403408101000c96003482d05081900040110f01c4020240141c0c0e0341c4034281001001c900300c80152083c1c40903941008141024400c0340e4648500059030003103008082c078160050455250a96000010300811042c040015101072200034000d8024101c02c41007100b0007072030b003034420100d1701e918282106650300252111919945080c1d2020000c01c81c01300c0001008010266044003d100b0b000d15820046801e5040c3c0c424500c080c420b0200d07a82d031042080480088400b01507080d0382196451000c545c0320710300c80c0e56090780300d000c011001e4074140d1548042820841181e00c10306409203881c0c0000115078160142070034a42c2525010010088001682900210a8400e4074041c80d4001002030600514004464400008030104c62105500e40d9000d995202d049840d42c41601941e071580351000343c04100 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 352744091 1250 352742841 352742851
    0xb09060405061513120605040507060f0503161e0f090b040b03040311100930020705060f220303080105030a0c050f040b040e0c09070201150312020a02150d06050405 72
    0x40d081080d440c0c03c9000810b60100c1c2410f00001107440c80003858240c21055014600d206113004900c6003024039100b031030400d2542100081c080100ca403021802d60090907260f22020590380d52030507008001040c4e440702c803915129801900c140c0401c40310b041c0c03c42942d003ca0421641c45400b06561840d0000b1180158020340c402c2c00020004500801e00c9680891494902c0c642500d62001219841e0011660014801c50742014580d8024100340b540c4507170190210800002d454582152540c006d444e80280d0080911a13a004206042d41c7c01c0d40700103a41d070300c1c07107604011100d068024040c2a080c124603c412000903262200100380c90a010801c0c1450542c021008007009040000b00b102c440c07409540c1384d40150782d035250382000b56918081c000100765245c01801e048001d410a01901c2034004242c481503a0501e0a1710f031031044083c0020302103070782000b99041009001c05007203083c0382c041d5001a50085001c9003080101400300002d003154000000d0404c40340d6641d000f88400c1d1042222 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 352745341 1250 352744091 352744099
    0xb0109021309233108070b1017010b030f0703050709200a05071a1302010c020307091409010c081003020d02150a020c0a08060c2b0207060b0906040506 66
    0x41c204100081508032260b50f00e060a07000d0a00300c21800040e070050421100d0b00b5520aa1080c0e043e00070744003070402d14103101d042c0054061001542c070790900e64403403000d0042c4081001000107205080800e14940540480d8191201088034400340b103004c3e00c158844a8400c1c0a00500d50102c842c00041c2d10003165070050250005900d044496001400c2202c96005010006060071208001c0c0a004148200860703c4494503100d19081040c0081034101d0424808d140c2c0c1c6040c400d6000000c4c0882120660903e800c1899070300500c042401c211150303200400c0142803c0d03608000c181140b684504c1840910001c0010551000b0122464031043d074044601420700f907801e2015040045000480500140104510400480e0084400da2003610000e005030000d207072a409526014414600401845000b40901d0238000d19081240c400c9107070304021150320f6441120840900320900b485103040900440d2551030500303005015080b90640d20313100e960400e000521500c0c040c030807540248000f42c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 352746591 1250 352745341 352745377
    0xe0604051f0504120c091d0316020f0a06020706022b0c030e090c04260c0108190515150a080105010f030b0d1112030703050304080d0b060706090b010902 67
    0x80c0ca65000070a4056541d410010100004564000c040401c102d90600c58291111100d191038845400c54208040c0b5008284440d6103c2c0901880002555900b541801400b6041016407000910340c0d1101540945c0000303c920b0001040e50300414544200d69094083d074000c14160034211402e449000c52420009094000862103184920b00c5103030018402d0030300014070b1144400003540c0601c201c40341182030b403000900788510415a00483e000300c0b4441c80f4a075150b0440e164450701c40740e6100d2001d04015064001902030f20002c624140d1402180f44200424280b4034400c00c441041361031301c3d500800111088119004103042121f01c0f0500c00c0d0b07200902741e401c1600448464140d41400c00406071075200c940d80c00c1c2c1e14105102e0482d0700c50724100302d08070408000d11034864120740f00d0280b203410510212000c00d4010301100d9100c0d034840c010729600d80840d41054000d00324004107540040c40480d00c01c0410402d540010f104a01444c0c1c4c05070302e60782e54100b6070240d200344820440350512403 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 352747841 1250 352746591 352746619
    0x91006030e060f0106180801090b07030b0406050f040504110d030309061401270e070b0408070f080a15020d02071a06030d0e040218101706090105090114150a0903030e060405 76
    0x959503046c2c841c3c00450102010b6560f442c1c82400e40341c89401c2a14290055001c3c040030f02d8052052001041090300c00b444050701d4540042c00040003001303000d020703a858000040030019080050922102d00414072480c0c08000d04008005001280f411101d0340d10f0702d59114036210701550600c1c120341c1d8014500c0040d455401889000721304c542ca040c1141510b03194213030700d942018410200a088807002c040e0329070385000d00e03003454a140c1c1d038458026420080e00c180000040440c0094442d50080c080340204180300452000a104210700c1801003440410354008001001601070f11081004010308419240d1030308050301e4103070805098010070b00b04601035080b424141c0140c011618006107000f482c000b50008221310211017404140003c0501c0034801801d039a80c0d103000d420041c01d03070340c401581d03040101040c00c0c04030600842d019050201022613143e540da29209a00920340300b82980c5419902001505040aa0100f14041225a01c00c00c20070709006041c0c5c0c0490303000400180c2e1442d09 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 352749091 1250 352747841 352747847
    0x6040b0a06050a090e2a01320f040504110a1e0e010311070b090319030c02030f0f19031512050a0b07110f0a0b06040c1e03020405091006030e060f0106 66
    0xc21407a0b00501c2c01b0700d01c00c0d081c12138950741041109040366240b0006544100000501c07025140f20207030541341420b503002d104032143c1040d1030859981000000c1c0e4904124140d92400e028036440554000d04052008107020415009031801d07d001d521a00300d04192483e000203521612550076002641d0204410707265071080c1c118104622a8042a518011403038036000900b2074112200c1c034440e400003c400a1030200c0b42c000c06541d400e1850200318446d0742c1c0b140251207110b1041444c0358540040350500001d070500c0211607159030498100581c11004070006000b801d05404c03410300c4403050402c0020400b1709400b5251b151988040074040841c415075070a000d96802610080c03c0250960303994407807240812041d0200c8800320020450101b01d403510b003005980003085180110f040840141c216504148074205000741000003800c1d40d038100600314000e0140d5806140c1c00060354003409501c0c08480d1300b80040d9039540d5414090006030340b418a5544805495080c40059000d0041100c188 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 352750341 1250 352749091 352749101
    0x8011415031f020408010e060f0c190804061d0d030b0406270b03060103110906042c01110406051c020a050f09060d0f0b210706030b03030f04060206040b0a06050a09 72
    0xd00c25006082546804005d400c5602c04820520980d01400900403c00c00044501e640062114082c0c2d203006c0080d81e0ba00c2107030203014107081c03d00c000e0801290402166411014003a0841201652084010500e07950f507003d801c0b80c1070002c03d24041004640d030038580154021b0700d0050043c0814500000700c1da035500c0e0854a402509103558101d00035003a541070000c94025809074104114000001c01003180c41c10b0080d111034805d520309006c490101100302c0d9502d241002c400d102d500f18210880d0514058046101064400d4100040109600b60450f0107408070282400d040130b601040040d00001f00d03c074000341e2902050050128151070302d0704400030240b240000d48481d003000790020046003070720320102c2200c20517501c6122807861030502110f02a584115200b031218030302d007103054550300c403006800781000301038072820103482d280c40400854101c581c18807001a41c030759a558000703440d21380a0b43c00f280c04d0809031001c1035607683c80c1e000348410348000400d40004286040c4a0f075008103 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 352751591 1250 352750341 352750393
    0x406080417030739020d0606030b01062c0d02100309050304031112011407030f1b1110020f0a03050402030a1523151005040f0801141503 60
    0x34900078804540d000440d01031800350f09240c9950088891840c03441c0d5a901c0200420b031040310300b80700c502042c14011040c0030000d40d01a00c6100c40c0d00c4150801c00c0c05489a90409002c0c589020000201c440d4400405550140350700100c2060980c00d880c1403840c4448094015481520382240304050310300b11408003c81405404e001981c407010360389041c216005544140c601003a803a00c900903e0800700140e01e000d400080c020400c010449041a20310403000c1d0502040540d218500c03010b5015a9104541c49034040d4400c4010b488bc8600c021f02c021803104103500c2d14002c4019103041e4900c18026164030743c046600c1c840c1071656440045008000041003a82d052003101c16030004030325035032780c0c1086640c44844045250440940030107200c0c00c081041180b14949802006506440c1c0d80c100741c00da15003269030b106103858010040f100741c0a030381c201c10340d034a002d80740003c0c41070b8056103c1d4644020501a1032600d550311442003641540c2040c800d0341681020218580340d84200c000c2039803035 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 352752841 1250 352751591 352751603
    0x7020c100e090403050313050124080604030f080a06030c03120306080706080c030c0405040903170c130b0903030906030a06050f0604080a11040e0a0305221212023a110304060804 78
    0xc0d01d0344500e400d4840e51001040b0704a807990220314400a00c4ac4d0074806080007000824403801c0940c0c2c0180018a0407074014104648140400c45504041d000380c0e0040da0007406072840f245d1681409040c0105e02e84859001c04e11300f203000140300a012440c0c00841c1c200e41c8075140e40e660307140c00552203903200a1010200040400c00421150b60f54440d60305420300075510790071105000140701c002c188000e420454468001e00c00d40000700240300b292410b1759105207070340d0740350034001020034918001c02998640c0034070007204024208006600400071110100c44114151501d07406211280c4103500649400d81c20080c04500410005d0706400d0b65404007a1002610b42e02d505c1c04541840241c0b8006c400062001031034000305414140b91a40ca4000c2919845d0f40c9842c200f0300005514205a0041c0350801d05a0b928511724001d011082d58920368240350403862524101c0140d5001c103032092000c42880314100460b0080c81001000703d014201c40003180b5160a00405032684c2e9001042240e0b4 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 352754091 1250 352752841 352752871
    0x20a031b051f0206010602030c0705010e0f150c10050411040207230a051e030406080405070e01090e1b031b19030c0f06031b0804030e030607020c100e0904030503 71
    0x65440701c0c1e00c211400102e030240c61802c03420716040242441010f83c094030456005201d261000c0344042424801c5074800d082c440000d19942e4041490f841017525078545c000905000c455001c101500100b04102d812425a00c2032000b4041503001c481c01903e002d8803d0039902c0d0070700e80e0f0782001d60090440c80e0207031142c143d01d8521641d0104000d1845c4c1d040341c916030024034003c4100301040103403000900800c0000d000e41410805059500d0013144076240400034100d0104003440000d02610010785508100000ca5684400941000e404c40a64108681c03003a41d4040c2240803091032100024100200548650240500c00400580342d1036145540500d41c00707080c054007070880e0f40e10340c000d41c810712001464510b00f980328400030741c0650104090505261400c0d40d000500d448143c0600d4032418101100d131940d007002c982d103c4000142a40622440c000d12002a0300001c0d2a01003031402c40b9921039903500303030b0b17011150008100c3d10650003045000105000a002e8009940c1c0070a6903031314019 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 352755341 1250 352754091 352754099
    0x60207080c060103050318090f040605180304030c15080402010806060d1119020601060503040f1707021201090606120506160509180609070507030f0e0406050301021201170604020a031b 81
    0x400c140d0b003a4000c4400f079000003215407124280b00b034080d130100070403a0b07485030303520713220041d2001480d000308000c00ba59901c1001500c1d40c09984100d88425000d00e00b00c0f5111364403032818111a04490189240650400c0d048592051080340c030644070b26410707074902002c0c1c0c481100307026803508040510f4506940f1141031041440102c8041c0c4099050f480007880c24118001e80a8141903042c0c10590400c0401c00070040882c02506416026903441011040b0036440e07180c110095002d0a28006d5000d140c1c61141c5564000c1500b000c2c05e0540607000c1005034940d030b0388154400000c0341600615641001000449040384103a02c80c0c1c14109500302130340307800c1c12030002408251201e0060100c104800c02030042509201000d5544528181040d502d4160342d9240981003460019080c0100404240c0305202602c0310b4001900604028000303545503040c0f030f54280040d0400740203000054414a80f039828180c40040c03200e0190b9005400e9011075820358580d03400d0400f4010600e003450301802000a = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 352756591 1250 352755341 352755343
    0x203030415030501150f0c110103090c180b0402130302120304030807120219030c0f050c03100c031a06041e030b0f0403030b040606021e0715020606100c0305030103060207080c 77
    0x95881c000594000075a981003031088040c0e180d420030100e0400844501744405582c000d00441041ca4000e4a0160724040c0c2c40012006010f031018020a41445400d001600300c14000d1900f02203100a0410b101000c200c8043c80700301c3c01012072030b9411145c104003c20150070040d070013038a281444426245890f07107984a104040e40811001c41f01c9a1500e910749510b0390b410700c203409100180031500a0100a10744008101001c0c402015080e80300e059020340c01c1160400a2090030300000d400d554041d00c8000150001b02141c080040209003400d1400d01102408041d034070720080300034402403c1904010900301900c0607812000c2c0090000c0c0408400f15040d86000ca1249105040c82e45152400740b80082c19541c04500c064011803c11406101c055004185c0c500702c5601e100c0d142c42d01c0c001c41c1094a2600c10380394001204013000c01c1c000b140441d030205407540f003040d06036415a140c5000c28006c9a0080d0050000b40c0007440600c0180b00280c03180d001004007030b009001c000d003000c00302d407002 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 352757841 1250 352756591 352756619
    0x501080a03090e040c2714010f0605091011280606120c1701021303061401080f1f09050d0305010302121b0411040806010e061306060c0f02030304 64
    0x8012a48504401010941c0c000144000340103151050003590610340d072800f45000c2a030050480e41d4102c0c42c0d13261450340154441111070004058180041941840c0c0303400408403e018640c0c02004030100424103034020421200e034810050400050386000110458810404802103038641c0540d9100d102d40210402c0402d003280c001150702c2d400000b40d4900346086481c182e1008106d11100c0d01804049940000420119808903c02006c09003451034564024801c502103100071203c41400802441541e0703102411004c0c050a040080d6620b401030f441e0744020200c60302046500c6841c0f0070064024100e0020071000b0303100c03c089100744950313070341e1803c0444514a10740001d03031743c000400562801030107490b002c0e84070b200501718450312112005100d05440056601484d214078540304140d40307007000c840003001e00c02c0980c2e10650711800420100c1506680e204d00c10f05104034001c441c40050711904085600f240c962084001060380c0711008822145030680c1d05010034030000641510842c81c1c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 352759091 1250 352757841 352757849
    0x1107061b021201090c0602010c0207060801050f01080a0b04060b092b110120010c021002040b18130c0c03030f0506011b020a0b030907080106080c0f12010b0d0f020102100c0e010c0507090501 83
    0x4111000c0c9c40344020314125540d805401045081401002903031140145c1c5000450286041c0c0501d0342d0b00ca401502030840c0328a141e400901c0e0100000724002d6401c0a800c580404031040070f0105400c1da031078440b4480c1d2030100d00400d0740b41141f00c1d00048143d600c105a500701810510105102c081443e0704010b6042000b69490351200c8049104642c1401a5040c1c0c1c54010821030400b405c2186100d040c1c010109a500700040a50b00f90031036598180c204200c01c18092002d00100c8036015004080c413491002c1140070070305116207000900e107135001e0148240c5040e9900390403000140f040c600303103025a0740166000200c030707503010032a100f203200194411032842d0000e00c2e00500d042000d500311240344d0b00010254000a54024007aa0b0b10181e186e04180115404854032124900d41401052030010030780c0e00c408921075000c10041c04040482820b8002d809a82d00c1a19002c112030079201c0403201c8400042002c020450b584d0300401030440c803540a8021200500e450700002c2003241d03003c1e08 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 352760341 1250 352759091 352759093
    0x1d030a1a0a0f15080c0d0c0b0f090301020c0c030d08040b190b030709051b0f04090507140c01060501030e01021c020a0903060e030304050d11070302012307031107061b021201090c0602 80
    0x701400449000c0080c5c0a0700380d02644e5142c130305c441703c1c2c81d42404084540070340e070034400d00000c00354026142c280584281032030081c000c40d03841d40504400d503950642c07520020b0080c0686120b40b14018000e1803100c2c419500021058190b642c0d00c2003401c883c0031200c020034801a0b50361413811650310200b10b100041c001d00c52002900c0c0c01c0c41d014084641002185a80110074100001120182c3da00d090398201c0e12460701c0032609844041d0150b03901e2026020701000f00101189003001d505054000204503002070301d081042a06040e0454280d12840f13484401c000c200512000003190240e0081528030720619095154903140d640e80e009035041b0404182c2642c0c404010b100070b0080501c814001d000c2141070020a000b000b00340640c030340c5040d100180c14441503981304194510040441a24454450051580c426a03071070702a20400460901b140640305170200403850900600b24044011140301600000e10455400c010050403ca40c500720389540ba13010001c0081c0c01219050041d2103550 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 352761591 1250 352760341 352760381
    0x90601030b011a0d0e03070503030901060612020901020d0c03030f1112070504060c0308040303021c020a02100605150906122401020c060703030e15071d030a1a0a0f 72
    0x104001c0c40c18038060708401c5100103122a07110514901c1401c54140203021031010481100b109082d5081d03000d004030140c203500000040050001c07040d8030cc0c0301941e040341c540d442c04601c070484800490140c2007125015900030f030b2004426130b000714000c01a0307138480d28000c5502100281c1180a481242d44082e010920100c0d42104501401c4c610642c007160524089003014680b850080c070791184100b0103814808854045024180300e6011100f0120121416142c2c0102d41c960b00b02c000c1d0300c80070440005009801c0042c00c003080340e0241e40101c0e0002400c0b00103082c0c906140c4a6281d110101c0250b00001c1040301091001d58143c0c0c40388103070480071100c104481c400c400030200e4001c4c103644a0441d0801680030744155200303800c0e00d2040d501442d001500c407140c82c5403246417114950044024404030010040c40c190b00c00d1a01040c0c0031000c25003440d00d51080240340d6103a5015500a180090440058418210200c81c43d0b1b0b1004c00040301040d003529444203001102c5031619a80f421050391 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 352762841 1250 352761591 352761593
    0xc1101050c04050a09361e020a0317070b1003030206091605120118030206061305130b06040209030a05100e151302150403150b10021b040e07290315010503040f0b09060103 75
    0x9805d12455184aa68048084400c80d50004405027103d000c02894076400070010510700c102c0c0000d0340d1125a10842a201904003d508520408178030f0cc022801881100e001511212010130200007140c041807402c05e8041c145010031014000b40305604029641c1c408042d0401c00c0043e0311400c0140c001d40142c800f40c00c04000780a0000c140e10b04c1c007000c0c02d00700004d200c00c680e445105c0c22111a000307203102000b41c54510001e0041c3c8030b8040040e505101c1e81510005000001c20f82d440300f50414001041420030510350151900c07080e0f007110565180c5400060030b038103003160740900d6051008200c47c07641d51311802074008503000341d003042d254440040360303a540c12130b0030b4802d00c03216080440302c3c92011098400b00a40c4d6400c802d1884104100c0400c10580f10380f00e5400405040c00c1c000142c581050300e0300c00c0303009900c0074541207030019440007488030400c8410f80c040b01c2c0500b25803200c03110301c40d40540041d6040d900c050710843c0d5220500c200c007400700305000910390140c10040301400710307035141d = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 352764091 1250 352762841 352762853
    0x1c110d051608010b01020307030e060913020703030e0606030d1d19090c090605040e06040e10020a03020306030c0405070801030602030c0d020c0c030705030313090b0a0503010c1101050c04050a0936 86
    0x304180450540d8010860300020940000328403003501c1042f50065528800c50340813501000410143da41d02c2c50010601c84101a01030300302603500c0750b1080455065507603490425075034000408181c004104103488130016166540442e50882002070a81420b813416035510340f0410950303920412449035928a94030841c0d41c0111a280100500e160150800f414010b000b24684000750078240f00d030355610450148040c0c02e0100382012000400215121030392000f01402039842100d086219015841e016840f61400e407042500800c815a00c0b65056800c1d40d68203402948040c1201004620900c0039071004030311400149200f00041c4080c0210b01c02d1141410710340703005d9400c01c5c3d21030340003031220020780b000702c0201c90100c4a00c0d01c070200d103040b126004140068404e40000d07405500b8884a00b1186802c80c1d410849803021a0080082da61a000441000e001d00d019a6034016840c480400601d02d042d00980b0b0182440540c0d0144603c5c00071401d2030001180e0200301e0030384c0d080d900071824800 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 352765341 1250 352764091 352764101
    0x20706021b280b13050c0907020d120c0804080343030506030c0409020a1e0e090c130507260709050402041208031308030c04050901051c110d05160801 66
    0x81040d0351400040215520070f032183c0301c002c0c5035540d00700c1c0303000900b0b060101c2040440e004010140c50030440c0d05100c00b0081d01c0d46038660208000c120100340d51018002e041c412108810015a51900c0545541c1d40e5807515501c09088105c10b80029a420364079042144492020780d085211100003294040f007065501c0011002040245840e02007004055140070400841c0d800e0100c500041c0000c15100007500310301641c10601c48600c45800c0c1042502e088140300003600c07110b8812247d00c0d81c80441e1140d640c004524802e400c4620345000044040c540e0300070b41c0e041000c80c200800740300c03c000c600c030f081c110800030012150440e0b0000d0260722500642184e01800064801354601428107800d4004000040c0c8024810345000001500c8130011002451200d54007418240d540d0902c001040703400c1d000350140601c210440400010140f5220394881984400e5075005100d108043d242e2104c030301c00d05c0c0042c50708070342e00714526400200b00380900d40085243c1c007851605541071208841c21a0 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 352766591 1250 352765341 352765393
    0xc1505071704050a11060409050f010602250603110f0d0504020112140103020d0305120a0f152103120905010e01060609260a020d0605060f091504020706021b 69
    0x3540704144400709102003850080c05403c000101e1207400d000e008141d407403095500c0300300645d14180034081810110419641207070665400c88920801203048100d1714601c44040696800e103043c0b00f080b01d1806900410030107802414600c0c2454110042e007c000d03401000390040c11580d0760200b104540e04142e00a412441c82e00003000b5028684503e80c0c449101808040e1051030071080e1141050311803002c0352405060741424003410701707024842401500034050300c00c4400e408c20182d10245149550040101d8200b08101403414484c0c1c2c000035010b10946805504004404240184000c0c15009620b030b018894000044c034100c2c90002542104ea00380c11003010010b003120204904296140f42603a85251461540444524191103914000204a00940010180c0a100309000f0103038046441150b0603191141c00f02400d0041122402080741c1d80b50645107086445141d506041d0b01406545201d0840149451222402c0d200181c0041c6128170f550b52010140204a058071b240000c110 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 352767841 1250 352766591 352766627
    0x51306181206020d150609090b0316031b0b09060403081c0203100306060509060f33030a0b0d0507170a020604090203071e080a05060102190b0603010b01020708030304080a0c150507 79
    0x40342c10101c0c024507110f82446442c03070150b00c80403014119501801100e200da00c00c00402f0203140d5807440c1ca0104904080d04071065084c60030b4000030840c902c54105c0e00000e9000344628a814210f94804e10741e90004000c11009441070081c20350510101d10003940148001004a0f5086145240003802d80c1d130f46802090044030b90030180700b084d03180d410502c48102d004075411440c0710b07a0350718640c40c0c400d020110b030840c051701d0144403529900c01c0c800950140c2c60205050101c0841c640a110a45004180080003130707100403410400103540d16046654894044c00340da0110206070002102900b00760007655101d6400003e100c00207420400301302d80f4108299031a0f0090a180802078800300000301301000c0140c0f81c800085e00c0c0d038803c1c04274465001c0d044c024109094101e003840c03100c068045030454000d41c07909841c040c1940c000206003007203a01c1c4000440c615960342d40d40c0005904071034811000e2102482055000403520000005e2420401800280134a0624801481030341010144214 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 352769091 1250 352767841 352767881
    0x3060308030604021e040b070c121a0c12010f08160b07020d03200a0209060d05070314070315020c0d031a040c14120f0601051306181206020d 62
    0x341440c810750350300c01411a4010303181c90311308122148004590307400841030040000c002c2680381d02030b4042c0c42058002d0000002d00b40d20382d0440070700303820301d84d4028080151089003030b10700d10709050120b507202c03046c03514890406844095170303041000203030091440302503003100034483c02c03500b0488103000c042e60300228540b0070300e003d0000900f4895284003038042c0021200000506018201418200b20394640c810000038010002c90b031a541451001c03032140440e1000f00d0071601d803014041d0b070710f01d4010028001261550359442800b0901d52181e403000d004054001010480c5080e070034401c0d0061001c00341c2c2d40c2c1e542007030b601d0078440b6000c000404e05261014810710406034079007000840105131000103214041d030b4401c3d10300c41d540e2408400341890001d094020701f800c07008c0b91802210f81007143c241c140c80d4078005641600460759401f08002c0c04d44010000c81c0e1240140902c94940b1288004074a511485c0f200076211448000744c8810b80c000945200c148480d200780c0051004107080d01c26 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 352770341 1250 352769091 352769093
    0xf01050c030c090a0e0703020306130b03031815040305060108010b06181306030b1e010905040f0326070504081603020f040b0f0901090e0609150402010f03140a0209040c030603 77
    0x12181c00003a04100400c41c0201d46a201a01c492100304040c05039820440c5003464040d9000b006035200b140d07080e0040001c925040f10510480c0036409000b0030045c0a54141190410b02e030080521070100d40703078400a14102c480312a1013034001000950b00440180c5102d6041450148c255880c186a003802100100719041c2c84201c91010301004502c1184c1c5811403c002890f02c2c4041d00080c0c001030030800e0180103025803d2080540801d80c070180302111030081e030fa6040090102e0b0022140a000c4001c2e92503043c000920803079001040050680c1c180e07000c803d08000c410404003040f07407507002085000a0a1044010410030002141c00702940d80304480d0441e80803c86100701c1d02e43e40e0303000c1c680701e4003100302c40d40d90500e0329101c045024002e0f43c51903941c0c1c4029005003003081000e10f11070007a440812850070000c02c8200d0707860705c00ca4011101f511690300444404a80d201038804040d03541c604102004200c00d1a40d014031813060003d0f8031080e8030b00030030044400c61a015418989040c0c8100 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 352771591 1250 352770341 352770361
    0xc030304350a030f0e10060501051303060c0903140a0c0509070c11030327040b120a030e060903060a05070206181902190303051e070224160c080f0105 66
    0x107214595100159a12400700007800e902074660f2800c415882400c1c07640c01c11580c44005807803030710000840001d03c800c80c1d85200540e041d12911001801c0884850000c2c008900641c1000e21203903581c3c50711814030340d6681c0314058200100b80004485810015140c41030000200c0010080d15007260310707046508010030003406060042000408205500c061042c00d036605100766414607065456000c050081c9500c4569542000305056100310b15105000150b400d000a000320071005601c000d018a008540301500c00740d0b03c48030110360001d4201314201c0f06890510107140039070f41d00c84003c5054248054042d04240c40101140d00c0419462100d030480000028440d08100500604241544075400480c00c4031181844925101a01c100b0000402d40d014000345205110a90681c68580000700014854880d41401030340c0700c0b2001000040d410700c030304100070041e580340200f540b4151102402d505400c40180c0709079107440035184100001daa0503c1000a03004625008000301c1c60100528 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 352772841 1250 352771591 352771673
    0x70f08010f0209031903020708030c0f060a330b07050105090706031109091003022206080c0607080318010e01060e0907050a0303050d090501020409020403200a050f040906020c030304 80
    0x18003c805c3d0380b503107043c0c1818000d00c030207005840c0c003600743c0c0c1d0b942840c908440c1d0f4512032503000d101140300c0c0c83d00103032001e00c15100c3e42c0b803209100710b03a40110f0800040c01a5036100e1034a80304510741031681e40080c0b2508000010907106100e0390010a5a14000e07801c5410326240d40e0200b0300b41410b0581c031b540d01c032811a080301d40240e02141c2405c44d913140c100303507151910070503013000f5000011b05841804481034140703032084a102003c0d0600c1125114a00070b0344460001305c0b50b94200009008d988009075030034001c1e5034412300260580324007603802d045c91802d6414021480301c069542c3e45041c02138090204603641c1c024010300040602d1071800001c205540503602c4060304211021a140c252036070303550030480350b80307401a0003035484644842c06280254418401114541402d1420706580355550080900340c840042c4002d1680e1301d0300d0709210460108484a81c1d00c207540d8040d00380020124070140c44480003040083d038481c50315103041d108000b079011009d40f005200500343c00c05502000c0325 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 352774091 1250 352772841 352772863
    0x19050a090e07180203041407030515070c020a090203150d0b01140d1a07080601020d080106110307050609071e030b0105041802030a031701090209010c02040e0a05070f08010f020903 79
    0x64900741412980d04107a0190407002c0300c070290803407a209155550300030314004c07030040d07104016841040b10410354500c1309102c024000c0d00320089090030201d551070130b954010a82d09000c1d132007001e1980050a80d81c007035085608501d07400710900c10300c07001e51600380f064058241d44045080c1d8281c4ca400700410720500c41c5c6801180310002c2a01c3c3c40d1500c0001c41406648a460103004400c0c185644000c039104441c040002191030000030020361000408188403003580d00c410409902302074080b05e284150701c2060120784000c00c03105c4001202040224031a080030006480c01741e0810303032a020054030100304451003808048041c00070079004521107044a00459001841c200c0400c91022101829400603505010b80c0c0160030905030060a601d0055070520065604c585e200c46860f07040f8010500128000350707096080314010709141d80700c00083d4030301400f00c912642c402d81c0c440d443c1c14100d4100e50f4124011031400c0142c05400d0190140040333240005604020a0802080e903912442c10 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 352775341 1250 352774091 352774109
    0x60c0b040611070c1508040b0a0b0a0503120c01050603160b07060618140c0c0a0f15022d0403021c02040b091303080f090606150f1819050a 61
    0x800300d41002126071165601200940902c1c0d2100c4060408100046107071150241c01d11012280d030500e98480c0700b400f813203207a01951a1031070742c0302d808da284002c0420040c1c0f07907044120184c01040c1581c04100503494000710104c0141c0d600d2410030402d080d66001b074021802603114075040c031128040b003000b0006881c0e2417140962030741081d040c107101a016039448804500d01980701c140080d60300c1d42211150015446110745c1c40c2c0c0b04c1c60820400743c4603040d034402980c0c0024440d440011340c140c08c41050130340201014010f021350040c440e8101e900007401469591450b2401140f00d42101081400441c000000c0030309103407550b0080707003d41418500013031103000c0c2a054141190759aa10161040002a110b421903161007145079071344030448001540414038060008400140300490b1a10070507140c07010300304d103032901414032000302d0701031207589014081403000100c0f0520b000d01070081c00b44501101d5014440040600c080d01342095120251342c4007410303040c0038a07141e800c041c0c822509051 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 352776591 1250 352775341 352775363
    0x801200a050f040308391b010e1e12011a041e0501030309090b0307140d03021005090d110f0c011d090103080d0e030406021c0309051014010609060c 65
    0x640e1490244078680000340203400c04102d28096040a4050300c1d2211b4080d4641304101191095a00c08004091a40042a4081840f1507105095a201c1006414043c1080781c00c0d800007800207260150010a410447d5245040c001a1894103404004440a04030000c001001200004200515402411b140566200c40d0040880a64880c0070359061002050030422543c41c1d142c01881300c0c812b4171540c4111400c0c9000c071801454003081e000d0454200010042807650b2401c107000c0010008030043e003c0d401303a040c0b82c0300c40841074050640b140441601401302c602d8100720281100ca03c00c080788070594081d9020702c3d034900f0006250612003a003402e08580c40c0c1c04221007201c80d61115604142c0003010000000100034040024000503880140c05100d4800c1c840119541c9011b14480c82c40183d0211881020460554910441140b035515020500b611940c8400703160003245401c20010660b40c1c0e00c0501d403956180205400740c800c9207010071000d0302c2c240e070040801d8840c200141028801c4 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 352777841 1250 352776591 352776607
    0x100207051e040507020c15040b030604090305040b070b1603090b040f0c180204080c0607020603011a07120c0303060602160512011b110607020a0c0e04020a05060f040801200a05 77
    0x49800072801d5005106005034070340f94000a40b40d240c0307010f0107030180301034601500d422503030302003a1401e44080300f00d030500316030340c0504002c00740c09403035815400e100c0308200103d04c20904030024012580103102c55031643c24075410300b6500821080c1d0130b008040c0307440c54140002d060713500990303009604107460317400c03240c5181060140f90300d245c2e1216601201040c40d554000c903194003e00300300c902c6001034900340f4003c2c0c0284202c501c2442070081d0f02100800061004c2c0b03074240480c0607003014040c891414003201d03544140070030343c1c1c0024500105802c010304000305a454060380c0e024004c10310180c600300a03100d01c000281d003c1405040d22403004031402c014141425803100e441c100704070f0400007840306104e030090549194007440400901a0800241e406030002441c04900765100088040903480c10098600d004005001264000342c440c3d0001002e03034900000d01480201203040780c1d030740c40c5400901401c58020501d5a003440c545200c0e812b50f41d07c0c3c00b0051301c403c40040d00340342d651903540c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 352779091 1250 352777841 352777879
    0xd020901090b1201060f080c040c0806010c080c15041401090b0a0902190303051209010b01140703030e0a0b180c060d05061801060305040b010602010b0d03110c0406080109060b10020705 81
    0x41050320f6150300e04280003565100484a4100701d81c0c564041c0c44c4121181c90034081610520042e1038042001d0002003501c41d4400c04400505d540100041c0e802c194008401c0f6040c205111160700300c01b800c0c1414081800b80714942200c0100e9070f0402000104030303660f41e18180c544c00402d00e19800c0d548000e04415516030300846130882c03040c40c6280002a0b1a81303800383c043d40081136500103407038681c400901604030510402c03a8041c1d058440a00740100720740490050760102c2e808804143d181e1406540c00b02c0c0400c038111469110726050000c2d4680a040d07008540e80104080040d60322032001c1e51101e40b580c00440b4410301b0344840c081040d6441501140308901980c1c15003128159081c00010b01550503070095004600c141109031032070341d0301c1004a00f13903616004029404000881c0180c0001c1c00303490700302080703020341f4165500301c29690002000c40301d060303011500994645d0210000c1098901c1500a0007408a9110246440341c0078000d5442c0300d02e000701402641e102140361300d0500 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 352780341 1250 352779091 352779109
    0x80604020903060405061e01031a100b0a09090c02030901090b1602030703030507050d0806060d09030e0a030501150503060106090b031b221406120c0c031201030c050d020901090b 78
    0x3000303000c440c3d081c10940b4015076149401c0302d0f9449200c02200d01084d40c103800d01c100b103041345e40081d80c48900070500c0c1407010702402c01410505022945a50003e920809180030700340c00041602c500b011941744c141e80d0030550310b220081d10110b400800c40a0080c0c0e8120802006555407042d0f529210142c404e003611850b244a04041c0d030510a000000041543c06001000c03030b14030031801d0b61a00d04c0500c5007035500d21400d5a071103502c110b06220401003c080ca50000310036034043d1500001c031142ca0004102d10351310b65003060300c0d665152406152480824a410002482c058000b0324656160400042c840da04a01981543e02800030100704051880c440c00c0010010280d152641c80c01e0f55030307403c030881102a04500c171029240000003402c141c40b03100321010110103031805180940c580803140903041c0040030311105031401c1c0441c0101c40c1080000e001e003082e100004080d6541181071055400700e031176003c1d6106500300806e0f41c0040e01c948481a0440d009840d000c02d544910740009000340c0 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 352781591 1250 352780341 352780357
    0x115050906040f03080315060a09030b0a14011403060c0310030f050f0312010e07080108120a090e0403080718050d060527010606030b0f0f1507060203070206071b030207050108060402 80
    0xc03c0580401840384640c0298050780d40d0003a0900061074041c240151b90181d101c102c00895228482000441d844001c5107600003060703400052810b8810f2000d01840700700313070050381c111032003078441d40e110741410880280c0003c607140246085190120411201c2d2445000090818080b00200e004100003009036421010714401969103405140c0055600c04009105940700410340c180460300b4140103640e494140d03075500c406000c8044420403030700c201341d01520461040142d100710016542c0103140095005a2003940d80d10b100d401c040790000c0c04d51800c2d6010051401c1c441a04000503a214641c1d1800705600003c081015511201c49103542c41c01d0000311014014001c02002c90100103501810640341d264500300440302e400d0003403114402e41050740c550052a018101308461404120888801c40c050510302d140082581e501010380e001900d40601691080d01400b00c1d0a420030000d41d101d02072200240240c00b40d64038002d540301d4030340c450103042c48004004a000d5484070b030100c5e0326007 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 352782841 1250 352781591 352781609
    0xc0c060f070c0b0d0b0616140309041415030f0703121106070906020706022a060403020d030906090605270303040b130e070c02031c120c180905011505090604 69
    0x31550f41c404100f03903a40000c0030114a1490f005e00b0506903c5c00700281c50440e0242ca9240302800460703540c004500180e0000303810184014040d180c41a034942c01191000b00c4000c0750000c4a041900d01c2c200f03a06081c1c200b140c403a411000038821104000652881140c0e04a0448581c51400182c2554668031400c1e2840c1c13540280f908015a0981002030b5400326271250342199002a9500c1c0c040361281046a0707411038241c240103040954a1003d900c004490f00014501ca00d03003aa41c0d4000f0b1000301a40c8011000b180801004021064020240d20f0041039a4101540f4140380059402076021003054107600c2c0b502241c121a185071010400c0c2c0300904040381301281e41c0c48503002202c060114612507041d40d1048400050841c138440c40500c90344650280c02800080701c1c984600460390200341c0340908100140d0030904c440c042d01e01a202c281041ea444030600d442c0c10940c5c2c50181252a088a6601414100100200700704210003214803002031600315283c0204000040451041d0f0b4843c400f1 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 352784091 1250 352782841 352782863
    0x724060608071814060706061d10050a030809010f0905030303070207080f07081c020c1e040c030504030816180303051308070302090115120903020f120c0c060f07 71
    0x189500148030728011003581d122408201c003807141e490a9900c013802040700b050903580100409050010107881c0b40340c4694004904940c885408500400a4400089001c69000148500c0c101e0080c111006401c083c3c1d6803200450441c0c43c1c0c1d0b0000d200307410075241040560100da000c071a02c50000c0c1805043c0041c00e0b42d590741080e1100070b540d55802e001c0c0b0391040c001e81030140b14082c0c0001d4000100c0f0507000140c2a51119010300c002c2c86517691008900394020064201e601c0e903118001c613901500c03401c001007960141c080034041100c9083c16041d0030306181209110110b900603407066130024002603101d40c20740906900311000c98100381c110340501d15007103011080541080207016074241ca000f8209440f0303a50140103555494a10002c1e41103c200c50041c0203050002441360030307070051802e025005a4100c070f0841c1c01c50790107040a400603004651004203084c81071281442100e60a4026401c00c401c00c40d100d51510f004130301c11446090002405031340d071001502580e0034241c20410401c8 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 352785341 1250 352784091 352784099
    0x61c02031f02070c060f0e22050c120c0703030501050306060f1314090601030b090a080315280302030d093221120a0806190918020a09020c03072406 65
    0x6e002402504000705452000f0032a05050a000507039280403c2c02c00314040d00310340300d20308001741400740c80743c0200601006654250040e000c0c50074081d020b038039a0b803580e031501c9040003030441d03006820880c882d400c07003018401141c0e103c4030f6800088408076800310b540141c1800f0903000707210145c3d01410b808403400800c041d40d1404165203048a014a000020b1070740c54141351741d142d54141030001c0420300c1c1030000c0f5400c983d85540000540c58003515106100c9842c00c00c1d0764800040c1c009408095804403801e04c1182400d001c900340241131402c1001869051030901c660704038400007002c1212220030010036003240804002a0004c80252160059280140c0803185041b4118088915442018075013182403481c107040340c40744d100076a105601760319903e0400031071854418140c060304441c147c002c18260b40300d100c1c045250304441a030711b41d910a580b06100e01080e80354880d4144900c107120006843c0008412910400d80c44003806281c1c109190680c04160b080c280c0a022061400d14085 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 352786591 1250 352785341 352785347
    0x41b2409121401051302090a09020a0e04051006060206071b020a0b1b06070804080a0e12011a040b030a050706050d060f0605090102010f0507140a02070b030f061c02031f02070c06 78
    0xb00080c11070b10001e11040c1e9800b51181c000b0849500001d40094110000650712802940100c0ca041d100800c103030359403a51242c5401e002c01040d2000c0c2c034550002070041c80303024107034411803004006c4c0d400542072500c1d29a030050900c0b03a40014420901c10514000001c43d031720003400c40090004103405507200c0c200d1100c800840075926032200518400d401c0403500141c0601641d921540d0b120040f286068240300b800c880300c083c0c04d003829030010742102071000c144000b8021544503060b8103d00c20404544032007000142c804c4000d40d40d0203904101407000c0400c001148050076a0154103160b80d5882e0b1040b0b03820000d00d03595002c00782c801000c4102003910355000e170080580d020700b41d00a0014424586c85181211070a0300c400380030030b800384c0d0444041e9400101400d030032602c50058450b55950fa0401401d182d100311035120490102a0030046e03d85031609c0c0806070410383c080003030340c0480d00f9804683d84a032070040018000103840f9444851a10580498400c0d9520803101501166115005 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 352787841 1250 352786591 352786613
    0x50f1303080a090f03080301150210050925120305091f021506040506030d0f02030d0501150212120c1308030705010f0b040b1c0204020918041b240912 66
    0x2420000d2840f040004000007216505000ea030381040a07146540d1800c1c0d850406050003c6025040d8090f4001007404c14076a0b20a880c4131310441009420b020500e10030350f0001103491a0396007032030711104000f4042000000c1c4542c250719410b08126540e1210300340003a140310300d0005604040c20000c500501c41c10382c0440c100f49800707001c0c046208191143c40400058450403540160154031454220400318441c0000894000f464015207140c442c1d6111000203840f004d030080b80c4c04003400000d8401c1260b04104040134021544516820003142c00107030409070781c0140a0285000d40410f024540e42c001c2c51943c00140041c1c8103da40d41c50741c0c0e14019000c0d00441d682815818a0504140d4980c10140103007c8c2c00e0310002c2040b4070131081c001001600351503c0c6801da802a80c01d010781c01c15605c076003000c07490549407140e0081181c540761070444144d840e0b03100b180141514142c0200958240c02d07000039074040001c3c83c8001c60b0141c01100711000c0b60203500080c00420043c42d800d052000300e000c0 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 352789091 1250 352787841 352787857
    0x6180506091507052b0b060403060e0f010905030a080c0d061d0907180f020f070b0a2328240902130512100c080702010c02070302090601050f130308 65
    0x104001c2540e411400352940d0080c041504071102d45014043d900300817041d50043d021a4106000a802c030b862004103a90ba005504111031031f9683d085c40a004000401c400b4840b40407510003880540d1042e03035020303103d019500500e030034004541c01140d081065801516420407001e4010014a696044014200ca4004030342c0072507048107a0210303600c0c44010542d0400d48041c0300d0313140e0001c0c003d102e0046c0200b104442071001664241302d54810170814070000c0800d00e009000e80700141c2011302e0b41c003080b6441b01c200700c1203800030071602312030b00c1031560203c69012100c10266070140c0602d800244a0054000348100c1481c0b0b48842c1904c0802c1003580845000c03054085d2542c0c9644034400c9008902c500d042c102541c481c0c00900b04141c0c5001000d421ba201e90000507506d07c41c1d40036440400340d81c0c14802540c0490300e90002c010006509218441901c440c910083c24802c0c07440c0c000c516501da001e0200c0d810014005000610484c0e808201c442c06000c5a100c8488540d0f41d00f040b100c160000c4038 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 352790341 1250 352789091 352789123
    0x801060e0f03030f0d06121103070b04080c0607020f030106030507060e151603090e0108012012070305060102010207321f0221100504060914040618050609 68
    0x41503810a05081080d181900d4000e0021803400d0344007020000305030404106038000f6600e07407201042c0c0403440e80e03c854049110302c0c0d03209541c10849003003504058854000d02c039084030a00080201400c00114607103c1c44003a01d1081e500c07441030001c00c00f4103d089603070382e4242d800c04000004020001440c08100c824640d24502e20740100740c20440314000004a402e5001000e110740c200c11544600c03e0001c1078403034105a007800381e0303c00c08804443d800b40e21100c10360b55074020310481c10101c0e5003441104900c007282c4600d005d402c0311300070301c144602030105c0d82015078441c00917040364001d604441009070802441c03020500800709401c61140c260000303280c6180c8100030740710141c00c00220000c20700c1c981e0b14103507003002040070150000c0d0401e84446410385864000c80001480d1015994003a80d0844542c8264508001c240300907600285d10000c0807500d445400c441c400b8030320740f215401907400480445c8007403204600c0c980c0000700f24406441c070301560040c040150000140c250003480740f14 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 352791591 1250 352790341 352790357
    0x60914101107060b1f05040e0109061d0703060f0f03120804020102120a0c2f0108010503070501030905030c0319110c010f18090203090109020a0f21080d0c080106 71
    0xd59841519059020702406035070038044400002c1960300894991240074200c83c5842c074602c8600c84a0403001078680303012450000e018030403291045511800360030425400d002580c60000d0542d094101030314a94003180d0081d011606041c400d4210b480200280810b035040d16840e14208013142d0441c4c80100c1d0041c0310b12aa062085020712101c6104580580182158548402c440452070b03109135400c104100760a1060400101810713020100102d03102407060015003544000300d4a10070014680c0e041c03001c003400420007568000342c41d4060303502c03e08e0049811046850060b1450040c182c0301c040d240004a00030180c40030000820b05800c2082e50b520000c0d0108a04807620f50f141c4070b41090002d012515008a0640126030000d480d640c129548001c09aa442d40141240c0050350250141e9440d82201c20a5180c448902d2001e8020502c00702c548030724201e03030340500b00c449032009400b48043c0390030582849102003c1d00c41441030740c0d07024802400440c600403c000030900035076010400d11 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 352792841 1250 352791591 352791613
    0x102010b0418080c0309060d2c120a020102090619120207050d11150906010f08031329040303030915090308041401060308160c05030a030c0b060d060914 67
    0x103406034592040d90180b00351216180b5440c0d03449141d1100e07144600390f100c200f0003c0c02d151901d10050000903040a000107561543c4a48446546c031081c0f0041d041d101000c480000c8110041081d08014200a00150303a4140345802a80640582c443c01540443d001c0b03a203500d10021944519480e102d1942c03091210b04002c0e4840049001d5410003606a61140120305011406006aa00c6a0351124100e03140350f0300c0803040700d00c08134044400c1a4950008001002960700014a410141c01800080d504007020300d0001d4002d00c00c43d10500d6140403400010f03059840d404002e401c1c1902c1d111000da0b03a01d41d16810050054040c080d41100d540060300d100c900b12507481d02c03c0e5145141d02d0fa540b00c0e01c64407540ca48031061106c0c00c2520101d0355031420000002a0000e0041084410305240307440340010504004941041650149002ea000005d4480010740c4c401e1701d50744541e601c200c1c4040c45413151030200f4001c62850a005000314580b000a0040c00b0003600902c1c000030b6200b0842c0c182c6842 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 352794091 1250 352792841 352792849
    0x905061206010807230a050c030d1d07060e06160506010b0307090b040b030a090501060503071220090117030d0501090e07060212070609140313090506010e0a090f091407050102010b 79
    0x21a04118170a0300742840400ca411522008100a2404d45059414800010400c50641d80001180e010803070f82c4564902c243c2c5014004d0b081083d4440001c0c04205203130200140280350100700380c6101d00c000056188041c424041500070913900413044402c9503840d81d0542c503403588295001300206480c040d000403801c2d140c81c03c40e426a82c00c02c1e13801c0d045441c0c00a03050045e01c21820203d032655261100800d00c1d071810004107000f00000040719900d20805d0074816000a41c144082449000e48008082d107615034444c6141141d44807c44808010801d065060031070040030002c203660307810840006a4500c454002081d02d2001c04c0648070a6642c4000070390b038480c414824050218030070310502c80410841d80c082d20340c03280a440390180c0011105c0c00c160031582300d011a0104513451034130900410a09200b0389a02000170f01707040910504041c009134460090340300d01c90486031900807588076a03c050b00b00d21000f03503021401c02c01d00058488041c2e10390b022402954015883c00701128041e143c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 352795341 1250 352794091 352794107
    0x210e07081c051b0a050f0d031b091206180804380d020c01022a0604031b140f0102220f05063105130b03060609070905061206010807 58
    0x100980702c4501d81580300036001505025444040c60f5030140204403004650b062141451140340d40001d800c0707605080e000a4203c03600c0300604610709902c0580b5004150f080140003003502d1000c40030003c414200d292440c0917000d01c50041ca00f070031034002410204007111006e0400d17180104150004c0c90101011440e0f03e403200c10440710341ca14520360799000c000d110801440070031035020025162540c120700341d6003a45d0007800c40041e030b684110703180342e020080c4010f0b0325604255900544054105520020603000c0800b41c00010400112104008c00c040100d103603506611000940300c130011200c3d0514002d4100e070041000f020300724100c9180d801080d603007120641e6045000604000d042070140803da401c4800c180001182102ca4440b0901c04007180c8800750782c101c03c84905031800c003814003110070a08200d1158203401e2214203011540c020075980d50214003038580202550741c4100032214039002d5802140c00000021f00c980e50480c0c03080701c9500c0b501e02030322140c442386c98520044561503 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 352796591 1250 352795341 352795393
    0x9070309020906060a0314131101080c180f12010b0a14030a061d10090203150421030609090305071b08070e071e08091605060901210e0708 61
    0xb0201000443d1890300e00d000d0b08031803015290014800303030761a01c1e003402c03158151040d00130468000315000412441c3e00400101c07003001c2c40c0068184c1086040803665004040d188080e003500e40c0100019500c0b451504d1004410040c00d02c0781010254030082c0c0207104250806004017020140801c0619030003041082c034000240081c040c130003640c0ca40f04002c1a0103485001e405405090b00f00500b1400c105861903503400c620001415101071040500d0461584980d196941200e41008081460356032414921170a41909201c4c40c14445170440007030501da0001e08036070f03240a50f60300c28980d2110207041800d101d02044003d4003030f05042204550f0312445004600d90109109102440807421642c0e00725141b8105503620012000483d618a02c46000c41400244001c00b08041e5400c10051034500309610b03140a4011410403003c60080d03c9803c9100c2d040c000540300c14001c041d41e004240b00104180e0200700580d9140403025516007000e1303c9141c0e45e40c4900c3c4102e016a0950111848043c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 352797841 1250 352796591 352796599
    0x9021e0c0c060904090b070503090d210b0a090c0521041101050d06210303150311040e10020c060105100201050f07030e031201080609070605120f04020d080c0601050907030902 77
    0x40200050b0b64810b414203500161141c03483c40001d004041c03124060104c50316040d4030707450204c6215181803100b0351040f080061084501c05401d8100401805000c42e8100125009030650080380f0b480d03c0951040000c0b030700e444011000c941c6d1182c041c01c041460700b06120803541d480743c04402c850500307640c044c060f90a001000300080d0300510040802001820022a45a030f4031308001c401d2170542d0300545540d0344d48003105c104150381849025100d8141c41002c007082da055858818008041000f100d001e0361342c07081d00804800c01080001c03003400d5000c500f50740d40c941200c1c146d0344a0000303204d40c901440d541080400c2441c0103000310781c807030071210754a421156190103045024020010030000e03030380410000780034003000003030744079018280350801045103041c090055442d02400340c0c0003004002061100b0b00300c030300202000c10780060b4541c60540064840e030000034102400c40d0700c0200310120000707564810079808205d0341c0c12504219520355840e030310f1810030341c00c0c0e50600000946c0 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 352799091 1250 352797841 352797853
    0x50d06090b0f06090a090c050306091305150711060109090b06030d08130206070210020703030908070b0d0b030f070311010f0305040b06010807030e01060f0f06111902040b04020409021e0c 82
    0x10301d00b440400744c01050700003801003070000d955681607000c0b01c83d241400c5001440c00010440607003402c011058000c2181c0141100c018144d03240d4580b611201d20f81540d800306210042810f0754440d02e28951041c01e620283d0b91070b540e6545111006002c1c5034000c651141c0d800c4009407907450049081c0700040301c591125505c1c0d5a0b00280d004030010303448001c9a10400071700031440540c480e1031326280e030391003145c004054250540c140500714000b642d000700e2150f03010010902420354064103903038000020303841c0030400741c001c000001c0c1410321002c1c0503a035078802c4040000c00e10030040b010a180c5142a00c0d510302010401d0411000e540c401c880c090528107149011030700035481012403d6000210340380008440184070211402d407041503002014043c1c81a9082c4204224500024014047c81c00e01c4080000f40a04c002d869540800c0044040c5c481407074814255200c0e50008400352034002e20455403107480d1030040e402500080b00010040741d0a00407458240710400482d200c1c1c1c04248000d041c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 352800341 1250 352799091 352799119
    0x301150c020109150804050609030405030c04020c0a0f03020a1205130b0c010b060309011a0d0b130807120f02011508100b0a0509040803040218100e040f050d050d06090b 74
    0x5412645000304904001e2044400600d0b03a4600d4900d030700408030303544c4004c00c1e8201410700a20f000405482032125400811040206a03000120100019002e403070168903042104036003030900382004000b60180480000b01010035601051140d40b580c40383d4001e55110311100310440d80c0d0300440d4030400807051651414001800e05002174040245c1003000030031180c552002082c0641c1090351090413907034452500c0d42003c400300c01d002d0300b0400b0640b070040202d0680d4903100c3c0e000d03001030b11040600785460311100501600404540b65150403042103944040c500c0e400400a040368400c00700107519021070b505035000444020320444407000c00400394200b490200c8e81c0181900840198800100070001030b540d10b41d00d034a98440c40c010707021940c807072510740103001c0d1061404082e29100401003040000503000010b08605a528584a00040b56a240b42c0400340c1d078100403025025102e040140b8440c250300030000c00031000c16070780034403e40b41d40c0d2150030142c60032403401d507900c1000340c1c5d410a = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 352801591 1250 352800341 352800347
    0x1052e050909031e0a1112071b1203180531090606030501230c030a020708070b100623160809060c030d15030b04020f0303251502030115 60
    0xd0b801151140a0302e25007111003841400b00c20211038038060070301020405181403a001403204c0c6003464414040e090300488070224424a00c42c4140080c000f02c0d80d410000213810100081c0000340210780025088402c80c0d0801401207010000e8071010282140d50208981c10511100d00302104003001d07000c0050950b410b0810b048030380d4090741c42d11a82d15111440401c0150044c140258090000015144108035010890003440310325040d291081d141802406000c060881c1d40c0406108801600e400392498821824403a00c0780103440c4071100024800f50a40d01c0b000c010480710551101082880c10a461214100e0164802c202c8110305000d2501c1d01c60305800518a00c2c0e10668050745003e00310000541290004c014103003040e40040341c61101c000307151255035107100b0f01d145c003040071614560350405038044c0144024040d00e0165802546070310100155106a00c0c49015040d0000c002d40f07245034841c3c0d100b10180c0f0b034041d402c03600c035080107144e100b200d06a032003030304030a40c541c40d00b00416 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 352802841 1250 352801591 352801609
    0xc020108152205010e04030f030e120d020d0506091302041a040e030307020c0607020d15060e0c090411130303081b040e18070e011701020909010801052e05 68
    0x601100e04481081c0c80c10780c0c0e01c400380d89034800d80c41c20118003002e0544a4500b283e40503040100d1002451041c403004c40e8000340341e9442e518841ca4080340076440001c1e003a06103203c00c04026186003011885261452641e0090682012111810002a90748000f0000d41480541e0721814620b0003610a5016060a8010003c184c040007004640740e00c8500c0030404540300400700c40d900760804010b00800507414040d181100c00110b841e981400d4164001039142d0903150001840c42c500d450b11103240d01e40341c2d08404010818083c07040711520b080c0104200c0340c0d06c20001c09100f985080000034203510030800351601e218905920170102800c5030b41c240c40d03c42380685252090f81110784a403a070800c8890041c0060146506020041d051140d0b0161a0311041c0d2004400c5801c0700f6014000c207400c580351941100d0310340481c080c8920381580e03454024030587c2502d5400c00400c20001c00c2d04001500000e0017485018640000080000c0b0f01c907923800c1502065440012010004210030b1404400c1 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 352804091 1250 352802841 352802851
    0x21806062215030504140610150e03010c0f09061103030126010e010914010c02060a1a06070b0f06060a0219031101230106020309010c060f0e0307030306050f0d030c020108 75
    0xc500c800d641c4641601e07410b002d030409a500002d03115020001000584110307600d28038442e10080440d03003802400703030b001200c49005540c4500905511040014803500250381d44ca40050004c0004000c5414010800f50003800040b01282d1903500020348244207031307030000140ea4904091400c503401d14a40090b010707900881c180300b94002c545201580c040c20f100380c04c1c402d041341c000003e030310020b4a845000c01001403607149141c4d2401c0c210621190300850007030741c0080075400005030313072200c0104844a00310982609030800408105041080808800140a8070100f82e10720301030360701c00d81000000d1080b814170000582041d080760041c0d00c1429110007945219040c241105c6007000f410030700b1207000407000c2e802601c01d424881e00110300090f80034003501007880030310b18081c03102c00040c0c4501520300d0000c200c0c41d680e5602c90004c43e8550f100041226a004c03e89503108014140280600882d0145610920341546038102900c2c1014840906603415110050021580c2c0c00640783c440000301 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 352805341 1250 352804091 352804147
    0x30c020c1002190c03152a17090f07080106051207060207150c080313060b03190206030a060b04120c290d0b040501080307030306120b061311030a020702180606 70
    0x440081c640c0010205202000d6000144481440f2001c000c0e607040800c0b218000b01e0071069002c0c1c0302e23911020740340c540104c800192680e504d5000c4660302d00203641e00c0e8010a40100303040810440c00640051045810440c3e40f042881c640c00e0540c0c0c1c0f524094400c1c1070259024010411071850b4030414030780004c3e00d0742481810ba8509486180380b9034000ca456403003109c60028442c1c100442c900ca87c090b0380d0001e400524013003002c0380b0002111189540040e00c06d07800840010b812681d0342e042440076140b20644152079503520700f120108403a048100300c403148201d081c0170602e040800342c6070000f65126425203803d4040f440707044245902c07100e21304840540f1540ca025040c0c8407030045500810041004590701c108a040007001c40e409030300450b0f004848100f2000200315072101c62a0441012500114141902500e0344000e082207440c540506001000300850020680d010341005070007a81c0e20f940d855031012908c402614120b4540d030307000c0c60038000d081b02041c0005412a00d200350301 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 352806591 1250 352805341 352805363
    0x40f080321150307320f01050f09060d06061116091d070f0f0b03090a0204150f03082a072102090420030a08250b07030c020c100219 58
    0xb001003814031a42e9000320508441e14641d464032841c1c2e5200b00320803c140a20f8507134200b600b100009110000c010980d504100000c61044064210501241c501c4400140038582d684001100f8801070000791007640003145c0105840d03a60350b040425926001c0c0e010a20304403010f828041c0840c02421040325000809280000801c2240c3e010000c031809807000402c040005860070707460601d50801500120b500c1003003881400451000003500030b800383e034100d07000b0485041171b04180700790404541c880308400207004000018030826000401d0344c1300d610354800d504079502c200307a04500e01881403d0801588114401c00a401a610384208048480d5581014100c0c0e10380000300d9080c0b095409903021304002c0704141000641595100c0c100205502070311a1000c9034490300340c10b00500d1405694410990a40030f1048039809101d6003641d0701006414050505110082c001c00c00030f500f8501601c6507002100709031510280826040e01a6801400b1043c0c4001480d40b500ca203035441114884014 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 352807841 1250 352806591 352806631
    0x906040519140105190608120304080d020903030a050a120204080a02010e01031e0e0106090603020904030c0f0602030c2101210c080307150605010c030909020c071a040f080321 77
    0x1380078207402002402810f040c99400e104900c1c08842007071340020100c1d40b040260005400360349050700e40c0650440e00d001d4407005403c82c0c3c0000303889801c4000d03034103000c0000e626180d00c0d0400c005d084442001c0e906c40380d80500640141040f407080780922143c90348002c0c060801584140b00c07080601c20103160105140d283c0b1055100d441c03444640c82c01d981a210244c0d5220440300b44140c10082c15680350034400540f8540115010aa020b4070150401009000d83e070148104403034802041a4004402c5503a854160344488094011250030306d1a101c0c0052220b0082c00e04003040f074181d0729010030000e0312041c40d200310b107502030b0012002c984141c0c00c020000f07092142031000d09030190013203405d0002c81d50020741000403a043d83d081581441064010a40403c1d44081d540b419070741d595100696900c2042c1a003882c1100380da004e03400d50b60f5401d48180c00000040003070702c101c031410300c0c0c41140d03641c071030300907035228001c0c0910681e0402c1094040800c440040131000d8001190714443c2c941840f01d = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 352809091 1250 352807841 352807843
    0x20127022101060617100e0705030c0c07300c1806080d080702070905130201050903010b0411090f010207030803151c0303061d04020102070e070e06070c0509090604051914 75
    0x9076110030042014072071042401841705100d164000c104094420b2290704115280103004c201500c407500b08540400020624051041101c28180c0068115410070f44e40c0d00040130b40200d8805554840d039030341a08a21002c0303080007080040d581c0090216001414241040e070b082c02d0381c10b60401d01984900e00011000020702c00c407440804c680e41c82104616201c80e01078502851580514101d901d040c040101c00c4001d452001000d95092810541c1d92202400103800b6000d10752115501c80e04c7d0455003854540c1a038002e05000c5010b9845a00d0300c0c20080040e81c42d00d45520016246030010800611080c52891f009046580b008021780a040007402c0d2048004101d0a0110003103a40c3e6881071050050401000d09040d0904500c0d02d0245442d60000b5102c4649224010141c030407900429241401920b08520000d0040e003030580b6220141401c13210701d42544a00c0d4026948240407a000c0d440200e80c0c24403d80e0000c0040c100e44850000502d1680b0b1048020b4607000c40c414503600c0e008030 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 352810341 1250 352809091 352809101
    0x20d0f090606080105070513030f0c18050108070803120103080306210c0a05040902011b0303021603030f0608010504080f0306130f02070b0c210a060306110a020127022101 75
    0x8010364001491500344036083c0d003103036805003802007403290610028111090030500d00d030a0b00d40c4180428042d42041c030701103034503081e40d8100750400607041820420000556210754100c6421134101d501e256620036083e502c912800b0140c80c0c10303c3c003800051004c81c445c80003e50f0403a00203064103101e60304983e007101c4041404020070000d40c001c0c00b03c01d4920324008180e903014120450b020824000141d0002e440c0310317040d2854608030038420103c0d400b4540680c0c181c826080d601c85c40c241c00c02c2402d140082c000c2070161010038070785240004c081000c1c00144280380c8502d070b1107628a0318203030a07210885040d8100802643d0f021112401603000b20a09003d1800314404085c2c0241c0c540a662500004c0f01d8401001720000040c10f00c07046901d94500481c810000c194a00f00b000d03152680f5600c9405065150400381002c1c0c10013101c031158000386030003400d4164a40d4001c10100c544500040d5204841e42c69011000c269001a135001d40b80c9001c150308542e4603480868565984010142d003910 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 352811591 1250 352810341 352810343
    0xc0d0507081e0601051902100e101407050a050c010e0d05120603011a0d0c1502030301061814040506030c13150e13110a0b0706050703060b0703080703020d0f09 70
    0x4041c841404424501140c9910b0140342c1480c00c0b628516110b00000c0c981c1c01a01078008001541d001d00c44011802481a00f5100b104e02409106100c40c40422941d5141d0303072410b003c2d07240c1c038140508650704c4011a2040c01080140d580300e00d8050824001c0360345401c003041401c800d55a4262015500d50104221003949410313803542a150307402e1a00c0c04c03600c900020709150103641481c1d286000c1c0b000f10100d162046078100d0308070f1816241410a012400666003114900110081012a000c0d070000003031750498600307a50f1402d1030b0035483c0c005803e95004e440740c6000790a03003410b40105031400e40c0216622960283c11221445400000206402c8520fa8003000e016a90308105940048e00039102018200c0e010407012070341411101034035803d8882102400c5049440703984111035a80e08031100c010500d00305219114003450621a0040c00d0644060010902c1c01000040940f0181c081e40c8002e40c268540c4403080e91103c42c1036019510010180e181d00d43e03103660394284600c50344240314800e = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 352812841 1250 352811591 352811597
    0x1f0503100b1306110a0222020d140f1b0307080c1603171b09060d2306030712030f12110c10050601320909090604030906050406090e0c0d0507 62
    0x400d143c140050189503011000d92015003180c0d0004025840301d0b030061404281480120786c1c1340726914542c1d402030048840d0484d05a041494016101d034241e41d502c0c0c015003903101d00c45515240c0665081c0120307500b01400540e40c0d418800245454001d010480e0300c03a040c2e10000b03150225201c059210720030b0500049012a0400d00000e1944520940541c1d0110b000052061440302000c80c18145005e0420214800c50000440d0300001ca55500a4141002580c044080b00c000d5100000c0c80d8080807951903010388121580011182c0307840307102c400c81c56003540780d18071800d00004c0304030384210003080b1021109844800000303100c3e0010000304601d603410009005030040e038001d0b45050314000362032641040f0300c000450040700341c111941111301e14480b841049540282e40d076284c0d039020344080c00d03a005c4924400c100d9042e0b8003003100351080e8840e0303072a01182c0c2d80791b850035649405280a404009000e454080c070030130148454803a04601c800d8055820b0074040041941510021103501e800 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 352814091 1250 352812841 352812877
    0x90a06120b12100f0e030405060706020702042307030207030e060d0e250b0406090b0c0c09010f0e1303090501031104050d05030c070b040305060708071b06020405010e1f0503100b 78
    0x190fa0580c4503489407510601e00500461002a02c0e195030703401385000b042e00ca508001088010024640d0468041c00d901030301c18000041001c081c00d0482c05106034002d0111103030000540010b102e0310841e01070560584403244040880310601c40039030405440000721503031310782c030035106150200a2425030700c07a81c1100c0d06220481042881d0103100e1a4042c07405984140030602c10039401110480641d0132a021881d11220700c00c00203481d02402c0a10143c20009440012440072058a051000c0d603950028007500f1382c0b1129405c0280304107041c8060b0001d800b00d80248031a41c400d400c0b107021859503a60325401c0c652603800150b00f141c2840d40403640355100103803042d100c25007444108014030f070050f040b80c00c240c51500e0381900ca00d40100190100200e5100181c0c2a43c060203014038a145151007110018101e407500e1002980309010b00e03800301c0c1c00d80603030403014a80380e0310601140d44401c052617021252941d040ea40c1c0d030400f0709104a914507031240440c044038040301403c00741b502c050312408 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 352815341 1250 352814091 352814113
    0xd2a0f020d110f010306081507120203070504030209060609010c02060306030a061a0a060c050601030809011e03090b0a020403050a11010e060c060114060f1c0e0a050a02090c090a06120b12 82
    0x7150901200f0f60505142c1040340c02c02004002042d40d24207440185458075456858410441c2c6150b5466610010244040180710010f54001c0150095902c00d0721412515100c000c2000028090a080036000a482d00d41c2c082c014140907001d0350300418003400b103803002d00c019542c40d130507a89a0005c2c940c1066000f610701380546800540f0030000c00d40c605103e01074040a80300c064650a05001c0a8600032000032107002991051380800501c1c0c2880e243c00824905481c0024080d0105d4101601e1401801001c10056901c0d44201e030200da6003c80101051812545c1c0c02005034440702c2814140226100c0190054440da802440440012800f2b06040e42c10282c0d1030303100d400103414080c0a24002c5c072110070790542c0141210181241005d03076090b85115030110501600d01a850300c071960095441d80e104100300000d445900900c21158041030361303140c08004a880c09200d081c81e904c605008c00c100085802541d900c07000042c0940003255040c08180032410074109509888110b5120f00741c565 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 352816591 1250 352815341 352815349
    0x114060f090708070804020d08070b100501030c0e011103040e01080304080d0810090b0a170f011107020102030304020603070903020a03120f080702120d0608060106020a050d2a0f020d11 81
    0x24010404072498550381c10940b000400c8400c0090415092100710030119040d541c0f038160544605600070103040d610079503450019030a900a80d841214a40200f2020500b58068041c000c00c50626695501d4500186c8004480c8a403040c00360b04828081040003051440517400c0d0343e0b000c4c0103541e000315659803038400034510341410040b580080107810018041d06c510b08008040031a82c649501052004015000404902180d0711a910002d0342c002e660510321f00102d00e0442d82400c0390000c010101c0b41d12050740c82881102d0009006070400c1001800602d8074001440c0c100c0d000b403414110084d103d90128006040300c0c0c00a80342450f02c0174000f2145940b000611003008090314002c3d0041c10a043e000e9070b15071150020040410001c0f81e40440154164006e800800e5031000321026569a840041c3d1640c10300b0a00381c40701c2c002c09408030700f100c4c069000341554a40c001a403504008032007007001e144080050b003c8691350b482a1040740941c1c0c403a00d0801e15540188000164505024200 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 352817841 1250 352816591 352816609
    0x109020c0d090b030f06030c1806010905060313061509060902030f240f040b04020318160f1203030e0a06050106090807061e0c0f0506070f03020408030901030b12011406 74
    0xe070100702181c441403004400d80e4040e00d400121011010040e84c03a00310029040007841060150000340300780258020701e5045c2c082a001c0c2200382c9401508607211020712546e44004c40e07501844c0342d101c030700d03000008034550722002000004800f4400001c7c2c441d0712240a4440560002c05a02c1c1c001c0188600410704508142e0400100480a81380000250a902080da0071034601c6200745449480a08142c60b1074024900200c1c00a00441d41d80c41c0103d5098a003400c100348100051040301800c04240c50544010019950f60307040c2c60003054541008a242002d091808404054072028000d400d0801004250072045c440c45c00170441390304001c00104003108603070000c02d0b1507003c10004c000382c541110035440071014250881e138105090f00c00550707240d00e00d650010100f608020862051200206849003e040300f075640540c0441a50400c4003070380078038022501c1c150000c001d02909580203501110390100701911402c51b82e41b0003041c3e6400c4444142c0e85444002201040000a2034400c041e = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 352819091 1250 352817841 352817863
    0x1c0c030c03120206060a0302130506011b06050115030207031220040303120506030c1005090609060309100506030c210f0d0908010b0d0803010326030403030c02191101180902030109020c 81
    0xd03c221447c5400043c8040b26010414054603641c1000c148164130800c0d02a0072409070740701c6281014000d2030035a008103c24862400f80c2040d5008001c0305500c60b000300d034000b54059035241c0341071460704c8a440003801d1401010042c0c01006003418401000c12001e8001035009441d404c580e803000c403071040b003074800c000e060912a03040360902c0106039440300054510310b540c03454119240c078490030202c0c0c50b6208000f038541c2d02000c040f08101e610040010005208000c61205200c940c50381418107a40e0504041c0240d44441c600d081c840001020307a81d4904003c078528100c41d05180c05640b0300e401d1007032180c08040040c0c5441030130702040c1001d0081018010b402c0d0ba0071045a40355854001c0580410b00004003024140003032148840c40c0c0c0304490b005001041181940ca06161070090000c15014180c5005805001344440c101c000201409a00310380104175195040101d100455240d6031803400600c2c4120512004100303019a813016602902d116a00140d64900b400d24013440e03d208040e07 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 352820341 1250 352819091 352819099
    0x13060f23010f0b0c030408070906181e020c1f06080c010512010504020901050f0c0313051206070806060408060405030c07300c03020d15050a06051c0c030c0312020606 73
    0x401003041c406200ba60394102c80060110640b165042e0061130f00b10b1085502401c00f40c8900c2a0200304000b81746c1c045021540f076407424040a521501c910b10695050a590a004140564500c09122242e400030701c0c00340c41c0481031b90701c1e00c81080105150210b411000000d401c0da030b10b0003808000750030030401034554001d080090030b2400f12903849141a130140906802150045a40b0b1a103034003c100307542c500c6110f4010381d51900000d01e60b2075981d4000822411200b4002c49002032141003000948484044000c0580662344e20140c0c1514030038800303402190041004c020008010f8024000f85010324480c9001d143d0358804240c90034130703004568001c803001042d5442c400c04030b80101360201e071280680702d808840e01071207400c1c807031070011b510f40c00030b0341000080d00030328100186503400b6401d621081004011640f01e4440d00c8085503003a001303080e00000c0e080e844001c070700c14000f1440c3c0708030710070310165031250340302da030f4442d240e1000307074412540e0350f841001d0383c590745406000309a404a8183c2d = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 352821591 1250 352820341 352820411
    0x1050a0218040921030b01090f050d0b061908150f071d04090b1f08010501050d020409080f07050a1103060f040803070e060f04051f080f13060f 63
    0x4000050250320a80c2020310a690303460103003080101c51181c00e8413000b549650400802c0840c2c0c0301802a02504014900260b440782020030034050014410701030b07480c080c0c03284090368803650710b9656034003003e00b4030b0358800305070014521000b1003440301d04050311048000d82002c0c5201180c40300400c6010f0210441c6401000030041400d50000c4511809507182039941e003880410781c041801000c3c104006021030030440c080004800e111034200082d201b00c48001e44566503511036013422032703070f003801600d9109003030381c2124004d49002e80007403149501907542546440710b44c0d12f2081e075586c080c540c00c4509402640b00c035000e0040044044007400c40a40181a45103040b4034480196200104001c00e80100480450103003841818103904442014200d140c1e104500070021050740c02c50b10036188555865041500402d400140011741c000c5991640da0035920740c501062030758200201441407005c4079180144c04a0464002c000100316010300009203810344d41c007414594174940042403c1d4040e81 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 352822841 1250 352821591 352821607
    0x10311040e07080417041410110318010908010c031e0b09010501140903060106020303181c05090607080f0301090609020313150608150106020601170706030b0d0605040b040501050a02 80
    0x8148426485410b0349402c103041c0d83ca620b444a00f00900d074071010044007022402150f2400210044800101c0840350104a8131007154204d0b011000342c054078403aa042400654400012102400e03608001414032086003512401c4035802c40d2038100d0b8100000c0d4450301d00c0725403c40320142c0442000383c0498184410440d00d00803481c1400c041c840c4904101c01d2001411710281c200c0183d60f50398038001c00381c441e6546d4a0704000e541c1c7c1c20648a10005000804c0b8084d803090b00003035074400b102981880310740ca580310010b0940e8a6008544103541000003000410000740e28400102101c0c1d651014113901c039410500c02c141100c07001d0300b02401507403040051041c039043c6041000c40007503018800140c00070302d0700c58080181c505a488130106100d510105804500a06c260300d050b14100d5086416907a620446002c0c000c26088095510303803c11402480442e120390043e9004044c0641900700703160b103543d140030844400301c4040d1101d0740d1000500c801c0020a01503a900600788000a600704212 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 352824091 1250 352822841 352822859
    0xa05100903020f0604051c02010305130f0215190507031b0503090909070b0a08060f030706050a050a031407030207120305060a0b0d1107080d1b200106030c090b01031104 74
    0x502000e40714800c41404403c9541d00c000407500605000f400414640c00d400218034841400284100d0210b400c2500055007003043e004080009034000c2912002100c1c103400303002c296182c2001e09582d842d0108408042c04d10105502814000c065840560381c00c85030034010040c100340c07980621121441d0f40f00ea001703d20000f040e20001942110128181d44685d800c0615105c0303039910104040201080310381140c0c0d001442e1a2080310190361401c0184085410151524518011100801c1c800c0c001c170402144075001601030702019060008200515400c40d80344004201c0706440040e0700050003002b0001a0803600d417400b112810184040d0a20b000080c002030454004e4800038000460081c0c0c41100c250460301102e031642c0c0032a0350b81c20082c03c1488032030707010070039100c1001d0802616250b64130842c0180500d61404e42c1c1d9039400e92040b5501c902035500301140000141d92508000700100301503a9401d0014902d03000700103890f068040c005415241041162800504140010808814 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 352825341 1250 352824091 352824107
    0x30b01060e040f2306120618010209041107021906050a0507051c030605100c110f220507021b1003090c091802041b0c020108190212060a0510 62
    0x50a05016040001c20720206004124070b05000e403620f4280030300006811100310950701c5105100e0310000040c0d950209024502c8408140d042c900c4e88081c0004008086903c0307540e04008958001616006041000401f990f5100e1481c0d560440001202821442c2540c15602400e580000c41180103141002c090014003030744400c1020300800280020812500b400402112240c90145e2600c803c9940ca00400030007990203001c0c0940c800122a01c4030f18000c40c2c080400f5540884c200c0c0030300404000740b04072050013200c16908102c1c18440610200400101d8414500c40c030500000c5903c0c003450000d1500b4030025100e4a80004c00480900343d8950030b0400080070b0f03403410041031001c501d00e401b681c09109a80703d42d1240d450326086000c0c140090590100301170003202c05210018441d5401c07030329640901035420205408506e07402c0154002c0c00301650044200702030306442c10590300082c0a0368807410384601984030359001c210192520b02a03140c05840b054030581c0901100d11000780800d0 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 352826591 1250 352825341 352825349
    0x2a0306020423210a050f0309031204150e120604030201090204050a1802061b030d0c1409060318280b15060d1505150702041a2b02040e06040b0a0204030b01 68
    0xf101104020071a4041219420711540036045030716068410f00c0d1a0349a811110209119015644440040c409205c080d01c003035a00c4003090300380101e2264016a02030700340060030380d0001104061092020828130060340310301d000e03400209000503180f0412017120350003045640503600e05095010452520708c1c080b010642e040c0c1c1c1e165034960450030309002d0b2503003a01401d4131901c00000c000801318005d401c41b00d01c0c10340075107030131400c1500710680c0e481d980a44107020307400c03001c207200098640e0901d080c0c0d080c2955442003550805207003c210040d42c030004d42605280c0c60361030751422042000240c41f4540c80001a200030f04d1092010000035114452200a50020707901e8800b4018910070315101c80e8028000148400105648111103513096084070006030310407407400108148046c0001b0030324100758001085a4141500c0c4031031420b02c405d0b000200c4c507843e1103003a0b4100043c1c5540c415840c0e204407800040c1050720b49403604c1940c101c1b000f407000302401e005100410000c0d0510074280d05407 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 352827841 1250 352826591 352826629
    0x15020127210207090e0102070b07020a03090e070806040b0f0303040603091502030c07120207051f021005010b09060d0f020f04030b07031e0c0210090c050307080a0209042a0306020423 80
    0xf405ca0140701d01900403100050015540c1c0801c6c00500b80d00003504103103892103501d0b2001c005941b00c5403500106003c035008000714401c03200242d49483c00d076010140c50680203120400390144030700424907541258001d040800c0d40c9810b4241440002001d600078401c044109601d0340c5841e502c0c0300c60600441000612a0030046990b4114074000d0042d1405410041c110785e00440c0b1700f50b06c030902521400705020160151605003104403600f40521816240c5558440c0d2030030440c0c01c180032480c0e0045008250203966401e60100c1c2d8847c600007003c8009003040c14030b4179181941801880c0542c0a04190181031a107580d65541c44000c0e0142d05080d40100d0000601d60b82804c3c003030b810400f000301c801054501e07104640e401c1001d13000f041400d07104158112204d903501c0703032511982c481480d00007944c4582c88800041c0041c0d00c05003011080a034001c0c04588102155403502840c00d00d98000b203400720340101e0305000c00700808103074a0b440c120b2100c0a03281070010b0000f007916840c0d1440341d4644 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 352829091 1250 352827841 352827851
    0x50c0706091a09030d06081c11120304050102070308070203030f010513090b0915070e03210708070317060913021e19030c0b0c071502012721020709 65
    0x34808901011036400c2aa00d808002510707103e42215240d9004441940400d4a014808101031030002544103160902040345020708844000940781e07000d40714400c0813644178107118201040c03464800383d070043d4422400035032100258603000d003403924000c254100319030040c405c00008001d1500300c641141d85c280c0300d03200030b40302100c024409041624000b0b4912103d190900c98071b20710004903060106450709444201c1d440c1c0080443d203c00140740d040e54107520440011110084928190a039004142002031500d52642c1d92140c480e0000b260075408940c15842c2280d4071902004825031241c07040f42c1048031031410107650300c0346c8100100040d019000d1400050031040000c40010544100144001030309040c034503098002c00c10034041200c0302031407102c002405036000019181c5854075032001c0c00e5100d0030f14000450180d0f030381e00064210340d2201241da4443c00350f003620b001070303440c0d110896941d10028205440700394441600c0d000c0210391032804140c0305070b0115101e02036a0310054080f038 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 352830341 1250 352829091 352829093
    0x30d020c0102160b060f01030c0c030503100e0f070219020616260705010b040b030601150519030b01181401031503050f0f1501050d140102130f090f050c070609 70
    0x802801500010400d0070101503800042c484440090b9109460031240104940c511b60011400d964402d090071300814040d4000d03000090090020b10f41c48181b07090112030941d030344da814003100d40040d0740101b91140924284807800e5818801c10112469019424906141c242d02054642c428000c04076118000c150089040140400c200c0c030805002c0201081750282e405580401a80120011a029807a00c003a2003500d040600401c5034410000b409803003076a29000000510804014820081042c10001c800b0000f11010700401c4040c00c9642c009030701d41c403080014120550541440c0c3c0c42121030784e810002240c0911500d54810420700e408120031103088041c86003250981c0008049001e401410349d54a20006424156103414a0884581a04845901d030200d0804e001b0f890700000e00c428154045000d001c1109180c8400e40c0c0011320b131110350000741450313200701e40240820280d45c032802c00c403c1e01940500081d5541c0c0072004c100c0e504283c1f8240f5103500c640c40005050949610440c4 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 352831591 1250 352830341 352830343
    0x14030304030204021803010608010608250b07050a0803040602040f240e0621072c06032d1603062603040b0403063903270b01030203100c02030d020c 65
    0x1203800c0c05c029009009050700d65100714060040350040500d54480c038a424100e0744128110500402c002035450782490b414034001c101e07680d1006009544c3c3e80b040c000d48500041d1050000e62140740143c00058503a0309041d0446888515035220204110315055661841c2c1c07031541a10640c5c03042c6050100c440903001011400601808140480c0d0819502c1ca040d0320992426110703106590641e180c400c0c001d103410b08030b4000a0041214507048608600a103101d003480801160001911468071010041402c181c0b07043c20840340740c028900002c0380c28080702105246182c0e00d22581403c2c00d00402c0c0c10007142000f00d48002e010381990501e070801407260341905004030f41c0900404184682d4075500c905080d400351061400b07c002007800340603500c251000152894030545d404000c0c10188204010049015068030072103040c104502d40001c904050b409020f441105114401143e429031441c01010304046280203880388260600b561403649540c00f2040f18002600b5000060f1103040c601c01003 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 352832841 1250 352831591 352831627
    0x405031e01180c0e060301020f180a0306020417010501050f010f210e030c060a02040f030818100908060619060503070c050610090c0c0b0c07021224011403030403020402 74
    0x30101c1d080c1d40b9040a0040b42e507490b03001d49058425510b003e0320380b081854200e10503140c80f80b0410300706002940012400010038200814010b109240c980d45a0329040c08a9110764089404d0140848490b22404428050140103100407607031801c032001b081002130084404410044104455540e80c00f43c01a0180b02e02c20448103244420400c0802c03d054007079aa51050011107600e1281e1800211112002d0084800740d450300c03100005454a5075841010503002090070007800845c00410325420b88665008010b0a00d02e6601c0041941c9070002150520354090022801506c10113090240c2c0d40503008142c0031511140341003a41c0750b882420445018a00d06c0b401450343c041c1005000384007001404003c2a25613202041018803d821015140400c00d840010018080031001441804c205405084103600280c185182c1c40071584078141004062071030b030400440116902604e44030000303492030240c48004c191010001580c0d0000766240210f1200910442c0c0000788981808010b40003 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 352834091 1250 352832841 352832861
    0x403150908040530030304031e020a060b01050c0a05010615050421020d15051608070915020a0c090203100506040b0d02160204150305010f06050604230d0803100b0405031e01 76
    0x4e03484103c01100300c2c0d591a40d0083d50141c00040c11080f8007403425098420a4040740041e80003040700c0605952044090180741d21002c1c103224040c0078001223420144911905244141d000240040c144846405400440d41c10102040002e001c20300c003080140000329402e1580001400c1f01004500c00541250540301004140c2101c40d821031604800780d0304050301648444144142e00606248125660340f0110f81c0c250000b14041d07000c001c0c401c480d001d949200d6a29105807600e15190303884d11320300d2640d50350050030301507800000c200c407a46843e400d410103800704482c403900c0c0600c3c10910340704034002d40701030300700580d800221018a90800040c80c0540c543c09001440800020b8940c524114481c0c4800c2e034280d428200300d03c0284005114400544071b009002da81001c0c01c00f032860480c0260098501c1c00f0080e4004080c000395660707540c0f0540c0c1885035190310350b41d25040410a1807819141d00c00f94241c0400e200070b000d03a85c0e021a9002d4400d603c0e018902c3e00b11070b00c400e42400344c070603c89 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 352835341 1250 352834091 352834159
    0x10050405241909051509190506010f0f050102070b0325020309040515010912021302130311032a030a02100f03050915040201050f1e04031509080405 65
    0x8080c4601450700e410710710981d1160702d001800249040040103030303030784020014000e4001103001c0d41e66503c40e2022031307001420314003290188900413504105040e0f56240c207555950000004110154204800202400c01c006150b80c540f460000041d5442c8407900503000c54220100c0041c0180e1440c20404480000c1c44811580490000c0000fa40700d0b8060a001c5000303504100000b082682c1c030036091050584103945000c1507510308592860410420305080741e00c02050f2072040c2a0803c2400600000500030b0301c0414818030b545004220b032042060300e06c0c02900110780c0d41402501070a86003200040102c0048907940070900020b0171b10051020007944001c8201d0b1000c00658815416080d411030790300c1c01c000b15140c040995540b804889690400c40114500083c0154442c5018040342040e0005180c10150700704041e0081628182802c0c5120601140030000d11007144841d00c507950b00744604024025035a200e4281074800ca01455004510a0241040155160300e00d0580c00641032 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 352836591 1250 352835341 352835383
    0x5031c180605070506150603060d020f0603090618070303050a0c061508100b03060c0702011103160f030807030203130210051201090e0705010908030327060403120c020f10050405 78
    0x82009850b40e00306240c10740b124400d1200059440da605e40ca04204100020070017030865840303108016890050340012a0440350111728003125445050240d40201c0c068006080d83d40380004410201e421201a4001ca0364040d01d410800300c4e8003c000c6030509501d500d010000c41509041c080041c2000c210003158020f40004001036100d40821400c205108855041c80141c100004141d0b58820035982444043c80030043c00005600400781e028000586a00707680c00d14081d28412000151010380030303501c40020100710005c240e4411f0905503c986d1b03030705045082d0304181000134801a00400f009006902808c500380d1401c0c01242619120340d444408500d156031a000460060080c51441002510500c0d002142540c00b484821013591000320046040d903075204916030b9030401c85922441c2602c9000c200010100302405420b10075400703901d07000b140120032a002011907106400341011074210401041401802150544100e82404800b042503255401d00a04140c00b400d4205480c42c100 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 352837841 1250 352836591 352836599
    0x7050a3905071701060315050709030b01030302010c0825080711010f02040f061e0e0d060f0c0f030501050315151c0605060901030206070f0c0312030e120405031c18 72
    0x10311070155200050003805001440d10010b080e1740507400010142d03809522550360302039065001c0d661043c00351a003226800d90320740b02c8201c00034081e0401d8005035110072104503503503040b18986411402c842c4000c00d15680707110000034541c800800706ca080140700c1c3c000c218201d1042401d80c48114142e0b008225083c00c44014000035030151140c0c4a00400022001801c540100100445a141c04400000c0344203006800c540d0085070076051603011500c1000200411040d224540e4102000040040d15425084000c1e00001e5514020b40030107081000501007604c0100d14015200d91000040b0440d2301d42d07415450301001641d040940007441c641c802040c0c4004a6030544031a4050034007040503032a0701080c00020802400043d4100401b00175507000242c899065200c41400f8401e85002a5200d075141c00c1c00d41c0fa015800e00c002501d80d0301c0d00d401c50109200c4840c61a0102c0c0035146007504c1c0001198484034040e180c44403d0f50300980700800d1078096402c400300c07445d59002e410501629 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 352839091 1250 352837841 352837843
    0x60504030201140106170a050c120c0c0109030801060e030708071401111516050324030a0b0a05010504150e060103022209090b09030c0c0618040e07030203010507050a3905 75
    0x1003032004121180e80100c7c80c4038499110f010f000754030030b0f14490328210040398001c01c0c06c007000d00708046054041048265400080c420307000018800c1c0c1c0c524100754036042004040d01c3e5804000c510a420608007001035690011300c1c00115001c050601c0700d5030034894016188140c0c01580c0502d2030085030030681c034081614006920a01d58601c2440269148040407617190104a404000490342e140d08071703007419981140641ea11000404507001d283c4640d8070145003080980354a0362040d12900140f0592409005002d00c0c5010078485081c6540b40801790030391301602425580c145540020001c024190a002d0081d1041c03440e400485184e1350b40034080020b00c509071060715024065008200d5540c400320480312641c507068001c00c04d44801e00100b00c169400740780c00b49007039900e983e401e0034036807078a000300303840d41c080180640900340c9180140340c20340308001d102c0c000300301042000601d42d68000041c1080541d800040c5000c40340c009a0601e4200e400e20109003680e6142e401e92010004 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 352840341 1250 352839091 352839107
    0x6010c0c080a0215040602070513020706140a0e1f050c04050d0b0a1503050309130b041817030f0406091106070516140d080c10150905010f050904060504030201140106 73
    0x4404e550f840c0d20441c403070b032181c4498050382c011800140c01907441013100740f4206c41134900340d03451800010310b002142e40c3c85600322030103400715414440d911000c0140d455000d1003090f15241500c070280c860741e292404113604010851285111081c0c0c0c51000c81c8440504000f603402401c0b015042c0014100c00781040900b042c41200e401880c0340c1081c18440c03000c0140b0220800700c1c1c0c2d001c002581001c03806410001c44540b000341848000d0b580e2201c2502a03580e6019040c1c1c4000c0c0f407141011b540b0500c1c1007001440280e014910100402001804a0029004c452960007500050001414031042c40e0003d600c64078040d22550000c004a00c14041c41004a81e09404000e1590180714a960700c90035030307101e00d501c00c150540c8010380001d8400482e4030f2000610b40204003c0c242c5040507072100c50340003222050880f020301c004a515041c4005256482620b014000505464003c2c034946000034540b4039004000800f100d0300c503004181018001d4200c3c11151080c2d250b0310b00b4541e1a84c0009044030 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 352841591 1250 352840341 352840343
    0x304050304030f2409020d151514090a0c050a20030307030614010206071d1c0507030c06030506030d0302160b0114041113211202030d0e010e0c0906010c0c080a 70
    0x1030419103005641300054401e103540c0d15030180c4a200c100e042a10344050700130140246a6242d51150317050040c00880010b824082c090040d4180480320700c0c9010306c40d84100080044500302e1410300f410308000d80002c02d56860021b5460851808030031155410401e440c81c491007102c0340f1000c418080c450390950000f60580d0381700390072005084180d600481c0c0d550300c296082004a026a8076203004001007084110465002401c0c0d40d0204661400f00651201124000e03120f0b508006030620400880c02c5040c001081140b80500150400e400000c0e1600c0001201c1000d01d580051400200c44851082c5558203400401c0340c8030715079480c40001d031803c1440ea4518402c07481c2c840a0100c00c9094003c0c1c0c1c20010002c496004414185800c200d41c100d4a4003450b44803c140b44074040018031003962000d44c14403203a01554a403092101e070b100c29181c0d58140c000c0e1503418240298081c03000069407515140342141c1409a503102c400041c2c0705000b203e100903102303d1200c1c20114010200061608100d = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 352842841 1250 352841591 352841633
    0x607230c010f0215040b0907120b070215071215050301020307120513080702060903010e0307080901080609040506160e04020f120f040206070f031407121107080d050304050304030f 79
    0x100da800d42c01c0781c844282404420b40e84403c10045001301e640045041d074880d6003070f0100c80140b170325a0300c07070b2014000c00042100c4031500c0201b0000b0b9942d051000c2d4800e1003409003110707102d0900c2c500181210b080c902d50340144a5880c0355190107801d020030b00358010180a80219943d04004500400107400c21941f003250340e06090101c4c502c5e1000707a9420b44000d03003010380360342015801d90800c0207650124400550640d250780c5004104403090008003031040c4a5003050740d95900301c00c000b509100008240a01c41d0b0340c04410172010550110301c0513400380c1c0e13070f0040e08001c015894080d211120b4a8a140d504203101242e64104110b04400415419a41c02c011040590f124601d140c0c482e4000c881c020340009080c08913100007090000e5082600e4840d052100054071140100129034101c4982901c0d0303e4040804840043e03009440b0390011540c01010b0031001d41048616542c0740e1700801c00c0010801c0010014080c4007040c0141c401846d40040f0380c48560480f41445042c20203091811089 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 352844091 1250 352842841 352842857
    0x1d04020d0c03051e0d0509061b150103050c040204050105030a0c0c080f0a030b060405060708130302130b1305071d010c020402030903280804060c11010903120c030207020f0607230c01 80
    0x50070400554405c00d1155940d41a141c10404c03428031601ea04188040341344034100407400c19041a042c4840c41141115058032581c82d855800c005180c052070740107981c0520720400003030026903070110032250f011841c8080842e5000715100100c0c0c40c1320001c41d000d041d0303040100e8024603543d811001850b809800c1d80e814030141c0b0340c02c4100a46440355100d016441942000814000341810700a800c0079004c1d80951a1810764903004104480c1d5404d8526030380a5840b01154101d181901d0310b0105111064002c0069261018000d80221b011948a05002900452a1030568071401aa100c05540a0010364580c04c03c000300640c0c13600240413824004403081c8040031030080034262214031050540d0b030110107441d00c0d2a139500410004c07407001c04014070304035070b04400d40c4240168034003544a43d07548541d0304030a1100384212482e11040b40105401088401c025907180486a12282001c4808903903d011a24088443c69107a1000a0b01c14044140480f07d144021845508480c801e880f501c0c0707 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 352845341 1250 352844091 352844143
    0x8130801060b0403031404120309150513090e01090f15110f0f13150206040201020d090b041412101b0801180e0c040f1d06011d04020d0c0305 62
    0x300365480d80c019002000360600040000ca4855007403541e040100b402c03454076203901e61a40304220241540301b40c010827050601000180170f01d90030060180d00b076180c585e0501c0e6410a015030041303140d105a00489407111111b4405074000c1d8820b07184658481c105c40040a00c03450b16080c0c0c810403201c690700c11442c0240c2d040c004a510800c407091182c80e84e0031203103000c59108082920b50021280440d40c0e82d40e0300f2000ca000c610b00504c404400e442500141900d241600c00240341c50050342c03490b020001201c030100a810302c0700059400781d90f44680c04c0509001240c005c80c43d940100c180d002214480c4440980039a0b60030350022141c8076440f08805c012a48072441650115028419404485099905240e9501441c0c1c40301c001e031510042030f113140c100400e00040a84640049402a0320365803025800006403400b070054005078983c0c050328080d89001031080341c241040707502100f8408000000b034219511303030901850082d13200e41151625034507402e2581d601c0070030b0346180200c0200e0012441c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 352846591 1250 352845341 352845343
    0x11b0c0b0d0e1018030c1a072d09060c060209180403020106080a08030106030506180106120e0d0c0807030e0301020304060603050d020a0b070f0201020c07060809330402030a0f081308 80
    0xb2081c041000950305130550341102c01a4500005655140001040301d50050740031540b14054081e60f510461211829a1010165460795110007840083c0818480015400444a000f04c840740d091003548c0f4030700b5091200c003a10640314081e500030001c0810802d50058014114001c0d80264002c120150702e070802c19036118409a0082c204030000d00040110340c0c440d400156201c1005005a135088410849599459000f81c0060001c14032182d64941a03501c1072040444480201c401409009030078440a0400d4040300c8000d064204000380480038903020f01c070038514883e000350085507a894681442002030034540011600360180800c2644e00920000d001401f490700031010724007603102c855050ba546a080b80318030007503540a100500320120305000c030f00010006511840200c1c03800400c8242003089030390480c00203e0400301d1090215a04940002200851641d10020f41d00c6900000b1b103041d086050061030074950300c038040104a50740001d004505440d00099031015294101a = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 352847841 1250 352846591 352846601
    0xc16030c0902130f240f05070b06030f010527030403020d061125030e04050907090c0c021f090f031505040602220306050606090f040f0e070f060906050306011b0c0b0d0e10 75
    0x26a0006a0501c88c0c6070204401469054100300300030200c0c0e261000741d0b15041c3c02e60b0001c80d41d00c21918440d1940028a118894600c60008030001c051032034a81150f00041c90f4a040710f101400903642c4003c2e480c000c2d002c00d030844426824000c44d484000507100c0781c2c100b040c002e4680c12070000719407c01742d00c0242090b0140303a000b0480b450103040c070107051400c140c0090101000c0e0b0000c2000c840b0503500542c41c1c25080c12444c0c102e1081c200560189504054074242c041e84c4002c1400e880c658040001c1a0219005072840700140030204403070f1101d08021001c1e000e083c0541d03030003150f00b8058601c0d81c05078541c00c0c82101c1c4124418030036551010708016240c000d4008054010190143c01d02d0b291030507034454031811200301c41c00541d0b00d0400e04003030725200c0c0681048203200c42080c8140300b00ba4100c401d01c0028216460400d103503281c6140020710a042c0c2441c4010110440d0424504210088904070b020301441403845448514030380c3c4441c042c0003a110b100140e4020050b89d6104568039001d0 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 352849091 1250 352847841 352847867
    0x1060509070c030e19080714060c0706180e07020303190605060403020409020612070203183a06180c0503070602150c0c03040603020c16030c0902130f24 67
    0x505000c0041e6843c182c82c42a99610030a5100340c0d100d07511441c4240d18006000030301441001800700c181041c1d01c50f4451010347c0c045c20f110307001c14003140031205400213245080d41c42030710300302150f500011025034a801464019a007081c503814108522168004040c500c078410f54440c01010540f8416500308031429030003082e4001b88200000d0015062030f80190022620160007203141101420401069010984a40005820020b01044109103409280304041002ca81c0528070113200c0421055496030768001c61403044004201c0400341d80d07001019044107401000c24800202c16030b60310b0f5400040d11000301c80c10401c01c540858141000103022095a07035a80081410032000e6540300b0801e41c005101544500041008803c4135806102a2004064588002d0f0320b5190700381520341000810f012281200e0300042c0104081403149a19034110b4501d540d00607540c82802c14140b1010807250014074140100c2c000001c0d080c4101080003501c0f0721115020b6010704101d8904807030745490850 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 352850341 1250 352849091 352849097
    0x2030717040203210c0f07050a0e16030b060705060411010908010509030d02030606070f0c0f0504021207030b031005041101020d080c1c06081509070b04050904200a0f080106050907 79
    0x11540150541354440d40c41e0601c0303007401c42801c000e0450081440d00000a01504403a0400f036010007080c2445001403018009600d014203141c58038000d07610401c80d80340200820180c43d44480c2c00b4039180d030802c07145126000000e4034000e1915040072580e902c0781c0d1028900048060f10700007984081842014065001d000c0990714005010f207040011303401c0544000d42c4900100b0004001400c0b4040d0185070611400302d41ea02c491414242001c0038000e540903901481c010000d0b2001080a5081140c3c050310900b000190150104007007440e10881c0701c0d904a40c03d251800380003d01400401e0038801e10402d80c22203054a0020300300712034509050311850140c01c001e1288400441207042c40c0e5800030b5100c0300010f040d039602c07e0090b2400c50128018a03800d9000c50500540200a220042c00b80900701041841c291510001c0380c0d0802c0300900182401500324034108840200d071004010009001386040b035050384803102d040340700d00584200c260f19842c100d40041d89003021081030340300710860380b = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 352851591 1250 352850341 352850353
    0x2131a0918090f0a050609071d1612090302010b0f0105160b0604090c0b0703030b0a18090f060e0615091303050307140409061403191b0803030a02030717040203 70
    0x21100c80341000251801e4614050f09610801006007040000410380c040c1005001c1c6e801d00725149400c0c9904d43d040036560500c0120418209410511040d820166441002021981400c41120b10031301c0000c40417001400c1c0b020040a040e8150003010f1007105c100d1f280c4a4810900d030040d04c1610801d40101c220440c9020044040341215000030b80c491806000130804800542c5d8002c400398141d088804a9040482c6801c01d05d641441078006003681a19181011400c1000d40d910b181180d108104407540c0710424501000060048880044d178004014080006030800540d02da00e41114140c3c40161348840e820070a2520f9030b136080c010740c00550070240f06081c0307440490f01c40e400140a80c090040c105a40c0b0340c03c14594008000a05507a840058800d05111100c03100a002480791071081d40209050030010321809403c200840c0c0c0020222030b04030404100803112200b95200c0002400040f0030026505019001148550560b030b8941080c1003001e444505a21020758011b50154010 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 352852841 1250 352851591 352851619
    0x90a050f091801091b0311090f060d11061201030b10150c02030c0a17011113050609030a0605071d0409050c0405060414040f0b06030703052107020402131a09 69
    0x300302d0044000004a0020501c0145130b16803024500d5844c030a10340c42410f00c1e80800600c950031200101600b82101d88903c02e040c40d03415000c3c420400380015200c1c03080007104508101401590401120000d0000c54030f40c07810005403c234204d402d11003a0350104c20300c00080d402030b061000341030541d00f807240b03200088442080112a4484144400c0fa0144540050304525a64000a40c001000b050002e5405265200110fa0a40d1090030605030b029130280501611a00f420303140009980741600c1043e00e55a480e80081c0c6050030303041020384030510704800d10103181c0d84103940460324080080c00308441507101c0b06200c11294109006042500300b110505902c0c50150040c03038200e400180302180c0d444038030740707898242002940d04407070100d800c4055004001c00311a8160303006004401900204e4a1030716590349031009940c080f2141c40480c0d58410080b04050240c903c2c854000d00215196020120050b01d04010b82c01020000c1a10351610203c40030484202d8440f1103000d071201c0c840c5d20007 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 352854091 1250 352852841 352852861
    0x6070f06091a190e0f06010513060e090105040203191509080c01180b07020106060c060e011116021311180301110f041a0306011e02120c0102090a050f09 67
    0x400008486001e0416100b955528101072190b0140c00c00c0d5841c5003030304a01d142d603402100c41d0a1407413066034008880702c40042401090840c111001070349c00094852114110314010900ea402100b0040220028800b0040055004d90b100ba4825400c486000400c100218440291500c000300f5020042e0501c1060b880550480740946205107011030520b404c4001d10303401e440c107131500460025000002c1506029010b905260448801d00080103858103100b4001e00d8101d4284000c0c0409460b41104da808040c00d52188409803d1184444d0310b541d95103149904004002006078410b01c071401600384090a0342c8100350b00404010021032400088451000d00b1081c0c806142d680b65613038185040c140e561410050514032030700d802440d91035007444e034404d0740c46900040c081041441802080900d03604045c400d42d003000403c0241d0090200c2220480c50075000440381c2460810100309900e040d10150003808070000f04640b81000b90707840783e0900c2140f024061038030b27911101c0c0c44045036282c24 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 352855341 1250 352854091 352854101
    0x3060609040609021c050a0504030504030305030405030403060515270613061503020318030918180a0305030a060602030903032d1903050604020702030c0f06041e060305010506070f06 80
    0x10010788040380c8682c0d19914030701260004400b03d000c0d4010528040c5410401d4414940e2080001500b00414101510014020f0040380030003001d006c0004041814418100b090345c0096078040701c2840305103061400c81090b0160302c2c0c0424012a021f4045040000b44000e0345903124031601035007401c0e581e81004101141d02c0b10f1b4040003585951795001b198454003d0300303030040e076030360340e103016a403801c5c82804500c00b143c14040107030700c0380c00c288000d100540d40d10a00c5016140c240c480e9050a0b1100e82044100000d0403940c1612031003801851010144c01c40301441c800c0180110410000784d94000036604e80c42640c00b05503154004011400c40c403a101c030f1443c030105540d603c4030403007100a171925039641e40c0245040544c0c00228000350b08050b600d4041c95602010a4034150305000f001d502003a40c0d0309041e1400c41c41410070300300450143d141d000c04d50740208500c01340301c141007103012141000329a503070080c000000c1c20000080707840c1c1400740c1295402680020048080d8646444004c0100 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 352856591 1250 352855341 352855357
    0x31802090a0f050108030a0215010303020d0302180d060b0306010f0308040b03040606050d0c080c06040b3708060306060d0b0f0603071203050d05220209090a080c1605090c030606 78
    0x41d9126180b40c601d40c5a40728880c06085042c0046582c3d99109201074640700012241501c80b10b01030006100080d40031400e00320100c003d040140c0ca444013209201400e11503d202d498100e032030020b208003442115003001070050000d4061303a00e56601c0f8030440d00e51410900003d030001da4208010050101201d00550f4810b004100005420343c0b5200044c000e42e90009058540c50440007050004003004e1024420784074003210664a45441c1c03c030301c0011070040550500341c0101c1e10700c511021000d549007040b00131a00c15480108034103981400790000000782d034000d010388030701d0300054058242015860344058001d411308040b40e0307580c4020300f82100010a60b941500407494001075070900381c000c80e00407510139127419480e584429080d00845900500207400c209114400040490143c0f81141900c1e806881c418825625441d80c030f4944500302d84024070f84500010411000c8502240e001d0f141c030141581101810798403020030031400780603507a05180c002c0800200c2c9984c0703460001800c1c11 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 352857841 1250 352856591 352856611
    0x100527030c130e0a1b060302041a0a02070f09140912030f1b070309030b0f0103020f010c05070314010e0f010e0303070c020f030703030207050a08030c030a140f03010902041503180209 80
    0xf9000c0c0940207420300086141c00c84900c52201040c80c14004440d2602000c0d208a180460406141070440740101c020a84089400701c40000c42614a510030b2000e5009000c10b601c0c004905a0f98003500030051800742e043d0015542e41601162907032501207807001500315040003590031911030700d081040040300645443c560914448105241d4986c0002508049010340c641c003049614600b8840da8282c0002e00d070b0300f00e81121400500040e607400741c15140011081c41c11411031180c500c1c15900e410b900c1c0d003010b011203480001207c5050015045002c04511401c00e039121030b000514220700f601c0e494441758000750001d02c0011041403084602c00c83d2640014840248000a0400720b800d019680c1c10940050304082410b000d0b034207000c0b10715001080d042c0021403a00005290b21900c0703024849940303040000c0b8480b20518041100159180003001003001a500d5a581c1c02000003540316124181a4110310140540c4083c0244580e60714120100400c042d2624654204a26404010311690030 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 352859091 1250 352857841 352857851
    0x40501030e0715020610090e070b0f04090e010209041104060806040b0103092913030518030f071205070f080a1212020703090302031e0d03020a0905100527030c13 71
    0x4100320501003050283d07034000d801d040c144212410b99074103680c0c00c0400043e0901514a00164001039a4003c40301100c82c10303512400518014103c1d031007160b024081c4541007552101c0d5800041d4002c10f075102080b10100524504412901c01900482c402c50740411010000030724103013010381200740700410502d0000345509540c3d83d1700030440410a140301d84001c0302207043c04040e280400e86504182c40b80e0170000d600d0056500201107103c0c42402d107038803110b0100751020a8030108034109070701c800f000c250380380c003600c503800d01e14004400b00040c0d41ca0f00c15618001581d5200c80108030588207042c0107011415580c0d01c4a100000c0385254090030405000318259101281c0e03c098100e192003a80c0382d0040628500425251030040d0150640c003594a140030f58540350700154101035061581400b41e00d404010100b650140107035404140c100d088820040700c07550380070006011a5035a07a0542d014070170092076003038941c010440115050b40c0044610201460100001400b0111444001ca0 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 352860341 1250 352859091 352859099
    0x20d051606021b06090f0a230a0b16050405011d0d0b09010902010809030f0702100507060603380105012a0b0612010c0905062a07090606090506040501030e07 69
    0x80f40d02502d002e000c0f03000e4543e2280c0300720000b07201040c0c00005400003881041c081c83c10aa480740d018135070043c0072202d80d2541d0000c2d50703031034407030548600609010f4851550450410ba0004c1200704c401240300316000c1e0741c003810140a141a1401c3d204e0613942c5104001c20b107810403040039101d07600c50794080130301800600000c111005407445004c0c10000482e0311541417001410340b210140040c521030300140a00300e111a03181041e01c0000d501294803650400704100306032424461400081c081d00d05140e804030501050800c1c4100c4145401002ea0003800340d02c1e81c26211040f0113078604070b0100306500401540d0301c103a10500d0041401c401c5226520300b1040903892021201034129841511a8104210381c40c1004003121380f550050700a1017200709002c4c0c000c265070054002c11748076290110340c011884210404000c0b8808034000010303064500f413002036a55406921501c07071b1107802c10030041821880303104107030105d94001d40703002d080604000054028000390001d01c0c0082c0320300b4074005 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 352861591 1250 352860341 352860353
    0xf0209030105041202070503150a09020d06140105010e0609010f1134050607050a0303050a0b0904030801140a0f050411070b13060b040e1b030f1608010e010c020d0516 73
    0x2c0c3c01180305010300ca0007840c140b0000307801d00143d42d110074403940007400141c1707c0896005205a1101400703600042048003840081c0c54040d10b284040c040e20b02d041041d80007140070700103043c10b880c026220f0001c0c562a02d420031000c0d200b600580b034005248507904a0490340200144500b180c0f2180c1651541249000c0311511031184071220002601070982d020b0060fa110120400606400d5a03058903051040d2585075941c0c0000703400608041e900c00005100d80003da011100800c001007460503a400c090500403c400f1080c050b4075007890074800300c00668580041006c040700c007400100c0007a41c1c0f602c01084020044d0650071183d02c4000c0021400103540300b02c96074403a02c5110039040c0060201d0030103008980031010954048c42c40d1261401300c01c500001e114400d01c1c00d040040c040c1404500c0840e050131190b083c5080c29100f2030a07640c10b01c080d0045c0c041e05440d51358000704120100150741074281c451006402000d07800c07041e48d02c280e06120381c0082243d2100358900e0740504156a613a6 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 352862841 1250 352861591 352861601
    0x2c0606090f042d02040f09091a1306050f0f0612070303110a0206030c25020604120c0503060c0405090c03100501051608030a020c1b0102072603040b190f050d0f02090301 74
    0x1803d48030790004003030083c54600c61210000e0001044200b140240960300c20030010b0403071440581003400f80c1c0000b24408134a40c0b503a074403e540014240b2032030030000000000141c050341c10201c02420b401c009503103070620b5a8200c000e9020b03000280b01c2c1c06d2664406030b880003202c0e092101c0a0085c0b0b0141809616a1401140070380401341d25169101039084a01150b121030b200f1100304440141c80c2d14001d039540500783c43c1594003000d0f248503804803618240c0300041555000341d0b0507014800800c418044080041c008466050750b07214501d54541200c584184001c84e10b0700304070701280344c06104551090002e045600b80b030001940030200103840700c24040c0c2089800b04100da40001c0d020281c0c15080c03014803580009403500741c00402c0300600103900c41045015040240c00c1040d648509400f80488941040403840103a070b40d40d644038032000c4415407254841c110010b034480410100c50740f042840d4070b511046179031040e00f0309580761812800707001e40342c00c0d41d0350181c0c00b400b815000b55020b210f6 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 352864091 1250 352862841 352862921
    0x1050c03030915010803130e190614031203160309080c010212160f08240a0b0d0627090309090c021c050a020307080903072c0606090f04 60
    0x82c50344210300c00d00e000030f405058001020360780091020302e02059440c8038000c140c504100c41c405c03544e560581c0007a100c180001301ca204160070000e0000d94562a640e0744000e1520030350560300c141c10b104064051902c003d4a0740ba0b0090322407220030000a12a034081319090344a610410b24062903d032940d800d907040a443d80030300c05169024441005030030744400711403a2a500340b035944001c0c2480043e04844000f0300c1c0d1070605001a200c0010140503207840941e201c0000c01086c245519614241e40300d800444030988024904400480c6804a4840d219400c070840115076501c1c3c220144004080c20441d40c0890a000518001191085550242a0340c41c0720070b074010720a40c941003071217000c90b00d9008161014410304002400030140e011040307070000f40e082100c40340e0342c031451030109290104030760141002c56058052480c81c00e07001822284c5070406611400350325261201003040d03500c95540925404010820b480005080c150400c82559200c4000e42c240821400252940c070103080070 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 352865341 1250 352864091 352864093
    0x6071e120e040b06030f0c09190f05031218010c06091a070306120f0c03120804050111031608040c0509071812050a0308370e010507080c0901050c030309 67
    0xd08211a072082070205108412039007845034106110204596100140002c0b91280070003000030400001001140c019001c0078140d444001502414642128928092154220907001000a07075180c0007800b82d03088501c0c600d42500e00701c030281054003d650f000d074010341400711034009130000c14402e10035200010300070300c02c203e1a1180d032000c112001100070b1001007071614190052002001602c8a0314081e54002c247e440ba6131070f18100400705114961008008070741c5c4840d00300702c0661008601780114490781c000c0c4004214420b420030280821180c0e0401d0381c1c0003a02c03110805200300e5400e42c0290107400302d2110b0030b0700c400100da502841105e8210104100030144001340300c414124000524100c0400708540710603640700c40d00d810380d0841c0542005901030101d2544240c1c19882c40c6030121070410b1326004001048210095640718018001c1c0e076251160550b64090180243c82c851102580c80c41500d41d10341c4120301ca40e40000d0030817410420184660036070f0810400065004520a074 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 352866591 1250 352865341 352865363
    0x7090f02040533090f040c0306030c0909030509040209060c1b0f03210f12010608061503060a0b0a0504030803010906090e0f28020310050a0e1b06071e 66
    0x1052194003003d20030200c03151003486003030311001d003480c58600a03032a00c45000380b566000190001900740344010300d46a40203180c02c0391009070315096804001101d210399915806540d603040214116441c1e6a805004640104040400f9142a900400c40c1c1c40004040300e0400301c3e0242442d10b0000b0244102e14000010300c0e01444510b03000d2102a031501046000741421500e61403101000c42041034a2411920040340e10003130940c41070281c4103c0c007c03401c0d03816410741c0c4d9940000e10068040c2d82d00d50107442c0900091054001c00400c4a10401d0080c003298400362500c9440051980200d41541c10010188400700000f0340120003140241070407400452002d0900f5050b6040780c41e0410280443c4d444010440ca8015010030300e00d803e40d025036044400200010001d081d0410600e4000798140102404030500300c41c103600850140c42810010850303c149000c0c5240c2e9040d40e615550303510701802c0d00da240f05140801c000c3c40900d01c1282185504a0100503c1a189907a00340480d1020421 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 352867841 1250 352866591 352866599
    0x1509020a111e07141c0c0311090906070806010504150806040e03090a06080613020c010221090c120f070303090618030b0c0d0902100e0a0f1d070207090f0204 69
    0x820038101003060302c50b018507080340355410141d81e03201d5a1062001e84111111030014940e569690744071000c260102c445440b10540c900b050301c0c1040e80c0011a1940c2c0341584503101c6050910019108013082001015141c50703500302514850070060800303042203c2000003007042980d40c00301010112081d11010f40500781442000f043e501e23228512041d544c02440040903e590f8540c540c02160014104561992030321070100d0220301c3c5400580320074030b0001a540b6180d510540c0204520740c510038440d400100b00104640c1084070660740b0741c9150b446451204400e00c1c112010908040e0444200c8400b030b0380d200c030580d08007445030303100f5004101421020441590414002d2a80081e14600072400038216a22191401000b03410700340692004075502c2600d690710303441454116001402000461480000280380150400c0341e00d0040f0840301000410508041c0144107070707a401a64000501c89800310590000d100815990846c41480f0001618076002d100e000c0d84081c034a02c015a4031420 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 352869091 1250 352867841 352867843
    0x110c0a020117091f0e01111b070e01060f0302190804020a082a040b13020904061208071415250503040f1203020d0513050106120507091509020a11 64
    0xc088008981d160340d0100a005000802c5000700213145991401350740354208000b4008014685400350344d5071810019000c940000c50180c45110403c1500805110125140641755500d5100d018100c10001c0014080d042c05010b034605068082d140c0141070200c2610403060301c00404552002080004013030006506006d0b02201c041e080840c01405450040c50315150340184d6144800103144602c40380d1482c0d5556508240050320000b0b200700440015152904025031004100c11303c03e07454840e000504855003076030040040e40204595040030b0064540c0366610410b2440d030300c580c0c003424071b500d001408a0f024050050482c1e086440e000318146000640c6084024040d40c1402001d10411002030300f150080121142e0060038015414804401a0b001c1d02038002e584215a04000800000c04422042a50410b00442c02800f4195a800420100500c0c881000d80300f90001881801031010580141078603100b24045004859603664050040380c0168205a0004050b00c442c00c9002d01c0c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 352870341 1250 352869091 352869107
    0x304030b09010e1b01180e0708070e03010908160813060302070302160509070f021e0312011401080a0c0909050c030406050c210a020f07120f0504030c030305030604110c0a0201 77
    0xc80d6600418180c1c4d0050098401e42c0c600c5940079041000071401c141490740c10400010050500c0c10004907607007440e040c06054203034205c9061000070300010f0181e2592505000c0c0254860b0858409032410441d0310128070300c0c0d080c4a00c1520403642c00c0000c03060311322100e103496008010f41d130390060b2074903540d2038004c0c02e0403c809002448907000c110305010130703a43d2686840d001180707800e01d03114480820388141d051480121030540c200328090000c141c102804001010141c1105048001e6a82c0751b40742c400c010320101c0d403054002205d410029a18400e2544141b80198841c00d002c40c0c031b655100c42d01c0c01500c00417107119400c00e0010041c001001a113004140d088250710101c0f83c14040e508090242c0301d24016821020504c0d504046000d60303021364100c41051250300905a92040c05040c80d034140c2054140040002d002000440f07110340c841d206070b800362030f8400784c59010350345107450489180c0c00140150398820340c0d80313440d01a02c002e000c0c01408a40025000b601d00e11196000160002c1c0c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 352871591 1250 352870341 352870361
    0x7020709140c030c030907170a0302010f0510121a07090302031b010203091003061208040816050a271a100509090a0c020f01050109060905060d320304030b0901 70
    0x7007a0248442c1c208001c0030b0301d03400603640a44548a07503c03801d80500d0941c055000030310310b1090010031950b1140108070307170700030354025002071050041c680c041d8030407640708070b582c1c4d5400c1082e154144040e00d513500c030700a0958000c8032a40e003855071050449000000079513a400100d000301c1820030031828240041e40c0440c81000c80016451503202c0042d45034412240980e01c078030320003008140b4490007944040701a02c140007516414510034a030158440c0d2060180b81090300c6100d04042840400030702d03040945030003604040c1c0d0305160005000304c1c40100000840c0a00300c1503210200c4070754a01c58a01042d01c184514101b03581103005008020303516400b032104114042041841d60f8884100a40d000550302c440010b80741c40400080703090043c03085101c000c0c0d509020000450041a4100c1000d503840320604111a440300002c10800d4060f804001b4200c1c00c1010369a0095541a01000c0c200c2e6070034280f40a09a00303500c6604c0c1150302c16002103940c81001000d100808800b445600906 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 352872841 1250 352871591 352871621
    0x504291b10061202010c02060c0f030c0a0203150c0403060911030615010306050301060302061207091a0c060c2701050c0712060b04051308090d0204020406020a03020606011817070b0307020709 84
    0x4820f00c3e000200108588040a40111400502214504410003c00c50312400c80d00c10360361190304504600d9201c1c66190000e9119105034414005410003241c5898000c295003c0b2462410f440c2d0350350389015000050099130b000300107080c0800c03240c80601190b41b04242c8460101c1c0b54045080c009403c5600a402c180e0080c4e161180500c01600d81c04101c0d580c00c00070000d001c1003965000e60484581c1420380042c00c040601105c1035511180303d00251840c8807000c4107540742581e4050300d524541c01800d04c0608142c6070400e00300108079944081709258981031500c01e00e031820300c80c1002d00d04015a40082c2c640355072034407008140001c80c800c01043c135804880600450805006480a00d0001100034080b060001040000c40c1e5604680004066000d0401d6480c0e03070b40e03520041d45601c543e050036000750090000050380b941c0301381050076160480c0d4224216250604025401e40201201d08041510402c0c1020421024103000703940b05d003c1950040c1440341c2042202c406851480c801c11100b = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 352874091 1250 352872841 352872869
    0xc020a08010516120e15180a0b0609070c0215040915060f1b0f0b07080615220306090c180e0309062809090c0504291b1006 54
    0x703c1040f040b481122640145010040d00503180d41400052000c1038a032074552141e444141c0c0c1109141c80e401e8843c200c40841d1035280b0b8003c00143e52109440000107241c0380c00c0b100002c4c51842c190301c02a8000d0000d10704080180165030118101c03001c41903032181c0c2030a000c102080b1750388460189101131140b140001c125246020740c0504070317446a40d034500500c4920743c6281e4000d4011042000c0e00e07a006401c02020301110b080800401000f520b04500080f00c842c0011110f080c0b2038074102600c0c0040014a1400a00c0c00802402c40c0b445050000800031540700040880d81701e000c0d0388001c038090005290454507055989a41a903a20070110500c2c2c10860b0580c802c02001c001c6d00e035414820707101540d407042c2c100b44002c2200d1005001c00c10f5041004c4403110700c268820544c8082c0c0707040c48020490001501004d0781c041c0110703c40d00d542807980103648080178100c18a00039040e4000c00c18103003003031110000321100311000144200d0342d43c40000c03080d95010190048100404403541c114403 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 352875341 1250 352874091 352874101
    0x1d0c040b03030306040903120f060303030506010c0c0506161b0905010e1e0601050405060d060501030612021c050a020d030f02070b03190e030415030209040506060c0601060c02010516030c020a080105 87
    0x42c60f030000a140901c110350b03d0b8500018907004501e840f07140810500200142e240c0c0001150007400c0501003500000d2500d400210607500a0310040440354100007900c046d1440c0c102000100d507c10820701e403c0d14600c3c0c840b00c1c00a1000c4000508228550f100400b41038145a500b07000c5070390580c440b44440312190188800d40c1c1014500e0f0300a20f6180043d2501503450300010794903840ba0760f1004da041200051040d4105e00198021002d5601c266020302c1095958445242c54030046070340a541300c0e62007046030074800042486e11445c1d0b031140301941c040c058690005407050395100010340104114180c0f4258690341441307000060016840c00a0650801401114681d014440e5011005988442d100e04c81e003410410395000380700702005100312000e9428020041e40000c2c1000303000d90b06010104141349491811b541c00200614002d0000e62b280042c122070780100c0040985c1400340412070302041005c01d0403034865240c0292121171400e400b40c81880b9103480340d54840384042e4074142c2480 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 352876591 1250 352875341 352875343
    0x3010e060d0f060e070506030a0c0201060603050c0909061c0b07030b04021201050d030e03070b1c1a22050411100e031902010201140a15080606010e01030e010905011d0c040b03 77
    0x1005440e008000040c131311002d001214600842d6400c00c542c02400070082104500c41500501030121181d8000d1043c5c1f03a48020640684105407650904c0660500004c0c001c0c0c1010b5003841d501802c000c0900914880c1c481d08440c400c4082c00050325214504000c0204194060044414011094800f185400345441c4801c01d4004c0c10300030184a41071840d036040078103114849100d40c0e0900103090300c08460f51000000065880b0130941550404441c1d050700c00282503214a0b00e14945038140f680745079107914204900c00b00c0031030b404d124252481040c01d89004451180b588104c1c80351800c1400c1c0c43c2c203c400c00416200f418150703000c105001084440c192000b0422503034408900c0d1358100d2486d42480140e01500310344140c4540d40d40c4c01c804000710300c0c0203a0856518401207030000d680054464004030f40300c0034101c420502203405062100c10b194402d17400081c2d084420070002a00341e80607500d00d425240403001c1680031030750203410310007818824040d6001303e00c2d00302c070200b0000c0104400b00f = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 352877697 1106 352876591 352876613
    0x150c162109050f06030c0906040321080a02030420060c01050f04030f0c08092e020a020f0a060c0b070302070c0803030f070914040908190503010e060d 66
    0x152904043c012100307012400f910107482c5540d14030405a041e405a815030707030894820031000000c80c2501500302002408020b4502503800f5510f001070081c80060140a012403040050100041c0fa4030742020300460311190035000b0107081c80014120f4041c180c40d2040550810041081010403021940d1003144030742c4a102d4646a1500c08403410b1900f041c00414000040100f681325240c03109030402401005203c00da01c001e1003072021620b00460740340070405070b80102114811440e0211452203003400030f54640382403a2a054006001100e00080500620010000300303848074400d8045900e00c98021601d2101c4955569081c0d560340c1c0202e5404102c41d54510200d01c1845c4207601da50100c0d03140107680c1048014203401c00c07005099120046402178420414400b19101030071002c924220325072203164032917141500d404c080400051a580c4940c0682e09413000103112480d40b = true := by decide +kernel

theorem cover : BRFrame.Cov 352697841 352877697 := by
  have h0 := BRFrame.cov_init 352697841
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352697841 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352697841 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352697841 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352697841 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352697841 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352697841 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352697841 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352697841 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352697841 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352697841 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352697841 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352697841 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352697841 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352697841 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352697841 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352697841 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352697841 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352697841 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352697841 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352697841 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352697841 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352697841 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352697841 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352697841 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352697841 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352697841 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352697841 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352697841 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352697841 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352697841 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352697841 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352697841 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352697841 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352697841 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352697841 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352697841 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352697841 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352697841 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352697841 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352697841 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352697841 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352697841 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352697841 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352697841 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352697841 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352697841 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352697841 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352697841 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352697841 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352697841 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352697841 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352697841 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352697841 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352697841 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352697841 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352697841 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352697841 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352697841 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352697841 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352697841 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352697841 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352697841 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352697841 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352697841 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352697841 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352697841 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352697841 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352697841 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352697841 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352697841 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352697841 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352697841 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352697841 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352697841 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352697841 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352697841 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352697841 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352697841 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352697841 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352697841 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352697841 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352697841 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352697841 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352697841 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352697841 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352697841 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352697841 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352697841 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352697841 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352697841 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352697841 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352697841 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352697841 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352697841 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352697841 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352697841 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352697841 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352697841 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352697841 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352697841 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352697841 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352697841 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352697841 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352697841 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352697841 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352697841 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352697841 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352697841 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352697841 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352697841 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352697841 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352697841 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352697841 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352697841 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352697841 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352697841 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352697841 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352697841 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352697841 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352697841 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352697841 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352697841 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352697841 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352697841 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352697841 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352697841 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352697841 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352697841 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352697841 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352697841 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352697841 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352697841 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352697841 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352697841 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352697841 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352697841 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352697841 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352697841 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352697841 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352697841 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352697841 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352697841 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352697841 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 352697841 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 352697841 ≤ n) (h2 : n < 352877697) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
