-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4201
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:51:46.749384+00:00
-- url     : https://prove2.me/submissions/22a5a94e-fb27-4fa1-8f83-db4bebaf2b71

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 755395683 ≤ n < 755575539 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 755396933 1250 755395683 755395687
    0x606050a05030a023708010b12130303150806040224090111030910020307140606010203030708102d08010b130b06090a1d070e06030c1b0709090c08030304050a141002 73
    0x750501c80090030010581170350319040c6241c3d072541028651409180c5803a007101c000320340010b0200781191070f070806182c0242800580d002c501100304410000c0c07600007190b658083c50a000442c20062042d174943c89600030411014500d00440054610440402d86d0401000081d00900c054061044a560700801000101003003540f500280d1aa003060b54103840002100e4055003559002040300e910516050b03024519550314400c003910701860291040c04a450103138000324031aa8101c0c594100c100d0b040420b50303040c4c0c40c03540034442c50a10756005061141d04114031002262110741d5680d04c603c0c0d00d0040400c0c05145030dc0802d41c1400350000305580001c4061002601900701d22030b20049c00254200c0c02e032181d40d1250151050744855494a4220303104000050f01e1112010207000d0400340c14040c0c0c1074038456000100d1801c00140c002041c143d6480d6040c00170402c20295a40040c144a030203075096240c00d40300c1645500c8100405850904031010a11410300d0900c9242a900100c9400715 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 755398183 1250 755396933 755397007
    0x130203010810060b070302120f0d020d052223011401060c0c060507020a06080402060904091103071a03010b070510050a0213080a0c140d080f030601030606050a05030a02 74
    0x20b82e40307070701c590303031100d00c03189040000b01e4850b41c814103c51000341c140c0c004005000f00c03091143c0351035001c1860142c403580d003481443c00c1d51601d400100940c0400310000700e01811b00d0014140c0725040f010540c401c4500741030140d40020b050f03260600d03046401d40c02006000400c004075a02406030000a0b0350b80c84122000420500d170030140c080c548501032400020300688482e015580c03071151420180d40119651000c00100f442644990350261020302924141146007004c00c2c06d9619101e003c4900d40040b005500b11401d0420150340201851481d40c1c40c1c1080010003441107100c18002c04d20340750400a0040c1c140501081a15481803003801d08102d1440c020b0040c200941185400b400c000c10600300004001c403001610818540c1c100400042e00352822820903a242064280d503500901d00c1051f003404a06200c01601c400b0650508040d5246840c1c03000400b01c0764681c100400f4081d0030302003000780d82c1c0e102e002c2c1e0380c0c0b00703030769000c0140c1d1810031888070020070708030710410071a1283e055808 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 755399433 1250 755398183 755398199
    0x80703020901290a1422061103031302040b041a131e0203100f0f0510080610030b0411070c08070b04180e0106050a08030a020f07060f0e0a0e0f040515040309031113020301 75
    0xc10f48070a503131b40c003044009845800c1180d84040c4244605030a0b070090000c940d1186020000c070380030b10b00c000c01c0042d03810072440102e01682d42c2300c0c414810980301c2c4940d001c00703402c04061400000000e190200605000403003145241418490900c24007a404800202c20b0f03d0074400c501c01511464401d029001d542c1d02100d420120035004081c0205100700049016030301504911340160b20080542045200e0700f00100c005100a1441d41d40c810b0f25070070f041d280f040f107010040000e45c0c051800c01c0707940d5040c010400d18000b9581d100d170a80c2c03001007004001103410010740c041483d04803800400c0d4001202c2c046400f5003c10380203254004180540003885090000c0203194601058003607880c08043e90304a940c48212504c0b03008003060440d002c50b00740c00c1c0306000700c200c8040d008140201da1500e070064840cd00c1c4007150181c01c03004054052101b40b110800001c98010034028111201b0701d8a6507000340b058040c0d20004041221803003484141c0c1e030f940c402c030f112078040d079910854a07503135034880c5 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 755400683 1250 755399433 755399467
    0x52703011803021005040c0b030915090f0f0303070804030c0813140906030607090603110f0c030406120b060405090a0915052a180102030f04080703020901290a14 71
    0x710094840c0300d100c0e0b610303864180a59445150480b40350315616107030035888e6010364401401c030b48550140e0860700817600002c1660300d014039000030040c807844100c28103162420f040c003042902142d005204001106d036004603d603078420f40c58505419a1a524506008980200e140307203038a030003229001185070b071070064900344103a000710355006254950710107140d210b00c01038806000003104102c0900c980ca009030000f03640e52844c120404e02d01440104645c02c103400600d002001034100040810402d030303100d0340241d1140100201089a1700103900010392502ca144201ca001e010460009503003007015138400c171a80b80d001206850003003440c2d8403d0009003000c41d910184800030f01c49040817656a00800c0c05182610b90341c0d2841d00c203000d520740b04c802c602800254110710081140c1740b0000c40c8840500020b11240b001820281d0541c4100050410140c2141d0300503828809035455400314903401841c00702402c4a03c030394440b441c2404403802001003410001c01500010f00101404a40310 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 755401933 1250 755400683 755400731
    0x16050d020c270103031809230c04080703030e011202180307120f080706060b0d090c060516020f011b050c040606020309010203190905040608030a090501020d05270301 73
    0x10711510401d020782e4408900050050990007100d0a2500502c00203018031203010030040f0b01852000042c1e83d07a1050760550740091080000c0c403411065151014404003005074101010704001800d1a080140050340c4100f5444058100050a103405105901801c00c420f08101030f1030055568005880c1c03032020745810044114084e10485c000005c4090703120103c00451507102401895800240d02c035041940c00442c800c1c2d500c5e9585000009007507184600500600c05100d40c0400c5e40300782800c007040c02d034a982e8040c4060003401c1010603140030002d208000d81d154100c07030540d50a00303c82d00403a034404841c20f00b280d448004012140500600203444c10201c2800c640034461151a0102241c60b402200d042c1d501503841841520f02a021000070785416035042d10740040c000c0e9036680001c003650116403008240b070700002a010b4810ba8840200e001a0000303000070040c904545000505030301c00c40e0842907013001c0034000a03c0f5880a805904000c04000b8001e002d6140445030345202c40840300 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 755403183 1250 755401933 755401939
    0x120f100e071809060f0920040303020a060e010b1804060b1504090b240a021002030f07023a020a08070302370602072a05030c06040305070b16050d020c 66
    0x40c1003c80e8058802501d14072500500f140745000e075480b024080c0c41f450000200180c50702c3d80758004c1c900000c0c1c00158029401428061060300303250f801c44009074010061a410841c0684641c0c0b03490b08020703060006170b10005400e9550381086002070200a42003580010144039416481403124040c100340c8a107044200441d55000c01044807403a4040110440341c144a040d03a40512622409424074512500580e6528114208000e0482c2d000b104e032113003075000341b10500085a9042185c02150f500c03040c00007881c6610504144c00b0840f020031079441009010014444461092202d20301181c0d019400c103850710420316010b51120000c0850403183c1c00c0c0d40701200d802541440ca0710000020b20a20405094803039103640002e0340c00140141c5103540c100c0310011500440760480103200a015030003498860030070081504000f07411440301d1090384240400d002043c40415036008441405000300d551711510743d0440c01d01d04040d071000e00240101224514440d40100714081000011 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 755404433 1250 755403183 755403227
    0xf0d030f11030309071e08010612290610260a0c0912020d1a04050606040f0b0319030e13020a02060709080c040c230403060c0302120f100e07 62
    0x10740103565030b00040b15101402e0744490742c10030640e9440c84031701c52002d52440c1c1101d03c4030f0301c503001c00f401d4401d282d10000e00746242c02030200070f206d07240c618500e1100703121b00e15041c1c0200034141d110382004050910f0b440707403a01c4280d01c005070380100200079911104c00008441e03903110001420102004441654103e1300780403543c0c2c0d002d44201c00100699040e4940029605826000c0c42081000e09008627141800141d05825001100081c070348214803840040c1800d28208091000352291400ba1080840c107101080103169801702c0d048070306400b0808403600c41c512500b012504110725245072030308404418101c4048402a4001b4440b40101d602211416107880400719190145881410195001000c030014503107000d1300030404074142468040c40d00384807803844100144640303013076030304402c0300107002c104005090080300e0100340039040c114140510f0000c868850900208200c15260303050700050140c624224000300038000300b00820b01145004500981550701642460708000c0130 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 755405683 1250 755404433 755404457
    0x60b09010f0e04060e10061401030e010c05041a1e0c0d140712031e0204080709140f18060f01030213200a050405040912080a09020901050f0f0d030f 65
    0x30321907050480307294040421640d950f0b61280d0f00102205110072400f40664800299507081c280610301c081e00c0a03442a003601a000000074040f52075115000c185a414080703084081504a4246c80850315000c6003944c1c02c0e80b0041c0c403854503106101c05040080d40405204015403240c038094030b04076019100321140920900b00a68a10449602c01ca642540804c0307a003002440003014000c0821684c20046242000e17000850340c00c2444400745a01d0f140c1c082020408207008104c103030010a8a1102001403088000201c5611134005040401d0141080d012801088444601211144501d4240c40c43ca00b095034003c5140c100030b00c800d03485100d4005540c260018103114100741d400c0b41c02014000482c250904480350b800c81d51001040c0703c0b0a10000949481d1402004550380c4905444d00da00c042111015241d44000780105031050b141c441c1c4000181c88624143e030564031f0032030341201085c8403000000c09902d80c03507540701e4000026106401c100741e0010040c941550107a1214011084 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 755406933 1250 755405683 755405699
    0x5030d0206040b0412030b030f032d0717070b040b0a0c050313060507140f0301060216030503040902090a1d01050913030806090615130504111804110412060b0901 71
    0x2040d00c01400240f5a80007140c00039018486681c0b9041c3c0c1c509000c641303140708400090400b482420780202c641c1001450014600034a80f600000351412145041003055154040146020310360300281846003150030030814440800580b00e0050b48880100d40e0b502d414608620703050800d8078051409030900035182c0c105405041035921030f80380000700401c40b1100d911020090400500341000380b210340202d402d0600490802402406c2407851166640d500d4814028074003054601c06182c6c0221154045c000103a001c0700b160101c603100c0f08007585036444a0001903844429070b12051180d1401c045c1c0a00d00710003040b11a0403100100c4007400607584040105000603464040100042c807807200050341464101907150300a01d000c0d010200b08414801013a01c5540b02004038500c0c2100e000b0304000c14540341c00707a141081c07164058982080b0706006c0d0900b042081214952250b9198094080603a4000003940d0050a442020365600d601300e040c09030013007410303442c040c1c020903903d000451001 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 755408183 1250 755406933 755406943
    0x3020910050f120712240e0f0103060f0612060509120301081509010207060c0c0c091109060901140d090618030816030b09010609090f05060f010f05160c05030d02 71
    0x98440c0b40c1c0745203003c114004003c03658200410b0300c82440318640010009207200d22981080440c4000b401c1744034070301e0f005030340c2c613111455100940c4880b004e4100700e1001c1151090604481c3e00001c04603050754441c0144c0c01074100e9030810f142580240701080144545600841d0090070404240c40d0384290f010700b0545684801d00480146900c03480034022400c2d88043c98a82c0108104001806d041c415500c080c03c0e50901300e02c22002076a104011024400807030400c0b001410040c20410005440588000c43d0f0700030b01004912580c400b042508003640a81001c010041c03503030410a541ea03e000c04540001d0000100603103c103460403001084102c1c50000111030103130581c58400365039a1302440a2942e00c100c00a030010903031600ba8600c60307034407101c1d14140640310316120700d801282025014030444402182550a1780c0c206820b100540e1106141140c115000307203480081302c6591740090f205403242d0011512818101c490030000d02039158810020307150100e082c1e03003101e030b11650100c0c1e541c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 755409433 1250 755408183 755408197
    0x14032113030e060f0d09080a020f0307050a0f0305070c080102040602010c0201060b09090417120106030e1605060a17010902070201020d02060103151503080d0b0f0a0b0702210303070302091005 84
    0x102c0c0010300b452002d4034010010300704000700d05518a14010b500700044042d21004101101c1d0047c002c85c541786240e8041c8007516010000343c0046051440c95280c0d0383c1d5403200c603840a031065580c3c001d070405042c030840071180d21640002115200d186c0d00d0301d01c00d000307500902c5810010b5180c5003c2a20461040c0200012200010142070411038058100410124050001c81d621500c07081001c0d224040040600b0041030603030403214166150040250030385080c1005492aa000030361503d468081811444042c0c40050380e455483d4404044182e0b4061900c84c2e105044041101c000183d1041540060010324400c1e0300b601d81e02e41c50220140c0e90b6610a000041c44003682010b9007500700460349c8002c5012060380001c2500503983d80b6010499482000320326078444d11520591030170308120350303d24020101602c0a46d03050307203031601c0484940201e410080c403910041401e00d801030048039043c400c11010303500b602e80d01e040a0303001400035440b5250660040304078070040300042d0300400a40d104 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 755410683 1250 755409433 755409437
    0x11104050307090e010621051e150a0b0415050a0509010f0e040501141518060607020904060b03120d06090615210c03020d05090d0c030c1403211303 65
    0x141d40c10f203900d00d40640340c1c0060418040d9640d4000151183d10b16900c40b000f010710300f003c800d1604032030908604007004041c206083c40320040040280040c00070714211408a00b5035034503030070380f50310702040702600702910126440f0b4241151484030117508158201140e800300d440e640d0355079a80042c421140741c240b08400b0131078503503c0e041142120040c40c81e0340c4a03100d0301c00091107810300c0706480c09400c02a0303502d00c1c0584480035142c040f030801240d1410804500c40c24945a8035000b400101c4500c91003400034007800040e40480d04111568106c074203110f50050560701c4544038030121802079001403c1c521006824103c0001e9082103510800082d6071402d60521070f060380b0340b94162011080c00c041c0d402020305200c8031000e00c540c1489100e00794240c50fa00944e0302e00d10751651009540703000e049505030303401028003a4100341d00301b521015955854240500c400f003260034200e000a0301034415284500000554904888280e104a220b03410021411000390f10390268444034010407110040c0 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 755411933 1250 755410683 755410693
    0xb0f060316090b030c03010806090106030c0513090c0e06090f04020d080a0c12030f0b0306090c0d0c03052e09032705030106030c1a07170a0c060c020607020111040503 73
    0x118071081031240c000d40030050610104107662082402e105034022104242440c001000500c28000280000f9400c400004000d100702c2e4195120b603100d40001e40308452050070358402001039462607821442e0303801c2d042800b0020660b5940074804420404440191081c07088100190059105402c80f5000319000340c0030000d40040d541c0c0b120155808081d84000b80310b603001c10701c0000341c078060fa014042001d5940c040f40c800704e00c04210003902c03811004c2c02d209400c0041001481380c800981501404070071200c400d200b581d0f41c2403400c140c2c80c80b81c2025086004914804104500c2e030091080d00b0240050b0302c00c00d1132805a200c800700c0742507200050020384807a040301d5511400c0400036882082e2001002c03251a80c500001e804c44002d944102d482e10f100c8501004218007074000c0003000441e0404061a10406503904552015124900c029480c804103071461054402c0701364200304d942c0600f080007425080c0c00083e5881d00b00319112401903082c2607840e411001003605a9086510244c0280 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 755413183 1250 755411933 755411941
    0x30c0304032f09060607080310061103070812040f020a08030306010909060308030708090c040e060a0f050112080d14011d01050a0803071e2a05030c0a0303031814030d0b0f0603 77
    0xc420801414483c5e109600f4404c00340860300b4030700118021010012458826454000e0190050550b0004100c02d500306000440c00700707001d4800c558091044070001d4030070b40d456207414803400c41c2814019410041c1c0c000d01140400340080118021882600c45004199440e0f50784026520b4900000388040d4040c00403451641c040d015240d00401140191143c642101c03022408680c1498401d508580c8903c0c00d000b0114000c0c89a4810300807588e03400d015560620301d10034120781c5038031401003103003600080410a020742c6902081c210050090240110759407034080141c0c00c03284184501d403126045000184601d04031240c03104554440c1e010714144907441d11100c9540c0e0b2070050600e448160210184000780c2d56145660000c0c10480300140f101c00d40444003444140d241d002180642d11602d400100c2d0707526068400300304c9a05150201d035007406019030200000d1000001000601101040c00030030001001138200c42046103000c0204407852000c1105000041c42100c0c3c00140800200d = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 755414433 1250 755413183 755413189
    0x50418060b0a08060a0f15032112110403050d030506090105040207060902101e030527011812020d080f150303040308030a0f1a01120b01030e030c0304032f 68
    0xd00301d4000100071100556a880d441c038200401261010030716952000802d4050403603110348000c006403030788003003151070035907443c4080340040500200003185070a03200400148594a000050046032800f0b0001505203140d03080c044d00070b0302003202e080c0600605a01c00030311034481c0601c9440000c2c010100c03646882d0911000750702c202420340c2d80a84400d980c0000d07132a50b4030074104041480c2e40786026424010141c40343c0d013001841d80010142004240142c0141c981d0000b0030004030b14040c06080e200750313840c440c014000d54010f0070150050703499540a00038401314141850034540c0035174241c3c0d8010174007168012811607001a0b021500800300e041540d44d11044602d450010301181d2500e51a82c443c0002500101d4031622101d4598290603c2c01d40310b40200504006525400c49802e46250006804007200d0300d801a0280c1c1d58492a421980c80398200261412104080d40d64032040e00c111a91207070b00901084e00c0246440e1003944006e06c0406c10011a030705441a0380318900908410 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 755415683 1250 755414433 755414441
    0x5040e15070c0804120204050f010b03040201030b0109051e04050c3103080d051006050c0a150b10020703110a060f0c050c040e06041101020c010c03080402060c0304030b010f05041806 80
    0x79204000500121600203040000200b002d0038042102138101e040520400041d12001049141c2c2050311000401c00a8500c000303032904541d0900340030039280c42050040f9103100c0540c0c80356600c0700c2140030301c4520744610b25601c811441c00751018403466a48503c0074001c2d10681c4009200b0035003c5800201d10340e40010038001f20454050076142559594440c0310042d001005c0246400340d9810078001e038103001c20030a20040c8528241103040c2100040ea2076110340e20160090310018800c0001c011803040d561004541401c020700140015028583c025920585800229018190080c16150700c1c0f6015540130102d81d0755a0f654030a015005070704441030f41c2d44034012100c0b40f10743c04400210b030b5218029100e508419200500341c41c038181c206901d606d071101c05003605542141c003c185150764082c4905180070381504058032962614401b10712148501c11104400b40070202d4040100700ca403041981c12600c0651110349032a44400800c4215090101d104900d040c641c0509400a031440d08 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 755416933 1250 755415683 755415691
    0xa030509030717030a1115010b180306090102070510091101211a010806240f1b01022706030a1e0e011b03110703050c0a050a1b05040e15 60
    0x10a0700e00055449a03403418001410fa030b40d91160b000407842040c21a40300c603a081d070b8450860700801c016909a500d41c40d0070441070080072080040040c0710080c07142100c0a40001800c0030342121410329042502500030340040b43d08075054016170842c051801c60900901d0602030300040020142e0340d220006440780f55120080400c0185d4285031604280280c2c4110350f0701c80c1240030076841c41d0941c0d0380014000310b001000e02e440307251900c00b480c0f04581035030000b903540410b10b10020b586e003070315204203c0280904040c0900c3c041902060601c401019000f030070100459080321308070f0740b20008840c85903208140e0600d400c02c4e400d000003280200640c21201d0f4036503204e000300392104000c400d80010b503491105510300e660b441e50002c848501d4880081071041900c0d1030100102110101000c5481c421000040c0800502041803d640303001404226104c59002c000c649040c1c0803807400d03100710040d40c004602d031702020000000301814036008102c0e8907066030014105006066080c031401c040003030 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 755418183 1250 755416933 755416939
    0x301080d0f023a0f0206010b0c0a050304170d050a0e0f040b0612040c052b021504150e150a110c0d05010e010e01020c100c170f0402011403090a030509 66
    0x2c07500c0244846407100920301c03500d4103c0308030f10821034555100c03840400c04100c00c040000c00242081225400305a4505441d00050100c0c0d80f61a44a44549403141c00a030251a60100060010b06241203451616104242e10107440e16154044029076803401071103040008641040c02c0c04000b4074010000c5000800c00602c000350443c5486c1c00704580340c110075a0314155007032020510007400b051215020040008071030f001c01c06100203940c540e84c0100c0c2512200d500301c20b80802021036840c600c440900113010400b258540341d40300c44003006400c070110440045800c0d0056441c0301d0802c1a4088102c1080310912440c10010300402c5601060140c2c41210354015140110417668404850814050141b400440d9062030355a126003181c0c045641c07980325a204100300302c003412020038190303841c2c00301c0403000580320500700c411b40b4200b42d8500c82540d0100b001c42008891041800d049000c0c6000303907504001103011100070285488182d92680740c50340002010380010f44070350700802c061200a = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 755419433 1250 755418183 755418193
    0x50a031412090610080d0e0120010207150c05070f020f04090501020a0f1403040210120e03041203030c0c020f041a0a061e020d120207140f10110301080d0f02 69
    0x644590030001c8016a601403443c1c0280c0140150074a4002c0202d019000c1500682140c03000303508090060544078200b1814040b581d0108114002134a204900da5401e0340e0080d0340c0c400e594500f60803282c61a81000c00007500d0561440100d901c69000d6450403980700c001444040c1c0c05400704100350103881d1800b588103031240d602500040003800a0003803012541c40f01280700503010030207090810350000d01803640006000308409680c501440710380025050034904590044e909081014102441210545100008001450a120982517903165009640800505041210446600c103003c40b02035405440d10310b4107400d61034a0341c002e450032030b000d284485032140ca10f4040340784d131440c9030700c43d00c0400d800346002d1040c3d05c0b4400c01580d03080d420f840580440880d40e8009003d0050f014142d040256020542a041100e41e607581c0d6050007400381207030400345044190a079a40c05a811070148241000e0080784014600e4060700e042e5402c0d40b0250219008000044030800440c00c1d43d02c04520032 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 755420683 1250 755419433 755419447
    0x717070516050a030e100804021008040203070e010f060f0c1a06030c19030303180b04030309170c010b0a051e040c0c0b0411030d050304050d0809070b0f030103140a050a0314 76
    0xb0401c96007841d240310707850300044c3d81080e2082043d072040361160507003440210700070000180d58400126600542c58200300710640c5075030003c42c0c030345035a54108401d450030700000440c1c01e96010818000301c1c2c410f980c5404080761902c0c001c45504451850003031404120107440806415007410f0300b03520100250890721102e03028800244000030f00d01c103078403000010303d03030601c24540c0c54010985001300306000c030b22101400756100c500115000700080c080554519101d42004800307445a10314800440001340c60b81c5d1601c03440390092500c0890175202d440111703c00289030030940d000b500301421210715500c464500c6c6050202400400307450904000900c042d000020b0020429640290700400350300c0fa10b650044141850a00d07626a04030600a0610412000039400a1140104d00e018070340945a84c540c0f605840c035207461030300400e103010f03008540701c00207281c0040618100c034000e4400a120102545071151942070780302001c1d020741c000c0c035204000310b4000c00d0303c103442c900d401c0819132408903 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 755421933 1250 755420683 755420693
    0x41b1d1303050d0c050c0106080c090a021309020d020a090e1023030312041109040c091e0c0e0f040213050d150614040e070627050a030b06090717070516 67
    0xc4041c0106010950114043d41b10b400244074140c007070a030802c0101588819400010148200201032002081e00000c2e080c000401c7d07000c07603a00400b01c0b07501c2991074815402070344020b9084541900300061541400240011443c0255401461410003070742c4440e06040f101d58802031007882c8002811504100400d95807003c200900300810361a5004a9504042ca07042a20091245c1403034883da007600140804107d0065405049641110700060344042801100501c10340e0300d0040800b0602e00405003089980008003516941800c5a401c0088010030302000201d0141490000300f00200300d82c240000d003420b400b49030b0b00e10300840007804450021880c400941c3d4907074100042c5241110b50380344d01820306000d00c0031300c19890409850520f0820070001d21001e2aa180e148403020007030300b01001004205a400040c00300600a00c104548a060104d002001034400c2070051210b0800154410311550036980313000811a9201159154100c00300e07000c0d08600e21907841039203151a000d001076 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 755423183 1250 755421933 755421941
    0xc02060f19060515252001020124081e15040203030408250b16030e0a05040501030606080d020d08010618180f0b01030e0c09100b03041b1d1303050d 65
    0x181300944031569800d900c120003004981002c00e81e1241c0050007074040004d1039014070341c812100c0b04c03031401000c0d007100d400403409000811844070308414844808142240000107440543d4883c00c01c48c0c50840680c100029091603511300c1080b03980040348400717000c2c4413840c030311034003c0d00080c02c5900b01a00c40e50124103019213020481006031480e40c480b4808500403401d80018540187e406003010088a00007400c01c6180900a04104901d810b0040541d074000b0b00c48041c0c480600104440e60716858044000c0080d401443e03401e10851031010340301840041c01403074204035513403a0710403640b03011410b8500420340030801101250030180031421132452402172040030303205ca40200e60480f030304007542c1c21030301c1d81034840b8101030a14a00c0406547c000aa400c14080b064800903826512a240c10701c448000b03030040c1d02c4010000082c0001d20503851440500c20300e440e92400304199032400b8400030f40120384418040c21682c1f00000700280080f07035041030400e00a090291415061840c00b100716 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 755424433 1250 755423183 755423209
    0x30f0d03090c050d0506150301240305060105061c0905010f0509150124081302060f040905010e160e030a020a15020708061b0a050d060303050c010c02060f190605 71
    0x19a4501d2020103014101854200401c03094804202e11040354640d281c80e0600184544200000c00380f541030707a918254058441e000784034142c00920a54001078082031281840156180c2c400c9400200d014030780103048414a000640200c3c2c00c0c002101c03a60009820302c000c054030155602e0f46035520340c600c94001c8034818955200600045c0402c14cd001e404554182c10030100d000d1034503103102018800c43c13155404090f580c180a12180e5484d2401c000750755402100075000345012079014440d80c04e40c000390064a44089092040d603032a600c4915000c01d04651503014200c002d08000440750145a46030f525100c081d0640c0c42d40c14054010843e45030f56948852042d00040181240b050341c103100460140c03c040004c0d00e070b40d081001604241d010f040d1484001e140b0002018030109000340704030740311040e0204041c001d1507903906000e040d07a040800c1c40714465082070060300031180302042c014800c2220081e14491611900024848480c4c1c3c00c00d440300310b9a507403c02040c180e036410180b9204c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 755425683 1250 755424433 755424437
    0xd02040b07060c0c081e07020a260c060706020904020904050108100c0512011e17240402090703051503100509160b0306090705040509041b0b040b040b09030f0d 70
    0x503a81d50740c90301200f2202042d00ca40c08000060401400050003101101c082e481044088089195000e61082c843d102d034000c02540200700510004403800d82118a03992034043d070100d480c48010400c421a11000c3c1d03840001d0b0b0182003003041800191440d03000d0200488003030801400c00c10030324049021a00c080c0c208107050381c0a000600c8045580c0e000300c0026007114039100f0304007041e401c0d004480c901c0c1030003003060070302c010158100000d0150401e00e004100c126082d81040714011036041e02c50a1a81500301c4810424070b40a031801040d5075141d00480e8094112145641c034048110018140500b00010340822002006040e903000c1260558069002100091508000b43c0e5145840048040081c5d0300c0c0c5404c104111000c144002d40b90700980569200007a9581c10104661521654102a034419821b0042c0b100380143d1005511071041c06076000700747c0e251210102080f5001314031508041700003c21080c03203104041000b420164a01804032021041c2c2c4200060502d030a000480300 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 755426933 1250 755425683 755425687
    0x307110a0c03021e0d1502070b040b010e1312110708250e0105031b010c0210020609010c080606070311010e03040e190207170a020f031b102f0d02040b 66
    0x41d4075081302d0404600c0600c80f2a07401884034840803c1410680c001d024024000403030007101c94540039011103103059800820703500d151a041c034108903a90020702901c404111080006050540200d00360070300280c1150611001e0203096004846090800394000c205024408001074038440410203100c60400c10b1a008038100483c070030607090010743c0d50000a0118103000100119100450091003001c0b4030075215500e05c8081c80103072104885d0150094110f0350510380301d1403455000c18014001c4506100034442402a804100c0e00d00030b080d240c0e26408007081142d000040c1c001d05552800d800c50000110300c2c6481c8403103490458116130303c100140303103d59040008205000110241e1154182070840c10145c840d25500000800718280450b03400e0f0003d51003003030714000c01403160390540c0f00c0116680d60f503548054003821700d6509500c07a0144a03007141c029520000d8024507400c003501550380c3c80140403000700c000c244020102c1c1910449002c104072240c0c0030503800240064140c01c80015 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 755428183 1250 755426933 755426939
    0x210910050a060812040b07150e1504020103051f36050907090e03090607151d1e0c06030c0d06060201090c0e0f04150f0f0906052a0307110a0c 62
    0xd0300f40101443c4c603110105081100780800031100042c2c0d03a0043c1c004100104507210320707091000400c0201c800700c46500c1141c841110700750f40b14a15038880d9100382e8050146889209110001c4e1115440d1a06113010348103017880004568590399400380315424900c030203180700843d42500f0301c44000404e241e890300c60040008401c010002600113001c001410001491880909502c031f008a20000e442840001184006d00c15000c100700452449520100502c1090b0b9454408000302c41e6055541401a410049142500001c5e1143c0d40000b00c4041d0102003018005c004140d480100400c6030007900303000320900320b1800c0c81004003402c0315030000a8030a407142400001d142d80c5902072003d84124408100d882c0d90405402500701c4d600c80da48002c2d17444480001d0003e08890350100140a04c0c0c80b8090b900d00e440c0d0741080940900800007000b9079200d1440340080503410760301c0500304c00382a10030801540250802554003c0d0f8918003a60a00400c121903800c008440600b5110480440414 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 755429433 1250 755428183 755428199
    0x90d020909011409120d0b010302190801061b0218040804080d0e091612090303020c010f29010f05090301090b07020607090e0112140106030206070b010602070b210910050a06 76
    0x49500140400000d10410100700c0c110b8a142c40750000001b0003c0d154095420141d01035010b50b000f91060030400b04000000810080c5a05000d100f400d0001d43c4020004645603034040d00c400d131031500900400d8820284404920603484041c2003201c80e2541080300041020090050321505031241da2140c00005c076074030400c25144000b41c41c0703030092426810381ea0003407500725140041c502d00445000c5184d03002402c0540090140c0d82148515509003510301d28117100c00d9000c4240c0b1114100d03409841403245007040d0b000342c0700344c0300c0c680400c4011400c0c4138040c0c0a00701500004100500100da5070301c0c00d540d292040c0c03006a0308040903034000000d10a445810146c070030058111806000200d6140c40791003c082d100510001d04245900c00d16110b1415080d0044005560041c200c0b642c0e4001c1441c000302d0a8409224410060103a8100424101c0305d0200f01c035107075910a550000e18803201c6d4460705035141c01420801207485090301c900c1c2c2a095500032144100d0142c000090503518000e61 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 755430683 1250 755429433 755429471
    0x3010603051f1401090f080d030f020a1b260a20030316050c0303040c051c0f110d02040e06090111030f01090e10091101030f050f0705090d02090901 65
    0x710b140c0c5026150b40481c80e8440201c960103c50740f09140c000070040d2000140c0c1c48542a0304209006070401d800462a0f010004210300c40e21500d69041100e40c4001c0014400ca01608448200040b01d4003044034900c1100540b00b00c005024031408454505156243c400d440e514945920f400300b40450304940340751700140b0301080a100b100c1d0343e900103100c1009107520b0b0304c4010704403880592184081000c0e50300c20010b590780890302c60112543da0a041c00c00406038492441142c1c03041400c1e62038142c1041001c402d40300b00c26407090308140814441d030344000d264000825220741111068152001507500c90142540d8122410040c110310704160f481c5030300796181c481100d01051001c00a22a801d503400343c04a04540500308000f80210a600c03c10b4200f04a003880008183c0c1031012a20601215203480d0a0300302e02620200a1031000251310403daa400300d4400c07500e184414006803410780104000e003080032000b01107039510121a80010780556083d100b0220580d034460540040009040c5 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 755431933 1250 755430683 755430691
    0x29070b010614090307091a09040c08071e030816050d120e0c03030d1a1305010602060105100c021212040f0e0603161502030f18040f060f0303180512030301060305 71
    0x400a071403c07580c50007090303440c1c2c0f6510034100c200381c0ea5001080580d000c03801e4280030000081c80310307110707080604010607a03000602668806010710b10740011101d080340d150340004903600200400302891511180c031590008010580141c6928090307a0000c2ca080c80248050031090300c80c0e02554081000240840b2426003108030301740e11207111216079a400106641305501e0480001c686c60350004100c0070441c0c0c10102390381d0455030000072140c00924a410a60603a0244d83c201da106030ba0380c0b03041041c001c2241f40c1180114144210580150419441e069000380c010003c82d4900b01c0d150802041c1940243d01282e05603140c06028050a18141e10160f0000c00443c002e0070102e03000080e0020a2029100b842c14414642e034009040314000d006036021085103484140d00e0703054132110282c0b164130030090745d8416031509140a005213044e10888055401914103159941e085640075660421052200c1816081d4610000344680e1002d02d906181c807518805151030307514100029040e1140a4 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 755433183 1250 755431933 755431967
    0x311030a020c0d1805090a11040b030f131110090e0c04050a05030a030e0904150c0e01110d050f0c19050a030801090504050d0302210901150905040c29070b0106 70
    0x3094804c0c88100f00e440c41404c2d0b071411a41c000040c3c81e0102420000c2ca50011060f85071000460300045281a4501461264584d00704035441030b0b0b100c401a01d804c1c840c0308801030070722010702e090002ca400c1c103820110003044d140c1050408580c0341c10301b103c141c080440d0851403400c0000340601250906410041c0200420307030041000c07112300d03640076182d900c00001407030003120518006001c0c0607103147c3c130b401055080001040410500b0200800d0482c030507440601044010030070080a0100060780041000c0641d511400e00024000c296003541c000903001083d881030300030209414540e02c1004200c2807040000303040d1a43c241c503010f0080070b4142e0100301d40620f414100000318401050f582e081c40360604c0c005a03100b02018408111303840c9588070300104020401042480074056000f940034048840419210f50760b03420b0710a042d51001c41340205001c80750401040002c40200d980320300c803001c0c9000290030080c048820714203030704038820030758902480d54010000540c010100d10007400c561 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 755434433 1250 755433183 755433197
    0x10207081203060d0f06020d0207020a170c0402130e01080307030206060105071e0f0812090106140a2612040509060406060c0b04081903020418140c09010311030a020c0d 74
    0x10070384141404010314050040121300821403c01411040a90040e640040d04544448134100c030040250460314089005024007400410201440c4006c894401c00d203500802c8011180020f00c03000e900034180c00b05c15524000e0000c00c03c000880c2d100350180c0884002141c5400060400070b14014010341200c2c10b001d001c00c4400e01085045c07183c40d400741e4480b81d020b41840b9042c40e10100c4103400c1000945010070126031400015111040309025501c804000d106441d2525a4216580650020759034000780c65070317007080900711142c42c4440d0071282111075401074400701d5455051030503801d88040540d00000c0d046c004c915001411581180094404000707045c1403644c080c054040955000d054020300ca400681007022002c00c68040e0741c442c081d0049065002c0001401a4005014103002c41c4400c1c94102c149003440c0c42145002d0300e2042142c0c48c6901c13240c648804641c080c0d0111410103403682d40d040d12000c200c4000f98001c0424580c0165186620fa401070704211740e41584500300144 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 755435683 1250 755434433 755434453
    0xc0a17060601090326091201020c010e0105011805040618141c0f081f0602010b0301062102061606090b0405100c02071502010212070201090b0c0915090301150b030601020708 76
    0x5c01e10340c3d841a1540404500140390030b204820390702400612070750080c00209202051801900174207482c22421009000c0d01460840702c88c01d880d401d00074401c0e5180744400c84440e48007150861034105001c1c440000d00d24035080450041c0480340141070f00d2956200820441032042005080012001070142140da1f0f6812000104400c0301d00b42d021040207100000b05108596000c102d4000e4203400c0400c0a034a40d41e210060701074625840307540e00ca94640032001404544c1e0904100d040c4086503450803602c1a0b907420049690000300088680b1803c80b4844800209644114804180180c1f20f41441d072a00b464801d24003240141400900c0e4185032418911a400080c5e00040d18036843d008a0b40c080496402c0b030081c090445902c510456880901c546980c042d80010000c070b00601c0e0f102043c3d030703401610202c0fa214100b149034118506c0003800b4112401c1c3d1025101d4003000500120b0f540034510f039490700180c02a0420b586541c800401e004566804100340070080030130001414802c02 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 755436933 1250 755435683 755435693
    0x109050402210f10060807090218010c15061404050105010c020a031226090705010f141b061e0a09030e090402042405040c051213050c0a170606010903 66
    0x6502c0c031169044048410800007109003840b4240301110140100c512030a8070f6002c4e003015040b18400c0c040b09004191010400a450740201d804005001e0100380c20040810011162100f0404054031054214201c01c0c031840110b0003054000d201c200c110b20180340204003000304072030040e07106505109664500d2001600c41c040801c003140d0300880c284191060022043d04e428950808200b504101032106284403100c5004241c054801c0340c00f2038000503101c5006461402071034101002080d010f05c43c00042c080d00900605d00247d01114003070b0380704804003025140420a0f1000701d0301e580040001d252400c1c180c00d0165000781c4040c4280220052514040c0ca000b00c02c054690095203007500007000e5494030740251800807502e452484500e0881854001c000d049402554400c505144540414620a00580749400c41c061007805d400e8440c040b014140c0801000100c1e82c502504650420380e5a07100b6040d0014404000d4540e140c6a01580880c24144020030301418002c1001d001c0c00450 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 755438183 1250 755436933 755436949
    0x5010b09011d03030d020a05070b0f0c04030803090307060e100b061602011128031b171e04060201090b0108030a02060414101802010f0215060f180a060e0109050402 72
    0x140400d10502e540c28000001c2402c511912007892041400051002010b640c4030b0001d209041c080c0f54110740c90f44610108480f00801a100040040403c1c0014808201d51b40300540d04810440c04480c83c20340b00d523550303009848803e0403207100c036004504030380b0b2031005c00c2c010a8000d000c04c035034041c540500202c3c41d0038044a070b050068100305c038415028004450422112180780c0e05031103404841d40e417a2242009606106c4001c400044d420014810084903620b0880c0410341c1c0403228080c4080d84044000040e007080c4207410250a0310781c2021161400321000740042c001e150f0001c035041c0030704e0918400729001039110343c06c1640204034120281b54085002c1c1d4005903c01900000009440c2d901c44c54400982e0300c2004180c9400d8004040540c03564140d00001d20030703210109034002e00103013039844c0c0035101c0743c8040229608001031901e01d488801b02c00340b940010400a1002440c3d001c1e18082c43c0211402203034207aa800050144050441042e401401010024046440c003580441c0d10b007 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 755439433 1250 755438183 755438207
    0xf1207120306081b010c02041409120c03090d0203031204050601230d0201030b210a0308070503101a0403080c070801060b180d0c0306090320010c1e0e03030304050a0605010b0901 78
    0x42910344a011400360302c01e0541b4039019400a100b4018a001d41c600160311f0f0b42c081d11520b41c180315602d056020080000156148004841d01440c1040450720900c032403110f494038101c7c1d040c00100295461345200a1171580942d004100900466060081010040d11071039002e1300d10811116041808d91384038014035034043c0d42880d02041144500b070109041032844485d0402190f11021707400000130300043c880540901075603c04246848a010650300f030b1109840762800c4040400c002c0c06580404000300640e803100d850711916103580c036240c80c100b0341c12484c0a0207140e00880c1c4200040042405080301078003840100914150f80c0c006041c22a4000d21710352805403103010950300a00070761140001c01540c0000c0107202d10301c1c041c07800070002c0d612040202010981780c40c51040804c0d0501c07904040c5c0419845030065100d0411019540d44001c4c06800c0400000d20b644020603103052000d10b01547c41070000382642420752401405544050b04820103511b810700c2107680c2e036a031201104880e = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 755440683 1250 755439433 755439463
    0x91406030c01181509150507060506010912020108040510090501060e0c040819020a0b0705010b0a0b0c070e1305120a12050601050a0c032c09060f090610020f120712030608 75
    0xc40e0084c50165001890b9600603800c0051401c80340d9480d98210f0000c0c030117588a10f40130469a9500c42c0190782c405118024200342030669181a40154005c504403a00680500d0440d60104c0c2c40342e0700c200c2903400008045503140d4540c0004c001d1070038010340054100d01c5600b49c0904213410300c800c640c0e680e00741416140d04000340c85000003d41d05c1e145501000b92103039001d400d07a04c2902d0704080d070103061900e003164002c080c040000140d07481044155408200005c02400300300d40751203154000031001422044481140070540b60000714200f06251030010058601511102d0780390b809001c041c0485803044509003450200451a81c0c468110b40005d4201e040c005100d510342c0c207048500c001c401e0b00c0000c41186200489042d081041611003041303008803588442652054184106040e008407007540007a006400701740a498228000400748000d44120350044081d940041c0c80c040c0c2403034105000c0400082c44205005188005011701c4040382020300c05189030904290f82e94441c420781c034030 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 755441933 1250 755440683 755440709
    0x151608130f240c091e03030f0e061204030306081501061403251d06070b0424060b300c13090e07060201180804090f06091406030c0118 59
    0x51004200b0032120248401020402c4401c03602200034000048a0082015640d60041c5103225514482c50f8501a258165214600244a104281c03104661a205c0300d42c0000c0500c05140141c19503010300c0d210300c0c043e940120f20706103040011070030308410005c4406403443e0580184800b07604160b402440d040441941941c0e9075580301e4131030344c3c217880780304102081d000560b00b43c1c000e951001c00606440106c0d0300b003a46041c445400c07c0002d106500004084203004c40005020601c840c0d00130400ca512502400003541406000d08112803064010f80206000460260781c03030070191194114070032005034070090740c9401d0b9120300c0c100d04004080c0455200005858807000d89500865002003e4101d070501c04032504c17160309902c035005805840c006628054540450440c0c111500100b1a0425500d601d010704061220740603114000b60f90100649510000446040350b100b00a1000c220098903032083c14003804040c1040b1000d050383d8100702c510401c120300d00c1510380da1a4115070321090004 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 755443183 1250 755441933 755441963
    0x15010c0b0c0d0e030315101110020901090e0910050606040605030402090c0405181608131101140d09050c0105040b0d0b041b080f06010c081605151608130f 68
    0x1001a29a880f0310459501010041c0620a03580010020000c00e00b05d0302144000d00000040303c4000b202c03840301d4100d90150301038944521040c4d00810321010103141c81840e0381e0302c0f826410000041914410b031503502c04011502c0040c440e114454200c44101e03120340c03a2602d0940024180e000140000c5c4c07240080c030000c180c2046120f41210002c1c41e003d00181c8030100300800000700f0039001c07601c40c005405d0402441000502c2695403c1c800d1200031035200c04070783c00e40c450070301e500d864401032410301a441d01d070445551100c00c050030b01e002c840040440e000000b8070f84142060980c00d200340c1444401d10003440710a440c0010340d120b00304050000545014881c0005014220082c1d1540c104e401d0282e4020840d80e01c007031803601c602090f500c0020395407182401100c00140303120340901145010310a01c4085109001005440b600500441d526003007070003010410902c00362444804521489000520190001c0c1c2040d8404404506040202c20540741c2041070350b00c8940090000719603807024 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 755444433 1250 755443183 755443207
    0x815302a12060c180301060302010c08070f0503130302041401060815030a0c031209060804050a140f07091a0406211a0708040212060910050c0403021815010c0b0c 71
    0x14048405140c02c5a2040c1850b4290300c0b0150f100c003441605010f04001c424800d41014012042100d506a5030b04200d03103010b441f40700607a04001c03030869003141c0034442c000109070208041c080c0d6949400c00c18440600c1c61041000301c400441401c1c40401105004100031030700255450743c0041c0c0c0c05046014060064002424860f207a100140511110b07607010043c041c8098200d88400d010f42ca0b120401a204c01d819178000170100c0d00101180d101d03004450000e001244480300003205001203640b40b80441c820241411400c3c0c1040032081d0351056400c03821825030680d20b003c0c0710151003c02106007484820303111014002902c041c0059038903400001c010a29113285021031407403503000724034102014000c0404d90182d40c00c3e031290249041e0003d0240c000714041e40030707a410306d0062901250ba0f8540001a15008004c5410980b042c0000009078a900801c642044200d041804041c07600300c5012a400207921003d80c10800d0804007400054400c1d81803641041990340c606840b451030b9480 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 755445683 1250 755444433 755444449
    0xc0d08100909033906050612120d091a0f04200d080c030c030403151a09060f0111030a0203070c15050a0302090303090a12050d030209030d0815302a 65
    0x20b6000c0d0300c1c6007442c8130074400c5035071085000b5141154a03a441c0c9950b45c003c907030795100d801c105144001d1700308080210b411007548202121849940300c1c0d40c0072458081030183c0d0020448080030340140c10001c1004102c14001d60f01d86000b400415003142d541e034100800d03450943c1001c010300e082d400081c3d154141d102001a14010100e88040320754654803803810654400d00003025010300750600c1650144804031104035a036580c0c0c06428100d00e69240000c07c50b10540c111002c0d03060004950030024880c206000504241d00c8503001035a40b422180342048920301140c1c04020046444450b10140b50703800f1003200c0c00505985005078888000200080c01d610030300301030079400034101d5800103240346040403001d9294060403e6885c180180e007825400e910886200a625400c0103290303021840c0982002600700200074100d60750150281c001c40c040380700720703508100000a840d488089103100786944803107a9405030090001e54452003c1546110b440202c0e40104414070b4100507000c1d259401 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 755446933 1250 755445683 755445767
    0x70b03092503030e01030507050307050717190e09040209011502030405040606030608150f13050c030604030201090203070f08061602030d0c09290316050c0d0810090903 74
    0x401403403001d41c002500c0d4010000744411400704014a54604e05980688078092081102d80c554615594078401c00712242c0d4410759040390300c1d00719840b040d18145100705c054106e1a45a00b252030b23000054100c060148002d00103000d00c00c0040354100401078988a003018112510607140c0390140482c2c3c01c05a00b907008075005990400c0c909100014402d034560054001c858540d000d450662406920100045074215584d0320403410342070105070540740385401161424010410b0360085201c4000081c10213000392000e40050b910342c82c0032070544c0740501000004120100c140c41045103070902c0c1039111000205141304640310740801c500000e00a100311555090760410400445002c080094018401c0740114000032842541580e0940e40ca41e10f04d101e4249500c04090030b580c0c8030a50710b806034584080381004c010090040c007070113500c1000300c0e01f440022a154040546441440c06c03610300c0c1a0340c07001c42420700b00071120002c01c0d00000b074800b20f54141072010100760b0020900319102c4410107 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 755448183 1250 755446933 755446963
    0xb0925080a0f0203101a0907020c0a18090c0f030209060307061209030c1223040803040308160206030c0408240711070510050c010c0c0305031513020a1101110408070b0309 75
    0x2034201c111128488031000c030003880403a51a41e40d500e80b008c049130383e41c0d4240c1071030782c0000121005115030340744440302c4104054800b002142e44c07501f0740d40d00102900346902154690564081c1801180307041ca42a0350b0042c0260000d2880030301d004401001c05444a40304540c059464006c030051511420341c2d5001c054014004203106e0300003403070003006c01409100241d90950091150690748014400f15021038003c070008504240c11615000c2c0c06511070100d5110604040d0310800050300d1304005144200003841070540c4403454103074458101040d0380d840b03000e100c81c940300041400c200c0781303900c60b080611860280380c4800b0b80e0000e28940500c030f8108640c8200540c4003401e070991311400401c0c0c4807241200911001d454148280c414840d411402000319a0a00018199801d891100390862400804428068103804450b104a911884000000402914680c0a0801d007405052051030b014004189000e2424105a840341d41c2800703450391900d8000041030070502c080213010031250000c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 755449433 1250 755448183 755448191
    0x601020703110a030b09150105040b0f060f04050d081201080d0516060e030c0c1f0c140307081201050405130209010504020919060e0a0e1005120a0b0925080a0f020310 73
    0x6c4c1c551a9961401c194540000c00749500100d02402c16000c1c9107a46000540f42043c64942101041810340044001504014040c840000c2c130b540d4440d00c1201c514001c8030f13226500c1c04c1c0600c1502c100d500581044500d03900010007015890350200c1140c0f8030b00b1000998000c0c002451030000301604100d8480364080c44082406400039201084002c10802c045400c4040340c14025400001208010312000204151740c0341c0e03d0210700070000300e9800c031101074252480d0028540d14019603410410110810701600c50060006003003501c111a000481da00000c11510421760009803e40d005000d154011600071659440c0303a250782c1000881d02d10000f610061031a1201700062840400c4001c181c4983e40b00e110020344004c0d181c4095001707240d595084a4a20306101c1405965640c0003189510b6104000307801c000300c1c03034402c03400b40103a800c94064090702010641e00c9440300a805100d902c1c00300140400c0000c00da00140b5034411581c01a032000e01c000c0c030f40c000a41405d075840501a501410 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 755450683 1250 755449433 755449441
    0x61202071b0b0d2901030e070e091c0813030f03061a03040204051f050d030504031a0108010606020f0c103c030207020d02150d0213031101080601020703110a030b 71
    0x1440d400303051401c01c0c031002004180e6030000c030012503203040f09188070301e03241070131404100d03520035040f02d080040b00741c003294034440c2d0303640c1c0e000c0c3c1c03891003241c3d030310b003540c000d40e04260300030745600b20020359216640b03402c002e01c0c184503220703105409000d4001011300507100310400c2c4083c0a03400800c001e00700040b10101d008502040c0749041d9104440803440b603407030000020403412a926215001c2003c4030804110303a401c200070b1080c0b04800020030390500805010000c0041e170000c000264819406d803103c20154034110713038079094441e41e0f0001029074002d5032a007a040c110000b520310f0054002c0328200220f12511405031214030000304001030036100700c0043c0d055160064140c03030401d254014200b8041d01c24840840490003400d50003980814a04845c001519190f07444194030310070009210324120154102404a0780309842100c061103e83e1800c000780500703992451f0b044182030908007a107181040000b0344614407404003c214410340d01e0040403a4441a1451010b143d014040c0d11507400c0c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 755451933 1250 755450683 755450699
    0xf0215220609060e071a0d1b0e03010e070b07060f0f02130311150a050d1b090f090c0206010e0a150902030a05090115140d060507200601061202071b 65
    0x5800310607912182000d03860603035483c0005e0900300715034a00d1131107100e11402c281010aa0780c4110b15501c98151100600782c00e0092212001c3c08060440d01c3c2d81000d0510070042c9800c3d540c04840c40d06540c0c204c42d070102700c0c4990740011551601d521810009801c0d840d503290308010405101c1c01c198032440820140c40e9000701400490669015035510081c5121b4a010802160724a01010600f12424002d640402d40150041e0818140e048400318041005500d009038504c095840d131000201b211804000002c5124000c01c0640195182800720001031007010b03590380010700c1155542c0140d03600055000d000d980c40040c45003141800004050350b0b592145001c1d40007555100c9080c1e15200201c3c1d80700505114244002c0c9a11050480030780c503108644c2540e050000d04550000b0f228898240081c44038419070340301d0b900315101d180d05108000322900c099410000c201c1e2040d480741c001880441c0d0040c2c61800740306010800580da40b0a145801d8180d1b080e036200300f40310081c42c07100129800e2 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 755453183 1250 755451933 755451941
    0x201031e0903021c050d0b0609090a1e020c030403030f12110310090b030c060f0c010504061406010503040c0b07230c030c0a0f051219061406010f02152206 68
    0xc0e00a41c00c40704c8011400080106400c40c5a00140110f03104224080c1e02e2011604030071000c2d04004d10f9142000c4811021550640e412a1117101d1555945010101d800409010403810f0502c550114200000c0d10701c5180e481c841c600000e8140001200800d11003481000124101e4074605024480711114803980030103500166114240c2c0c2c41001408500b1517020302c601040504001c004000c04185c0b1400c0c00560740c03141c01500c0c0ca14104005101c00307008240035040c010b86c813581c000500154401044101030744058011810441e080040c000802d90481359501900c11110030680d42c0c0c1240d01c0e00030401d032240c7c10b6100d000d03c80381c0c81500300d044000c5002e0410080c183d00f545c43e083c505404100d020708180c00798000000d1b1059003808182004070100701c0c0369203188100c4164036650703078036009418080ca50072110741303445400c4050384207058414a9008202130a20103206035441e80302035210364500505414601c0310400007440e5010178000d03000058844280701d07120b1801c0c0d0408001030 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 755454433 1250 755453183 755453201
    0x12050712060e0c09091005060a0b0c03180604081c121b080c0c1b060c0109050d0908060709030f02040609110c0106350f01110d05060406030803070c0201031e 69
    0xa003c1c2880c401c015003424280644141c80d5503014241001c0c9076800000109405000740b500110385220208504003284002e000d003c206e0001191100d8a10040d04c3d5045c451307101c41801440300344401c0089043c0041c00324142c6000c000550490400303540d00321501d060b00038031a141d03035080410300070408001105511400360301d0395400000f039071611240401440380107250304090380510402e05043c0d103d2a02c038500c03191300610551606004031405030954041000640d465003054080c1c9079002d82210a00f8014142d14024082920b4025005403e0305524400034240c1c20301402c00f0000c650b519800140508840700d42000302000d5080000900e40000791014000d610f0b0a00c04203940744840c00040e5900900a03400c5c60040311000108031407801024403101c02c0c852066600ea0b441801e004000c4806034804400d0707262400c4800c1d81055800c00b034000e60080340380c25024004a0081012a58400030f40e042c00d407401e8500e480100c0c0205144038921440d04003800210140e200309804c000c0700 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 755455683 1250 755454433 755454461
    0x30e0a090b0f0904150b010c120206090615130906090b0a050108010c0201090f12050d0f050402180403270b040311100807020d0305040c050405070201141b03011205071206 75
    0x2020410030500502c10404d40c2c01503c8104440405400200260884a056001850009024205a52402c0c0780010504400c80941c0041c403c0005100c400c11020ba401717020403018040b446100ca003c124000203c550000d6000e40700c6110fa0107104842d0001450345912101d9a1010700c0e05100c20303801010300780150041075081c00c0311544010f205005401103150001031685a49500341d46601021842c20f0208040c80b1041c02091020714507132054428420b805400442d0382d143c41d2042001c08081c09030151410403001040c031011aa015200c1e4011034864095148584400c078211500322021703500c0900c6c0a440054044100041c0b003690b035445000684804010b884401821380f0000701c200c0e60000141c5c07003078072080c005602ca900550f8000740608461104151100042003c1d180d041311032501603034440010306aa602600d40c0030340c0c031000c1d1050b6106008040c0c002d000403480188100e800b0b00c0c4000f403501081c02001d00c4041c000340191041c10303014010900c3c1a002420b125803680075 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 755456933 1250 755455683 755455699
    0x3080a08040605180c091320130c02030a0e010519021b0f24090904030f0927090212031b0601050604060f11010b090c0409060918020904030e0a090b 65
    0x100314013001c02a150810b2001001d030005611700070a012100d180204060003000d0394200480c003051070f903d014003003000f5203d0302e5889460784800341310368240c000c2c4501c40042d18001c0f103d6040390703021054074040310403803405010381c951030320040380c3c2402194000d02c1d8209030343d03060f1400c1c2a00012400c80c032550010413101345032030520070840303a00082c90455811000031581c14444c250f40c40c00748001c1c0b10b0185080c41c1001402c0c40070401804007228124082220980c4000d00c00d80c105090500800c600b04d10301240b243c10015a8106c000b1102902e415540c0340c0020204554501208410703c005105c100d0340c44035400744e1401e01d1080002d6002c40c141c0aa1000402c0f01d041a2048070103880154407004403080080c501101c2e410101c0000c2d0f0000e544c0d03221410640c0e652409100d01544400841070b4031541401d40103800c0303a401d5480f0716402440d02c204a0465101e81c141904940c0e011190350000d941c55080a07100301010203120f41d4011b000050214508015a0004103040402d842c6c00c4 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 755458183 1250 755456933 755456941
    0x28061a090105041e0305030a08061230040815100e10050d05010216080d0b0a050d06090c08120a090e0f1b0909090a110613180603080a08040605 63
    0x101840361514490008500700018000000468200480d100b07209040400159807034642c2421034010070545070010340b08100b4001030303107007480708001201032601c042d01c00b80400081450b8480c80c1102016011300d140903e48089904160548004141c3e482c10780d200c01c1d203d070b5403030070700e0480403910040440c803800008a50180072001c0c882c401c44088c4415682c40f8101020040615045d100446466400300240302201900135200007565116030440343d120100300000034250340302049407600900a1150411555a0385800c04009a4002c07200042c21130712410088000da41e15080840c0c244504e444070060915504014841864240e840f0203280384c40701e80501c080c2da82a40c041150700c2c403103030219550742d01100d544680010034000181c50a00c450000c502c000104554000240e0010b241c541c051219514400c07250980445055161821002045180080900458280c41e136202c402075000c183c1d5074000310145030070001b070641364007038504001c1010104a60403202a0308201c003003 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 755459433 1250 755458183 755458229
    0xe0d0804080d0206161b0c03021305010f0504090c0b090a0e09100c05042d150804021002010204080a0b07031d030c07050118090b030102070c08060a0c0e10082806 71
    0x24105a8040780d541080d400940c803402500300000c0401aa60501f0502c80040142c1e030710144803509440a03003012889614060207010008050350000b4021410f020202c00080c2220051005540e0b0514695444881d08404100102403a030005e40c1c0491040091201d04800082c81250102c4440300c14401d00900e10400c40302c9000e203103d01461400010401264401528060030261000e216619030850b6200e403c21016103142d042c2c1d50100d45404140410b5040907130000706041c9146c002580703060b150102403039036102049405080b1644900105031041c1c425006010f50444c00d034111102e8031070b150070303042e2281d00012162041c0c4c07080140c009078030b5010b00302c110780102c0f4803140054050302d000c1c262809884481d0722503605550821406c00000e000421150140880000070030503441e22001600484030300c002101c0a001d12180403100a9036070403010a1100c0b000c1c50400c08988035503414403040403031041c4c007851800300e514a40b0b00c5202d071944104101c83c0c0c1032001c164004005030309 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 755460683 1250 755459433 755459461
    0x3040303090509040201110607120605090c0406050c031e090f0a0503061305120301080c0a120f1e050d03021312050a2a0e0a05150d030e0d0804080d0206 67
    0x10081001c400d401c0203145081c40c0b07800c0d8032a0043c140441440a500034003400c3c0310080b20300e0030110360b89404450f40c241c01d0b8417408000c0c00c003c4d1a5804242043c51081140340202d21604040200000b906010440180181d6003000070f29074452500510031049944d003500907812071401088205040035013460300c0304500c02250406000b800c4661213030184e04083e0804030f00203648030f10401140403521140c0c00c000754028010f4002800c0040d502e0700800c010424a64040c2503d5007408038a10003143d004208030525a40c48400690709016000b10340011140b0900040e040c1c2c0101030a005d885a0950001c2c0b100c42600c90418003642c0d200c0d1010144a40000000f503d140d003c43d0a443c0003d911078840c00f142c0750041040800080e00514030050300c2c10315001300480d41c210605000c0c0c800424024981c10902031003418484060070740210301d5101c0d0013900a010841d00f0215134409898081000582c942c1000006a0b21901c3c2e050302595180e0340402d000c018465840002d1074a440010 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 755461933 1250 755460683 755460689
    0x307082b020304230321010504051f210204050f040203060108070e040f03111609060902190c08130803030411091603051b07050105061e0d080d06050a0b04080f0304 72
    0x41c1c0102c41051842d0300c011320900440b0000590b00c000c001c40d003c010303c0e0500782c07200d40d4005103100b0015030420092006461000c0c014000f0740c410100260700c078040502c510310507030b00200c00c085100d8491080e18403200c0080c84002e03400c980f0f080c007440711500010703c0a03481213000b42c0403186683d9850418684d500030360302c5141104803806000c10000340407851603862441c000c0c034142e9840070f01203640c1070034075080323044c00d1300001480c002c2048801e07118001d600050035544411409d0803510020a110707407010b80c010904201c540d805110410211070141c452110009502c503035041c1d250090356503203600c1900d0985d8046c0039224180d1291070014070b014803501d065001d10003042d607001c109901800000d006005080d40550341c1808410289028145990040303002080314108041405801c140450f200e00c00340718420a003484e5070300c8108040d02c01740d034842d10880d0789440390036104005001540010b42e00951110780018102d40313400240c401e9481c4002910005001c0e500c61a0703407445070384 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 755463183 1250 755461933 755461943
    0xa150f050105090402121305010e011a221d12180d031101090b010e0f0103020123040306110406020d110606040b010c060905013804020a020307082b020304 68
    0x16000d100c6540718001034805240042d202505141070f0041070121180e048a10050500c02c5540410a0043c24000d0140324011540200003000000f110300303100c0180114594000d00403505030300380720030350030518400341080f51200700a40125040d90340407410841d060b0607407500c00c4050211180100000321628160340003040c5540b803410700c007800361065482c401a02400000540d4200c0c188003030080d180f0681c4682244121581071089000d0901c201a00c0201c40c1c43c2c0c0c0f4001800180d0b00002d9408800b80b0442400c18030152814002c0024071071604003c0c80e0a041030304080c103846044d00079009641d0f20341c0956003000220b1500300c0320100c0340200025503034070100220b01c0340c0c02d1641c0800d00c00c00b010703d40b001c00080e45407500b1040e40c0103907130304503a560b540e01205155540c244003504080001e07181042800c51500400000e00403500d401980308030b900045010805000b04212400c0300d078030000d40c07501ca02814520440001e02c920300c50f208140740d0313043d000d0b0714122031088a01c629448 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 755464433 1250 755463183 755463209
    0x3020412030c030c0602041e060302070201021e0f0a080a1b11040b151801030605040213031716060b09181c05040503070f08010b0f01020d050f040b030a02030a15 71
    0x19101100e0061081c0c00940034013101552503001300f45580014405000c0e9181703a400050a00c40c1e46003a6a40242e02201c101403041c4503040050380d0100301c11940c540d4540c03d018103801c0d00319090f400d005603c1260700d03103446822140c408005078440501802025a01c5440002494945200f0b42d00714200000301b07a103006003400c24061038158084038100c44040c04c0c07002c3c00321410038504c40a41c4501c00d010b4a814400c064400a50303403501071080506010385c0c043d07052200e1920081140d00003804000d00361151701c240900324518640c20b40352482d09192500001c05031600f4070300010411112418007540d80f1800251f00901e6400583c0c05600019000307008110303861a03040b9508001403000c0d41004000c20001411790703420095100a06489501c0d902c082c0d14000005007125404600d19000e8144030f02075282581c0c0126121500008506001c0e56441000461203081d00c44c64018a5030300b00040107002c19900f1960186204070000b01040103040c2c4107240110902180d4841e00042c00c0700 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 755465683 1250 755464433 755464469
    0x51f050a030b09161712090d0b060607081b1605090103110a05030708010f050105120304151e09060f020a1106130f03051f090b060904050c0a03080910030204 69
    0x582c6001c550000e410310940b6601982c1c403060071030810080c2e01844101086081d0140703001000d1000c002102c0c01000070302c0c5400c40c404003003841c1007081c690140840401d9000280503885040444826541c018031803642c428440c90076450303099042020f55a10310030080000080380c0700032188001d80300010704c00107480c0c1c40c0d0740e51510602e0032031200740d4010012420000f036075142001480040c22120340082602034490303001c90102c0340168803461041d1a06001c0c4940d801021003103c0980f24005005050301c0c20040042d20781d01e5024240110810010100e8030765030b9442030030031081d60b800303958440e51041d000c40d04030b940703020a1002800307490f800d52006505180c641d000b86480348200003442e0044da0355140c0080d4000031a4010356440c0c02252803886850440c44c0002d4546040c49420813220310261210403071a1001042680200c240c900410244032081001c48500340c0e0040c0916265900e038038107510980c018800103801403e00385c00da204a01e0003030007900c0075660900e144000d0028 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 755466933 1250 755465683 755465693
    0x50c070806190c0323071b0f060b15070b0f010509040b0f180106080304090c180302090612060414101415060714070609090905060a2a03051f050a03 65
    0x1040c0010f01c400c1c10369030589188500c008180d07100c1c070149910300c40d0f821880c0000026102901c5118200001041700012200052803070714881465504804002050054000400d201d41083d40095008a0003c00c120b0200010040910320501c0790000160542e40d030b07001809680c0d0300c2070781d00074800001d1900080c01c03800c00c1c140403588800202014803a01441a03111801c4481e281c015001c207400015050003a01038074000c595180c1d40514001c1c1c101088002110003c94250200031f1149502a01140381a41c070044030711100a040c1090f50b21604151034080741416180107012100c0c0130b503200e5003628504034410710034a8810120455095520a042c0c210510584580a50b101c0c005003c2980031801e50566071190200349030080102c28141400030389422001e5014400460810499100150380454080d400c070303032030030b0380851808020140194500040c003215030f981e40380710007140e030b40c90760580206014005001c030320700d422010085020000035040c0600b40d0025035100301040090 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 755468183 1250 755466933 755466941
    0x30601150f0e18060a0909051b010804021f230a120209060913090506160210020f09040b031e100e070e040b040804260631060b060a050c07080619 64
    0x1c01c4545e1040c0c035a07951004503540c1e0041561664000c060800c5485d01c0201c21440c8044242002d130300c240340c10781c00201040c80f114170140d21511000e400c14092401100300c0031000034101100e04007601c40a01c03155468001100c074200190030a880060400c0d0341d407003141c098000191183e0700e0102d0100c140810541c04102011a4903070f03904007000807a02c00d010b028020103107000950303003011051200910741841c61200026940c4100700344076408034030324201e825244080d00d0105280c0150400a42003104000d25013201503104071060441d40c0c80896414000651910304000b103910760861fa5130348800c54090306c10b0f00e0400c01d0118000c14050041181d00522420a6034a45a10358041e29459422000003400d03984117481e201d203140300c043c00200e034044400700c11030107031030044495000c01c000c410040600c481000c0d00d001c1c041c0720458120100040015211550398500d2080007080c50380100f00c04840c9000311007002c20304001c045080350064001078081c0c2403085504150304010 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 755469433 1250 755468183 755468191
    0x60a05090105040e04050105040309080606030d030e0c040f0f061d0703150f090c030e030304030c02100311030108030a030c0903030e09061305090604033c020c030601150f0e18 77
    0x102c0400c0c440040c0e200b1018082d144100c0c4284c0000c145030a09143c0900a201c1072f4101e00300b15000f0301c08100d003d440000f0391101e08145490f0110350800c0d42d1466034140b6022071160f540240c188000250a044260024001202c884100b0040e01d561003a402c4038001d000c401107030841540c080032845261280e085807088101c03440420f40c00c0d65403000000c000f038030b00e07a0003d11010f440e0149101e2040d01849510914240e07500554a5864141e07401032041100c240001e102c3d1510200c554507042c03003680681010344032900044d07038035611840d0a95403500190902c0002030f04010740e00d03002602c500b035000b040380d5061b294611a642c50398200085000014074450f00030300a100040d00710540c031302440d40543c28410107414182442d0034020f140c11080305400c0002d03c0e050307404054500e841101d0380c030182203411b00b40780d90442441089007068006000c1c0c55140c07042c6400403550319035205030420130b61900e0311807031080c96080b1415940904800041944858a4000b040480300e034200301c0c5907c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 755470683 1250 755469433 755469437
    0x60a090e09190f050d0912060507110102040806160221030403020c060f070c0b0f0913061505030a0c020624010c020a0609080610080d120b0901150f030902060a050901 73
    0xc0030040b6a1140350809400503a402d5208501000a00c5800c0c011003c0e14200e6241940c0e00d1403c00c2120610020780c10b2006000543d50400070703001521400c2d0400401008100a65540d9640c007621650381310207644072a81080085201d05c072480c000a4486d0554000150721000200c203103402040d1034100400030f03000e60254000c04007041da6410001c102e10b04040c3e240640303500c440d080c0441c4400c260741145d07a4800b410440084105a0041602c6040208940e50084400924003401c0681803d5001c042280c1c1c00e484030107451074010000e140b28038840d000411189400f2801240d46070001e644100d000404101400141a03910714035140683c0103040016a009040d80410000b105030b0780000c0000d4a502c205104d10f030014001d1503000340c4180c0307000211030709104041741c580711030700700301710611160707100d10745c60022190041040108007c158804640e500e650030b040ca0151445024000f50810880702503250091140590b115005030100b030030869011000d40f2254020200581 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 755471933 1250 755470683 755470693
    0x2a131a0f04030b07080604140a090606050904051c02060103200103020c0f010f0b010201050405030901030b030a0b070206060103050108010e070b0307140c010906060806130602130308030f070806060a090e09 90
    0x200c24100c100410056108031621038042c6080c0000a241d81ca010700040d11540c24500c80d00300101003082c00c0350b007042000c080010401010300c1c2c10801052980d01c420f4010000800300018008003003540d0f0858407041a01c0d03060994000800c1340c40e101c00340070040104025102e1540b141c41e140443e28070f083e406040c01460f02d08600512840c204002e4001840c40c5e44501e01000a407a0b0342c0910b903098682030003b8412800d244e07482c00d440e0f01078410038034109584c0c0c00d103d0f2100c2d5070410205a284d03400c84401010360500080094460b0320441e09240030a04000002903a41014401d180c40c04402c0f070b02401c101401c0ca075044845130b0016200d801000360000903121510a070500414286d034404000107100740c80b07071a140099842e00d610020a9400402c200840328041c6150703c0b40390350b8040001640c40180c0d80f241c56074075100742c00c0500400000310420042e05026000c440c051001503c5019444e65054100505131141031980b85c00a83c0050040040c881a6001300f500443d203401614 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 755473183 1250 755471933 755471947
    0x705090f0607050d0e0d08180a0e01060305100e0f160315080f01110406080a091a0c090915060f07020d08030c070308010e01030804050d0c09052a131a 66
    0x10080d0300940401d503044d41142c2c5001d444950000d905440c0b0750340541d00d0500d040c0d0152280010341c0903598203007036101c6821901681a658006400c000b802e41450401d0203540c40d80c038010700402085503c05102940d101010030310341c03025810540718600d0407000b4011541e4a004d510714a00c2840f04601c1410380324030007070b890791031881160405400c14000402c5c1e10001e02c541e031425100599010444820108018031500e60712a55950380880142d4002c00c89904901d0b00b4070a1800c00d10b1407000e6240b1020601c03044006400051441c2c00c400c03074503050300d5202d0903100c8024020030b189142d0701c0b0704104425004200c454010b02110f030f00083c48403040710090b460324607441d0f00450b505681005c0009025041541003403a40f405003d98111144441d811640c5d00c0c00144038900915102d8000c0f14611410803444c0c4400c0340107401182c009000c02c4c1001e0200c031015032070450041c80300986c2407414803a01440d68081d41c0a40c50302c01008828a85021942c400d060300d000802c0c45203d20421004d = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 755474433 1250 755473183 755473189
    0x207020f10021f0209010c1410050a0501090c0f27170a03021e0604020d15090804080c0405040b010e04020a031b0f06050a09140a090f020a020c06070b0705090f 70
    0x103608042074000d48102c04043c40c01d020b052024031071a909151052082c0e8003642d03401285140603d078044c0ca040540ca1290b020f040c5840400e403090074006040804100c0350980a8100703e040310072603081809030461928041d00e641e041200380701d000442107040c017000510001d80350340c1420204000d05240e02e0701d8041000c002d80c9800180706469001c0300700c50040680c1041142c0e0748214885a2501e00591034400355110007025001a00c180c104400040c01d2200201e01c8075203a2544c280c08010703140c41c501d041d403542e41140c400c071401e5000351100a400b80c2002d015940c811a4005103100d910303800d20f1002381e10f8410251042ea04035070321f031101000048a03d884074a522154081046c03040e031038020030100d9080c4035000341007007110a11070582d0140d004001f510a03648005017080d01648240b02007584403100c2c0d84400d448900f011014100030310283d0061050b410242c0c00d440706081c100c1705226061145000041400c0e9160b170000c1c4d0340500c10400b501c101c2c43e00411041c0a80301074000 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 755475683 1250 755474433 755474449
    0x1111c0e09040605060f0a1d180f0703030320090607050a02090c030a0506040c05031311031504060b061306032d0c0201050a150905061906181d07030207020f 69
    0x81120742c04d0355602441050302d4844441c40070b2003c12241c00c1d90302403c140d80d807c0542a0340703600d0712aa845900108480750740441412000740007000850303c00129000d0b1180c3c1c0c0350a54402640421328102d03125034988080c00840c4a084e205440080c6004401410300416a104a1081c0e9403402034000b202c0069443ea950240107641d05c01120b5164104a0b440000702e520251201e03215500c0c1011540d40660008180d0f5400f0194001c030044010480c01c00d680c00910282c2c0c295814014409400c85014036640c0240c00ba6004203420401b07229418103022180c81106107642c0080702a11081208a00c217400180c2d0180160240c0c1030400400c0820100d641580c034100c01450f0707141c40f42802a45d50902c9800c0d4000d030300c45d00034080d0817203144160b02c869640f800703620f0b100c0340c403800001ca0540320b94031425071400d48180c07802c40c16503440d40c00815286030083c0405624242c0c000004200c0692000c040d104680c1041a846549589030190002c0d44141c100b2a040f04e440e043c0b01e110365a440d20 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 755476933 1250 755475683 755475691
    0x18010c0f020d0302130b07230a030e0f060f0a0203040e1810051b0f0c030304060e1603080301211b080d03050f071b0c15080601111c0e09 60
    0xd5288108410410103410010b00c0748241d020548140a04052859110904012a80c3c440d2546503596500c1c20301c040c2021720a4000510745044820342180018000307100c4030020700035a03e03050091018410070062080c411b8545a0000c0180110a540c90700c1e100200b544081c1801280d2034141e541c1000e140507582261107e148903031400540a00c40c0c3c091000c01020214070342e01704441d14200006021044a8190034502082e010440c140c491054070300b01c44420880e501100d0302c915080c90980040c081c20104403005000d60540d0a100c03152504410f02aa0380c4592101d0a5030308100084021014180325184001981c900c00000710381d04181d813180000902c032041c1c00c481c6c01c06810780c3c50904406600f004042c644010030004101150b641504001d003031a0a207511190361010030714aa03040309015000785078205000803a44025110003c0c00c64071a1a552034a42d50600103454600c00a040610143c1000f00a1000c01d80443c4221108055504203030149410300c1011403240342c000c903 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 755478183 1250 755476933 755476937
    0x1503060903020d090e090703062016140a030206040b100518012301020712080405060d0501260d20011d070504180f240c08090f120318010c 61
    0x9400051203a0203001d080250456030704041c264180700c06d0b2140d0b121810302c4040c140c81e6880c0c01e41c4202d0b00000458103a9200c080d0055030700d500300313a9601440002542022920705042080b401d000d104c004c031702810026015001380030255516103401c50311040c020000c0700140030004021880d079584000d13104400c0d4910008141540c10041c08200000350f0045440501103483d0102c100c5a0780014040c05640c640048040e00940d286030100b080d00032034011300e501c007001180c2c0113154242039010504076802d030028041c810003070400c0c0f00001c4004035854401c84c2c00c107606048846001c0c070010300204d0350f007500200c80741c042034034180e0841d207045404c02e021407058011061450b600700700000140900b00e5042242440300a851411018000c0c80103000044081503507042c080030b401071a89407800452404203849a02802c40c004000b204100c0001c2030b0740c00d0202c1d140350030004d640100204100003c010703d030411028042c40390801420000c20940ba60500c03c0c2d030407000e001c3c80c8100702540e = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 755479433 1250 755478183 755478193
    0x9060905061009050d0f0804240201061203091527050a080c01051207030b03152a03060103020714030c061e07080601030f0b0d110a0e0603070306150306090302 70
    0x801d04121440241014031020440900c1d4140110740d5140748041c041ca034000722109542406280c0f140440c01280c0c41240040400e00307a442145c01100d6082c81c03d020306078001c00880c1c0e11a0400c10800e05452000340018002100c140b05c2c0c02c2c403840100c1503050050900e846207017028071001b00400801844400101120310040001e82020f41c5920050954400588800126400000d1060007425805d85d00401c1c0f1401040f0058040d5200b5100440041d0950b0030944290b04080412401a43d100303820040040c031038103044204e942c0f1010300981c1c0a20652840e141c0c031004501a40004406440c2100380b1008200107540c2000245400104071000e0401450401810460802d031801e800d45203421900800443e61340c46609507510000074200010142c030041d200c00c00800101216603040258503200e40240714410780800503041084424000c06901c81c069210f086000340c070800d4042d8004c0d0320030300c001001c0d90402d280c005942641140030740d1780c0e929514142c0700d0b00c071000e60258001d = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 755480683 1250 755479433 755479441
    0x60203071b0e040f060209220c0306080303060405071119030e042c010609020d090506090d1713050d1106010f14041a060f07021504140111011d0606040e06040812060a09060905 77
    0x414027407184d103000f2504080010f42d1074003105540384d110080080d41f0036a5900c001070306490141048842c0300e4000c5007116141c0407090281d40b0381a48a00044e40851050015801c080c5810b0040d015120583d00364014082003102200942c170000078010302c110354031100040f5034000c1c9031000c0d000d42d10b1a114003141084145c104541032003809041901c0315003000c00703d80300040e0003402200550b85841e003031104903500c8902d6520403074000b400c000c01030300903805504a10340d03002910703001d20b003c0300741a01c3c05642d950071500b42c2803506106400d01c140b018880c0f05540e10300399100180c1da950390717020791519421240c00504540d120007141d4501c0403002c10840b05600b000d808807084403c0c400b011504d000e050002c8120350015610440d8100aa84800402200c5d003e400080c80400115950420088038004560b202c0710b040b6010b50003149028944680a440000d84c030b8080d580241d0b1562402178401c40c03403140d108000b804030341c1003942d055000502408a1003000d0003001d404c0702c006140d040c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 755481933 1250 755480683 755480749
    0x40816080d050c072103021606020c01060f0f030311281e0c030803130b010f0608091b0d11030d0503010e1305100209010e040501060203071b0e040f060209 68
    0x805000710708111403c0c400c20001400c00d40517581c0742c220303000c2c40707a48040e00c01034124081e218038020000a585440c0e44101002070715005049248020030090240544540300b20b0115503441c461400b550441c0d03881080424021004a00844424000d582c2260040c1c0b109050107483c0f0505000d140384164914028001c0d681c0724480d44042c40101507900440e2a1600040c0000b01e01000c1c0403880c0c00004034004216031079202100b2540705d02004002d41c3c1d1050080c9035400c983c8260000300d049080010705400c0c01046c01000c4000204514107007480b0b80707060244448140c042240d0071203030002d10380619541085654000b2182d03949240c0d403581818230b0a00c1141d0041c2c0306440201680c0d07220400604c000c02c001b540c02e041e03108016100d01079400101c0344a00c00400d5581c11078540f400108289901000801d950350140e17424840b0156244a4204ca00909110310070343d4240321000f050004034245040c1103560700030600075003400a0040000d40154081108400d414210000020502e07 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 755483183 1250 755481933 755481941
    0x1090f1b08010603170a03290a06020a021e0d080d1d150105011215080a03020606121203061825020106180f140a090b060f0d030305040816080d 63
    0x2090000070301030700c4d10b035030749004419082411141340b0070004148041624400d81c440090050700410b800c030742c0b01c801108036000c55140707600d10740610802072001c1081d5000085001c0c400e0713400381640d550f9031135144a9a80c020304560803943d029114800480100340c109014041c140c2942e2000100018122031b84500400800d003d0310b5550451404c140d1310300700500420303044030003c0c2090100701091807028002003003500e1100c20000c034440400700c0d400c0320024024503440d10070703021510b0175207a82081000500702c5400b05501640100d00340400000c0d060040c1d038008201500404000c1007619000400001c222180007500031020b10f6500a80301c00703034544014000314002007081504040300188030841e1450122080c64492840c02070724615603100d801507103694080e4a60341c1c101088688003034141c038101a80d00d42075040c0480c40d00c2c03406003240003036440001c107583c2ca40d20155409034040c2c18000d10690b901c2c4020321546802c5040000480c0541d445a0082541c44001ea03400300215 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 755484433 1250 755483183 755483189
    0x7021305092a1c0803360307020a1707032010020c01230a112b030e0d120c030603120c02130608060601180306140915041101050c01090f1b 61
    0x4081e80310503c00c0412101000c40390003180300c08034184041c0035001c0381d221981c00070440a9031021502c80035200c001000c00034141c9607208032000402e459990258a5486c08aa210103841d0342049208000080071101000e0030804440000009042d070000001e035007c19221002001d0381200880c0200c540e44544159400380c3e80c07e5000d03000a12005041c00180603c80200042c8914890080041c80b0200078002e0728440040800329654070042c070702c2807010507222115020074100403140d03002c0704012990010030b6420f81d440d400f19036003603c5414050304400182d001071642c0e030140480820042003e0306543c1510343c61b48071000d540e5205000d066a42410702200b040c0c500242409444400f03d84903420034000d03e00500801050800d01500d244240c1c0000c0200345410f8005510303002c1011100d20800355103041c0c171407254011011010122044900416012580c1d1210080398007410280c024041110b000040080c03142e6030341e101501140400b41c0e07148104844040d40701460034514000707 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 755485683 1250 755484433 755484469
    0xf111911061303120504080c0d0201091e140f010605011106010e1f0f06021e0303060a09020f040b04141f0207030b07050904020d0b01030e0307021305092a 68
    0x8206040c10440d881c1e91000c0e0100c10034107400c48a01e82494401e000c1c03040c401d0183c030020441802d0501d0250300e142d01c04e61006076140103080005903014010301c00d600d000364000360f401034080318400c540d144800440c0012207040513103a4204070481000c104600341044580300001d0307040c2c00d050002d041c040d0100744c04c41040c0d10250060003da00c15414150b00500304c03001c921400c1003007000d91000316201d40c004000c0452152000110f10354006100c000303901031514902000d013406850346440303100855003550007400340c03030040108a18640c010000e81040f000b240b81445d880d140b50455590069004000580050341417405500d03209080c0c80b42410840951560724241aa02030740300d0403035110160052a20200040346180104201c0341250001001151344a2020468900904a01d403419001918140c1c60303020341640002100c1600d50003d1501c0060703401e14030803501500380204105600c0c02201035000c1800005007801207140c12142c0c00b02d0b2611805820301c80b1a200301840c14031 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 755486933 1250 755485683 755485697
    0xd09021c020d1203090803090d0f1106060108060f1201020d0608030c070b1305042d020309030d023411010801060c02010c1721010f0f120302010f1119 66
    0x40182e96180b07800070300c1030384144600c034014007008082e00106400000a0103120300003041280c18100800c80c80419a440d44412047c24032001089640540313040058035103500690100b002ca6008101e141c0e07200380000d14500da104100404294003084210228007680c4d00820501c030441003d01405c009411424025401c10360b181c203a180d6108690700c16902000000521000302000f14030944001c0c100103007041c0080762800845519010ba90100204100030864220b8480405030080303d000e020781c04015403c0040000b040341c02544140c0d0780351043c05c0006450840098a00100013980580350000030703100c540b40c105282181c0019070800e041001c65801404140d4109500c16032664080c030381030150f01c1d2145040100c14141d0340e40300d070141e00e0101e00180c104600e03d5181c02001580e01302640703030340d036560051110800140a820340d1203207480e03410721000740c8001e06520302e00d01070b1002040b4410106400d5003183d02c0c6011030010000c0005002224240c80c00d8518240f51807490814 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 755488183 1250 755486933 755486989
    0x181b0a1412011109091e0705030c07050102040b09010e030607090614130902040312080403050f18030703080a0e0406030c030314041502010603211e02101401030c0512060720030d0902 80
    0x182da03c1b00c00502120078824040042004a102c0000342c886043e4000c0c021551540c40c3c28140103903401078200c0c20b000602484ea03206960402141050148002e900d40128640c10100281c1c1c848401d150082c034403407824001ca480d03155181004034006c00c104040140d0303130350031420055624651b0baa85a402d1122a40c14000080d5004084412910040820645500700e5403805c0c0c051f00070421020717a0510074105c0100034002610001c3c000710420762a5610002e407000e0922042d6580391001800d1801d900208102180c0510034490f007c000310352300c0c24074203510741c0b540c400c1c001d104504c080e0060b991041c088c01008000f06401e0385a140c0501d010248585101000b08030101d01405a08030308a11030700420068001c02040e502c40e0746d044400d120b40e0034504003240400303500b4441502c1c90400260300184a040148880041103421005094590780c0d10708280c0e05036405031464040164150030910402006001074551465100c001055190060040014841f10301c0885203250380c14207102 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 755489433 1250 755488183 755488231
    0x105190516060f0606030b0a0e16030b15030a0501140609130e01020706020c0607030b130c0905130f0605061918050405181b0a141201110909 62
    0x900121501403405941d24101101c0030841001545401422507040c00007882004141e43c0040041d991a650b0804c40c01802104000d8000458401e4010826402d8041680b042d508d80140043c10602c3c100800d8640311000851b0008056000940d035202004c41400740b880d4190050500400784145510740b00d8612400142c0b036441100d4030740c2d1040359001c0078419a01f24070780002105050000c001c54480a1504000003e0340c09900c0d0f00107071340909000100c01c2c5000f0711540c00d5501c0050400c4885114000c044401441c034803e110090151500b0001200c1d528500c840e00c0e101089000800d594505a6042d01941c0182e08054800c1105201080c925070144c642c9410340740c42803506116528403010f80301e0100030b5940002d6003140c01c0c9803c0004d03400084025030329120030041150000d01e003c02d092a00c1118040880350f000941000400111489000c12075640000604495900d10346443c158216260004400c0d812000451111940e01d4084540c55100d402190310585045c0701c0c0da81 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 755490683 1250 755489433 755489467
    0x180607090e040201110f010204030c05090c040e0a020702041b02010c030b10180b18270a05040213091b05010203040e0c0a0c0f26071203020309010e03030a14060105 72
    0x10700700e103142500c00000d05680c403403901c24680101040a039107008504048480c041d41c03241c042905d10740994000041d981c24100c03281c5120302d007507110540c28603060007410114100050814283c0075020301401e000350f40c42c0e1241540c55400f01485c0f8925031440031010703007136620320102503050500d03007426040380d41c640f1071300419501c072546060881610708406500f9180f0260304031076034500000c10f0490304960f041c61480c40d14a800c0b5195140c104284984c0c0b00302180c0759800c81c0d400d1250801044804265810498020b44010524116101c41e007100e40101d40304c2e210151609a50342c45400032000400c000000500801e2004d14941820701019040c2e001000c1c0c94001c0504001541d801c4082c401c100482403154010304500c0003280724182942501c01c1c85c2041c0884503812607603400860358050480384a203520aa8407603204514440940c000d4000070152480c55403928107501095606000562140003c030400041c0040380720103245520400416040c180181044034101103204030036 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 755491933 1250 755490683 755490689
    0xf0703110a030e330301170715050a030216110f0a1d070e180a0c0f0c0b0907050a03050708061b07260d0209090c1e0904020c07080618060709 62
    0x280c6045540f14002c24105040d04460000c070110414984902101030138100650481d152040c40300b02c130304000b112458440116100d603400d81c00025816008041c0502e010700340001c1c09040040c10300c164086401c04001003a80100d40040070800348400e9490001d45105040070182e0300d080c211400e00803000300168030450003244085d00800001c2c0f070366126184103500040090400d011270741c00c10100b4062408140c824802181c00d164004154a105031030300f14840e0b040c0c0e5900001007210340c483c1080c040f409484103010340111940407803c0e460325040360006512401c010032409103895001401c104025081409a0b908102e88003160706031201079481c403d4108111b68001080040c1a2036181e56002c00b1030540c03d070128207280084100d07805004407401c01d075445804da90356514900c0c441e100711b90100c0044c040106000c070280781c03000e0140507c040080d00051402500b000380c1031520380700e648001d8003076001c1c9042015042d00301740c4880601c191200208204e0800400140584c1c9083c0 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 755493183 1250 755491933 755491939
    0x20409050709022a0a030e040207031e0224070503010302091e0412080601140d0f0902040e01020712090b0f030408090a0303030501050f0303070b18120f0703110a030e 73
    0x14a01051020034000a801011418001c668903075241e1003d055409002d13141c10600c144014402c04540d402094103407919a0503035900726084c502000b040700942040105600700401c105c10301c21021049603004901a81c690010100d90b03441038802c0301290312103003111213070340e00542c14092425040310a0743e06407a411100d0782d1441d5207054860700d00009080072000090400d1045c0400e0000000381e002d0004150f945440090790750400543d9560030044000d003100f42c04105030288210283e1244c1c103c01d00f03620010031042010b80004056894500c05881d0596000074500104030145c80c0342942d405107400c0c6441d01c07914107484080c15001e04440e0071204140000024100711910301220f4030050000c0c100220310392070b42002001030000b401010300a0f00603031490380c00b62034000250f90341241c2c0034110b021317196035905141802201c6454000c0e500e00c550b15881940c00095400b503e4001428846581c0b944a81d080c01450030f0003070079240046400104040000c00c2c0d1020300904071200c10703 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 755494433 1250 755493183 755493191
    0x12060b01050c1207021e091602070302060c15060d0309031e0f1103100b0f0d0201020c13020306040b0604061d0a0902040b0715151a12091f05060d0204 66
    0x20005a45611888050703110743d02803510b08096040d043d070003400010340291102901d5011510b10a862040c000080d01d91203030840c00060064150000c0340c00140e0000d1042d030340d0403696640460b961f030b0046510040d65401c0201c0160340c0c8050011126400360040329252032555607514050502040f9000103040c0380354403503070128041c188840d1a00c1c00c9a000d48003141700911410a0540c07810a51480c612902030002c0140300d03420766025141007884000c0810000802d140100078132141300f000100d0641c05003101e00045a515081d21500a0f403042d0303405683d0b850004104011a03105442080c440d4000344428820164440c803446848495459001003081c4000c00107007502036298803c1c460140006030103c2c20028640241102c00e2042c400c0541c203003000c1c68404151a5200c0413011940c1c45010704208810380004102c1c0b4004d0f0f24944a4907101140403900303048441100e03004910703805040701429500703080035601d08622650604019030f082100004d900d11481e801c02910807615 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 755495683 1250 755494433 755494451
    0x30305180c090c25060b0901050f1507290109050601020a0b07120912030e06130809060f09100c02030c010306080d050903070f090506120307030e06030408210109151206 74
    0x213110054404582c40c0620700c85881c0f0b04030018150116100b8055000702000080c01d051504c80071101c00e40044c020341c2100b958a5000069400c02c8800396000160910b2548003903100d1086200025030900e003604582d8100600d4106584010340701134110340c081d2010f10041852101c41c1078008000f40780407112079002c0480c0501500e2401c2c03000e41456540c80e40e451449405a0007281340204140c10742d00107544110b0301c655100700a01c00035000c403000b04030644a40c54403800400030402448422810701e11010007103004848036144417408a50042c50200c2589410050180180401d02e4103002440c240072155440d0241c420b80c00c0c041c407101048002980d42e080c440344d000fa1140c004402c0b035050741e40b408030300581810b8600c0c60240f03150303c0300380404401c080221413115416455104445c1551814040a039000520640e40801c090050320b2030400c09040f0424a40041d2481c0603607941840b03109000c89103a103aa00101110001c001c0107921324a000701300c641d90b041100000d40c406 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 755496933 1250 755495683 755495707
    0x2030f16020a15140403080904090302161401030506120d0f11240615160807080304050105090f0a170c011b050c010c0e24090d030305180c090c 63
    0x1582180258440722031500490541c0101020f092009a19660404040011000c01c4482c3c8201d00000d0b00c1407508000a44141c1090f030801070a681c4281304499070b508190f0000f080c80081071300f2400780a4541d08a80b5050340c0c0c18028203400180c215a82d0303080b40742c90070025540328a00403012013400080b42c02200181d0242c030491a0441c000002d981d411140da070014112001c0c55011181c005900c1030101e034a904143c603242c132601505103046881e00032048d20400394845400400c07110b04208100b80343c0051081130165004d42e1040c4001302d098240008801e04041885105000c1c9601544030310300402e0050001031001c20710040768a980d5040b503c03000d0302422802d4491200c0441e0016104d100c0c1c0d0b8880002d0100d090807100070003440b001c0003c05c071141c510300201c6952003503040c1d00268440304a0b111081c04941691140351900c080680860302c9103004400c20381c0429039540030071949404d0301e10640320a4030b000c0c0c0500304000f80c00b00003500000d800f0f02505807082c1c01040740303140c0c45 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 755498183 1250 755496933 755496967
    0x50f0f041d0102040503060c0901050301350f070e37140f01090203150906040e2e09080a08180a301e12050703200a02030f 54
    0x70200c0701100c5803400051103154041c0d802841568020700c9101e00080080006209541c0c036800140d640300d1540c0d280c0007041303103050340440d00d45080304d50b450f003d00c442d000e18840564074200f40401500c03e031003003a505142411055800324254143c448204665564200480c010b4804940c405440511000548420b034030106a110074043e0310b0400c00d6000b1440c4803105522403031246098030070503030b201c01c1c012042c1d00066510f12200700f800b0241c100c46260940105c0d070b02070030240000805004c00c2c6801850320f40c4060000c408805440103032801c0e2800040c9841c0f00d107910311801d1004038011780d02c6408a100c1c0b900180104004200071071f0386134200c0b540c40000c10744140122a0075029609002c03501500d4030140404d851818107080554115440c0500c2842409844a5504030340c401e028480da5202c10034582c0403c6241c0031804001c14680c03140a0144075559400141802015501c0d07951018059200e030b800681071141d0040079500008a84090a00840b4107484601488001c5000 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 755499433 1250 755498183 755498201
    0x1407050a0b211e1e0a0c021005040b013803180304081b091003080313050601081011160201030b060d0207120816080a09140d0c020102010b0109050f0f04 67
    0xc801d8007000d209203c0f940303118a0790402a080d812030100d40340e403030b0580c0554000400035040c00b1001c00006004190b260301500003100580150f82464102c002554215101142d044074600980c8005101010300c081d0302d4104c0e6081910b41080400140c4440348280744d00700c040700030052000002403403610f011703041803142401c1e4070704403522140c07070709480c81e111359100030f5915550003c003920700359030700e030000c0301902a240a58140c0384050554540404a600050a0700000c0550200150004070200b2019009081ca200545060070030b141612003544c40900440c0040a024004d461000b245600d911a02d50b509080009072807a281000c030343c2600900c0c21150f0010f2010030804184888600310f1080c2c18038030303580c4600c50342c1d41c0f01c0d013005075007040c000c0080092584e000298440640d0707400034051034010000c0e400c40b01d150036991440c01c24490700b80400604001461400c5580901440c0f94100702403e04203035180c10100462046019801198425504c4204114841d103441d4481450 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 755500683 1250 755499433 755499487
    0x5100b040324062106022703070801020406080c0313140a0308091b010c0602040e0c0a12140703090f120c110609060f1b06131407050a0b 60
    0x151580d038203199a50070030102c46074545104210440215401500c92402039900d100c01088031881e02c07000f280388120f9468030490b074040e4208440100001030034a004104800b40b036907020fa05e0101024141051959444850581c4c018007042c0301098100c5e42e85503110f184260f281c0d84a03614500e40200b0321580d0403001d8041c1d00305880030360703080301c0110f44030780c0850007900c40500903142c10b00300565503021030560142c004a04880c1d5101076108000c1e04401c1401040003506042d1940c66000180e001a01c0168400d0800150340380d40680000100d03404006c2143d007044030200d4000c4402c5d04c808028545810581d5402d2400200100018a0008a5041440e650341e002d09c480c0050075072655448140c44003400745c0340d040000c1c0b6000c01120380e05c0c030002c0d1419003488003140103000c943c0c2107885c80c42e00480c180841c00002c11000c02111744102d0700360080400060880c2001d18520010035203e039890b400c0404144240e80302e5120000444413040f00391035460040010314041c1c00c0221180d101 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 755501933 1250 755500683 755500687
    0x4030915090306290d11060f090604170d0c050d0f1e0801051e0d031103070501020706230f180106170d0f022109041b0c0b01080d0c0605100b 62
    0x100c02100413000010340c00c1034034003072064402e03808100003103401c0c024401400886840620702c11030500c48050500e04020b05d40d460b0034141610001600c030f41043d0451880002c814844015015041001340c40c0c8000c103003414405401e254403042c0d1958140400c0701c0a00866410313100b501807080c8502c0940901740364050520500d058801040b07081c0a11400e8800c50184ca11050140c140311042c18100340001d02000154a071b541d07060382e101c440080c80c60a6804140021400326100f80001d00381580324040c005001074160100c3da0000f1100c000100039486c1c1c41c4c00b0012a242c1c2e000a41e6005045629000012182d90034400d000d040550854031482801c011b0086800d0800113400c80c062440b51034118464140050072a601c1c45e160640c4502c5a095001d480484c4098600400d006000131700301007400f00d07041d120740040725014100c2500180c03e22a03600c00b40310946429602601c1030801402040f0340483c2c0c010440303005ca01001e460103654901060451442c095a00020081141c04030f07 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 755503183 1250 755501933 755501951
    0x409110d051c020114150301061e0f1203050d111611040c03020309100209010504050a06080406050f091f091202030403150204050604031101020703080f0903010605040504030915090306 81
    0x591200301d02c81c0c88040c0480e0300205041d580b40107024140c2c1005901c02080415500d0680c50501031015400942e015561103002080d40c40d060714100700041e40e140175454069242442c00c10145440da0b105051855440301e078400081e900108482640380d80312004500c3d2030000300703c02814400e0b0382210008116003002c010030007074907000c6451801c0048a04101d119514a420303800d922084404809580202c004071404003055405420f610758107152090619440e00040340341104241c21003030100d030b0042c0402082194038010181c0c40a01d6010703103211070a241c1011640c4100c1d2010342140e0b4900c8040ca01034044540c3c0c850062503400ca241030030b24008642020f9180c0d40603010a481ea04d203d44e00d0380c2e281c81c60314001c64048070740140c402480c2a15649409100d401402c1c0d11030304500071150000702058003500580f2200c070000f00125500c504038410142112043e83c02640035906010411000c01c0d00505003001311002040a00c07003080080c0703c00c03585550103420041c501840c3c40c041c0 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 755504433 1250 755503183 755503193
    0x103060824060303090a12170301090e1b060d1e06030f0b090604050604060c031d0102040f090b1318080a02010c030506010c050d11070b0d0507020c010c110409110d 72
    0xc20720901d0300114116901e480092613100e2007030b05072145c6c005041c444d0403c100e200c0e0411000350300c3c1c00b542c155072003181d005124001980c0280e01100f4102d0319800d05e038401000610000c15000403540c00045d0110306d80020800c1c0340100b800e20303201d0302d60f140204281c640310b28100a54460340300c80204003040c2c030307440c140c0e20300101c001c0d0940d920b503240e10016400510001e055402036030081b0044c081581c03503503140c0c000303014082090f0081588812050640602d00c2411010007900500056103950400c0010040e210b800d81c06007800904060345105261150300c001c0c0003d0071407900c0400c90a08680604d41c003008401002803203010b000410900c0e0590650102c640885aa5000d20480d10b80c44d004480c031001504028100c0d41003e0710a442c0706002d000011281320011041e55019a036426000d41301c1c0d00003030302e4404115208d004000705039606102150441c482404d004040c5007064945000d43c1480c882414040c0d0341e1a0080e81c14400041e105590302c000052440b00045940d141c4 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 755505683 1250 755504433 755504473
    0xe040e07050a1d0105030303010305100207080c190209150d080f041503051009020a020d0e041b0c0b0f070507030c020f0a0810050a050c0703030b060705030f0c06250e01030608 77
    0x2001100f4003c24004503035441e01000f143d0499800c4001800c000c0980400e050003540b140504850b0780008001c41c1602c54014490b40e00c3c6410f060b003c1650300b04c5580103102600c54003e11107000c60000b401e0400440c1c0d110303581018080e0b04201c0c00350f1205107600c419089440380d50841016010036043c01030380f25074142c01042c42034131880c1ca0b04038051307607403d0f4800a9008821407100580c0041c01080c031020720400310007141300c0c40144041a200440159204448101d1145a00050006070a44140301344008510741001000143d82c241e45440704008140b800394900c010100b20156924100350b66031208190507120340142543c2060b82c1d5074119607a6843d070f14005010b00c42c2004000354422010340720f0781e4842e108990700315103400c0503503904400500c80301c0e003080d90003d010f010420101d00b0810289c0030f0f00c902c8580150355001c48283d920b2500382c005100d218651483c80010000d401c100011702d003074807071074103010f0580800440180c0107008943c1100d0101e1003000080c18401d035141d90 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 755506933 1250 755505683 755505719
    0x3031305010b030705060a0323070c0201020c0306070c0f03031b0c0506161b0c030f03091a03061005030a20090f0a0e01170a0b160e0301020a0e040e07050a 68
    0xc001c1000503415401c0c962688924403c1c164044030038403c0302c9143c2d000303800030128001500201c2481040440280c100020141e40319000518041218011541c04110703405a100003180201824586044010006001e04074010710b950954540702d030030140260041c0c01540080303001001100c003014801009113107221800d44591045602088451110240c1c241ca041c0a960b6031020021074035400c60a100300c1402c0407220342c070216500002041c01c00b00c0c00020f25200340c2c0e03000400c0345400110310701c41408040c0100e14400420038082ca69032100814101301406003855a01d958458002a00030103400400b11000200d09614490854094009281c000400c898030b1964100d0001405000e032082e0081403e0006240300602107040c40040707420000f00301a044884500a954940c1204481a12804654001c2c86070540101da0071030007001c0c2910b81600214245207000a000b07080e0146511554001c50703495544040018060100c900903107000360585020558410302c1031040c1400da0 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 755508183 1250 755506933 755506943
    0x100504110f070f0f03080f160c1b0503060a020702040b090f040605070e0619090b04051809030f04080c130e030714030c07180c0201092a090609020d1d07060e030f030313 74
    0x143c00180b06510b0520240f00d008c0d00b6030b685c4003170505c50743d07112104e0002c025600055a5510100081c0c143d50400846204041c260310241e00d0b2059403040c40156168820800d00c102218010003210000d210152070340035401c090003040d42e44070340c101030380e411914100fa81d82000d40002c2280c1c541480c20003009200c07226941d030900160380d80074000c489009501030300340d10401000c88004240c8142250b41c0e089503110040c4c915012040701c804d40c503540143e00c281030036007021107000c809107080510074031111101002031291400c011001c0b900c074840e54038000c14043c480e1502d0305d51804100241d41c82c00c0905070480d0b2106444110011384410316440c080325890808001904440c8180603d024076540310102c040c4c4121905039082e8184002d0011450090440394000354030301032801500000c00c11442c0c0181d071a08405154000d445100b200c050442600d40001d0718094800919541116060b10740a104c41079402c0000f07050081b82d1801d4146444007106001c42185d0200c0044032882c0301d0 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 755509433 1250 755508183 755508211
    0x2105041b030b10081f05090f0102071a010902040b030a020c07050310020702030f0c0a0b030c13140316030b070f050d0e0c011b08310905100504110f070f0f0308 70
    0xd2080217546103014078849507a00303005100210141c1c0e1603001580c2048a10065810a20300000002c0c226006030400b562444152140140805c0c001782c40700c1d000d80b240240c06c0d4905418003802c06940d2002918010900b640041e00e03a11144041c006000a04401402d030741c2c004d01c24102c1d140c040d4100e03440a9110b40194030821510080005040c0290f0310041d040b400e82524100320702c4a60380000b48000406001040300140c600c14250f03001e00a48031560464621041200c140751a02041c11040c520300c01a8500030b00100d1503850f14580d00c0042450450b10141101038200c8450188640e0070080d1410000b180c030013807001091494043e0320a913188050603458601c8640c41c5c2c4505040074044400800020141156041c041309210905040c00031004d02d0303916100d15165034a40c010081c071647d070300600a4070244400004000c200c100c6090007224021150142c03288a00496a812400c0000d00f2800704030a01c0d0344951000e07008503c01200c801603080151044d01300300e031400720724141 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 755510683 1250 755509433 755509439
    0x509061e0705010f0e010b010915030506010c08030f01031709032109040204030f03020d0224040f02120c1003110d0c030e061e3103090b040f080d2105041b030b10 71
    0x220f02744d00d030121521030340d6600050a110304154010701000c1d280d28100403010a0030000305100c500190f001b00710ba0705d0501429891420609900c1c41d18000e440c1901104100c5034849690000312a051309200ca010341c04003a09603c10f20039140310762240c15070440e001080010070300078150326580e1180e00a801751680000d001004a0320740310101c00c1c2c10420520f404002c030404403050440d0350301034800c15860b00300c0c0070260009069940c040d608010594004480e40d11103042407081c6500c40e000b81d003005c0c8200c0500c5101d40e041c0e80a00340781c000f02c03183e885c0318958003240700e85c0101d04460b100d4010341c1c03c14105040708034240500380345c83d50046401ea20108042e480e41e00d002c503184190fa410a03070711b015003406281040d00e801d01004e4080002406000c51000c00d0180188020040c5d6625003100510703207010503091411002002051040d2002900260b00ca20003085000c1d000300500021203a4580c030303200440800c00107424289014401010040010701e1341c3e4a4044c40580d00304d900d00c156 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 755511933 1250 755510683 755510687
    0x1e0305090705280b03010b070b0903120a15060e0102071806050a171b0a1412030d1d2e11040e010302190305031c06030f0506010e01060509061e0705010f0e010b01 71
    0xb05c02c0c440c00400000030000580070811030584c0c10380010048043d0b0346007011420130070102c480305a03a8120301c0c950b00d41444c03a10700c084408050045c0102e06140569500400010b0f445000902c908529034000146049554034550f0166001e48001002000c04584440e14495801340c442403050151095540c08000100342c11844034a03004000d0801e2891424580030b1040701400c8181c080c0c12081000340342c09501e50a20180031141c0d43c00388000b0702c14000c802d010840085000310044a90400210319010001c00240c1c03180ea40a400c0d40c148804640100c4540140000000d001c80c00318007140201d16082c03200b00c035030b0403207000302d4a00c111703020100c0d015030b1224014400184507030f004000c2c042d498400011007150b052100c0d0000182c090b640c3c0c5071000462046503040b00c407070f0480c2c0010310484c0540c50015014125034586a0704001c4240080750b024070441c1090350012166000c15200d51802104443d60355a0200c024400c0b010200c81160243c0a5450942c010354200080701800354 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 755513183 1250 755511933 755511937
    0x2030f07020118150921020f1311130909020901060c0c0f060905270f1008060109090201020105070203040e130c1502062a04181503030f0e011e0305090705280b 70
    0x40b00a440c1d4a00406d10f075400c010749620302c8001d5030f411a110020400003c5a644966040303220420440b5554001000c110400310340e907900f100202500d080003000c050b8803140e50403810746501e401d01c0b074030303a50303090920000400060f4403075000d0031310750800891400c2d4003d07880c0c41200d00945416003600c0b2a12980300a4020080680701d0303087d41540014a002c52004003640c000766640d611400b51600d40340100d0a12000b6081018000e0b00c4602c990210350782446040d03400341385440510705103824141d14080c0c000f000380200c003e8002d9403034282c0510000d1100c200082c0741010101d00384604240c8041c0d21020119040301041148a40c030f0f50300310068407603403100d11402075103103442c240c1004d04603800e2140c0070060131003142e40c0f825521804106103124201444c025214803224103c00d08006007051040300c580c1c1c0c10048017101c04e5130198001a40a44005224100889d56070707203401e034151030034020754011a401801c8003030340b00c0007008880d2a400c542400d40c08200c0426201c4030303100503c0c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 755514433 1250 755513183 755513219
    0x6090f0306040602180f01120c031517070b031603050613020a031e1e0905030706090c030b01141806031614010210050f070c03030b0907080105030d0206010602030f070201181509 78
    0x46488d0081c1000c5450556015598031402c0d410002a140400c56501410300c0243e003001510013a82c1c0890442044c042220300024071340c0c40080e81c6149042100e0450308140540c401c1c2c14103860390b000c19032995074541c551140803642d050854442c030880d03c0041c05807220152280c41c1031403005180040603010700808030035400010340b040e600015904040010612981d094a10307000070702200001850318042e0801d100d000300307004200030b41142083c403525003040c1d0043c04004031500c500c0407070380c41e90644c412455100b0a00c0c0c00403981c0c0c49010a04050741020303200031603a07400101040620b140c071045c0d603800f00d00f0780c2225044080e105280342110350644400f040000c10800180110703114183c2011518464500130a991070200017084c0e51038015100000400d1408006002609040000d012045540e1001380310f55450004040d459108440c0d42c0c1d449110005019011740e4043c2200582e403406161241e0011583c032810039031140410300b032039800213541c281d0006000c60780030a00200 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 755515683 1250 755514433 755514437
    0x611030610020c031917130e10051c060f0501060305090d030e1e07030c090b01120203360303010b1305090103050d0305070909050403090e0603120906090f0306040602180f01 76
    0x3c101100c10344010305e481e02d00c802c0b00e1080ba04141c00c11444500300207811499038124031060081e0600c050216500401011190348869080c0300304125a141d4442c080d0140b01c06403d01412034883c01d000340074112002554400504120000a10981c107070f00c018803d10340c000a50305c9450350130104405951120749028043d91083e88001d41440e040c0f05406000e09208045070030300b075501d0382ca5480e012096440314030015a9591900e505580013900040b01c0d80b00715000b145540381c8039400200c41c11540b43c007411001c0d011140b00040200e030fa5012484008520201c03900c0b5071f96101101960b80c007551003451140107246000840d0b00f000403201e4103a0754840c0141c290703900072200807030003498018082810002e8480000448500c0c07441128001c500990782c41d0203003400d040f5644030002c4081c2c030301400f0b070744551030345c07002c0080c0c21050719941c14089881d0755a400001c0c0018402d2101141159030501602061004011441d40140581c04a00036610355032034010041214900c01b154a0b140 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 755516933 1250 755515683 755515693
    0xc110c040e0c090a23060108010e0106021507020316050a1e150504020d06140405060f010b040605070c05031219080c070303050a1104060315090e070612090611030610020c03 76
    0x99520306601c10f291302802140001561a50403002500c80350060180005881c21820a1007110b590002d9150b025091282824140e9403400b4030003035407280c0364415000905440000709580c94030a00c1202e200b4070aa1078409801001c0c0c1c200940c865400d140b00b140c1010040810000c4e1500c0350000c40005a00540980c1100700c031803521001034400180120780c03000103400b01c5070008031580320300396092003d003080035854a81850024a00756018001480c66207010b4010080b1498241c00c8a00f0388181d480c10303980f40d00191030a0f907950301654000740e9150246e40720350f19a0303402e6640030380345030201a480503110340e01055040c0e8001d0410f60b0b00100e004420001ba0020074040d0300400d4101041c46000608000103503684034803608240c01c10030009495031842c1048091901103240036000d0f0a00170004130340700d000d18a6541a00b0b110b0042400841c018400e206000c0c1c0d4040400c091f00513109101440518403080d29560044941c1481031701115075107644241b00007822b006107100500181 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 755518183 1250 755516933 755516953
    0xb03071a070c0b0f0d0c0314010b16080301080d090603051e06240d0c08090a0320060c040f1418090304050612070e1203040303030f0b03010c110c040e 66
    0x859a000c0740c42901d03425480c450010300e03401510010204d5504103203000d61204004d0080c00e040d164200c000900b0107040240114158041e03110160440340700c1200e5556400c82d410382800c000b0100c0320301030403444003c00000b03001b800115440c2c0c4580c1050743c40500302d58072403405408841003900c000c1c145002c440e202d0f060604c00e002c0c003942c22840040016030700c8620030b03401383d81001405401d045100c13000704a01c0303207000c00c0d40501145155141000b281c80d242c640c000301c4c0d40f040000006000c2052183d24880c22600c14201b59aa807542c0d072003070786c00b1407030400134003052540280300307200007086041000182d0111404017143c0b4100d0040c0741040210706000d4800700700501801030308182c0410030000455907141c000a019901d100d1a075500c00d0b01e058140502040c03d8040d125004082c3e03500e444200c0310010003200e06a03a0305040000d040b0000750314450003801c402d840590150318051a400e01c5a030050403103015500441d04884e004200b80e020700040e18242c4907011195840b0391042 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 755519433 1250 755518183 755518229
    0x40b0301060e0d0602030702010b1c21031d0f060c04060507110307080114060a3302120a020a05010b01020d09120204090b0f010812031006110a08030108100b0307 71
    0x2e000d0710400074018042000c0e03c0c0c480034201c5e402511581c003d1707075468200b08904d0600d201c405009021011804524404980355040022044000808070240c1c040810b01164001c0d07101602c004840ba1b040070704901e18404c07850351078454803411000c82c8180d50001d01d0103c0c90104403402e4038070b551798a504189407540d51210b98124003510319810b0154140c00304a0607401d00c90400c00151b40502c10781c1c141442406c0c4084102150070a00d1030714418111000340c0d9032000728401c0d07035460038a405800c41ca0061001ca052110902020002d28400540d40584650004418502ca030042d070080041034440c1700166035544013010b070100030072460002005244c070302c2e2249144003400a031010031410802d940740003407264103ca040f0581401c0d280103002000d0704200010748452181a142d00d90300b0400c840440700c80c0b49104900420016425000090100380219245264815441a142d503100c2c9519502d51520000403c0d80ea0b00d00072212955140000b4844111000342002800360300da10f001e2 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 755520683 1250 755519433 755519447
    0x50906010909050a1a040908040e090c090a0b0f030601033212040f0e0403080a0504051c0909110304081e1b010204091d0c0405150a03050609070b040b030106 69
    0x15040c144120801c001074444000e0054a10404148500042107200300d0151607584604001d0390340141d28122910340001d6a80040310281c441b01c0100f0310b420b075220740c4070906c1d003113a020300710303400c00364250030300036000402e811081e0150402c0746c01d6501000944149030391000240310151000301c0c181c140e0341a11800b030390044c08210081e44c10900350780065407043d280ca0400e000001c6c2826001504001c61031003a500071014000034040404075082c203032401014400090110160300b60355401141c1004003c0110b48001d44000600f10181142c1c6a03004d0420092072203154070b10b07418850040710000c40c580c104d9110300d0340701c000c1908007080210300b11401000f40f880350780715030300410061407465a4501a56248441c880015907103504040250090354241e08400c1e00309075100c0c2001004804c042290080c101d400d460008855071015640b441c0d0b0031030100c43c150000100030002c17060100208a40d072050203960102d40c01c0982c0e56022659038421481140700c018400c2c0018400280300b400 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 755521933 1250 755520683 755520691
    0x60f0b13150305010e0309040c090b0706270c090c0f120c0215010b0301031205040b12040c091104051c0b01090903050d0c02010209040507030b01020a030c0615060c060e01150509 78
    0x41c0480d207507103a83c0d80908685050719140d81591010a0010491a003406515841d080600c0e01c2d12046140c886010000e014105004000645440541005800d1901d1030107030302c0e000c942c0c144034001190920f40d803080141d00946150320308000e81360800501038107a240041e1943e80d68444800741e191803590080028000c43e0085004040b070078400f20140308407081c040c0c03c02c0014140d50754035628000c2c0da010351750580074040c400148401c120580c007103c05d6030707101040b14000e004a0355035071401c2425013903203410100d0b00a20f442000300c2540725000180003960340c140c54442c14209200d2034501d222001e05001400703203440300014018800301c1c2d00801c902034841d040980c10007406002c1d05059403540043c200050303501003180003091400c1d001b900c2c1c001704941000c01c040d40300ba800003034860980200140c14000c80a0041040187d950b001c500b110175180f2243c0c120f15102d6000404040b09500b040d00c00c60704018a0022014043c822094800c2d052110042068a07140070700588000080c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 755523183 1250 755521933 755521961
    0xc121802040507080a061a0702061308030c010603150605210c10080405010c0905010f030b0d05030a03060e0106090e180f100509070608011409041403070b04060f0b13 73
    0x1040001600d880c00741030300845064a1321070651900000882c12510543d006071409031b42691820300e1900d01c0e004680c0f03040e405a80d0565143c0448103801c58008059010440511000071322a120f00b070b065010f0301c142d9100b15000d0700d1075000f540c441e000b920036038080e080c1e01221005040d03480001c10403140c000c1080c0a010341c3c1b040001c00b40011811058403092401251000c0c08200410200f841100700000750703802c1000c081420800001c00050302d03d80071074141a955480030b8841d6507203990140c500d583c00003c07280d03514020b0760700070702518141c828480030401540000c201240114800300961300c048089580030343d1101613180c84030400320001307080c900a02480c05a2014140440d20140c0000c00c0d000c161404d2a804151030a000e80d40044104000e08005101d400403c054205111000315a6200152261304240c68018101c40c9110341a01c40000c02208000c841c40210380700d18000c240411162015044000a60b001418410351100301264849205182e660203101500280 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 755524433 1250 755523183 755523221
    0x1002280c030b04060b090702012901030608030d021803071202010e0612040f0b16021509030f0304240b01050d0c050c0304090501140a0305060f060d0b0c1c0c12 70
    0x1a8a60042d800300a42d41601c010340c0b03602080a181c100038481e81e4100f00d03103100030400380d00030316000a14424400400d080740f240700c0704000c1c40c2d07a10940219000d0410741064036074601c07a80c9078074402540006910343c0c00700704c000006021854007145c05001c1315140004100750081507801103924903103030854694041000d010441c1d158440700200740c8514800c0f8a44584002c4908245003113000007001d28100c03621020710000903550201d01c55a080328075014000080d114214541d007540030710144894405000700c100400e00c0242c1600e5851201242d281340c030104070f450380e50700070f4031460f01913940819420401041c0d9819179034080f802e41c3c1e0252030f109041074681c0c00f905040d90710a501c004689902c0d040107015942892059a0708010100d0f0700ca41034900d076a54540d19180000d21000d141c030403640010382240c642c0c0d0b1207650042d502009010321032800d00100c0e00d950300226030410000303e51040310399402d8650300c01c640b0501c040f034481c00070200304103000c40050045200280406551 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 755525683 1250 755524433 755524439
    0x141002121f0315240308090f030304050a1e050301020304030807030c05070b18120c03070312092f09010e15100504150c050a080a0815060a1b050601141002280c 70
    0x50740c0d0704c0c0c201440c800d003402641e0b5500b090402507080d440c400e80b244aa007003008200656a1902940011100c0804e0a4020103504074511900000c1a602c5503405500000412040541c050a0709200d440c46840030011125100d100720b41900501c040149100c400300c010409610070703030b10b23460841940c00040318820007007903504401d1504880c40015a5030310202d2400704054100070030752207078501d00c941080754004d582c4643d074880c08044215902200442819401040d9000e60031101844c09003000040b96924400715104074022582410304d101c03e00c0010140c1d00e44410821010103950781c4d40340c00c16013840249030400c444c0c401c004c0244042a111640014803d01c03000b81d989000702c2c4003549422191001400c0888000c00c0e1014070701d17501014100039983c04d4152200c00c0c180d85004100e1401001c510030000d81400d201a000e2b01c514400041c4041210b10018007640051704c80c1c40c24043d4458043c0d958119016420340ba000741e5696400c5450b0344d1042101115004494070a03610745c3d = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 755526933 1250 755525683 755525741
    0xc08012003060d230f03190503060a09060f060305150d0b09070807030c06090501021203071d030a051c090e060f030111120a140103020d141002121f0315 67
    0xa4002d6550316000c0d8901c80605144c0c8140709400c0e1264940e03015515101d1054418030044005060030382c03e1210220100b0080c3d11655220340c041d00302143e00700450380d00c0754880c602d074510760710035400000c0c1404c0006011100181000c440c030500600016503420f86503640000b02d030401059031a00d4030a4020000318164200300e80c4c0300640c002d100300607015040020043c015202c0390050341c1554004a240c41a201d200380850750b0040d541e181c802c0d0b0b00c003441040014028194408582c1c1403281104804c24040080b030340e044201445004000e4a801900003902d00c080d5034462030b0f07013032135024000030300c1820305094440c070800005000103150700282000303080f00d030850800070302034142c0c00d8100100100d0502c0783c50903541c5110005c1c180381d8515030000d10070744002a0010400e1403400c1c0c400325207901c1084441030415200d10159100c00c5841410b00800d40c1c100c44608400209100b07019880d100100410b054035040401203202d1800c8030902c81c0940640030744801310426007103000088503 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 755528183 1250 755526933 755526953
    0x60301020c01180b060f0120070b190e2b020d020402030708011a031611010e070605070204110408060414030c1906050a0c050307030903051c090c08012003060d 70
    0xc0c001c20300c0e420b51410b040c2901c01130002880c69002d00003407040c0180e40e03a009501c1c180076026030141e8185282d08112040d042c2505603100368190140883c0600c0000380c003440009000c0c80c40e585000c41c41c62604100090074072070380c1200c002a0303200030040e507115610100e005052800586011844c10f00e680c0882c0499008507404c4000480f0383c001804070030104100b0701402d00341c46920a0450900201d401400b0700e6a10b040010300140700340c50700c0301078829044000c400f0a0b007000c0c0c4486642c2e810000e0210384c007603c82284103500e40404040c0800c03e450a072016901400010945c0d80d56559414485610502e02c0405a100901c40c0580540d01040884000f051440d1035583c09030141c60000d007520700103080c4000150400c40b244603442d601c00c095907403100640c80c1c041136a001c5030030113075600d04c0b03145480b90303403d410600d8880f002c2d41c0540080c0581071288544100305562801e0341422190074142510120111325804005500d03848044d641040e001400390009500076501e40e8a51 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 755529433 1250 755528183 755528201
    0x2061309140412050a020a0b011d0c0903060a1a100f0e1503010504110f0c1507080601020c0108100b0c0321040b040f020a0b0c0f0c040c080a2304050c100e09060405060301020c01 78
    0x83c603641041e0000907a0172100ad98000d04410b00550070500c40f180040d854100051020840c980c0d94003d83c8190907000b182c2d0552031401401051505c42456070041c00d03107170304940041c045485030051030502d00744241001c1d01040f4400c4018103603400c01301000050200f0311402004040180580341e10004103800828024442c1e0005080207660244549858138000f4900020301410100300130041c0d0b00032400c100500c40910b415040743e078070042c01c1c6070f42180c142c03c440f510b0400407428480e58207002004284500000d20071032006600c0c140302602000d0110740003005083c411000c13600041545841c044120310040031036a103603403540c404030915005840d640c074007580901b610700c1c0588002d000c007602d2005e0541d8140220842c0d0705002e000300101401c2e240d40306580e0050860021204201050358424404081c40070307042c1420015034641010010034170418860160f1074400c1d00a8514050300040035089640c00d945410400005081c001c08413501950204940340d11580207110b440e0007 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 755530683 1250 755529433 755529449
    0x601020a050d08160302070f0605040201050c15090c0a0f090509030403020904081b0f03070b2d01061707080601200607121404030509060a0201060302061309140412050a020a0b01 78
    0x7080c40d0028080c802d40d06138214800900d441000901c0c0440c1b040c2d00b10011a40d003100c00402c40e91144e00c0104c07114840c0c03c0c0700c42030710b000b0103600c480141d00c1e40e440d41d800340003803c1c03c503558000705004100c065107903071090030210405500d08100556007600301c20381c020300d4201070b21304240c0d507500401e0142604442c110341c05680001c4400d80403014044800740850900014080b8082410103140d03240300e03d01c005050140c10000282000250b0000342c1404014085800004581c91210580040b402e000e000045108039014607100958091f0081c40b80446607034a1180f916014012f540342400201a14044803250348500c61046003000030134060800707586c0700c07000711100d01c0600c0111004408003580c100c0b00201400b001c2544002503d41c02c81080b1052651070858260690060200f41e2000307402c4040810380c3c2c0050044030f0001000c840c0b0009041c4090182d00f0680c001104013264028070300b0100350200c240d010300c03943c0078007c0005a401140c081703500503101c0b01300030f44090703006401e = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 755531933 1250 755530683 755530697
    0x140f0706060503061005030726010e030a120c230c06011e050f10050306030f07060f030507030c021002031e0a06050117152e0306090b03030405180601020a050d 70
    0x4200e00f01003090310ba00041440c10041c6541c10000000e0302d4185078030800c0c40d1541e007562840c03203900103071008000401c0724034000c00244100e10f2401c0d032030390402225503000c581c1006ca45011081103014840c498810b0760354801c0d4000c607030350002040c000d49140341003034044180080c0340107080c10003240c0e001e01041010f650408a100140090805003900030768003480c207800038403095446465500e01c04480500f050740d266520080864900b280b5207401079014800c050002035065007228040720710790201d42e8240401d54400c2d0080d07041c1c1c1e05070046840180d000c40100080325105031301464124034103440354030740030140781a0f9403002442a5488150749070703584c004000c0f075030308a0300000084401c2e040381c03206d51410002c2d101742079404078181c5001d2003904401909101c500040036440c0e803442101000728020201000b00144214020810240d180c003445000d289000416181190b00041194203510300f80404114031110143c041070540c402e00b048c10000a05c2880b81941c0c0c0714690752064 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 755533183 1250 755531933 755531939
    0x19020f0d050a0e160e2e03060b010e0405070e10030b151b01050108070b180d11090108030c030a0c060b09040803150406050609120717010614030c0108040201140f070606 74
    0x4c1c240300700000b68440c01448480c007000310b200c0c400760321303540108a10104000d07a8810748030030780302a0420044c0c40303079800c103030501104100c46c07175001c0146110280e880d81c2c2820485003c0c0011103400342c6841c804030388414134415041c6484c59110800e28214640401d81403451800304443c0303030810000000741c2e0350119409603d1a640c050003c240c00741c000c024416549880d000b151100850700800c4683c1000242d80c1c115501d10607404100c0450240c51084400410b0820f40304840030100300700e1013400d0b2103000040010300002a50791110300180070314900140c120f000d44010418500c1201c1d41c0d0f0716124510002e5444c0d05103240300328010030649580e450002c0541d0306129828140d02d106a240910510907510f828007a80c4640c00240c5101c01e101c280004002e1400c502d66000c01c850344000006440901d83c190401c0c0122041d0124000c41078041904040d190505000c460740000c803649e001030701545c800c40701051400c080e1504180303440721441d4407002e294444442503d0035a2243c00c20 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 755534433 1250 755533183 755533211
    0x309080c0f060c03010f06080a020c030406080405011508030d0213030f030201020702090a06080c0402070510061e0819020f060c1203011502060403170c0405032a0919020f0d050a 78
    0x4503503c401c114800c5443c540c14501c000d940c1031594003401c0d007002154000104c0140f0664100c42030586181d0441346c80b20358a00008100c40c00495013140c455003048000e0300e84080c90005813040d0354151002e90306006002079107130000d40280380350303000ca440e02c55400030118005860f60b2034081e00a41c00581d03116514014000d9088000c0c00240000740340403410094880089150003001100f00c0300540e41f0320392070600758944030354240700c014460b1900300001201d583d00c82d114030402c055042440e84041d903a04003103840300d001540e80b2000045904140005152a0016010105004240a060442d000c8406190500001e404c1e010982c0010041c8032051030f00c800c1c800c0714105440201801e144c9a0340080445005482803600e20000c2000b24458403201c406940103800040c08590017004002030f042d0000c00084000b01d080d032170314416010a414081c900078401e805105d801f10b0001c4d800450907000394070021015100740c00c140440b0200008038010a401000d1140e00454041d000c4504 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 755535683 1250 755534433 755534443
    0x120a0e030d0e100b09070c12110d09060207060e0a150306180f050114060a0315150207030c060201050403020d08041109010314060901020c07230d140c0a0e06100309080c0f 75
    0xe40d0388108445c0d01001b000c3c5501040c0c4d254501c0d40450a891200c0900c1c0040d64a00c0d80c14060290901035010030b0301b460369100400c40215041a42200c0c3d50300c1e0368100a44080244241b055007001ca1110140710341210010080e5008502c0c0c600011001d03911004580c0f0500c0e5515040b20301c0d9200d03d10030030b980c1c940703011300c03405413085409007542ca80000d8001945846980c03180c40030b040d01e884a10810040301c4c07c00800400003c3c05108a54000f07040c029210702860004441540140e400800e64910502c2064800c5134190006d02414641100a4501010061045801003640c80354401940c44d80c881c00390082d8801c50308603000c00780140c0e440d4104800148086030b11780c070510100c40244030015841c2c0496101056000d48500c80d42d8045030405400c00760250801c1c80a941d030710821003010943c80b800e940010030380d40440112000c00101079044e100c1c5120448820010540d180b8201c404a01e070b44010b414001f034a403210303940340c808030b401c010589010360304108009002502d081c01 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 755536933 1250 755535683 755535701
    0xc0403051203130f060609050c0a080a06050109032402070f05010b180a15080604030203090a080607091703160308100504060e0703110705010608010b1203120a0e030d0e10 75
    0x91102d0840c03034508200700100b21002c00c06042c50186242c02c0c014010198890b602600d9540310500051404c1c2c0c001010b107911011a030000070b800f03d0006403001c98588181070a656050307644042142c550f85441c480007241110f500b02040c401600c41202c0c1100d4030041c01660b01c10b2844425071612801c0c01f5003115441d181c0315011f28060703403818059514030a1342c2a03010b01020030010f042402d081c40d080107000e2070340101e001886200103001c280f43c0c00201030041c4c0f200c1110400c4d11107071140502a1159000d58040c07000c5148884180500250048480c040309039450859044c1864001b43c0c240040621a003a008500303051b00f403003028414000000040d2509540c248006454010301d502c103000d000384070104059603206002d0443d0380003400c480505070004028808540c41c0c0310f00b113000340410020a40300f69a00d46079182c0e0701d0004070690302c50751452a541c10495494051a00107401c56140c0c0143d980800c00c030382c9070500c610b4410310b00c4400c0700710b00500360024421040d00031501c18030 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 755538183 1250 755536933 755536963
    0x304150816080f061c0f06050417070f08072109030c050102190206070305090d050c131803030b030304090c0806030d0203040b041a0403080d0212180a020d15050c040305 74
    0x58100b002e042085a411034002e501176448080c0680000e840c09400e120303840380105584c06455901d41802450f400c0240500e001d001443c001d0407a10540d0425441001740c014007556000c4443e2021030140c0000d40181070245900f00c81349e03100101070003041002c4602c5800481c0000b6014404d0120102880d0040d100a0004180306500c401e014000000c0b5118001c0c030401000692104052003403040da9070502014103020440e803803e14200b901d400c1d82601440c083d0010f11496804403031680120324464508010000715018079440172805801c05504054041c40100000100400f0301d12071600102256a508800307810b042c800c01d801c04045681e24000c5501c00d10003803210f10620300c2120215903c0ba01224910590121503134034501840e800502051400700701441034902c04c1d00213148e071403041048116199504c0701035014240072a00c10041d69131151400800500b0001800500c0c2401640040030780803110040714280e940c1150038201080000c40d0400c1007040411002003507e40384 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 755539433 1250 755538183 755538197
    0xa020a352e0c021207020d1103070810050f0f06040510031b08010e0304080303160c0606091e110f0a180305010605030f03070312020d0209040504080a1418040507020304150816 77
    0xc4e540d1010038059424064403a058034803a0340300700201548100410307030001d07081d01e807a030b070307603100c91540b00c0d45802c0c9440c0019040c00f001a0001313400400440c401d020a42d0640019101d8106020091000400f10404140d580c4008170210300d440308210904800c0c800c141103039905080150b030035603200d030841800321341c42072109102a503800b0043d07942c040c404a81980d043d141c4900e00311900c01c07028502030b10032850004023155070b100c507800c0381034642d102c01020403a07580d5080100d4121001500b850004a0050040c5135101c095200240140001483e10816480e86100c6080007107409a100716502ea5443d07404011505051100103a400c490741c0140d424a0100d0300c002d02008100200200620350000d0f95034910720907136040d103c40000c0980104020315052810110a90080e616000403c480d00043e8014601420850300648505071007410020144010700020b00300141401d03055000c1800080340050b69000060326000d195a48d030301481c00c009200c04c5500d00781007000010800c072 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 755540683 1250 755539433 755539453
    0x51c24051513031a0f0117070e0720150108030a0c030c0312020a0f0e060702060d0f090f0c0302040c050301050f01110f0f0a020a352e0c02 61
    0x244940801c55406216686a680c40260b84980c02c4510181c10042000c0390103540b2480d010007900c021071080382e80b0403955885036242c00f05880049403e500c0030b581070340032040130301410010301d11040d0408001e041000d03007500c0c18080b00e10406500390074581d00d68000d101005205100b8a002c0e03006004400c00395140030901c141c010000c0c0303401040070b0240b00442d0b2000080500c80d107541c0d00c80003030140046440e045a0000244101c100e10150310000e0320500411880746009030032900c110b81c2c028050b80c5003507419918400a800c800e8038441c1c16136038803d1020040b6038910701e400407451207003110b0440b803400c40c410002150031150b4810108582400180580d8850203540b0340c0382c0b0b009090000043d2a00071031240740c800c0003010140c49020700c95002c1070642d0b0004180305154822514000e41d00d841d00c0c48030320b080380190401c460000685000c0c030058009410b1840c03104041000396004118807001480c454106141b0460032841903058000c411090307445031252403c1984050143c4d420 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 755541933 1250 755540683 755540689
    0x615110628150902070807050c060408071403010e0715082a091f0c03080c1e0c0c0913020f0406030203060c09040b0405070801030b07020f100c051c2405 67
    0x703800741510107081d580344000b0403090a06400d2070010591080203640d1083c03035140598080e001440111a0780c41441055100c519000c81500c003652b907880010310300c03075141c950a0b2180c0e0b43c1c003504c0039815568612015202c1d800501c03001e4050070800b40c400d02015410b90740100402c0000f4200b810401c050fa014483d00092240d8920402c1c03250090a921014690300151a84102d82c100c0c80203803d1001c440c400301501700311900403060094651441d19541c0c18150040b6220300c40101c0600b01ea50400ca074401002ca1014214002401c000c6072545850a008665102416034510100451150070001149403240301030950603010380b002c0c0001d500d941e000ca5a10207004d41811041d0340081b84c2988a03850b281e01503003c03014020024862400c1c4044043c004d014280025076010790098000f0319198000035200006400c0e0100074041031416100070300c0140280c2c10908101b200400032809801020805c02a180c2012a800113160091041400402e8401c601016030b040400c242004142c2d = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 755543183 1250 755541933 755541991
    0x30c041719060b040f2a050c0c12100507080115030b010903020919090b06180108070b0d0e2b020d0503010e04230604150b0f010c0606151106 62
    0x950b10040120b42d6040910008003d031905600c078040240c03500c5282005041000c0e85015502c0704880e039620819890841110248144640c81031550700c49000c4403041d0408000f4101f07900c80e00010750300c14000440036101521020344000c0006440c200042c01058480c0000c1050301103030341000c10606861900207802d080c198400640300d41101e00c001200319a003482880240c0d802c08004100c0b171030312403420240c86130041d24524003c1c1d02502900707400782c82c0c00c11243d058407042001014141e00d0040c620000e40d008542148808c2d072584440484a14200f000840c104081d00403581401046c141854000d502050a00704640c41510f00740b181c95007250849042d200c094800ba01d2640d242c1c1042d844203584001c5642032100d5071040d030454100d004c914680680e2240d6822562007001d44c00c0f010564000c1c584c2c1507404240c151203c01c0c258040e091503c01584640d101040c0155516803100c0110030034880f06000c01c40c00070f020070b00c040060012a078400c0d40f994902007409444140d400d006 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 755544433 1250 755543183 755543233
    0x20607050307120e1806040608010608010504120c1a0a0b092401051804020d0204081f050912090127080c04050912030415090209043f03091403030c0417 67
    0x1003103840d00806d156440d41e4102601411a1034000c0c07003041e98403604076000303042c1100e003928000075001d500c42a4030310404034403041c1500121408000410307110a43d4114001809501c42c0c1c0d9540c8950f00401e84840c210203100f0075504c04038000300e50b500c0e00301424103000304d0491070400038200401e03000601d40d00c0c5091042481504d005032642c15864001c0028421a0405a0b980c42031402c080c0084040d5400302e10b000503042d400748101c5d02c805250a07600c1174040e1000c42d01081c248075800c6554821800300d074103804040342c00144100102040502608241c2094916400c075090184450a090145607002404d0800611551903a41c10080c00781c080980014040c1600e0030380f5910b01607450300202c10658004083c44180d0400b0300e08034000744041c03412015080c0c0444000c0c03001015005810402a0454180300c03004241c0b40000c0300180303021201220850400d0020b691040d8003040554440c1c610544590765030360406800c40006400444081c0036070b404000104c04442c8458014070803 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 755545683 1250 755544433 755544469
    0x303011202060f12060a09020702011b0305090409121b0c15170106020c0f03010203040308010911280905030a05030a0309030908160e070f0503040f0f020607050307120e 74
    0xc00c8489100090581c4121440104035181c04a40103040700079500000c1c0c0212011903000b014181d03151068401d81c0900403010b804202c0c03040c4400408444000040501c40c802d2420034074020030000020111103c03000251107554490190256442d0819140c6c800c4110060000140b10410b944800206660340500503611011100c0d0304003440c0070313034004458044c1c0e66010681c10741c2c413490001d640300b049003003541c8240c40050000a031803c061080301d00070340c2c159031503d01e035a00780240180a4141d00f43c525840700010000010201442c00f41c6050b90040311604468102d120382d80142205030fa07030001c9204c1d80041140c1e200042c4004102d07400c0810030b04011034100581c0c10705035021001a4810002401075188883c480c0310f00121b00c00c2074402566421000f901c0d100c808480d490a0f618400c03002c11010030101c3c0204480b80245641307244645520f0562a4007036000c03c0c0550071100303044a07940d201140b28402c01c45001c1c015402c00a1529100d014007007040c0008121501c88034480368 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 755546933 1250 755545683 755545709
    0x3090501031422080307020a0203100618050601050d06080a061b081305070e07050c01060b032e0b1c0c02061303050714030324101e030248030301 64
    0x110f01c03049800750004140c000b0125a180d1526800c0a51a04401c4508900c6802141c1a00180210380d100c0c90040d1590b4514a0406070710001381200100300151045050143c1402203542140c0c8034060140503000c824090f0160b1600c0345400b4041d2080c1781c8811480e407001d0806c0f0171109600000041c3d00150007805d180710f04d0f459081c5282420655000108582a103c080006858004000341034807800e40c00200101035032808500150300013614415200024414040320620300c1d000c010480c403040505408400c1e0781c0d10300101c0f09900021a1001071f190001d90708201c910141700e801c91811190002d0030142c40c046032184851034410784010f00b4804d021601006002c0c034402620740c15a0b514044039500d0824007060503103443d142207905900c80905a41071114140303c020494017075069101c41c5407412050304a4109040c0049003c01059401c2c03240c4803190061100d0034100c0d00c41e908107203814030240308074005d0078150444182424400c03030b40c413007900f604008101d03030459030f648507481 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 755548183 1250 755546933 755546971
    0x1110f09060304170d050601020c0409020f01120e0102030a1d07030309030204050910050903031906030203100c140a3b0f15031801051003050a06021c140103030905010314 75
    0xc51800013500941c40054008254002216443e5000b540101030907021200e03000318800410081c3c4078000380003900b116070100c90401e035501034150500c071001c0982c000f040e450005c507903440c22a00210380e010240790301c0300c618074a0201c000040012054241010300342d640c5c11a1400780c046580d500c4001d0095640708001144010b0600c04a003041031502010700140c242035600f59960b80040d03441d11070000101030a008401c803075104440880e0b074041c024000c0c6a0320624024010602000554240301980d4400c0c0701c07808850004002032419a11000c18502c1089036103c40404455108094080038001c880940d40c46c03c150608900422100701c1c90540d01e030008100400302140000d84540c001005201d920200840c5400d0710314102002002075580f0500f046045a01510010307029400c00303900d0002040c01600248085200b03c0015418001420300980841c2d001c0d0414145400da800014000c040e07101f0b1a0000611091030300740900d0074400400d43c29400c01030319100500303008040348 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 755549433 1250 755548183 755548193
    0x1f061403151501090e1603050a021204120512040c0306140c070f020f030706080105030105060603062b020d0305120901050601090612110708030114031209090910050c0c01110f09060304 81
    0x258028103811510174896040058440941342e0350110060040f0b400e00c8001101e450300c80c401c0c2c50a180744a80036031b0386178550b52680d030401403e40c5d0107002006030400c100540d49051020050180f80314042c045a4546141000d000f01da445411140c540c01c0b04506200d40660100291210640c009440f0002c082c000c0c80012400541c6510840d01405408030005403c2d410655090489000b074000340416501c92007000560321040742c00607880b540540110700f549181070342450300c0704490380440c0e06011113500003a01c446400202140002d400042e03042002c143e00119582100810001b0300c0a41403000c000780004030680a80300404c428aa0200031064040e002000b4400c0c20f025082c1c0d4500b9103040c000c80640c402d001d100880840c60410441d0307030900044081100c0b1100c1d030640d0401100f50100200f01c040500700c00c60605c20040420f0001034144110390107100152211075481350f08245640c255810740c0c14070100c00d5003c0c80320f00c04480c80f42048400402c1c00b02c0c0c40640d00e9441e4544 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 755550683 1250 755549433 755549447
    0x604035f01050a0903121b050c030721020f060103050c0105130e0a0912050f1c0902030111030a1503050604170408010207030221070c0b0306031f061403151501 70
    0x20305007503080c082488902d114075401541181e00a585100e40e401007110708805035850880994400344944222408961141000d462000400c0382520300c0d28a903a114661044c0c0c0d80c1d0442e08100d20907203031001150350100a819204008a0080c0400b5850b40c0c646a0700d868041c10094144000001d1024201c50001c0000e00500300b44208040903040103850040101040741c81201c071000711703040101c2c1c031038062420b5407001e6041b000c0aca880c0c40d0030b001c416003250403503900481060380c5600012006070f13428000d6440c014a0346220039181d00c0c00b001b040c3c094680b4200c005032607d0701c2c2c0c4414004941c021940d03a6110350480d541000390b20060344000883c0c0f06561000341c0c4d651000c1380082c10150b02040607020888180c019007110007603803220445502c00d01400410f50140810104080480c640245600080040a450926154072140e03510702c0312031581000480c4c5e4480c0d00740807056841c4a0b41c50900c5041d8020b0044010540080d020f51a01038000303001180c0342e1041c6d0085a01c9a50 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 755551933 1250 755550683 755550863
    0xb0307050a0305030c0f1207020d06140f160306034202040608181507031e06050a2117090a03120801150c0b0411060403 53
    0x1c41c030300342150389040c91501e036003103c0c0c14260a4001c0724981c40c0780b00000034014903008000708009203030141c181d08025400e401c2c08001c0703c0301d0381c1381d004680280d00c5848000b882015441c14845031441c140d40ca0300444024030784d0340002c2c5072400d2014004100d142280d41c5214a0020400e1000514a903101e0841da6140300b5440d480d00c0b40c0e980308030304503e00350054003c4032800d80302c840c141d0b00c03113400701c0800c0c0d1740403034440c06240d0200b0b04854094448804035604440746040000d00000e09040ca041c0410000c551141e40c40d03114036040005080403828100144002035110102e8510308420a045c0c290700d10000c1c0042d21030302c01031810a10042c0440c4c00480000705040f822595900d05100300ca0300d00d00c0f240001c101070100000e0803c81c0f0030240c0e01c1045803669842c80d07002181d034901011440180081d030701003d607448401c482d43c840200070009540a0010171800070091034494801e103440c03004607107040c00c0a0994283c0c8200c0003070355000a01580440d00c51110007903809a01d020071200e = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 755553183 1250 755551933 755551939
    0x1220090106050c01050f3c0108070608060603040201050f072a091506050d15080304080a05390409050a0b06032a102c1c050a0201030b030705 62
    0x800020340203400030014440d40189000a01141c0d88510f03034404010b00c01ca410081052100584520714080d0740800081c01550310321001181c905503c14800300b6500343c1003c8038649c03011005101080e0402e02c00d40c1d010307004071007031407443c44c250740001c10502400504100030130011a0707100403c441d848510041c4a58001d00d50911031150f10340e052004124401d840c5098504280d091814115180c180140d500079103c551928019260b04030040003c8038400c4070f5014003400114000e0ba017400200700a0441e000140314414042c18060b0500640a00c860390b01012b0040070002810010400b20300b259031541d000c600b4039040301c00303d006814442002851400340003604010400e4480200303025410a800712184030300078013540c0514802c4140d44124034544192a80761901e13103008908640d080c54034140c064102d4003d400013200f0041c03152803807942c0c503420031203000d8104400c0c00124500b40c02c940d600000182c0d01e03003d41710542908082e0415403940180011910b081060800824000d = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 755554433 1250 755553183 755553199
    0x111010b1e030a06020708192c180405010501030c08031c021c051602071413050907230f0d0819180e0915060109151e0503090d03061220 60
    0x1b0345000c41269010914586890300040c1c408241d0520486503244d09034a1891803014140000b01c03140745940640043e2584106404005915002d80401890240c0d21460012405c0d5055141c813406c2008250400f0703499510602c140011300100000188402040150069880c3c40800318a21030000c40f5000b95902401d2005200004417070b001e1848480000740c0c00d4440f10b0b92038044901100c40e00403401030340490518160103201410b07521183e0003040000894001c666035642c009040d000c0c24141e420354006c1081c2640170740c201030705060042c04080703c5070801c2e00000d64401300d180c060000400703146100408402450342c00f0381c28519000e4505000158841e56514910115420490307803105580201700a410540c0e0605141c0c50040070146c4403185c1e40d5090240710a5020743c0744840070b04004240103c500385107170140030001c4520b02542d40341d0b60381c03900c0a9810724080c0990b950808262030400c040110b07120640945c01200c0c0d0100f08041611100c119004440303611b108899071200c06 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 755555683 1250 755554433 755554447
    0x3050f0a020d27090e0304050d030c060b01080103080403320a110406050d03111002040303030b01020c03121e0405040203010f0e0a0b0105040b090303071a060111010b1e030a0602 78
    0x240c4100290041c3d07100205914074403c005044907002403c40a0010308140c01d0280900301d0f045030a035036005008481c01c00307035120009a0308a000000170b1f0045100195070390203202c114001c0700013220003804c0c14003240d4915a07410941c0d115a1001800d42c1a040d49800d0444e68050f00170302070072100e0052401e81b14003908020b601c50410200485994000b201c0031034060070203000c1c1c0c0d41120780c010480812888140c0b825500c2d00d00202e14000140152480142a2032040c07000d440a0340c06a43c00040c0e00c60902c002a1030207a00440b254401d911180000170300e240d05408035800f01022120400c41c0c0c04000c988001580a16081039901500200000c188060209503034411622858422501500d941985000300c448449090f0300040c002c02042c050020140c000384010318001d001c891a00e42d8a45a403406c40088481c240b08144280003404055139000310500c1100d0b070b024000708145407142c0f000030035080603035540100d0200d2000c0858100c3d64280000341c0c0301600403905540d1080 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 755556933 1250 755555683 755555687
    0x207020d0311010e101508010902060405090c0f16060c0e0d110f09090f060601111b1318020306070302090a050d0302120d0501150c05060a05252c090109050403050f0a 73
    0x1040d03841b0302c202072601036000282c440050203050000e0b0303000342c201c07442c09081509000103500c1c02415070640c020100560101030010000070000081c01006115042542d40380500507100003914a200300414019203800c6039841096003c1c05031345c400414042036105a001c61800c02141040130303449029402001740b10000031609d600103912030019034900d80d40e0140152303a9007081000c044842da11883d1b098501c2240034007000106440107058010341c0807161034100956207034002c81ca4000300513107881c0046040812040360444098201076081c22003080104e0000d04091003001c1c480c0740e11030389030800d0600038000d441401d41005610340c1c0e41c031040e151f100c1c05000c00780305980e10900d40740181c1c02074500c10403d030300ca0070368404007a00c22501c5030f0b40c1d50030103030030701070000d20001d102c1c3c20040070402140fa02030700446400344c031141070b080171300c41d03c40740c000c80d0f0101e16207044c3c182c65181c017a4569403040f0030390640d103294400050317075140d5050817250783c01440c3c0210844200041c3c3d03444015 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 755558183 1250 755556933 755556941
    0x31e1103011e2301060e03010f09050a0606050603010b1804020c0613050c090708014212061203050d06030204050f01090f0c080c090f060d0207050708010207020d0311010e10 76
    0x1ca022001480030901200200c002e80e8510f05200d08462400e00040c0301e024800d01c1c0e1b00061000c001c0010980a035800c150b5400c80300015005c6549a1004100a04018850203070f07800419080f20500e0556241242c0004c0303522440510301800c080d00500070313950382d643e039055403500031182080342d2072842c01581c01e00d1010601034055645116103103120740249440d10a0038400d242a036640a5140d28020340704a4031003140341211009081b04007442007011001c0d03099000f410442c1110301c039110081c03002810400c0c100321a2841d1604155043c80005564299551000d61500d8207175510880702580c10014404d90704000c2d4410308041c18041c020311585a500d050b2940f14504100075142c01400808a6942c40382101c0400e910000080c1e4101c10403005e00041c500161105a0700902d040005540c3e0b0310005800070b20710342c040b0b051414031104004050160110358021840c0402c41e4000580c03031021034600400304407541017100502c00382900079860810811048800c1e202002403414058 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 755559433 1250 755558183 755558231
    0x160f060c020f01090206090904020102030c0d08071b050a110105120f04140604030f11161e0b270625030206240409050102221a04031e110301 62
    0x14482e07580354910000b8113100340140f041d40141854503140f940b80901110640007001a4154001401031000b01c2c807080c400296000c819a9a00e40207217030a2034058095070748401611008a80044210b000030340005003226040d422504600440300e0b4040102c80d58410881d440c44081600004c0c003c08031700c0d40c03c500f1702803840761585030040e4814215085c0c1d01c100884010300050811003d41c4105030180b8209540c0384038010a030781c1c462900600e081c3c021103665010802c220038010200a00e561200200801f0781310300e1348107500d000084990700700c1c540c140d0308034910301a960020030220740d40d42c401203c1071f207810181304000310508102c45000445c1410000d8015002d550001000c1078a014a500010400d0501410007050907805020040c0702c0c1000440d2599820000c8000c580000042803090305921020741221504060741080543e4800000381d641450901060000401100710030b80e51080e029801030501145043c9900c0060a848a298242d46011081c1c0e603094040030305541e030 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 755560683 1250 755559433 755559437
    0x512030f010b07021011030c0a050609060132180a0b1203031012021825170109020d061a070606141c06140a020d051003050d05160f060c 60
    0x11a070ba1454904418030070030000950103014000d03039010700da0042e0b0403400b444002104030781c1003442541a062078002002401d440b15480101044601c0004106a601400c450341038144418100881748001c9005c41019881c0c0b682184811099a02c40151321002c401b10b0302c5510045092003289030b00100742c042402e9004903121203103e4241c181c0081228096030a0004201c20246488007005081e1070309a400ca030f00500c20000d12004071003041815000e11940d940d45410380410000c4213003a100c000c641e00083c042c913028002191190002124119580c0b141f025a032100e12103a450010605a042218000da8040202704443c8002020b80040c41c407400d803c110300754554900c00360000700c40c000d40341d00410810320085200302c2c07000e807411000d11a02c2c1c00300d4a0950240e80d804139235811070b4840e40c0e281d40810001c41c1b254490190076003180c01c0c20418280079040d84c40785619420301640c114180712001030388039903540e007020340726001ca80c01105040070100030b45044009468a8a14640 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 755561933 1250 755560683 755560711
    0xc08070b090c01090315020a0c050f07260703080703111b010e0301050405121b0109060902100809100507020f03070807050c090121021225080c0a0b0d0603051203 71
    0x10b00d650140c0034800540e50000c000121202900e11203402940c40020610204072070507054400240b002c11480f0001d02c5581c000c3d1044a0070103820341005011005008420070031003e580d100400041200800d482d00640860f54450b560b0a050f06d100084810b2801d0138800d1080381640c20f5a00060101d0005e4240d94030344410003140d040500b40da10554000d8001d800405c0041000102030005141032210b5032034011f400c0b8030074a60a421103648100c1a00d455480e802a0411460003c1d584581c4000d9420200300e40c0c1011600c156030b581050083ca218a90b841004c00c001a000b000310020806070b000441e40e4a01040ca080e00490b0452081200d03d0b00c82d0300c410360042c2c0b40441e041816110507400c1c484842d0008580099544d142e120203981001c4818600f00d40707404280042402d00c8a00c2c05d082e5104481c20304842d81c81502a130100c495a0820740d0070b00e1f444d45e9841a007904031032645100383d445010309007500c802413601e40d04c024064403440000c01600346c0c2c12030295109541d0580320700 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 755563183 1250 755561933 755561953
    0x316030f11181003140d170a0b0a0815060a0608041203020c0f0309030d02030a0203070602090f04090f050c060a350115091e0314070b030c280f08070c08070b09 70
    0x51b03031145104003c1c070125200c0342e10500d0380408803510790780c40a0410408a503c070003100114070800111b4200c0c0342540c10840c1c0d80079050310102407082e0080c605440450280f854040010454940074100402103040300401110140c402d4050324100407205040da0901482c0ca8209035484e80311001c0c8500074044d4102c0300100900100c19100b5024450b00514034003189584c8010007035219403d11540420255116201038039148104541c0303e11840031800c1c030015600f002d1740342841c0c40c2c11640c8507800030800e85500c1980018500c440195160f000c1012940300310000c2d09a1034890118607115100c070000103104c2c3d038406c00c0c412600d02c00d0745541752100d1301c48001c080d0710100d100c00c108810a02c050304100185404c00e203485d4a00448040c1c1b10095101c1a103203184c0c1e130050ba02201c240700042000c40540c804a9101f8a40341161044d05107081092351010b01a078000500c1d61040c04618000682c00c14002d004441c03c40e5400030501c0e546551070724042d10500421f035649002da1041030300d40 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 755564433 1250 755563183 755563223
    0x14010209010816350711010e0604080d09020409140303040c06110a2003011509112505120a090f0b0a020601030b0a1e0b0316030f11181003 61
    0x64260a6036030f440e002499010407080076900480d41c5010348101d400015070702030740c040c21111800780d08141d0f0b441d048021b9040300e075402d4031203155100a042c0c2043c070038800000c603c50120345001d40440d03008103e058440c00000e0040510b00c4000d0051441001c40c2c3e010100080010340c0304512a100280700b0f1354484000f25011040551400c01c0c1e41c0c058031162010691b0041195042c0017426454604000c0d248042403c0d00d029220494403200c1c1c400040c0310381801c5006440d80c80141007012802c0c88078035083c0e2418118450010742c84103003000c140d0001e2200500c03c41902c007513042102a51a600ca202c0185404a548113402c4035a88038400410081465002c4808030302090303009246130f90840e10f6903c98a00049c0402e8001996203141c11a0703168034080c003418029600c071000882ca42c1c4017080c941031802c07010380f802c0a26040c03941400051480e204080e04907420011003000d0318481c20102c0d25820b4007004412401c1047c400304052207107445600ba050f20320400300c4080f070070291101 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 755565683 1250 755564433 755564461
    0x50109050d17090604020f0d050f06010521060417070803010e09070b093706030e070b070c1505090a0b0c100e0d1d060a05031605070201050702010c0f140102090108 72
    0x303c480503004007000c01e003d454084001c29040e4001007440c1e11028450f079030503203081c5070034410318000d820900c0100010b103400e55007008000a240c4406e159516620106d41d100c00d001800106010180340c268003030081d01106450f0107a5010813180d540c3d58648961090032001200c0696984c452800f005c00ca400b0400c05681d030024000e01400182ca1010f8451242a59000300d2900030f07641e440440130040c048001031a00800c42d80e200040d40c41c60050100d41040310702d402861540c0300800040b00003070224030503902102c01052001c50380c2282050100d8152040080c0c043c1d00020514000c41d002c039601d001440004440812254007094441c282e501742d81000075144241c0d0440c52814001d240624000c200c1070950809000c80c081c000c10003c3c403650401c150080010701d02108101d41004411581481251542007040c10403c4035400200144074684000b810801c03612403900400501000b404031386036200365000800002d4420b080d000b50481c20b0710900081e20710000ca074602c001084 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 755566933 1250 755565683 755565691
    0x1b052d07020108060f03070605090913020312030a0b090103030906110c0a05041104080d030c02150c040b0906132403180303051905040b10150815060403050109050d17 73
    0x12014203108054006680c41c9400804950f004401c041c0d0200c160390381402910080d2580c1e44a4980350501441804059500202556081d82c0c0b02d480d2039000d80e0b40058002160b44920340104d6503a80d40001c00005085008405504190080c00107c10541c00010340c2043e13440e10355510130078a11142510703070f03984c048213040c60700601c009400748440d00b01904140038540f81c1c0c5015600c0c06517109480c900d0301c00c44a0b281000203a46111041006a0510004c4a20304924151225908003421000c205114510602141010000d074803141c43d1211815105681100c81503200c03183d54070000c2d002c0d0030039126078a007503607510901c101441c240244212401190117200081e0307044015901a001020050090b0051035003c0042d00841c0d9003a00130b0600c9103104503410b007200e0400b113202860426983d0400f03054001c1210f00200d0040d80010301982c03111404a504180c03e02d80b45c0420010b2246400180c442d500b480011402d001d0002041c00e8141602e5458007a456683d196030144c20340292 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 755568183 1250 755566933 755567017
    0x3020909070f0e06030a0522030e190825060908210906030c0a0e04050402030a021545030a0303020d11030703090201020c03010b0f0d061b05 62
    0x501160025102d5074000b000c0300040c0c14003040c1c0003003407000654150800caa0462415480301c0c10046c200704114001c10f03480c2c180e4106c60381030241664025001440b501d4005000f000030b44a05031591181030700801c0207210b503078290b801d458000d9841c000b0781010340c411844440f00d110390028005201c1c018500c21615040c0c094500390000c1002c1c100f00001d0036902c1c2c0e40b002801d0084210320303a2031500450003259841d4815660709403503500648016000c0000900c02c030f207810700300000345e200818480039140e8112526800411190400d0000307020b80c403040c95400310405051510141601c00700300c0358400450108c4d9a00c06c041c0c0d03840d140d0702c1c505c041c0290160000001000060b000b500038005423604000041200085038440480d260802c9460000190f01c1c2c0d00c084084d541c06000700c030300c0f54800341c0080c48034401a0380400c403907080801c010b900070703841890b82e501401916030151407600e940c0d41601111600703144009000c0c3d0801c08410004070580741070b10494003003481100f07160306901 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 755569433 1250 755568183 755568199
    0x312020f0106080f151b300103020a0b0a1101020a17010b0424021f0605040c3b040203090a0b010f060e090c070609050d090b070c1205070f080a03030507030209 70
    0x41c13420515414000c0d28800341220b168800101020607a009044100b011800d542c0140360310740801a01d0f0391f0040c202200030020b03c40140007684650f102d20083e1082c142002d580e40548210490318407110803140f0b2265417010592103042a03000d54560306e081816080d41c032459803200b645510318891841000c1042e0600245003214001100005502181e24015143d9080781d1801c80110414440850070480d0703565482840149454481d8807051036075850440150783e80c0c04c1c1910143e8881c10380c1180103c41c00044e007000303001002c020080c90700002c3c2c000d54407070401150090b640e0b00d43c6142240c03d00765950000c5903801d18204018201d4a40d661800c95440d80002031158882c0003909444181504005010203c2d142e4007400800e41c3c40b0740001e120502c20010010244026a000681c038204104000c101244041d5400010380c0d1100916407240e00711860101d243c181c00d584600804410840002010b12002c0f074102400d41c0691400d00036542e444904800b28800c0e60001540800b0b0 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 755570683 1250 755569433 755569453
    0x10e03070303051f0e07121b050d0f090501060812190e010c080304030e0a080d05040308090a150e010e090103031b15060b04031703060901090f02040312020f0106080f 73
    0x30a801058018540d01254030a0010b04a41c800c01e240384c581018245c01300c0b45c0c0038414015403080e1901300f00d4030518000c2214001000380c0d1100c84030a0400d010422a0205000d541c0c0511603010b03204856a591040002070b2007458401d02030011071007007c180380500020042c00e904146c04503401c07a16485450140b40c046880306a58503911010801d042200c6010300b41c0009a00c1c8006600032406034640c032010100985c20024801d159411140c0ad5810166502061681100c1070f5001d4030313070015140da1251840004120603e0310f59001214510441d1110303242141c1041c0780800640c420780c0d441d85502d0700031003404810364083c440240092a0301044102d0090320003002c4246074403075045250384015403c0000280e4855402000065400040410410110580c0200c41e1903900c840c0c02d0451034010b0003d129002d0512544460540354002c9070455030055045902441e4010f03e404140d400d0141d0003950b5221540789002c5640c6000004076802c00001801001c45a458000340400e500e = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 755571933 1250 755570683 755570687
    0x3090206160809042310060f03110915030106091a0a0309060b1f020c03150601110a02100302030105090f060f040c05121e070504080303040f02010509130617010e030703 74
    0x50768501c2901c0c0404203021180d03440e641d500901007440e00c5140e0b500038400c2140303000340720a01c019080f914100c20703108041008640120750807030141c20034200018580203001c2d8190301441094003135644980302d00200c103940580340c00a0341c16a0f5665442c403a01549402d12404400700420b4ac0381441d100912a11603410b00c650445024a881000e0210b0303800901c00118140d90400c5910005152a29083c10701140d4100300c10889204110014003c4070b5050900b81200007010341414104608180009000c480c00c01560103510340c0544900c050103444c82e030040082d0028015184180005130200714070030000c0b032595004d504020194081041030808000c000e0403481c0c14007050100601100300121848800c0e10322072a008400d4002002042c0400704003600d00900c07a8052110621051003040303800010f0702d5115500c0b0910044400403800103035042e004011840b5407101c40c0d120140054911034020700c080b140403640d04c40400c40110340c903e00740d40e41c110744140258024400c03240401c0c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 755573183 1250 755571933 755571967
    0x40902071a0a021803120409110c071d01060f0f0305060d0b0a05161106010605030c040e0a0c02120f03060d020f0d03030b030d031a0d0602040503250603090206 70
    0x1d2140c112805444200d40034409030311812a0940d01c580e6000c030b0562500b140340c036001e814140e000c4003d40b070440501141d450043c0100d0049106183c2d039014035550310403c44007186d04a98841c01101c074280d9580705201d4401c042602191201c0690500014420340150604c910410031078850f01d1a040c0d14500c103c00070540208020b60058518054101103280116010b01402000001003210320784a001210200b4030b60f5100c0080086001500a00c42e2011824a064030828030700070ba601e84a010151655020300c1c0c00002c0c503480740e0818802040d00641c4002e40300b00c1c45400f51032519003020507010030b5008240b80b0605404042000407081d141c1503040f03003021440103145c8103400c0345000119140401708682180817a0f034400304d00c6000d180801103a40a01c81d030f854107100310070300c2029000701140b07607466680c016008800d15404122a03901918094403001c2c2c1103a0b0401d00d04071b01410300304201e812100303d0103001031010030210721034001c0c040080e8015203000e20780141c507000e0945030 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 755574433 1250 755573183 755573197
    0xb0a15030509010b0a121a0f010e06030325023a05010f0c051213020d02040e0a1709150a0801170f01020f1803011b050c1c0323010506040902 62
    0x155686800b41c1d11141c5e07805040074090207164085080c44003141c900900d1240e24078607013521910f08802003001241c2c2546801c0e041d60700109400e4040c0e107514000c40d14500507002071403600500524803030984440c0b07c0e140f280840c000c40d00e480c6105c602c90369030758406903007a850040030f40204240c14051100c3d1a210100d0324440c4000103070582203145030000301c680a140130300010740001071071b81040c401c2c41d60351500b00f65003c4418095200503800941030440e1400d00901994991011083d09003040c001d01c800940c021001260014129038500c525502101c1450f02c82c405c044580b20340c8418102c10b50384080b055840d40a0a81d090402c4c0b424910504545101d040c03294050f61341585c03400f030010340341e0707040300f00d28441d2280403078041ca090a603400e0301a58040d82c500842c074800040c1d0703050845c1200019051a503074849004104905180c41d05d00c0044044ac0c07115000c454803580b6a022803012001c1e4a0510b1418007022841d0b1024002032094560201040c071040c0011251503000300b886c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 755575539 1106 755574433 755574451
    0x306010909060f2309010e06040e01050405120903030d0204090b0a150804080d02120906161106011a0c010c11060903041d06030c130f0b0a150305 64
    0x44041d1044c450070403200301c007400c2d508030a20700030242403070081c1a035406581c40d00520a07126100345c80c000d008500e0078050b01138020041c415a4025640680500290010100d4042940e000242001d5060100f00003038115004548000e0000b4201070300d0209620302e0010411600a80b00d40c020582051010243c515565002402030b501945c000c2c2e1039070311001e0f01550040207020701c0d413038240000c03020018402d014034009082c500c25062004144081c21425404880c0da1302c640300d5036002c1d0791080f001031000c40005601241d01082034a07501d418401d072005500e003035a44200f40c44004ca201103511401300c520601900d5480840c40b0010340ca0580341040c25410445080d042507015045240402e10541c1c050055503180e41009000d00aa000d10014000060500708890b40c001494000d1860403414500103400c1200c41c0c1c0551540d032404510019809000010f018001c = true := by decide +kernel

theorem cover : BRFrame.Cov 755395683 755575539 := by
  have h0 := BRFrame.cov_init 755395683
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755395683 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755395683 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755395683 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755395683 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755395683 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755395683 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755395683 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755395683 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755395683 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755395683 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755395683 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755395683 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755395683 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755395683 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755395683 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755395683 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755395683 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755395683 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755395683 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755395683 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755395683 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755395683 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755395683 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755395683 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755395683 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755395683 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755395683 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755395683 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755395683 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755395683 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755395683 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755395683 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755395683 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755395683 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755395683 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755395683 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755395683 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755395683 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755395683 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755395683 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755395683 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755395683 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755395683 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755395683 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755395683 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755395683 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755395683 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755395683 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755395683 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755395683 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755395683 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755395683 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755395683 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755395683 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755395683 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755395683 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755395683 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755395683 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755395683 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755395683 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755395683 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755395683 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755395683 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755395683 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755395683 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755395683 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755395683 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755395683 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755395683 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755395683 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755395683 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755395683 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755395683 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755395683 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755395683 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755395683 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755395683 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755395683 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755395683 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755395683 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755395683 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755395683 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755395683 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755395683 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755395683 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755395683 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755395683 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755395683 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755395683 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755395683 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755395683 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755395683 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755395683 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755395683 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755395683 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755395683 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755395683 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755395683 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755395683 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755395683 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755395683 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755395683 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755395683 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755395683 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755395683 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755395683 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755395683 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755395683 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755395683 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755395683 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755395683 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755395683 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755395683 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755395683 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755395683 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755395683 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755395683 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755395683 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755395683 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755395683 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755395683 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755395683 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755395683 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755395683 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755395683 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755395683 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755395683 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755395683 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755395683 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755395683 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755395683 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755395683 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755395683 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755395683 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755395683 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755395683 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755395683 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755395683 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755395683 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755395683 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755395683 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755395683 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755395683 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755395683 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 755395683 ≤ n) (h2 : n < 755575539) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
