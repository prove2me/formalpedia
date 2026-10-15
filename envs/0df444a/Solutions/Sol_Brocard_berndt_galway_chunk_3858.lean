-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3858
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:53:10.12676+00:00
-- url     : https://prove2.me/submissions/3c20f090-916f-4675-87d6-841ab9bb624c

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 693705035 ≤ n < 693884892 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 693706285 1250 693705035 693705037
    0x303050d0605130501050f090f0420100c0b18071505041206090506070f021e10060807080c030c0d060510051c030e010f0e0d0f1a01090f021204030810050402 69
    0x40f02c002165560703030041c44140740404800750080300039618100b2624282d003030b002c40210080c2c40580780402038040044400c04140c0d004140300c101038514200320043c00809000103d03000d10885030741c10858009000c81000d0b50300b200c0e6401885005206e55480c00184d21801c560345044041003000c1000007184007808500105549031207280005620005401c00c50305003071019180c0340800070101444520036a001942e2212091807500801c1c804e00315070511840c0400008610010904005002034407400200e242d80850321781c2400d80e100d50701510704154990425801c0141e114100480341008100141d0100da4000180502e41240303e40310350004503000211005504081c003664480c0c1d0400d50303c105444c0301640e080c00d040000c0303102240041c2c01c1760346092285d40990000c00004060091320750031180a1900003580d03a0941101400d802d000703040901565080c5802c3c003020314096020b91088400c0d81340045440a01c41c0c9966404490303103c0042d048000710700040700c0214075551648 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 693707535 1250 693706285 693706309
    0xf0d0b060403081306030204051f020f010507050705060105060f1912060b181f051606020406030e06011706060d02030a02040507020c0a0f08030301030303110c0a0c03200a0303050d0605 81
    0x1044194403010130003d4072142400315000b203003c140c01400704001c66100e00c1020341185500000312200000c1201c822480c107100c0e610384400e29801c16082c4078005410400510f60140140e06079401a82c0300d00c1400707a035214807100d0050000d01040180740405402500c140b00310301c20b2030b0034146900500d203414152005904019178403100012140d107100c8070b00e076074072540c00401e43c0e1000c6e000580e074901007d09601d240f203200920200088200c44510403111070500250b020f10110b4032151117880c010020011851500d002e0f200d01d20000c00d150719072180b0008241c5200004084640d2504188020b4864a8a04a03058401c884810300160340700e000d550b10501e22035005181d05d008200420007004c0d0107902c103261900f01e102040c0841000402104e042d40d4050501140c2d81c0d60a1111200b00d22580f03000c144c0c90300441d04043c0410a0764040303003003100c1c02500600c81c491100001541c100f4191004103600003034070300c81000003d0040c0701400b441e002060b00001e00d15074800116401c09503030303 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 693708785 1250 693707535 693707543
    0xc07030c051204092708032a0a090b0c1c0507051e06011d0a022101090b19080a1112070b04150206070801060e0a050402041e0e0702030f0d0b060403 65
    0x103c0c050142d003819114030054180c402100040201610401c02403845c1c0e00307080a4083c80300080010900e80e48070310042c1c0714210300500103589000d064026601600107803110b0001421502c0c4c0015520305642c1505c2c0003503241c40207001b0404100100d000c64500303005203902070000500103071010a00921540103000c00100407840d1440104601d03d04008050304215105c100f250500b803009503981810580c030000070980140d482c00031a91a90300c148807400d0401144105000200d1698103a8001400605096420380f10303d2018a1480082d40954001d402941e800018071001207031011441c030b49501405802d10740090380203d8000d04291664100c1a14441c00240411110800910b02ca96509081c801740000e814100b0005040301c1d4181300c0c41c0c0c00c0024100406000d42e540700a214010310b4000c000719591740c0d41e03440320410200b12103581c05e915003405c500000c0e2500e44000151051220b41d000e949005808040d4803082d82241034109030b402c0d5141c82c00315080d201c910040c800795001d = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 693710035 1250 693708785 693708787
    0xa2f120c090105060a020729040f092a03020d090c060f080a020c1c110105010f03110f150f0702150304052b1d101809050f0c07030c0512 60
    0x209051000020069003d2401900c04115540c0c409902092010544030020006e071800404941e860700f04c15068405000391800009002456129031030300001100d000a41c1840f10070a480c514969005002d0300d5030b8401070810503100c0341c00d0320950060490921150b000500b04800352142c4412140940061011803c007003814841160403008080e03004001c8003040d854504d6030701400341c444014000701000c030225001c0011155025500354651040d51400810041d0b9641c00038401c4d05846110a441a03c0d02118000355070800600100c240c1001605011403160203c600f00305c0307a0b01a003c0e5680c1c0420074080d070f200503603520f0b03c0007010480c403e134080d45900380303420824107103040c119544071000c01d0040d00701504000034510101c40340060034804030880540340c000075101d20142c621070340984202d017040303400c036000720400340307503501102c04242040c1e26501913004403041680e54481d40d9002d81c0005140c1e0b00c01a0041c56103c2c400e140621006500c1d0361064680361070b0314020101c60358 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 693711285 1250 693710035 693710053
    0x19110f1b040f2c03180d03210b0f0103020a092106110406021504030804170c100507030c110601030f05030403020a060201270b061005190201090b0601020a2f12 70
    0x16000810003144403064014600c0c0c0503010b41c21105841d04240300c0d6008110b01000b2105048c0501c5074122148103a8102c0700c80b1080203072685e0014003040021a224001c11543c2400c10351180c03080e561004555151502540d0900c5901d00c00103100000c0310305110002c0c3d140000084003170048149514032032200b9030b01d50f4103003800a410701010000407404003166008100c08280d001d01e0041d0460340202c20101c0850010203d102c05200f4804080d206208441a044c020a00740c1e01180c801c51030b90740d041000e00700c8081d0864510817800410384682d03115400500121380002002c0202e641304004503440c3c65902c0d80425041c0c40c0f2036000c0c0300940d640354103820344074680f41545440b25100e003401c100004850340d200e0588207400380c00d0780e00a00b0840300c402642800b5001715004281108020283c41c0c401400c028040c0c12111000c03141c0100318400706065500001d0718410b6190700c007203007000f00031198804003822860f51064602d150b1041104580780d132075411186014081c3c000103880c100d0 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 693712535 1250 693711285 693711341
    0x3081c0b030307030306080d0c0b0412050702040501121208010f0b0310150f030605030d12020a091a131a0406050a140a030f0515060a030b0a0302030319110f1b040f 72
    0x1091b230b40040e10074460305840400000d044900f205134010380c4441d0350424500d0400d01100da500824000075000391a001c004030b224900e0341e0003800090320a00b00c5070010038840300210348100c002e1040b0b000300c410320350f41806082c40080186a00074403400860a00507a20350f0944107000302e540300d10001c134003500107295070580c7c1030240c2d07070160801b900204584c0c425403000030300030084041140c28065010521880d641d200c0c0d04400010444042284401c01040101290300d43c00394958a02c10780b09100d00007006003040e61002e081c0111050034609180c9002000e0324141d00c0143c261080225101110b0410f0701200c02038104065180c0c7c00258859981540d0360486074040e100d542070b5240c1c00d0000c192036650380201c40c10700040c0c0c9400304601c5218004a1182000703500025414040030480790404c2800300709001700341110380d5506000310b03030082c0315a40302c915480c980300b659080700d5400300522119600304035460700003070b200040000401180204940728044603800362002c0e014482400 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 693713785 1250 693712535 693712543
    0x314010906080307030503060d151a1801120317010806040c060203091005090a0e0a050406061712180415090614130905030f0c06010504060e0103081c0b03030703030608 74
    0x540312000081000504268441da40c034002c00301d00034100b0800000080b19525080081e545150f0301c000042810403040c500c95001c1c101801807a182500c195408541c0392610800349120034440c0c01340c107002d50b420009581b0900c0100301043c0c0600c194103030206d080c0d540314020103008000403406080d19051a2601c500110f44581c05542154001d10442da01c40d81c503003410f000580b90320f003231071039a604d00344000c9444503007664004402c200c080c50401c0303100112900114840d61240d80100052501c80d1550355241c1d0041e500024551700642d06014660004e80c002c2c072122421b02b0616070540d641c400068241c1350b150310402e5500401c550f08000100142c0907080207062210301c10000403512402003000f05e80130003140e200903601d4a80394414000103000301d400010013a15025039410b00d112140f46d5501083c420f25000714a050700001d2a00b10784503000e41a254480342c502e14000c0d02d082c2020540e92042d910800310307681c41c40030045030f50b402c000400200d8800d40300420f026151074200380c10 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 693715035 1250 693713785 693713789
    0x40212011e050702060a0207031b15020c150c030f043c060f0c0f03090f0f0b15150703030507110708070e0108070311060f0d0203010f15030c0206071409060a031401 72
    0x114031f00510080707002039049074000441030240309590031031008a04201a400009070f80c84059548001544c41100720085180440400041c4488515841d606100030b250b10085171300001d581c03421030200c1d000a80190000c00111035200241c5407500032902001441000100c42180614160000804100c1140030f805070040b2141020000e0b208041406800c00041584a0301050340d00c2110504000e020712003182c1d900c1c3c00c5117003600c4217101864803c000800c240c407401403070104882400030514144404080c0c03030441c1e0160303504050315540c00f500038080281c842c40611040070301e1040a440204030756002844813200030041c0c0c42c82c00b11401d0002206130401945c60304080010710114007a8040280f40d40011344556503210340fa80100e082c180503102c000104d44d40008000a041d0451144000940e10503202002e61030740b807010306600321603142414101580006001070f10090080d07500004680d100e010061401c068400000c0c0c1c50781c8140f02e4600400d55503030009084c41030b40365140e40 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 693716285 1250 693715035 693715051
    0x50c01050d14150325060c0f05030a08010303020f010603050c06090f0306090607030c0c0b06190b1c110901080c130b0c030403050706020703080d05131203090215090603040212011e05070206 83
    0x80c00112201e0303040030f05d0514010881480303500c1245800300012481e1030801150040156529141d4200e4001d085001c2880243c0040c482c5080c006e400c210103201c0e10307007100e5000c0d0003407564100202c14080e05412046a00741d10010340034000905481c1807000034030030542003002c2c0c4058500241c015048070000341000e010031215104110000e0340c0032a41640041003240c1401c4805100409020701e880ba940260100c80340104001016480700716400400304010442400900350074400722581d0301a11040c6400545003602040c000f99500000346480c40c00254041e0310b590b00d03550440250740c0910030b524410303400081c00708240902801400040c146a2001d04105d0b86186c8800e580e81c0201c003080300416030b8840120301e600310008132000074241e20051541c0b050111800c080c0003440401c005074060500300c0d5400e444941214112409440000d00080c01c2d501d96400f801051500d03c0b003404840d40d40c50881e400a1010b01d0f1502490700d400007004a5985040c1400a0070003002420b0b041c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 693717535 1250 693716285 693716323
    0x303030f042315060a260601060806090402040f020412031d1c0b07020a0b070305070f0f140915190e0103050402010912110a080309030105090703050c01050d141503 72
    0x15681c60070105011284104140e040380080d1a14800118680a86c1e40903903d070740744a0442c0e041138503000062851903a1490141c0380641c1e80e07004280e0300f4210841c0c00c0b6a21580302e0b07001500505d02030307000030f070700c4184283d0050074a600c400303100c4103d4009410076004240e0364083c070b015030884e0040d005000c190543d000c0d13540a14401c6003d0400f8007ca0000f005a0000d00002d02d0180c0308204299003c0c0d000582603245040001c0003500420341640c1280005001141e041c060a0103280740440150b225523650700c004142801000480e0401b000756030b0312603042ca40302040d12500c0f00107080110b1416200d00c41c464407510000d0304000380b0b606071605140c14002080050f0f03070045200c1c03088807254443c0075504015840d080100030041c542c0c0583c001d62050020510200c0000038090100c0280c000f00402d45541400c01c2d40c9005d40d11000b8029808075800d00c8a80d481a40078000c02100c0c5440803940c1b10550a001c89900713822103007442003503660140044145001c0103425141041c40c0000 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 693718785 1250 693717535 693717593
    0x2030111040503190501090602300603030307121404110102100605061204240e21030c0f0d0606020325050d1d03010e01060f0608010807230303030f04 66
    0x100b43c95002c913004103040e00a008000000b070140a402400e1840c0c0e00c241c00b156120000c0003d03d00c0e41041400241e1040c802805949040119648040c00b42d80014000d5096658800c000c40e400c0500d00d1404001a880700714110400c1040302101380280e2086427605030f49240f1a00086c540401d00b03000c02d0140d03041900401007600e0f00d400301c03102c43c090240100e43c1035030780342440100c40043c070f400107180006072408280c080801c3c0e4010400c404405040c0d0f80d07500070b65010102241d075400001410800100045200021048002d09007034a15050107410100009100d40803219a6030103000560070016843c19000ca21004007410b0016020010f05803e807aa125182d80d40f0000d10341d10180701034000011304c0f145036041d14600c00760b0f00800034000b1a19000303529020381414464041c0c90038400c0000300d0201c2c0180711250680309000e00a00d510ba103401074071004030103181c0500c03040810343c6500340d945850a0009600c1051017044840013428546410702c008614440da0401c404050060 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 693720035 1250 693718785 693718789
    0x30b0915010501050d02120a0501050a1415030411060d02131a0711130f021b0a031b0213060603021804150303050f0c0f0f0613020a030f051513020301110405 69
    0x40c4a040d01d10038640310352140005002c00000b8444ca4200b0300464141c0d10800ca50401260081c0b410307560141c2e100310504c0d50381d01c0c040300008020340b2166032040d2044224444c90201c4000b0b550710900400800c080340100c031001c10340c5d903400801e0b030400c51a00028010340481846680a0050120042003600c6240c00103520174a40a0008020300c4440f1342000c0c20110398842c2e42200310b070300403140100803110640364414020340c04409202d804035a01540180354040205804403407503003549400054680003d4081c0d240b50713099400320381c003090b020031492070101207101d9000500015100140e8610300b060032084c0045200d00030340d2155052081940070700c03007450b05182c2102da06003810f0b074481003808081b0b00a40541800d0105070300c55151012400c0800284808c603100c8890240c40403500c078400031503075441d80c00705c001c0e420036081c0c00c3c00c00005100943d00c0035014002c00c1500c120150100300f021700c0f10420354a4091030003145213a102940307000e01c00c1506582c00d010301c040c5000d1070400 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 693721285 1250 693720035 693720073
    0x3060f03020a17120c01150515070f0303061e031a0c0a050a110d05040303090603060b030f150307030c06020c031b0409050f011b1409011d03070e040c030b09 69
    0x1e03061400e8848410f155402c0802c00448689480340104591101c82c25070002d40200f29008000b45d1042d186d203070001e203d051401001c0642d60b99000205d04c4c0400640b5103041210300240101e0415541e0703000081d00100c43c0392071080203000801003a085074610f041001400b13089550741c503010500034040c8034107c1040c00807900a010310782032080d16141d00b00b1303003a81e034090003103102802806148005101c10303034080010070980c0d220351204e0031016201c580880c01c0720301c140070b07440c124070080001c111200310255484c2d0388001c403048803049011101c00400d017001419071084510255a40040c0306142d01030000d421300020960040c0300040011464000e9a0650341c080e5014907907441c0a94240441442052004408400240218030307256240581c1099000360803000500301041c98243d5150b0300c4121210703007034140e5a041005201000d05000f0240d10710807160325120307007000040c055018003101481180580510008145503040c1403041100060620b02070703070006036081c0c500c10140e0f8 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 693722535 1250 693721285 693721289
    0x4030c0801050717090f0a05030717070804090b040b060c010c02060a0e06060d1a0103080a12090506040b0c041508090d05090121230a0b0301050112020f13140703060f03020a 76
    0x14094002584070070b100d95041580d103044140241c0034007d02c80c0f05009002008014051041509910996401c0900c02450080202c01082218100000c001001c80794000d00603040e00200001a442d03142800140c0035400006800368a945401d40340c28229014002c543e030081301100c00b8000a2220060309032903440c02084a03105080088020044c07040f10301e4000201412901c10354010b50b141c4c02c0c0341285400c80400080094082c040c65a42c00e1070b180103001d1180e60103030007025251116034031640a54001407122070506070600000a51264135003440d0718512194079079889070305148081c01c1c10051080900824400e0401404000c3c0e42c1c0003213140c3c043c8500701080001c402d500c40f20180a8504882c0c0041000c1c0c01a84921000c0c514181407800f860b0f280b03078104101b5a001003494280c0f24248100b10141c46031308000000b40c1480d080d09040c16000409500d00e800380210b40a0480b00b075411031942024241c2d08228415806105000c0600100f80e0106540b40c80c60b03002620a0400b8 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 693723785 1250 693722535 693722567
    0x115050403170909070507060c051c0506011103160303150e010e1503010c030b0f030703110f0102150403090e0a0e0303010303142b24050f031f0204030c08010507 71
    0x861400345072424410141c2e05000002410713500942070100e001002c5412820b403d45d1311628064041d80c00398011011501c1c145001100780010b10b0000c14284002c1c440202041e05001d4044030000b804601800101880d03a50001c641414032031038200142240d034a541000d02510713000350180100700c032910071541100e400010007500d030b566000307036a01110038602925400d5070a1020032007101c0c3e003503001420820000c2d601400031440c1c00e420147e840880348406850100e504074000150f007410070b4210304100040c012030325022440301142d01401d108580c00c0c2c000400c40101840440320074003200f07800201c0d40409011424203080d10940340d210610004041c081600c0c034040511140c002510540d079089800711303040319a00c1c031a00d405490340f10320a06002e840d00d814108c58003d82c80b0818040a091413681f0149810641406071807404030031550303494410004858128141c00c416050f502400713540c09078843d861450303c0d0034200c1584d000008181d0620b0b041000003035200c0711450304c075268 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 693725035 1250 693723785 693723803
    0x17090f1e0d0e0319051504080703030b1c020f0102070b03010f0e0105030f030405100c0f050c040b30070305070603020c0c0a05060a14090d1109011d040303020f0409020403030f02060115050403 84
    0x40c600170b898880324903050300340403000c4420001403005620151040600a46041c4208866241000780c800954002e03244905e561003402c10241c2051004030071400d5043c01261252501c80c0c82e8007586802c03d030301014218456050034018842c5500501e80180015802821030101d0b045540e2b0300d074091405480d0207007510010700c40203948552488c4d483d864110a1140c00080c032410250748510310820052300413401c0c440140d504c0d003007100060207000b00c1264440c88940c992106e041c4903400301002d440c040d1155844c0800484c40900a00700103002940b00103944840034606582400a00920f4034400c00c1c0c4e800c420410740c1c0b2680d0031940041200d00e001c19840f000b403c0042c05500441030036640060006070103504000e030210984030030321000c50b4181c401e41e84c2d8021915001d000002d8410040c8115004200064048c2d005490718180d00c541550906403590038801c1240c0050348103400003101c102d4a80d40300794041c04042e024010613200800c0341c05407410042c142d4032031031000508c0404 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 693726285 1250 693725035 693725083
    0x90e070e040908040e040203070e090307060b030c040216170708030606221d0c030903250f0b040b0f01080606060a03060306061707080d17090f1e0d0e03 67
    0x55180d0000b1003080d400f40406881d1501c2c0c201404441504031000c0b070103403090140100c9c5244e102040544545240001945405c5660751080050b100d1141001d130148200b13840c11106980740d0000d04601075118045c01c14610039820180100060003461444c210320030001d10011170083c5c4100d9500c028141c40c00703666080342c08042a014154141008413420f114240401c41414403100300c0d07a10110b210f4240050341351420007400034402540e2040256008002400105c0c11002a00317013101a01038200340c0803001c944505e00c0481482800703e89000c291000c11080284e0004030b5600403450603200703e410340c101903000d943c810018055520604010402e100c44078469003160014560095090168942d01d402d448246080203d5801310b50041d890045002da03800191111000e4280e540d0b280c90f80400894080c4981020341003032124000c194170208500020450118003a000f80c848030b100800103100c49060072006c41c000400c00407124400103959030b002419030a00c696000703ca030341d010 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 693727535 1250 693726285 693726289
    0x30806030a050610050415150f050c0703050607080708060a0501051e0d0e070b03190b0f040c0f0201061e052e03060501120603021c062003090d090e070e 67
    0x1c50080c00e40c8114020802c2c0c0311100c4242d40c08440702038409210707908403c1ca804d21800c000d405040345200082d0004109144508030069191141e42010741c81e2003c1005000d04020042e00180c6296120100b0310464079809a0b11590003036143c81d1940360780c01c000002810340a8184107441c1001008140c2c40904410076080358108222010b000c1c2c1d8940044102c0005444240b4045001c1c0c003440700001101e0000c0c03c1101d01c1070900c1451903404103000c00c00c86004104a03d422900800c450030344201d83e4071103116440700e40700d140c0c94032540740c8840c0030002d0079500ea43d041420018058201c520900f120101301c4419120304945040c0302d070000704082081980603070040580070300781400c1941a56056807010742074030000e07a2a5a0309d262001031120039a822840004d40180c1032000950075000c04031168011944602070104408841d01d4850f0140b5182a6014034105400014040880d41c1008140800940d6043c002240c6141c10b03e212404035009080f1400d018070308006035600c0d = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 693728785 1250 693727535 693727543
    0x15040e060d051c020606120303190504050a06020d1406040b0d1e0501060e160e01080115111605030105010e011401180b0307050a110c0a0902130b0325030506090403080603 75
    0x410040c090745610b0301c103e50f100942d034580540d12940038105528500c9540d00c00401141e01c04c3c010100d91520100c940d1503800300415005000380d40500841070f025002a00c180000c1c00c0341e402520300815250100b00090a000b0405001d45105903c3d09065400c55264901400c0c28507410050403821540420b02c0400c40f1440d010303008002e5460000d0114041b40c0744d522142c09034220507481c805111041205880c80100144c2d030350701281000c00100254001581109003040c03c43c80d105025407400201c0c2440d0801c1040794002c5001c6900e4140700c281000d208507401070800454074007895150121152404110441c03c604001011920044031030441c2c485400074540161080d0b0344c1d2500e00001029038009000c03400008828000c020000d68000540c0b10040c023000b07186c950b0f41403914503032000079070000343c10b985c1d502c9141000144ca5980400a10300c2072000400c20708e072407072180c1c66041c249117014920310107240c071300028081c45440301840d0581c095490f0410107010307150040000d2030 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 693730035 1250 693728785 693728803
    0x6030b061c0b1e0a090f0b2806050f0307120605061807031a011d040c02010b03030c010609270b0a06030503030403180501020705010c06020d0b030a0302070515040e060d05 75
    0x19144090a0260150f10689002100e10821003100801d0f110b6030f07030210940d030b0001e2018048242403003419001c2a01c2d142c03900d800c1446107654110710b401003403101217003c0074450402d03010350361401d040003a801c0a0701c102c0a594811000b902c6100e04129104954408294014003203941c2c6a001485a0300c9094001003204100c011800d05864840343c000c0c043d2100600301603508180c9034208815500944460042844c1254400341d014001c20510004058800c000d5003150f403125082405a10144010005001c6402c000b00f4020300305606c08041c3c804c070048902161134561329400101241c07803401c18103150f00c040c0884864aa03021074202a00d5a60000b030410300000090008054009113000320030340c21000c0d0010055034401c01079840d1980d03485a680400c000710190000120f00d40e00078030105441c00000521020410007282c40c02180c00412400b41c0d10158040c0120300d0203101d401c1c072030000d61045500c2c140c2410704010301d9107005017210f80074598010007030080007824004000c2d = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 693731285 1250 693730035 693730043
    0xb031915180b0f0906040c05090414011d07020d390507060e1e04110705031206040605130c020c060c0d12090f0f030c060606050a080a06030b061c 64
    0x6038554a80d00c1254404404000304103140450035041c90600751100d00c44043c008208031141d680d1102404003405441070a40c08001d02003164107065612032107581e401420005100c01903604003003094085240011107921071310340000401c034102e0b600045100801405280038250b26003401c003185584480d140c15850703108900080c0102d05503500380b54410403030180d030403a18207587d180c20a680080554054940000c88a0812102802c013181d00000c87d9801810002e4000c5100549801c01e0300000740468072501300044001c80382440b214200d40111080390104003e9261a00040034416103421100c0a107880d000c04651580c0284902e0051000c007400c00c540c0c5210103081d043c2c50384092202100072464600fa404d003049203034422110525844400c0d0804241142c40d003564881134a0303400ca0802c0f1b04944030500091482c01044000d00c55500c8083e25034080b020050014440100f03007200840c5042c0007000400d0b0103035842c68100d40b0a03950030300240010400b81080e0400180d002d0 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 693732535 1250 693731285 693731321
    0xf060d09051509010b1f1d0a0308030907060306060203270901270209090615190c120806010801030b0c0c0f0a030206011a0301030201031a19030201020705030102040b0319 75
    0x106011141d82c0c070252140c070416000300b01861001d81000f4072604a10107020740341c6590000c004031140030306400f0340c040391000460183c03800c0b0031001501c04c41070b5800407610301201105100000108100c1c5601820503410280310b01ea00b040302c025564007031500c04869081424490741e0b070010b400300c6031854046014160305125a1621817210080d000c01e106240c9542004a000c07407111464800d0b00d1140e90010421851030322107038100f0901c96040c500056260700704000030504e0180018511401031140d40b03d0307110041440c2072546155450b88031140c28003ccc0c40040042503a481455031303040d42d41c04010081d06440b00601446940100750301e021051054005030000300c08001030f40c5000610070b40c202ca005030303220b01810035000008060790005103c1400107200640c041d401003852001c8200c4c480102c200c200300083d0701415080c0524441d8100b042c000d2055507418003210014100660003540f50910340b40d987c40c00303444024602c0a0600c640b1901c0003400c289508442c10034001c0e10b000d0 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 693733785 1250 693732535 693732553
    0x4090e030d0510150516142d0c060f040b1201080c010306030b060405090f0f060f070e010504090b040902041404021e01020a0b0402130213241403100902181309020f060d0905 76
    0x510350747d0b1190702c81c9080d266070008c0072040c00455041c403d4403507038101d00078040305004181880115000512000e044100c144404a041124600942036142c2c540601e68600e5141c0760300c0364101040d00004504150400174284040303400e0300952508402e050303070002040c0d40c030401818281000c1c0c810105a1b4001e915102e0300d0b2506c00920240034010942c200d000d5078840c08419918070141e1081240400c0040c0002c104800d12540304d9042e4900180010412810a0380010100d91500d60b400304da0241200c00e0100351306217510003001f00e0312144601c0d15298581030004c0d40c2ca10144038010944400b80000504540751f42041c00c9019014600035900c0d0b1485510742d6004014a000e80061500c01d00030048100003525000d14070300003540c5884800600d0101600007560000b4842100c0750803402c40003c00048a1006203410345050860241a00c4100d0400c100003481044180f45a0b0800c051350000d82e0307c4802401000f901141c04680c0c90b601c14a00001820000c10040c180b40156950 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 693735035 1250 693733785 693733823
    0x913020f060d02121f1a04050303070c03030807171303110d0c140607050415110d0503071701080607030b010c0b010e01031e120e01030204090e030d0510150516 70
    0x30b00303a07507240d00b101503c4c1551401d200120050241a1501c0950b880700000c110350803205004c030300300c02102650380f8546604d54021074510b81c003120040300d0407984204108141075001e0303410758000d40320740b801200f0558040041039085402402248259200c480c0c440205801416240c0c984151042651081108440c014040c1c031079000080e07600322841001d10b40c0024020822605c22650381d1a86814103013880c1d0f0700c581031030f1281d14800900004d002150f090420070807032a200300c009542e5942e924680443d008083c5d130313070924001c0e01c141050310062007d0740011074029840b014a240014000141d86d00403900032865500281c492100b200000c0b98903521951501e041e240504040c1186202c48400c2c4210b032503801d800601455201e05020b881544190136071114410140360160826484000c80c40450b622595190700e503500024501800150307500035554440403c148259603a8900001c8407140f01c0803622803c100240014020105a841840001c0305600070850303100078090052 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 693736285 1250 693735035 693735037
    0x106110708011802040506060403030203030a051e0f07030608070f0b0f040e0f09011a0306060f0a0f090605090709080a0602090112050109050702060603010b0109050d02030f0105090303041101030b0913020f060d02 93
    0x70f400e034016405d04000507024101a0100c1d800c90307a0603801185182d0f02e28908000914025109087c1c500b050300c5481c500c0c51040030f8842c010701c407085100710a81000340c0064226a000e074081405504180c00400080d03100182d00800c0b60204ca900a81e40e20803146421761921079030700300c00f4800500205000d02d01c801402150301c2500b0f2080200f04001c120800d4007000c0d100070f01c4580d81075000c480040d61074100078481008208025005049107500d81c4156038622400d6003281c51801d41d80c030400c00251520300b8045402c41c4c62400c00203421420200300c42d44410396000c01510664001989580eaa44075001038031042030690002c004550f1140c2400001d0002512801d005200f10400b01e005480c1c18400e030282d66905031a11014a40781000703203c4901c1d6102d00c180d84c1405051481078100100380983c6d4459070368a0050342c0d880c9401d2414003030503500ca03069a0b04152514594131015111400740982118100540200c001114800618031402c520041034000b400407031f01110451140d0 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 693737535 1250 693736285 693736331
    0xf050d06050d0c060e0306220f150c1e020307080c190303061404060e010620190b01170705090402060d14100e090a02060f070c0f2309010611070801 65
    0xf0385c8024003426400704155848400742e44180200b4042c5030b558241010b0f408021120b14070441d9890744558081c1c80b01e08402175030300045901503444014180c41c03960710540c0d20300c1c0d214405d200c01282c0c0e050018001d64034083c0c0c0d00300900b0760600040601c50307070f0410054400900710789803512851103402e2500034050445031050451080a1810540039842e060040c1c2094070b200c10800c80c0c203030b86880300449060003510a00d46900c2c20018400c2c078009418000000302060201e5034000c8254946000301c80b200050b03100c03412514035001c40c1000c045001c100d0a0854004603081e84044d03c40d0700004a0394070800c03043c44150b52a024070b43c03140440c011400e610840104108108656840c5120603003908125110807a50304804441801440d182c0701808903041045003103424004166100c10b00c3d401250400a03000b101c2c0320040041a0f4030802203c4074060315281021210440c1012410322103040c05200240320b400c0e0600040740f481003140400409100c0c0007444240134007145503901003805 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 693738785 1250 693737535 693737537
    0x12030c0b010503030309280b0103060912110d302007050a1e05030d09120c021011121308010b0102060108191e06021201080105070f050d06050d0c06 65
    0xc400001c1c14500801030328450600e0002134000c40210f03180c065401c5801c040c00f002840c000c0410100443c17051200705018502c00c4600003600c11301803e044032401d03c000151010000002d980b0140d648021030040204e05450402c01c2070302a0b00a101110820045021b1003050f10003094141c0c400d0654002600d450021030f4410564500244d5150302c9102d0084050000c0c0c1c041000c076000600114083d0410124049403900c1070082c0da83c61600303640c8000a05031044e0b4071410540240b0200014034034010301c003406d01d104121069404075201403028500d003c24840156582e05d1440d501b8880e07892443d100007100f0784e40e0008090074402402c10b0f40102e0300950318101b01d852140d400020520b068807200c8006006102c0d80402c002203113244180e045411480045001c41404606000e210b402e40c859400540c0b20300e0081c00c200c0c0100b405900165440c1e0611080c041c0b1160014071000c100e07281441c00980c6c07a01402e51134030203071007c1c0d40940d03049162103c070141844000040c3d50180d481d5 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 693740035 1250 693738785 693738803
    0x20c040905010f06152001060801110711060306090c03070c0b0702070305192f0a03080405010e04060b0a031503021503100602010507080a020a030e0d09150206040f02041512030c 78
    0x171442d510003100b0390342642c1c1000c15241c0101d000b40040e41d980000305a04d40078004220f680d114907032a07094600c0440800510540411480100901a01c040403120030540d1185d0661a00c0c000140702782c10060314014100f00c00101042510313100e00e0580c086660000300c00c120134101004002e5503082d1620084e40d03103008076810380324126440c0e03072608140c1c0e130824064002d1502e400c0b000d070302c2e03071049101c800702461985513034034a241ca48809510040d03010303070300190715a458440098040e005003100148250701e00203050040940304000e030f4610746041d140c00034101d42c0340035403401d2401403500080d5015080d00c110713103920311051004500c00c0107985480800590b9940099080e11025114070b0080f0f1040c000040070034031244e0140c01c08080c103140105075000f40e5036165080140d03540c45140054104402840905204c5000a03814941031005100600d00344e103449080078229540248030750b444200035101d0309040e284000282034020348865000c0b6292a000d0601101404100d6003001 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 693741285 1250 693740035 693740039
    0x90c2110050924030a05070b4518090f01110703021902180708040201141e09060408030a050c240a0908040906030c03060633020c040905010f06 63
    0x10801851030188460480a0004103614007140079180303c51240c0641500c1110301710300204804011403001030803003007079090785c4110080d12041511003a01d1040624a1300d4490190403420721031000d44840c040f844d00400c014055800124410305140000103040c124006100310020301240c0c0105c120000d0008015824418200749424040c503140680943c2201800d62034a40c00041c4500303900b0302c0240400d40010002900c1043c4400950b4403000080840e0204411035801441c403403c0320080308255400d0400b071104694400c10712410422403140041120038454840c6815103000d8910407017501d8a07050203842c011700ca5000340c441c503005445401d011820b221503104907408141040003030080f41e41c0d40e40c40000060300301040300300c038509002c00002030ac2000500c10000550700c0f4001e078200403417442c01c100099a801750050340c1c02202e03008201004070343c06031072410b00641d00350b10541710b0b900c0c0c8541a403c20004402058000e802d040d03411080110651040080c0b000914080241603 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 693742535 1250 693741285 693741289
    0xf050a0510121e060c020c0a0b0405040e0c2206240302090d021f020f160312050705031c0507030b01020c04020903120403050120031005090c211005 65
    0x50040c1d07800500340840030303420b00a203109a142080ea103405094200b0501442184440340c07005442c606031441c60313645259100d40381c3c0c1030009030103014044814045190401004003407a2040d132103841d00c201e40d86d10f0f0207030700c042090001e00310342c0300014100c0840040005601d0404c400200605141c41d16001c00416003000c400480c4107c09940c1013642805205140e09070000c0d03100c0c0c803241d0342c40080c201405006a41b405170381e141540c840140c1c4000d40100e0170300a464001e4107601e14142e40c00c8807500c550290a03a618131021039030407081d0813181c003107111015210fa210700c0f4005072180c000041d90900d4210b9800800035203009074481044181d80d211011421182d40400c02401604101498a290b107010740103051620002801e444400446034510320080c0e210ba80b0848080e5115200203400c200c410007000c070a84140c4450380d243d490500c2030b098007080a401440d1254604201196142c00c101e800d86007180351421819400840400360450f0301c080071180c00007803400c418400704040c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 693743785 1250 693742535 693742541
    0xe070306051c03020c040507050c01050c0903011a031b120601080102031602210d0b2812080a0302070c09091a01082a06090d0c140607080a0f050d020d0f050a 69
    0x1140c1580c0940251710394001040083d0034064220303410003400703102c0604040400e109a90284003610302e041e40d2280f100040c14255510a115481166041c2d070950807251000b040b90103100c0d03c0b05050702403d80c4100000342192141d000c0545040c071801c0d0010481d450154015405101c040029040d070300c0d80b40c001241e0351400d0004401030750740e1990000301c203001048080c0c004107010b400c0106444200002040101140000100d00501080744000c541030600714094050411004030103c00c0c20340f034840228030710441d6002c008042e8001902018010184407034009024204400e01500106040240348903a0881c01808204840c00002680600005500c42d0750a400c400d00e40c40f071a5054842250048039048941d0000010841c5081c260b94088074145103900c100c02c040815814854111103004070a034003240502010422030000c24030302c1040c1c480000e01850607140f40717a4404d4046030213000e085017803041d8130300216850140101c00d400000300008104810406a99004c4000d429 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 693745035 1250 693743785 693743839
    0x20f0c0d181d040201030b04020715140f04030507030c0609030c031403070c17090a032108070c080706060b0d06080c030a08250b1014100e10090e07030605 68
    0x81d01c80c81600254800003014072040d0f00a0050500050000d8034102107026a40407501c1141c1070b281901d0008034684843c03089640e600000610381c03e4a192001205148aa0140000c2d0502101050006c101449020180c20965028405010300d8900b480e01800441d00080201c1c0442d00d120441c05450005a06a0b031045184e6501d1134a00c2e8100c0c0c40340c40418490761443d12400300c2c10068400e035034844166441c01940300750071320080e2103a184074060050301d080c1172240400580c0340520480b00d0788584960a600e4110600540d02d0201d0f10701070004007000e501c0704650080215002005d041141e000c84121040c0c00c090706c08107030041c000c05444001d01c207401042c10b0024840701030302c43c501c003d140078440032000380048034031201c1c1c41d001203500d4201c1c4d6011550b002040240114011304268141201003600d07841c200290041c03000d032070761120341d01c6039004d001d451000f44e034010300c5030702030340002c3c8150747d81d400b094201501c0c01800740c480c81c0035443c007030010194405441086003209180b = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 693746285 1250 693745035 693745049
    0x1806451419050609010210020a050703180b030402040f0b09040803090d0c05060f0711100f0e0d0c110a030219050f010206040c0b0319151a041206050a020f0c0d18 71
    0x70440d0b0800c42006480c4d000070300164110320a0344076481c1030141d1440180b00700e040c0c0e40c031026140c600d945002020118801c0c0109400000140c3c1003015aa1030425039800070350482e8085034401c0b464400340014503c0d40700160307008852005100c2840100070007140100c0505090780c503580d811311415a110381c40910024400e0b4042c200040c9080c0700710f051140c01c04901d00d801403100c2c0070322209903e090300b400819a0f0995039400701e801e00c21011311501c60050705070b82c0680210071551101401940040c03c0c09070201d014042079200780c0c2d9954501401941e401000440444880c000d840401e0350380e802504c1c050782c01d00c8102c0c2403540c000106070b440381e644102110907560600705030094582015102d50004082c941207010220114041c07201d6409411010800146ca441c0360040c500b28980051141c1035002c010a1000c202e502e80310590081e048000860107885031a86a40223100720000801d20403c082001014840301050410700706030240d54110041c200d602038100242c00c07612500c1 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 693747535 1250 693746285 693746329
    0x30201081006020c102c1009080d0c021909050a0e01090209070513030c03050f160f0b070c0b040f03202112030c040618064514 56
    0x241340e14201d07030003644140461505040c0300004117a03804002100121399840c0205070b45415400d800c101d64000c050312810f16100464034940000181c170307426640c00381c00c20041420720b21015920703450825402c000342e9014014500d6610007042004140540740a10b40074145141030326140c20500901201680041070082c49803074060050300d45a03c02d00c122140c00111040000105250070a5480114000c20180138000a0140e0b40b031b05002d43ca0403401c8003203d41c0031081c030101808115170420707200749440d119650049402c00d04c2c04004150300441c2a95000140400c1200f8030310448000c0364801e07060051044034203014034101c1c1a41c21503964000f4521340940b181c0c0c4610018041c15116820217441407803080c2d5100c6905a80111008a840c83c0000380401240d1340c41007100103900e11991980a40d5405c105008046110310800d000c0325100b00300100400204100c08110006111841030a10707035040e1500250512541c855a100144450300d0032040341000310020400055002c145 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 693748785 1250 693747535 693747553
    0x6181a1c0204050f01081807150f17240d11031207031d010e10031508030c070905101206090605060d0b0a0e10020d09350306040216060603020108100602 67
    0x4403080725001f4402c0c22140b800038110348801c0c90522a00300580540c010300c00c64140f000c0340c0580044201e40c0c20307508221180d4408016904908074642d00210341072620300030f02401d03a0352440180f0450500e1176000c0140450070042209281204141c05411307400e882e1901c0d440c0521030750074011420050003240519021060b4440c17852061005004141055007e6600d080c0104501c07017914600320022954500240e00e102520713803031240040050030010741c54035001120042d00e032980d40c80352121142d1160b000c943c802d4044100030016000c0d50b1804128102c0d40d04024000d49803c5200faa000b5140a000c50f180307003841d51107050601c1e00242502c169840301c81d014001084507280070411401600555410448540000c1c291105400c1d0040741c1a011800e0801351040c00c0c40c440482400d805465000059001480c401201c1c1080c3d5143d80300d43d11100407038064401d081d44021004042c111800c10443c81d0360056050300e0003a0317a55480b554038a036041c030202829000303000160b0700c0f6800c0 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 693750035 1250 693748785 693748787
    0x90d2d03110d0f0b130e0307020f0d12180b0705031210120b06030f0610090c1b031101110405060f160b09060117150106181a1c0204050f01 61
    0x104601080e9550384a1401c01c1c0c0a9018080301c0704140500c3c0310390307102d01451580d403505544690075110118800c000c2ca0560a18590b62807091600c0240100040703484080155500e02c0701c20180d03900070b070100c509101120301c0108401e4000d414040b440420507404203041c4e40d02015a039100b540b01004501d8801c04104118240b980144003d6961142100200f58080021f4000300158480c651079203841c20090f0815081c680354908810441e44142d04004d04005100c2501044992900c800641c141117040111281c984e0001000b140d000046811000c0683c01000c258180300f18074001c210380d07519210241a90700c554480d403030b80305500b0f2082801c2581141c0007884510071082c80441400230654426200719400c84410400390800801000305840d843c2030320500e000e0039006002d12110043e03481c100c006040c083c510802044a91440004800002c0e02024084514437505031200749940d0980c190300200030300340000556401403080300c5050007030314182c07900207040d44108020400 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 693751285 1250 693750035 693750041
    0x20f180405010507031122180b0108010504050f1f05060a081608010302131508010908040f120c060804020d050106030b1008010515240c0304030611090a06110c0405090d2d03 76
    0x87e0045c000301a5600000c41d40c0010709441c1d9200d5411101050b0755540760001351840c0d60590099018604241c10005003010591525a010301c1041031845070f62320794201c28078880f009401032900050000b03091401d03e5003000e0100e04c6003005a03030320b2610782c42203130045508803c05e120003500045883c04e410a144095048410407030740860b02d504207256207842075030945440440c107840106000a09200e01c0000028040140440754a0a210720303540740d80720b00103850144503040803c100c0c0383c041001c6564165000440316040030090212035203c0c10524100c04003070310300892543c48040000b41c3c54030306000c0d5a2240c1c8460b1395202c0c0c00701d810700a2041c003410141050a0f4403d8a5064106a01100d40540180d8490720000d64503a425480c02034102d426248000890001c244031610302952030307203101d800741e03051031070301d09540804907665515050340c81101c940d10600f40701c1004020400082c0c0408200c03403e0750307419214203403c05a90500b61703621a030034080c01e000f080040d201c940250 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 693752535 1250 693751285 693751327
    0x70510020c0120041d04030c03050a120f060f051206011a0702030f060f0c040b0304200406060210050601032906070606080f1018020d020f1804050105070311 69
    0x500082861045000f40221140032542c120a1995001c1800e00450384025810303e22002115904102c03820251006890408146402410003200150214219120389054500444448824480c904402000d00041c04180c00b80c21500320b58002c4c006118035105441d040c801c130160018008690a2120046240140001c1c0000350300342004050b0060310100030110382540b035038020f00a54201258031551640f0040c012000f1114188824407811840760203ca07040307580524850000c4520301ea060740400580030906601615210000501c0b680106170030300c02e25002803041089549144c015412a040c0107e20150102c03590160b00801e50000c6902c03038002c9000b000181850020350798481558459001140b65801543d00d0b800c00880070400c00403201c0e0005414402e5201c0743c408900c200301032030310180c812202c0b0054801991184040480d8000010b0b2809560440c0c4001d40301d20088140c0d4200c0d0550320b0400007441d03030340c46840340307a005c5a9181c101901d49407006010000d54200c0d0 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 693753785 1250 693752535 693752557
    0x1152d0302090c071202120a050c07090f06090b04060f0312020a0209072d0f0c08090d080915040e0c0d0f0507020f1509071a04030f030815030307051002 67
    0x8280800942d035600c104912504000d06a29920303110362501c071540c8032207409148255440300b01d2441d041c0e0444400e81e1086641c030300e00700d85c40d01c0d0303020b04c01c5181c0703100341d40700300d200524040d045062044c10760003010540340b204905002c1c90501c5001e10003141c41600c902d2100d07114000d018800124010140390404265104407468418181c00160f128441640c500c800b04005002e441c01400e4003107140b8000007a00c64820600c00d851600203001c0101040041c800c0140c8a00704400b042851425646446405000c0310250605403a001c2002d030b0002000a1003404001751102c90001c109044400341c80e49140d0310012916030380010340164000f00816003609443c0c3d40f18415082c4d00c0d104180c13003200158004c24800118400d528148800c0e425034401100c0c0d040300f0400003503000505203080318805c401b410300c123f03405100411240110340004000486500c030805c1410343c480b210700d000e43c8440e039403240c0c2200ca2004042e41c03407081c080e0003491604061011443c548880e0b000d0400c400003 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 693755035 1250 693753785 693753869
    0x151e0402060409150512031305040510030b0c0a180f06030507031e140a02070203070e0405120d0b0301060b030112140c1005120106030603080319021b030c0115 70
    0x11948802c00b40e07000c20440c0c00180c4e11104c4100100e1401c0320358008a403005101071494800410300321804000c281c000c49010b9900e07030000ca0204806081450011070b041090f6982038102112102059400150044000380525045030582d40044046e141125801e2980a80f502d1602c00150b016107030060110f03040c0350f90341000c0c01d221080000d12000051241c64000385030002203030009180308000c2c100121261051019600503100010044107480c03101140311850b507160b2519910b0007002c11021081808041f50301c08030841c45400261252b40c5c110001d01840b0b8446401a4250209209220190716a001004081070402034618203517402d14003a44d400002107008215004a03c0000c04006500000e506440130940021f06000d01701c2c520707040c000700c0d28540b100b445601000d0081c040044513254095410422607040706c0c6013404031940e0301c4c1006002c0140d180c0301d0b0400b00c02500b441d402d12800011408481c45001c00365810249510300901074030407890700e00c80c0b20341d1000c581050 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 693756285 1250 693755035 693755039
    0x103060e030f07060b0a060810090207050f0d0f020609030708160606081603140d0c08160215030708090706080c13050415170a11060930151e04020604 66
    0x5a90300802e0700f42d00072032021032038054030428041e10040540c0480100300152043c042c0d003042200030081120510800985c40e50741c60308143d800c02c1c10000302880d145c4219809035000a4102ca00000803102540948419a030303100e0a054403031158840042400e4410400d440c890b20072910070602075030080300300040141d10b58082c2464002e018010b11540c5901c400104200031600b0b410040310182540a03007001c0e1171030b40c0040c00825104074000c003900004281d8020b0526100307000e11480d07800401c000140d862131588100983e20544032200000d07004000503a240d03d00140c100101c0300a681d801980d81d89605606000390881641103641c100495000074156171240582c42c0381822411b03589000d44d00d02030207210744c001c000c129800c00d0340015400b2400300d044150740c6445042d00751440c60b41e9407210000a00b81c4600d041c04400b02d0010b4a0b41a000d01c2500e080c03e02070000c988041f506040006162541c2000c02180d4034044a4004020070200036464681180c101d071002d080203003016 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 693757535 1250 693756285 693756307
    0x4050c0d05040507091a0907270b071a240103020c070807050f010807020303062110050906011a07060c020316050a0b07171b09030f010f05011502060103060e03 70
    0x71000d803025501e541c45407005024490f10b501c100344814503010b9030344030740d41440404034008541c010421000d014000d0340504407200c0c0f10401d1040204020555203105840e1240010590001201601c10511440c550704d00d0f800c031288880d000c2d44590a004d0980e1140307140d07000c003c40c0503403001e904258080c40310300c4940c4410000900a4081c41010305240d908200c2400340c5800903000850410003020148201c0e2900441181c2d000305043c4c8000d01e00c1c94040c80c8850350900180d100301010300c9005400b541c108400c0d440940246241c0c0261403550766201d040f000480b8100806010443d0100048800180075502420a480d241c0c0152824100b161214401c2d1441c180002d503001c1d0805070144040010020002c1d0b4000001c3c20300c2d09114045007085142448000e04072901500c0441102241c41400d0041c1d8040032301c01400c40340210340ba683c0042c040c105601c1c40d0701400c3e0030000046001d4824408455501e209680140141d0780380d40c0b210409001c0e02c04108003c0d00042210047c55 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 693758785 1250 693757535 693757541
    0x80c12030304141c030b10050712030e0c100203070c0506041a28020604030207060306180b0d02090c090315060105070323130e07080730020d09120216030204050c0d 72
    0x3131005441c005003415285007070101540002080600f00082040460000b0b12066500d21240394245000900305511241c45480c12590f826402d910841054400800550002c003c0515610400c402d00c00785585005000203405107000c0c44403140004200740040d000c0b40b034003421500c00d030001c503003980035042d03400c2c0c500e030074040000b0f9001601300c031041200303140e0104041c00c01811117203402c000492612802d42480d2800e14101307001c00d500e44841e010943d4034201440103558004110354442d0800041040c141e60100848034001c1c0560951b07907400e1142761000d1407040c001a1a098900180341d6000c071108640200344044025521714160307405070719000600381c164106040740301c510703052584c0d0696400c0020030b80020020030004020304240c1c0710300d031480880140d999600d0b031065419140342c45030a0880306a05042e00c0411030380d0030b035a21508484035003801414004400d800c2884100d0316624941540e0010200005013080103040c1179100c55800407408403600e041203415450b800903 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 693760035 1250 693758785 693758833
    0x50409050709030b15010818150106020c030c03010b06040311060d0501090b01090e19050a020412050313081b130f0507030b0a0b1201150201090804060801080c1203030414 75
    0x1402c8040140104800101c202e5001844c4224a182c85040c141c0020030b454801403440d90151a145801e100610082010351761403c2044844002c542e101d00000f50f032103d21710701d018070920540400c5002400c041c490101909406044240380c5811a101d003c0124442807c20340c0241c400c10009188490328800c0714040d10001f0b2000ca805000d2000040100c2003a400c890f50207144402841003070101040f90700225481300d4004903040d80c074202e0980080c05a54081d404242240c018003080110101c024a49034591103100342500380c88221103541c5100d00203a643c6180d101800182c160f1420381040c00c61061030120104068000c0b281c1042990b1082d030318100402e448140303800c020700d00002140003500c3c2c2d80d00c071142028401e04c60740c840b444040c42649000340c51042d08005d514400e401402035590014401ca07034441e82c0e602c000300552400d12641006000320f81580000780b42070000c580a4070804001141180c031217840b078500c01c00420100388031a2150b01440e913190007400c644081 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 693761285 1250 693760035 693760037
    0x604030302012909060919060b030907060203040b042916021005030603030901030f090b0903071401090305071b090e030c011a030a0b0c0f13090c030603051c0504090507 74
    0x100c80003045280d001ca9240401c4071010f0030041c4031a50855119110700a0b4001c03000c442050305612042c01956032500c00d440384414080c2000404151903419800550003610b5a078100d403e8281c0d1500b00700e0300d070700030382c01100c20881302000200041e5604110703001d4000400b0500c040541c103141d15980880d03011004020104071035035010415880c0ca90603105480034641030092961610380000b81d205d00c0346006080c14540d96844a202108490340100c04c1264060760644880c240f20703101d1580c0360010041110b40f40000c03843e44e48041e0042c0504040780354141c03561130900f280e56952070b5280724841c02c070006001c00714200241c607000c1405880c503040c41c460080d5540720b040010503825204038140c0151544104a100d6119440c0012a46000354011804031115100c9281ca02a83e2190145400300760b8000308075142d840001003441c80464200000811028507161815000c0c0d0310141305c050143c1d0007402c043c40b503005400741d05095009061802c1c0d803400380c07942441411100c050320800 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 693762535 1250 693761285 693761291
    0x5030c1605040b010906081308090a090914010902130905010209042a0309380907050f1207030311012d050f090a11010c060525050403030e190302060403030201 70
    0x12950a05100d0f01081003c01e180208501d41002005040c412020f0404c81c003034091030080405010501d010303141c0d0030340d000b40600c1b400b903510700400014061070741d0141c8a080d25400e0b0b00c10001414400c034801c0c0385c0d0140c190042e13030700c14030b1800004000118090364155001c00c010041d03582c0d244070b00c09800807c0307d0039414040041103420742c10410b00c2c2c105818140307402004000f042144151522000b000b03040b110070900b4207030310415004c80500366925414074082c203100d165000850081d090314025034002c1500d507002010007500038803868200c0710903003260100780301083c850754103020304104920012422034138000320b00e4000a0f00054031498a00070059501883c1c10b9401040e80103055402c0000c0d03142002c00c01c240c2c40b4941000d00810328101c05801c0501640076401c220042e5402c54020012440d1041642130307201e01c1c4e01c4107120b421120085002c4428041e0060ba401da80d0980d641c0c050003d130610078007104141e042c01c00070450389016000801644c6180c002c04c0075500c03a034004 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 693763785 1250 693762535 693762539
    0xe0112020c0a1a0a0b0a05060706021210080d082712041206110a050d02220b0901080106050f070b0915040305040f0609030b04060218090c042409030f05030c16 70
    0xc006415400f0307102824041c1005c014400d1551085014800e80d20126070103a80d1301d005141840003032140064405102001204110b1105291b803002000c07170f0310f1001600c541410a0740c04591400c130460b903038082300c1641c03040c0c14a0700001086000311500780b07604507085011a4030f20811190000c2d4410140500007100b15020000340c0c3c09a000c804030300005040c03c1c2130107040041c00034040c0b002581c03686a408901c1400d0240d4840402207841035810121000d15250f4030f494038a5403000c151a80450480400021424494012500c030480b62500c0207041201d00c0da5031004000c40a03040401c140f080720ad441c80070f01d0001c04540d0082d482a21402e43e0f540c900008044420240c6d4810380c01c3c80001d07403080000c10405035103268041e512150041c1e8483d00c102980b03058802d441844c60b00940d6800800c0002e9022100900644801042400442c000c2261207501d082e025042a0001550200208000381200c0f0108208130711500941741850000000070b407800441042d80b0709028412141 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 693765035 1250 693763785 693763823
    0x606301103191a030a02010c05010605100302090f0a030b010b1b010e0a0201140301030206040b0a02030d09030f140304330f0603020f0306042001050702190f0b0a0e0112020c0a 77
    0x3c050301103030840c41d800300440040d0000b0b92244100722029062055210b422404c01c1002e5015001420004203161028214001d0040081d04400921806120341c00100c03411850203600c1c40080301e604c804111883e0b030922058114682246107509007070f40160404042d016800e005814031010094001d000b48622400010a1502c0c200e050500a25042005201580740d0310102d4003510740300c207001c50356907040641c02c928620030201f04198031352030080d1240030140e01008002104025a0762030444c503039115055900c038402a82c00400b00d18032144000091407250704a9800030041707221001a8141e021009000d40300c050600000c5c01d5902d49041c0210b142c0750b01d0348481010140c00401085c505682c40c580a151008400007500c240d50f0041c6500d0ba200304100d07001c059018080075903034585410500e03030281c00c030300891511040501300420031031003820541e4030414695440c070309074000303007001910020a84441070241c036030200301c01c0402400030840e4400103031103414070640190300b15103 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 693766285 1250 693765035 693765041
    0x6030a090b0f13062a020601091b0e04050c04030b04060b040c0525053405030a03050403060c050708040e0708090706020c090a090b0106050d060630110319 68
    0x2032901031001c8401c2c0420f0380601a01806040d82c0020000307041c0d10319442c9862000551440382040c1c0a0000255900590128455040320084c1d801440101c0e9031900050240e004002d620000400e4410a80000d207040c0e0495500003180944040ca000d48980720f0320960881140d050350b02c65141c41c01120141004c1c4940071074818a03240807818031603d0011481c0c0340440c8506198446080410300d401d101d4148017440c030104100c90749403402d4103040e010740190310384442d80c5900c480300064005214203001c00c0888883d94941e0315a0715003410b60b600c4100502490721100100403061042400250101000300013511003034401c05000e2515620043c11050028180b0b0070b2500328110401100d900000c4403070035084100c13044421950b62409003401031040603409000b0b54000400022440c0d0408002c0400380000d03c3c041c0311f100d4541406442c1440e614090400b56451425108115034142001c61741c42080e4450102d5030f01a2100d0540f030b15041582c1031000819402c40d92a16400c442c8 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 693767535 1250 693766285 693766291
    0x9052d250848040b0a05060315040e070308030714040f230a0f170c031519020f1206060c061512190b0601110601030b060103051f0306020c0c06030a090b 67
    0x9003441481c0744051060304a10780c19a00b81e0095483e12113100607540e5212100d8054800500690b072245000805140421600c031300c940c1c012480c1c1290f4940544001c01d540381034980001d041441d503183c1003000c031820154008500c02d406d00602000c940c0c48050480b0700020008010b1000d40384000781d0680e007100448a00007849003107202000c01c080500c4805280895405030304480020100c95502c508012288141030b6250090b641aa01c038060911516401125041d8840e00c07540c0c0003008200403031140b00048285500240650340c6000d6a581c0f50743e41c8000302800d880c0c103151030144490324081040c0c0c0c0e2600034282c0011301d0609410411500c512111821006145030b03150b945030714001e50318441c00078140c50355403000282c15901590940d020382e0100022035442d580c1d01d0400301c90504050710341d10700090030440450391661908820b0705030115036203a0604003a1550341c40c00025400050503020038094080807100a94441000e981300b041c5205000c1b0f20744525190100f9003000003 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 693768785 1250 693767535 693767623
    0xc060a0e0d1a19180b0604060f0e011706040c0e070c061a10020c0906090c070c060309060b040203042a1a042c1f0909052d2508 56
    0xc0800c2d00d0550711482c2e0000342e4141c10030005c881d6030701e540c0c1c0458090034180d0080800203610764800208240c4e040320083c12944200e40300034404a21100b1039480c0e06099074040c00d5100680428041c8665003c3c00750b8004001d8108009091800c0e950482524403141c981c03010300103c401c04400c1c904000e036000091300c1c2944082c200300c2d20400c0c0003401c400005824540202508000502005451011180d10075040700f2102404c60359080300402400150f001150f82038202a0300d40b06600f17250007030301c0c003da41c40500071201840c601200c4c003502010844a00b500c20802100244444c204120340d017070160b4010209584074108923080941c9000e00e020f212450904a000c00019138000c3c5980390402040100302c070007040700c9038003094506425080721140e0340c81c0c2142034042110010300b44080071101002070401d02d544e402c071020004004201d0403550781084001080000da24030490007810416001490782c9a2103c00c410701d4044404141009241d000d0390b044e98001000011451000e00 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 693770035 1250 693768785 693768791
    0x30307020106141008220c061701120210210b03070b0316140405090a0b011101050903030105060702031009050604140c06070305160605150a06020c060a0e0d1a19 71
    0x41d4010903014000c44111808100c0790170081044014102880c0704d4001108101c0c2c2040015810310001107403043c030401d0040b41b8242454002c41e44600e403094100c51b00310780782250018182e024007620b1758031510040704010500b4403034801000c05c4071010f01070740312001000900041c0c010078549088169080b807900c0c04410300c104810b60504c5d08420000c2c5500785080c40c1d65100c1114040514000d81c0c003c039034482c1c0502c0400120300030039030024061000903a11182105100c9140d242200c00c151341c00c3d2510740082006100702c1c00d06400600c1c80c188084d0488500701d405980e004212281c0300811142c981040d0306000600440002c06001c0c191110b01424085241030001070061051400050078000003144450105800f041c01040b07007031300450180300a14040741c0103280c032229000d126104540c0e103600810074501c0040c10026896016100c40e2030501c040d5010784078966914140c40e444004502182c0c005415900085840009800090b60a00340b4811f0791100e00c10184612951a01d = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 693771285 1250 693770035 693770069
    0x121f0801021201090908070b091c0e010801060f09170c030c01051201050d0609060c0c060f0b01080a0f1d0a0c050d050a020420070f05010f021c2a02030307020106 71
    0x4228082ea4116800340b40b0004030070381c481c500b480c003e000320440a05000e608004010002c1400f05484050280340d01000b16001804401580d10039004058640084c142d0300040c0255402000496171054003410400c1149699200c00c1c030500c406840c8000741c0d03400c095801d040d181000c20604000e10401d092135800c008403040c000d0650310051040c1c6c1d104100440307850040c8034040c2d0000031819005002800f00032a1000f0191034804568001c9070f5491504401c110010304a11842080d260305030b491003526154050000058048480e80c00d13152540e500c602944a450039a03040c4001410b4005091042c03130506010b20002c90380c0c0c2c0814000c11040d25800001000415003640640e41260001071240401082c0107a800802c01c074036982e550b00041e20b5084c80a150f6114446a00c540000d01a050508072440180d008000b860b010b0600035140a9014403050382001aa0780301e40c80b40010103030301c11450381c45040c0650000402503040002070142050b420300400707010303100e12500c01030380e11 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 693772535 1250 693771285 693771307
    0x30302071e08120306012f060703051005040509030d060f090e0102130308031911091203090a0b1b030f1804051918050f070608070e030c0103020906121f080102 70
    0x2443c000842400380701c001001801076800b034004441a82d05044041c405a015940800c00034005070f071041400303115003c000381c103e80c0300340501c0707224619000300249110b1034641403001600015001e10001c1c00706014101c007406051007000000d0221242030100689441034043c11603101c0398100f00c05900400a1100c030f104100b0705101129440541240d803030f521900540300300c81c0700941005856050840b54a66040420045c5c03000c95003c0781e03134100548111210941d24030520403440c1e0001c40e240f00c100304101d400d1024109a600b604c1400201b400f004100e54216480000381130380005011800780000e00030b1803d401450241a43c04001c5810011070448060349801d5051101070f48407101000e000014021041c0d2455000d0100c44084103210003050701c540e000c1c0541d200041d0083c00080031a84900c4150304141005000b82400c49600300044000c0e6000340c401e6a0801c008121a84e910010850114400e100c06004652f618540310b000301c8005c10180c0c13002c00960b00502c122110a = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 693773785 1250 693772535 693772543
    0x3090621011a0f030415290f03070312050c070806180a031d03030d1e051b160305041707060e04060605040b03060d0b0901020a02010c11030a0324030302071e08 70
    0x1043c0d0322903020b4407603032140b821058401021038042c54441c182900c849034004105450202c509680b20030b14505004d081c280540001c11450350b550540c00b103042000480c078a2400058010310620703102d4640803986c58401e2806131203502c035041c2c0f40d200104220848103440945070070310710b0640182c56540b81b070383c4008100703200c2e104003c13340718040c0c0340366001d03543e00300121480c49a500c903044c00207905e200ea1449001d1600f011446000b0700700b40000f6010000580b045665008030309603c0d05155041003e01c000d0b801c649801c5092100800000c1401d05110b40022511f082200c02450309504007940284100041c80c986030180d424054244519a08a01903030305803a4144a601d03240d0740c0b600c000451060020901410141012050002841c8190001c108480494000340002280c0d40c0b01110342e411350f607807480d949420074800c0940740da03c40c0d0821140394148400203401030011130400f9030080803c1d030040703000d039002210030400c9800441c00c0306c1101d81e1501100108a10b0404441e0b15 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 693775035 1250 693773785 693773797
    0x909140d0f090510213804020c19060207170d060f05010c02010c020619050711010207030b0610020f060109020c060108010506032808190201050a1e090503090621011a 73
    0x14600c011710f2007814040140d03100d0007100203248042c03044030001c0c5c2c421004002e40f140c40c0c085144d00e40842c048803410640212042403280340000c24180c00010140d40124202e40c004072602c50302003204c00c010400c15080b113440d110404003201da89400304480c00044441036400440300ca00100c2c0100301036a002454050010340a00b04040a00c8007071000445034840c285c4800707483c1d082c103c10303051099031200c06800311611544491600d1300304e1400590b50b40060703200041c01404032800090603805c003942c1e400c801b00c0c00740c011211901e490910090406009030451144a680880d000e0b40c0140304005050040c80c2050003000b042c00c1480c0401d482d00c0c20028840007015540b1007180c2c01105a0304034540c0140c0108000340c80d010719015002c1010003081e1203074015070804010482c1c0508522a000c034030802c04803504408107005191801a0014020a541a003c18441290f50340c44090080403400030801e00b86504000c800140e00d110601030f000406032907403c000b010445c542040486003 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 693776285 1250 693775035 693775067
    0x8060f010221070602040b090111011b0e0d020301062c0f0a0c02030d061805090d271701050a05010e0702060103061503150917130909140d0f090510 65
    0x764200e4400d1030003c1c4a60030000f00b05901c005800100f064401018003410b18090740c0700c240381c0991010581c244c440b01e5034400300f142954003845d045c0a015102d5840711039400b03030008480400540000342105e50315484401c00480e400301d6030362055404234084010034a2100c1101c0c1608003a1078020458500902e845112a82c542e4442e803520300801c00c1d206901ca03041e00c140500341e1608061800381e81c02c1c03142074007007504250225400e90800b10f105942f0b241560b48038061100c5003000390140030046205888243d0542001003404216901c02000c071030122000401c003410411407090807104140d100755120f05541085c024101e5000c0354150440303400c1140428441028505240e10130340340da00080c54140354031126800b0801c0364000400007409441d00b00d0035101001030004c440d215540c40a174440b0b0071850207204d14001c41d0700c100c18490003041e902d02000301515800349090301025030f01011540c901c0150180d07036400444040502800c0d43e40303034030030159440041c140d5280c01c40064 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 693777535 1250 693776285 693776323
    0x13020703090e181902090c030601120b1c0f0506011409070e03010b0a03060903020705060a170a0908070c03050709020703120c1701180f0905030730090608060f0102 72
    0x241c1d0a504940b2a00320380c5000c80103407110203611004d12804411000400c9000740380000005480303d20100c00d6030b01c01d28040c0c544080400350034446a0050400d2480182e0041106c140500c80150200030807035118030417280945200c7d107a0070007524040c0164410400b2010120035002e66032140300490f44c0008a03414000c2005ca4290700184c050552304000d1030304010b00c508000207201898200040550003030302134075020f42d203802c01d025140c41001c11100c00300700602400c1c1059a010131160342c0c000e4003c80001001301240c1c1c1c5400340c41d80498402e40318000030100900074080140308010040c428603404500c0e21700b0b03955000e003002240803600c45402e5650080000c5441c02000c1d10030b1070181c0c13031504075510344c1c54454610a4001030f01406d48254601600540c0081d880e206141403580c2190046042420b036035030740c0d04070702000c4058610f88041d01248420b074040103007100b0032800050711020015428080c0c01050658024990303841544040a00c50041e41c001c43d00d42100030380e0382100 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 693778785 1250 693777535 693777541
    0x50307051c0501140420030d021c02030f03040c03030f0e0f04020c010e2b020c03032a120d0f0513030f020c0604080106030b010e070f0503060f1003090213020703090e 73
    0x4180101146541014000700c13200c100010450303402084600b10361960040050820000d0605a07a0300947c0181030160740100840e40001c007004203021040203040c81102e00d0481c00b0040c221454006403402c940709071054a05004054100300140c3c0d8180b914940801403041400c00110885649101e15005a40c0002c00083c3c0f420300303400c140048200300e0100e41d040714a21210441c001601110003000c840c074150310050b503600c042042140300c10010011401c2c44005200081d90f0240f444003810190200c0108001c102800d200b903003010004100071035110ba180c07103c6242076564214445920700d15200803c0420002140c102a10035010301d4501e8842d5005281a407800b80ca0340c41c543e902c4a00442c0001d016a8150421130941c1d1082c41ca940c0303244d070b81c1c1e0520703d0a03081c1a1440d0010420501c00914100d2080f000345611510041000c01d00300d503a0b5010810b040c0c1070664080010391140c01d0f603401e600f4031f26119440c031801100c0842ca042c5554030024400400d40c012840c0c82c00c408408 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 693780035 1250 693778785 693778793
    0x801111201060e27060a0801020702060d2c0a0c060f05160219090f0c05070b0103030f0c08071b1a040605071b0602030a020c030304120b0403111002070c050307051c 72
    0x302d00d281005080c600c0c4c6100f184886064010390040700c2d010b224030014034010846590600a85590550162080c0c4c1440d602030a40c4000e407010449c100c2c03941c02d140c101007082e0b1000f01100060704036480058542c00c50141000300c98400107401610501032900b8510000c0e80e03105044074a420340701f07440d000085156100040c00c1c8588110041c200d840f20410100d002015944101610001000d0400034040c071400d00707464034060030358060b080124142c010000709016200d010a000550706c1c00f100c0d0700301d05559015007a04500006c1d16042941185042c400c0b40c1014280007030310305600c2d4500e0741e40c4e42c01c8420a5034401d502814042103c04038100c41001014405c0d0912880d0f1101384144181c1c072000300941c0c1e60400446540103200351080c203540c0341004021a0305940e00100280007854181d10b60645007030f4090000c808104002103404c204810a00c95903480e07a4402d80b025a91f80450306081d07901d2003140d00918441c0e041004104880c1d5a02c1c1d18600e840e80209010071200c161a083c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 693781285 1250 693780035 693780049
    0x1805010903140c0907091d04020a03021504051003050a0b150f0a2d17060307050607080c0601380d050c0d144c08070f0801111201060e 59
    0x24443e0805031007070921480c46e0300903603580c054070040d0006022a180082d40c00a5803001500e010f5008803c0180500150500300d0013510b144540e2000b0030316243e510303400b040180b01c00f1001032000075524410301100901700e0090b01e0384241c04a03004050003840503942c0d1102d2080360503050303000900007203c451140c09440c03142008510b400034520200c0f1a942600008000760400400040e020350320441000c554483c00d9000c0d801c0613008043d100c0c00c1109002403030b84004c2d81a00c021505104401821104001080c003078800c0007015000c207407007000c0c900a0b03500d000c2143d01c00074000292098200302010140c0d6040d2b010710300c0108694507200c03171140043c0b14200f1405125400c00301d6461444040342070840c0180038003000c0280b07600c111421302780807540e407041c40d0484a00158002000c1240925801440d0042d2000158480e03a40c1011500d17000895001044020000c3c00030811100288141150020811011841d119442e0a0b0103600e030b138140915402d00c00c58180c07100b02929085 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 693782535 1250 693781285 693781303
    0xb270307051515031609060614090402070602070f0f030914032805030c0c09070f0e10141b010507020303040b0117100507210e120c010e070312180501090314 69
    0x42c00351200084800c194520501d9280140e06c406818003200140301f6101c6c80c40303ca80c6540d46001e66042c4030322002000081c0d0b020179000d07104150280100004603502603016105a4420600004a040f280c0307400707030a4640355449003240c8615a01c0261071520301040c4944040a8a44004a280c071410520f01c6415003901001c1c009210100700946a840000340c00e07403001070202e0b130103196035840000071160418105040e00001b11842c035140c11a061100e00c1c0d40c8008800d007401e0709040b02e4820310b10072a400a0600c00414180d2031601840020300b8802c45070058003e03c01303580341d81707482d4540642e141c0041c410002010f110f0080007100407018070180d207202404541c14450b504004c0e00080c40103452000615030401c02a10320444110288a080d02142d10391b00508002070758408040d05607003048400c0f5071155250f51103004440018081c03400614800d0b0703000d0b1420049080d00420300034034008034074404015450284001e0f81c00080030300c02c0b6540500d014070503030b01c2901220f007019525 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 693783785 1250 693782535 693782539
    0xe01020f1917040812041a0a09140a1505040603051312081e0f15030f0c010c0c1208130e0f0f06010e030d050415090b0906070f0b270307051515 63
    0x455010600a0909030040045987c02042d6a4a004006c9440d02462046040100c0031490000040108411908041c12041401880c0380d8a16944601f588070000c440b040a00004100240512038190540710b042d030080305880072022543d42d1643c81d8030b2100381110011052050107000a00264400b1050340c1544d502d003000c000150030030320710103e06400d0981d101d40f100c0080341c00090b03890400003001c0c80b00c641044c004120040382c0301c1c015200010303400b00079240b5441d20350740410b04100701080071101074443c2000c1c55403103c016200310f200c10041d402c2500c02030311000078030985000d10036034960003445208e2303458415140c0d94016241c400700f807500681c00d4041d1070303600103810390040081e0044030010501c908421182d9082159007106030301851351942c005002c1c038101401e000026007051751240c40c8200071542d1f25104d000543d5012034044626078952000300c8800003800d480b03250a400b034580218100b95213541c0b100e4403884a070b94144054040c030800250641d0710340101914078080 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 693785035 1250 693783785 693783793
    0x503060d080c1605220c0c0b04110a060c0b0402060a0912150c02010605011b0303060b0c010209010306050603010e0402091906030305071a1e0c190e01020f19170408 72
    0x8030b61201900c90140c040c0c414001109614001240d00305000c00c4171070036503150646180841e0062902004014680118041200c40300c613001c00110f0740400da5014a0040d50081d03000411042000145000d54000b0b10400500319582000110ba07241282c2d0030a42c1102c40c0f41e00c603040789804840d07900c4960301100c00203580412003002e0041c2000001c50048110388180080d807820320040e800e030f074400d200e075030f0000700760540c8950400c0160700c11000141c0700e40b802013642591001a12242c0d04009004002a580000d0110540d07816100745401000300340d90306070071589030841130000d0300b50050010b800b03025200c0c0051901c004040280300c038a14a1541004000d4483c00c0043c13460b000f02d40111124241545c003001c4190103403800c584188020300042144101c140395901004402809100300c030740c000d024104c882d90700c0c0d584540320001c1554070000b40c000204002403800e1060341c580301664012824049140782c0c000b41440045821561201c17402d00003448100c40e030700c2150b1140c101801 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 693786285 1250 693785035 693785047
    0xc03192321090709051f06021b01030603441b060108030a0f020102040905190c0f1d060f0301170d110a0209040501231b04080d0503060d08 61
    0xa000003401c0c81c0492115290481860740c50300d00d105140548602030702c2e900c04102045480d18903006540c0c48503102c1c11501e08070011600408120070107800c44000f40e007060329046010900007070200c00380d51003442e080c0407003487c54803100c4805500e010340c24800006031b07040260f0070741411814001d121506880131901016068024010340051004900301e6100002cac542000d1000200e45041c1e40c1c1c0540514940700303000e0301c03d0310703c040151072900965400b40400105500a481060702c40e40441115202404a050040007160240000c05042c05807008002c286281d0044550f600f042c400d5000244d0301c07161000169543c000c1d441102482d410020006c110001040d29100104032040122420300300f48140c10745000d003000c0c1951449511000c4484090320300001f2194102c1d014100000d1260034038108410032140a80d448003011185505008180200821541c4900709580485003068101a001a15181c00d10850410044044041000380d910009008281e950220121380c2d686 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 693787535 1250 693786285 693786347
    0x4060c11100605010201110c10090c1d0604050705070b0705090315010920040b0a0509180a05070207121113021c060e01150819021b010b150c0319 64
    0x2c502038140103500b41940751001d100d40c5c00a4540104540c00940039001605054500400d5040300c160b58680d080320002810354002000c503020741031450410b03801172415806200644402810090030003004004250120b08ad648032190868032034905643d03120030500020f0314125090540481c0c41d2900c10000418910070341c410201c000c1c030560885005603103403000443c240a83d11460441070002c1042d100540d11070001444040401407035244404402c4810030032058044800045403607451080c82800c0303404203c00d000506400105524102c85580c0390190792a164130700c0e83c0074640000d080d202c0110705070141d89041014070105801c50459100b4038002d010103202d4a51011800000494070341c4d41007400d003400002545508025071114501105500c503480e9400c4071150342805040781418031840c0d20040315084c0400072a000c0d16450070880b80483c1c940300d007603031008100044002c0c06000f01c2503e90300c12160b100700e01c1d2103141303541c15103400c601240500302031a50030400c16007107 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 693788785 1250 693787535 693787541
    0x1606020d023a26190207051b0102010624090b031905040816150e0615010c0302010609060902040f2108310815070207050d05010213030501090515060904060c1110 71
    0x4c10307464480311505001c0c1580c040892003101401b412a800036030201c0201c000104090005400602c0000380b841d686403a814100800040b0800120380f10280760400d02d544451408081c0554442c014618240400320102d50003030f81c00340890445d110030026003407100b1031042c0da6200d403942e511a002c1d903146103009d00642880004008030240342c0112038009034000a2514461380c800380300c1a0105100e000199034031640341004504646d01c07400041140d003103900641000786000b400158447c2e080080600485520350030800c81080c0100b180411b038078100250711000c9400c00300f140da41e0708003d00410f03086000018924650100c0c200b04d00d000c13a840c20380707040498001030156000400c0c2c1500940300c030710080e0b0700100141c0c82400c00388058074040b0004202c0c240f01c0e0000621b40038004004094548255005550596680c00b106e01405424401b40c0f840c4032101c51008030f60b00e80440002c009020141007d080290342c5c0100312012400b410401005c034012000701c41c03000300566407038405 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 693790035 1250 693788785 693788791
    0x40b1009051002010b09060105030a1b030510060804050c0906150a0e040606030b10030c050c011d0c0907050f090d05030c060403030b0a0e0a0e1606020d023a26 70
    0x111030300618071406910600c50251917901c0148183c400d51100c80045803103400280c102c281141d501c0b2498021844000700da61502403094901080c585020000c00d0340ea01c1d400d9000e01d051203004070400c0b00080300850000c091610444415266898110218407054107005e8540c0190714002003250340240c01100b050070024045505001c0c0078ac075580c08805031101520001d412101c003804009403d4080e0b00021006403841c9800c03420452908005425201004011801d0301400388480c2c820000a0080701d240307610540d005070080c00c0c00800140349200d0303c2d50362280c0e90300201c4e1070340c1c1d01d42d90340e58201c1c142d9030071004590b254540e00c041c441d11807206403400c07008039240c001000b5517800d00d804048211680c19884040d159509111000588465194000c1c240134401e00800b03050701259168000c1e10103640100301c04121880040c0c5005c80e507004005440d460f0022021202c0f1502042d200c840c00950b5034a00d8005164000b0b032450f140c60f00102c66100491407400d100d0011030144284 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 693791285 1250 693790035 693790039
    0x21504050604110409030e0d020105300c04060912021f030218010318060e0c1906090b0f1822021c0b2404080303010b0405130b030304060c02040b100905 67
    0xe10100e43c01c1100300c0c0e5500c4801004121014580001450407a0840c0c008500604006252111280c0e040c0078059810200e9400b114080d499114110b1590013000e41c0302000d11006803500741003010140c0340381c00901c0341c450f80c0d0010002e07404c01c64507040000a202081c1034030303000f01106400d0014010f50401641d0354004240c204940d1076941c030074018250102c0c60494842002d00c000c0d1038540c003070009080030015600c1400d00c0c8042d19200d840c007400164005009102c401400c000000340b210406520940d1544010300542000c440c00a0031100c000b50f6099114804011071404120358007a07a10a000144148a000c3e251844098000b0701c2003804c24105002d00410301500799007102e40904032140c0142c10714a80510040e4001200c0030143d40c50301c90309051980da0015a0316562090304178000803500800c0400c043e041c240c0211550342581c10003803000042e4440071960f81d01482c0704840400002c0c0504600f0342d21594401000d2440150044111030700200c0d001d0700140c458400d5074 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 693792535 1250 693791285 693791303
    0xc030106090b1b1f15030b0a09170a031e1e0207030e09070306050f15030406050402031905070311061c0c18141c051506040b10020d02120424021504050604 68
    0x4002c0e2a405c410311000e883d8440311000c1142c440c0361920000b0140030400f140e42e4580080d441c1080b203500c0002e4821443d6075500455040d0030a401c01c024040c4422030f80110504043d00030007030301500645201e03000321402e80140c4a02150400f00e0b030041e100d8408503000740205051003440c0d40d054014a040d81c6003a10415039404031141480303101405010a181800c800b800401d0018416810140c0c100b80002d085070101c1747c034400c0164a02c0c083c0401103400c1d81c040001003003040700001c034150201d00103c80840c241510100105203c200d48501504026070341d516020503140942081d4945c04244640307050306a40328001100341c0ca4501040d0351040840166212005501c2801881c48603403043c090080c08480b05d00c0d00c044540b0261100d94400c1c0c0720398039081691645840c40d110900705600810729410f4502020b030a02005001000071101c0400c4184182102e01c00f0510f0300d5540500000c08040c1070380001c03424142c075001041400b544c1803052006006002903980c4c0905d014072541 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 693793785 1250 693792535 693792551
    0xf05090c030d0f050301050f030a02030d080901060603180308060103110d05040b06090403120b01090528060503070f140408120d0c1b150b06130e0c030106090b1b1f 72
    0x1070b550f50400e616140b0001d0700c100010b000710b040403070002030008005001c40c1e00304640381d4002410109140107850004000d0350810102d1a42401140c00814090804021442035040c0006000300e01c854041c0c248400c0c0c20211b04d903648aa844080c08480c181c0d58291540c12074600d0001070001610203a0304610701c0c00128841d8601801131a01441d8552124160601c0c00003080c800b87c1301a0002c036051140329140087e00341c4030710400c3c0c00d8954151070520b4403000d01034030140300124160407000c1000000c0c0100310340d0360341054030030030000b043e801c00320710b0b42c151803580783c9403407203540c0101000e4000d00300c0c208035084a80c8040c00254540510601100c045001c0c100c0340581110383e1182807551680311400465074000203224031249021006c0b0700f0b260a400485d00f0303075200c0000c08203c5c1001d54020040750203d4600b040d040007403084003e10750351400b0320040c58406d160052581a4000040900c1d03401074404000c1c04800d080000ea582941076659508041c0081030142d00202d030920b556 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 693795035 1250 693793785 693793787
    0x91515010816171b07061d01060e060411040506070303020a080f04080703110c03010e0705130e0d141201060c0201091d0c0d150e041b03050d050702040f05090c030d 72
    0x1040c5800368183c0d143c240d01249429180600d50025008407443d2091110082d4010200b00041404901421020400a00d05001c80700c02c018265100030342c5900d4401d0501030782005100c00d07504148120350100f0351047c2e010380300041c3d204a0740681d81c0000001015010140c05401908003036100d502c510300c4136942c40c2c900910142d404c581c010314160003001b10030006070060b5aa016600010000c56101008040100b800c40d84c803802c2080a90384815400c2000e480d180c4407040c00301c0c51030001803000d11030300100d43e995122158a03890a2000b844110b24514603003d0035100041440c0250003505d50b5507070000340c015070b4414016800038011400100c0d40c0f0043c0e1098201c2c107054000e90120355517032881080301e15000010041d121540303603071024030f0342d801407183e070000303030109824044281c141031400310307641021070100048003090200d04002085002c1543c603118406030524076500c20923403000900420040c0403407140c031850a030a002c130351800000c0000182c0000c0d001c0300c3da80b0321040c1c0 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 693796285 1250 693795035 693795061
    0x20c031c15080d05070c0305060f040506070c08040e0903070b0406060e01120807022e02070510030b181e0f0415050603071701090525050d1205030915150108 69
    0x60b12600d0b4400d09000740c04510402c01080c0c80b6002d854050909501c0b40e0b660390502c04160b80e0b80c6140e405c84d40611060040c00d10070a0703081550307420140280d09050f0785040c4540924400c1c8801490100000350054a0a00c11a44400c0d802262440980f90034038150340107108600600d031602d58500004104c5140d11403111449036002050582404203aa0810200d01d44100c80790f00130400781da1141100503c40304841d0030001d51170300503228440c00d04081c00303400d14620b45210201030400101004030f0700c441daa920307040e0801d18002002c075510f010100024442c5009030910a000e024100031000280711a2580180e21031005003001e0707240c0c01c0d400001d0fa9016078400d039154015031000c204c002aa0070148107004500c20011441c1c007015210300d070401c201c40184d22054003500c0b60352141d40341402817450103008100d88600024600d13441d15080c03c00d4005102042c0000040820b101d1a81040711b180c1d89084030011171380502d00781104141c0400d10305081e501280c8600080f40f524010b2207 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 693797535 1250 693796285 693796289
    0x415020a02060f0a0908030c0a1a01031a0c0708040303031b0c050c010f0311040611150912090d0203060c041802090303030f0c0408010606081b0a0c0213020c031c15 72
    0x3044607062110083e2881c01a6018002040911915010001b03181c002070019100e840182c0b4090100b004541c20414400e15106800c441d076500d4040040c800614100c0210300c1c3c6208075070801c0d45a54a135843c20b034440c800e001e400740c05440c02203000001c0590680141c81100c04a0044485601b4007800945000464001c010260b400c640c3d8401c0c1554070521240e981c01607985800b2403c044280c250070700540c010342010000400c1d0120007070f44c4480c10484800405203410a80356903103440294680c54181090350070390900d030001451404c0b60760340b10b401c0d0300b100c0d0028180c0e1602c0c10b00d804010226842442421201c22114840f400040602e200f0b031421410041c004d50314540e90383c0b40c110f0090400504181502000744008a01c0a40911501010f40b082e91110540e03420518065000c03107110480c80180c0101c104405d050b101e0b2700072114003204d80d0503031341034003a0102080900064021843c0210080c071010918414640b02610707070100c400162901013081c050b80b55500007040c503040c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 693798785 1250 693797535 693797539
    0x40b030a020618040f092f01080c0702031c030b10080415180305041e1d1017010b120a1a040501090204050702010504032a03051c0c050415020a02 64
    0x11048003405030814400a02504110301880c1028980400000d0304a400c04c0c20000b240641d038249070010407000402c4007000c005510440110305814002080a0400109500d41001181c0e008600c1c04400d103001d40f85403d07801010f40710701c1d4140c0361a14001080d002109800a410a42d170b0110301d00303100c0440002819159505089940e45071540c4007080800c1c1400d10001d550b0700c410340031801c0892086890700f80300e40d6485036210700d0006600c104650700b4031800c9002004160070040c40741b00c505601100c02c108140c03024269217245148505803001d60020355990103000c000503400c0c8040d4010728485004a0b0b12845007150345520a07a02c044070726006140310301000020030400d107a00d8519500c28824400402c403100d8a44c049011340c0c03410354640b00940c1d168824401003581282d140d448042581c00181100206000000040715000f84044e040c00700008030b01c64611001c43d42500d0b202c55002c030502103042d04040080c8a54050720808290048000d10340400501c081494580e01da00 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 693800035 1250 693798785 693798793
    0x7090b09060d020c0f0a120e061602010c02120f01060f0e040b0609040c091803200c0f03010905010617120406120e030903062502011803030b01020a0c091a040b03 71
    0x220700b203000030340c09a003602d0428070904114045c0c03020b08003d542d10144c4030b41c890800101d0105030181901d01c1d80d0700514468401403004072004007480003034004c083e40910305503034658130500200e091011140c1c20034101e0301960464124400c3d054011508840c00141c4102c0e4640d1303900c0c200103002c00b0695000700260981c1e0041602460a800e032280c005000f40c03207000c0784e03d03903070389054003150007400d003145071420f0240c0c0c8007084c1500704c0040508500e40724202044080d040e040541c90b000c04a41c034a100c1c45130007085030700e65102544084d0b00c2c594840001c005207a1500b003941c0c007011081d003c880c424485d860201c00050710890589040718011b0700c8003c012130004104101400f0081203003134540c0300600141000b9901000014003c0c00c0103034541c208050740000c00306c108500f00144c8401e6a0400420300c00c0006a202c100c0b150782d42600d000100c05070003000417401c00b03000c04805440300e46850004503407420140d02121900f00f04601001d03200303000d00140701c1640e6904070283c0d07060704 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 693801285 1250 693800035 693800047
    0x1d0f06010303110304080a05070f120b0f070302090d0b0a0b010914060a14030a050610111b0406080a030e010f03060b031311060c011a010804150c0909050f07090b0906 73
    0x102a030443d070072514150080d0390a1541315075029261049004040c3c4240c1e00c0041c08100440c29500c502024002101144030301e101c1d5034441140c0351801504001ca121180400035016a10a6054502d13100e0020101c2d1103040c518244810804070640c1c21603a40c0c1c0c6408500c501030341c0140340490845034129000e006920120080101079080100e50009101209401702035a8490000271840784600c0000000e15040c030310203100f5018210302d10b11003480b160a010000d03050001034030200b40e855501000305a0b940700000300700500742d181e210005030b2092001803c02c01da000008000080317402c1e03889000c0454001c10403025940316200d10040d10404001084134510428078031180180116440c46c1645002404036030194828070419800b40d40d40c00b102800110601010800300e442483c1c07c011a083c032341c48501e16508c503450299146944d480c0840c210034002c1d051040142000c80f0104014642241c00110b940c80440b92180020a040000304d8600c1c03248081e510042c201802c51070802c1 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 693802535 1250 693801285 693801287
    0xd020c0a090510180f141509090c121507020d030b0a03020a0e091c0903022706060c0c19050405060108010605030c090d0c080a0506090d020d0e0402070c091d0f06010303 74
    0xd1130807500700300502e48452207210b1400040c069245800c0807085021514039002080d01c0c104880305d10203901c240c01140030310401030000905002c40c4103080b00e0642e0800f0f11003152a19008820300001e25803d00d4100b000405034011a0080d504200c54034217101c00042d07901080041142e901009501c083c04202c1072200b00b4600c0042ca500a481000700c5802206084448440842002d00080001d03084503044c02141410341c10302e5117481410030940c0b004a5007200310b5840d45401086a0b0140b1004540b80aa118081001d4085c001c4007820a03000b40c1c2800030603801c41c039604d004040c025810702c00425141d500c40d464044c100c400030f50741c1c9815900d40d4503490a076a030000d0807070340d805100c03035101c42c01241c440104403009201840c02040c0360760701484d10508090008004801603007221b038002070120340105040320088a946024401c9452100000f002401403500c00390200014000110f1294500e03400044400c4410800b6206070541049140e174030303045c844d11151281c1104004100203 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 693803785 1250 693802535 693802559
    0x6070908210d1d070513090f260c010f060e04020d0611040905010b250312050c040e1602010b0604141203040e0c0403020901050f0d0b10080d020c0a090510 68
    0xa12244880032a004030f441c6044440b0b980c002c0c004a07402e800c000820401840e0a0000d0308100031054801c4c4800926910f81c200160140000a00342d29134421200115004120340e000036800d94101c0f0940740c000d4010018024401e007582d0101141c6088400302d60130007040c0c010782c49994000c0c07045500c140e03507640742400340854004c0780c503240030203201c0031444600300e005e0b0074047e20442d0400c030340b54501110b0134802c0150108000d902c11090040120200e0341c428104170662280309000b051075100c0d85000a5244036030303481100030b110b4020901013a1010070219244102d9680e00a0182084000130400c25100b1840390003034002c0281c81041362414101d10300354034101000c0940b41019a01d01c1c044800040442c1e003580c643c0d034000f805004514100c0c02182c0501000c1d203450404008400102c0c0b4001481c40c4080c0c200e01007500007070003c040350b009901c00391034408140c0b240300040140c00307541c0d040440c025900c030705480c000c003141620700340c45060b21500ea5001c2ea07a40181c5011600c01d00 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 693805035 1250 693803785 693803797
    0xa1a0408031b0f04080a110f0a03030503131202030a080a05062206030602030c0c1005040305070b0a0902031f06080a021026041103010f090206220f03050607090821 72
    0x495000f880381c001e100100c01c014100501ea5203019103403021032031030a140150445000544100c1c82030032090390366140c20f80b09005486d8035082c05030ba60385032405c00810007221901c1c014051300051004200899020016002c2d178016515540c000b0f0b2180c000600c203907141240c0d802d4011003170342c071108012868011541c44640e1003640000d0080d407070b80c03900c00580c2d1003114241c132160800a104504044100104200e000b00c10008214504066400038614814141e010340311020500200d404880a80d004001c5a5401000c44030441812030f4807422440c480e10064030301d0f0380740c0a03000417000e6002c80d541c20358650050100c03140c814094425a0102c11000c20313510641196a80004140d051007e01405039000d01010b0041107614002c142c00c0d44c01c11461103824505200c18100182c548000383c852062002d0381d040c00754100e1409410f840d0010398410900c0081c5408004144000070601a00070300440da07400f0398807521003210b15623825032070402d0034482003a440d07400000c02c2d0750700107084 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 693806285 1250 693805035 693805081
    0x1c06020408060907050a080a32010f0e0d0806060904020703023c030a0915170c071b0312030213031401050108010c0306080606040507021507020a1a040803 68
    0x2040584079242149000811514200d6a034071400091000b80780803420b0800901c100f00042840d80940e0342d40d0001d14201030030700300c4a0407101801c0208100b021391800b821000e400000c201f90a055464600035069041c50f4800318010950b00741019071090740020712172400500070328544004101400b00940c40400258118080c041d0181c3c041c41c00001c40c0f403640b099100c070004291514403c00c0080c200f045a03104244c0d4020408101045d41081d020301c111a00414400c000030700d046401d46001c022141c4a0451349043d208200c4081c0b40e2001a0000354058100c120301198200170148045450b404081d042d064101c1d42c01140718883c3e0010a482d59107406e004840741da0325900c58000010400d403c05040c0d450f4001400140030901c1225184101071400740403491410041513113802014203c40d0245882c0d0307000850540c0208401c40240c114032802e070b8441d28010340025200c44081c0700031a40e000e000a0b1840c8491014102140220780043c1c000340b07140c0350743d0900003659001d940096 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 693807535 1250 693806285 693806287
    0x130f1d1c0512090313060302040e1b04120b0103060c0c02150705070f12060509070501051e09090f090609120901081003020405071d0604120201080417070f201c0602 72
    0x821000280018140550b04250043d9120a88030b08039071218045e0b03400c2941054030620003040080d003564600c0d600401842c040901100c00044a000b6501c210f411808102c81d003c1c03260f00800041c4500b641c1264029502044034810505080b1909010080040c0d40604923024400310980039030014200141309504490740542c4e1100c5600c05c800680d031000b9002041040301e00280700c41e0f8002c00341d0280000010b0030b07840b170030480081e0075801403482845800f80070074a07400707020103148100c0d414034000501c640303a0b41ca0003030b000000d0110700b2546009580940707004500004030000b5143c6040300d5003c021810410300000454040200800002502d40c20200010158440e44600e501076070003580e40d000a4800a101c9640c640b424415940c007446c800c000c10004140c3d94600024200e81c2403900818607161410524403400402c0d44204504400180204c00c10016880410350507115100328540b030420015200c05000c00b02c200c40e0381020741001c201c40782260180c004130400344903103001 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 693808785 1250 693807535 693807547
    0x31401020c1519050403031407091a0f12091f0209060702060f073809060a0209030a2a050603271e060106022512060b130f1d1c05 57
    0x2d0016130b442900e060b404260f403860004243d540c00c598a59100000d8102103141c5c5142c40e07580c03101030800401e03003141854041000c2003289000c40c1200c0510f841c40d071040c141400c02c100101c2d100c4240b107403030b914011100d0815144041785030080e06d40030100101040c1c00d05665030244580d6034003041c1091442d220801140c400610640c40030602800310440e400201000100181040640408110040e078111420070441c4100003a149910096945016031940b036031401080c60640e1030a401040b1160500f10400380c0903259a98540302200044890b03007499844080c4816403005850006144010583c00340208080c54555811891144221280009600c850300304015100b1585501c40c0c00c054010860542d04001040c09203021808801c180b180e08507240b002904144100c00c0241f0550301c80307100340321040d0f1184140e02006086c45031041042d8100a00400004044403030651500340001900c0510101d5030f20702c2c1180b00001d0811452030b5031005a106c0e03000e07940304204501040f10f = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 693810035 1250 693808785 693808831
    0x90d020415030605060a1a0a03060e0103060c1202161704120c03020405060103021606240608090d051809040206130602060429040f020d1704031401020c15 68
    0xc1da0040010900311054414190f260035000e841d0054061442140001014010b1306070b090900c01001054201c02c5540d031240c000b0550240c241c55100070401d00010f00008103003c21034110f0300100115681e084008040d00d00d01c1001c07030144600c00e4244a0300e03089641e000071030740200031035104414100c16050955801440d68403420030402214022100103041007141843c0c002d03650005003d080c1942071103108400f2584085141034040e141c59140d409121440e0741c82c220244032440341084140c821600c80002030107405096480d840c07148584c04220b0030240c850720999180480b0148403180c0e4203981010080341003805007082c0d82c0701204100c04003256112010348802040c0e50340160810303160904001c008034000c510400006003007400c807a00410baa59696603803040c0c0c4094829040034039800420345840c1d0955008007600200003840404070361140c041c0044a00c03030107000020010100c842d40c2070b801503030354003541c5a1181e108945005a80d00c400c0ea03000b044480500c407103600d4486 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 693811285 1250 693810035 693810041
    0x8070512040909030305012c07030b09070c1407180f061706010f060c0203060402150c0129030a20011403070302180306040507170102070f051c080c0708090d0204 71
    0x4420b55102c0c0e0b95003058030801d074060041c1801442100324042c01d41800065003e12042e50b890b000200101c410300242405000e64441e4107080005444003e140c500840b014040304030068059458003001003071010100c600003034030f2043d51050104161031080b44e00200014101c4a4000c402060300c0e0300380856010840c2c0c102d501585008001802d065141c4181e40d030a4486540280c0c040100f002c200402680f00040d03c02d8201c0e9041e100002e1200451052001501030003410f00e06a50802d00c1403a074140f0396092500c0749200b040e00d800e4440315420f041507541c00460070f00074101080d003113031041c5e84284039110020303600341810208100001040e50b03500580c0215500008683c0c04942ca640b800340b81c10200802d910194014600b0b4282501c81d03940e01e40d001c2c0300ba20540e030596015901500b0b800c1d01541c855a40c8480100030203805071500c5030321038402ca0350500c0742403e00700d0181c001c1c61150156501600ca074581c01880c007402900c0d044c449521007409542c0003a0780c200220011b0300d8900c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 693812535 1250 693811285 693811289
    0xf02010e03013201050306130b07051c0b011d0109090b03070b030117010b010504121b0803070f02031009020d122f0c060f0f090a0305030f0d05100605070807051204 72
    0x3a030301107800e14070f540c00e90740081a00194041d9009008000b2514843c2e900d1000f0707160001001851940c170b0100071250b0b440350040340340034507a4003a8120011080c2d03800450340104242c031841e1301041180190342410b45540c41e0320b0f00040a24004022a0145a101c10303070004010701500c400d80d44507075408040381d0081c0c1c40715500309000290010004400c0c07040800d442c109203001450145406503c408010310002e01821142c1c0081036500071030fa95010310f40081c0000001da941314201030400300a64072160005a000e401101086103464102e88140300005500410890007810302d40c03102a001c640e240d1000e0240007400b460760000c0d500d441040f00c1c940300f084088800a0300105021401d20818000c068001c030740900c4a0100141e03d101502c0c41a080c0106140c0c42d0180794000940207180c0b07074409030030b5000028003850840d0590006080d040d0070350300203100310b0315132440085443c1810700c00c907030006805002c0c80c00010604002011914007510880304165404411040603500a03 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 693813785 1250 693812535 693812591
    0x12010204031a090106050108370c0306091a0330070b090d1404050402090102031201030813081207121205010e0709060203120a09021f090317070f02010e0301 69
    0x702c4100f0454903c00d0103808050034003840d0044031810400240b1404450401c401e072003102541d641d40e402c00c0384030807105250356150728042c05610400c0001400614160040030602c504041003148441c4010180d01d180b810050f008103003c144800601c5103c041e861003500c0c1d40341c04c5140c4110000d007800041c00301c0e1800760500c8201418035440c011714104240c00864207100d00890715103d980451400e8130110b40c070584015946481c6400100d0541c42800c05d802819214040040140302c4034401500130302c0840c64030200d6007600c1d00449955840041000405240d04001940020b49103210801d014181e509000d50300245400720305081d030700244c029442640c06071040100e0150300c42201d100401840c001385203081c401c545150f200c01e030000c01d0200304984440d00c01046403034030006110100c24010002c44509903044005000000c4d501c82551201c0300085184000c3e08140d003100e06a95000310302043c42d01c0d840e4010b4400340c401c1c1c0d13200740e899503039080988e04816010601c0c00b01c006070 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 693815035 1250 693813785 693813833
    0x50a2606040e0a030e0f030703050a201e04110d020307020a0201350403022b030c0806030307060e1f0b120c09011703090402040803070c06031a1201020403 68
    0x100d06000444900d0a241d2145030b0000f01c428002c01e4009009009501c8180d48803900300c0c541d60003003032900d04e05a10091851003050b11950500c8404003004004000b1202d407126010300c44d03030401c10717250b540c11408801440006242c0d8150300d8903500050602038010281e40c20001c80304050340481c0c104540340d001507005204c2020856900050740011035900100c1546031112150f4822140d0f0702c04413031249038100000204042c94003c2042d105030340c150403499104420030083e0428103000f400d40701b42c0401d0400840d000f810340104003003441303000064015402c0440d1525420090611301c1c884000314020881041100068045074143e90506004007041c0d84c5c0400061043c3e086d00075005036850340044030314583d541c0e1001480307411201d8200c85004e2030005252251f042d44160348056600030300c001400a95008084050821540240c0b0860300659440790260b090303c15904004455050703400f1031010924010002480e0791920600041c00c0549940e05da44802c0e1445070b8514550301 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 693816285 1250 693815035 693815041
    0xd030201020d110313060b040b03010c0c031220090d0c12170f03040201050f09040c0806012d2607030225050316060b0d0602030108070b0403080901050a26 68
    0x107460040d00d2984240c10340f0f5528500e01119903c0e6440c02100780104260344410940041d80d49a0b0003580c0740c04401030081060616141d400f03400c00e0403134202280400d641800f90414166a071284410340c441d40100c28000041e00710405541c0c1e804004d086074000900030341a40460000341503907018000802c440035551401c0e003420021004900d0150401a404101180c80480f01c0011349420179420f090980e103030303424440301860714000c1005040d041841c01403c07002850703110000c40e008203000e03202c000d0500c0c5070240040c03844c6043d4982030581000c000100c5072240c070901100030803072080d10601c0d00f12804804070507810001039900400007500410006180c19580700740c0d503400d001e030350088001d07400140c5c3c034203443c0e0140d07140c011014528407004400b80502ca030440d603040c000003031142c9422006450000b000350003e00078000305202d22000420742106d2441281c0c150303500301810341d04201d41300004540c0340e440304a4400070050441c00782d205a41c1d034008486062040f41186580e10301d = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 693817535 1250 693816285 693816307
    0x606090e1006030c05190b0c0a110405090d0f020a0b0a090302070501110d050304300f2102130e04030f0314061c050f0d05180303030603100c0309020d03020102 70
    0x51901d801c0c80d12440c42c094007040022000e005240469405031036001000e5444c10b15550180f200358400500300364006100401c800d0f011506c0c01c13055108031101e0103e034083c103040c002200c2e000c80e40d0b0300315640042450544107016802c482d0b140d00662045600e24103013603031403206407001550b09001498844081c40201501481108090f081c21b1030019403540d003401e0390f1030340c501980c1320881c28004000301082c1480034808201142007070790305482c003204041409050504044110020015420942892149100e185045920051202d600e9101e0040b020386100a512035100031103140b0307a40b180025000d580c0b41c0410311507070103a1903038100303082c0d02c8002038181c034040030360008051800f8003004130b5640d031204140f030340c030b00c441c1c0081d10f1341000b5260603840d14440d19500000c03071103208110007030319038003070010030394404a08002c9940d40c01240601d40d41b400142c4007140d140d04150030040a0642d15400480d0b6001340e8580411401c0d102c1e00820a1000880c4003a00180d40010b0380c4074901e = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 693818785 1250 693817535 693817543
    0x40509010b28060c1e020f04050915090606010c03110c030a0f06230103060c030b0603100503010b0306010308221a0408010507080106020c01030b040609050c2d1b0a0606090e 76
    0x14440d909199007540c031a45c3e100b541e210801d500c41640d0001c00e000d03050541d16420307a40400040f0180082080f4101401d1540c0d9680c04107559003815603140d00042c50807080442d400c0d01a08040c0c458040c2c0d0100c664060301c0c1c0740281100d82d8000e1044184032241035404012088841f8022451b4600c0c0c1081420300e401030f61402a034030f0000415a41116001210080803141142c1e00000c00040758607002108801a219800096911000200a0142d01c211002c902e01c1101d6048000b00810144281856110182480041d020040070700c00c0310180c103022031006e44d640c1644000e4003d101e0b00c40e00c540d1050707082026030a4628001107018880c803503091294a801c0400e900384a0620743c03404100030740d20081c2030401410580c54250420050700e0756009500074200241e4244100d2421040c285441c1d01700800c100c1d0340c10303480701c10458058007104580070444040c1e0b511070b1524407041c002000403103119401d031409202d410121008148144552001b4142e4014042495540e8140e1907141c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 693820035 1250 693818785 693818789
    0x14040b0a2607080d0f021e0303060103060905061c05030f04120b093423040c0f090902070c03021201060801050603030c03120709080a0b07021504020f040509010b28 72
    0x146912048041c00070f0000000c100906076824607292002e10384980049050258043e602c011101d01154510510080800590322480c421b03038017003110329550403511013a00c009650750f0f500140040c0310f440b4141c0c10500400700c0c940c0507074126450248000607038082d50307006034810ba1340700f4070340d0000c1010400030b107071041e404c00000001860108070b004500e0740409013814016002e1a90750b814072581c5003203001030380010000018020301508090000e003501c01c0c00002c10303500c220710700145a00680d01401e00701a510f915039071258032840c20042498025408840e094440142040c0700000503961200102e00f0318903070100218203a031509240e17a0960340d01405041c445d07007051000402c80400041643c1d40f205800c9440303000e40d100c2c00c80a4031944100d1700090403c4c0109964034080c000e01075021806949182d00700d51020a49030311024045e44180c3e4002c1d0b0041043d040c02106d803030130b50003441d0081000c800005680f0400c100240706c0d070804480d1000c1d103240341c0201080d011440c1d0031040c0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 693821285 1250 693820035 693820109
    0x5271305040614010b0901033303060c020d02030d0c020a080a030e0d02011806090f0b090304080d030b010906051e03130c08010b011704030203130e0a05070903030914040b0a 76
    0x10f850b5043c212000061700410700c10604050b0b40c0d000340e54a080c4007104d21118110070380c3d68440d15039101401c20b4400300450000340c82040c2003000001840740300003003c0308801501e5001d181421000803e2401616094403650b0452040c002805c000c84c0e0f45e50010f0495427040e4030001000d648070030342c1c0da0502c0200002d200959150501031a403491500c2c2c5007098840c3d06c01e90000342c1015915045100c0d40c41b58401404002d1031304100b2110070f00010040c01500c03c040121b03000c560720315604070192044103106500162207218104202070081d005010031405150716040d298a80240b4200147c1048620f00200021012140240904841018084c1006a00a11401e050040040e08510401c074801c610581c040c00040d05041c824001e550580d030810b012100d80daa610965a880c0e084240c58804200d49003e02240b81c1701d00900800d02103c0c0d042c1c0b1b40304207113450540d503040c0901800d99090341040d00c500410901d03a40b4801c10001516545c039102d45605c04621904000140c00e400801c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 693822535 1250 693821285 693821321
    0x6062c2815110f0c0901050f060c0f031c0911040504080c0a05071e0b0301030b1b030c090f03190b070e04020c0102070620030c0f090301050906040210050406052713050406 75
    0x260045d220f151000d415503c06480072145e1003414401300d501c07845007012040d160f0040e44035280003035a001c0001c080c6a03000c42c4004140a00d4520b402046551a2500030040e8107a404220411f0400750080c03644036009503c002c3c01e151100d56802c1c20024030725000c0790745400944050209598555001400d9000071000015a42c1024100c41803840180405808218464000f40100c251001a101000c0c1c4101035a526030908559441c0e0503080011234510982c1c400c041200d69050009044030b501c3c0496041341e4240103e0345400b08007880103003041d8100041404681d41948540c0000e1090100c41c03000160380e0202400d003142220082280407100d48908480402c0e01406001500c0c2c008244040c2a540c44820400307200961207480d0541d601542041d0410022200211351144914020b0300e035424004c4e00074400b2034080c4518040c000110b2010304c1046180178401f880c0400e10606000030410f0340b03010000281c2c0403413864207105184d40d122800c101c00c2120354012122043c1c034000742c070 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 693823785 1250 693822535 693822553
    0xc091109060d110c0a14120322110a170609030a0c03081909050d020d0315060809071a03220c06030b1306062c2815110f 53
    0x80c01a20554108149054070b070b010070f20300c0d011007408a0350b0300b81441e000c03901c04211501d0a210f8500710310302c071039880e8020922503868112450003160f224551404c1c0341804221060524050480d20400903a03a10b5076426500e95281c45450400c0c2c06010300b458040d84205c6030303000c994503280e402002002c480d082488458056030b00300d00c00c140701c60b071701d400c28410aa4401582061031141c000c0c0400900d818418003d007031140200342d8100c0244550300741e4440006203038068090302c20890080c0c406d0a090007040001c170741b150101b07e40120811080d910708903030318101c40648020340409000b54841c00030511a111101404c2c1a030720079003010031171207108040d4a548036004947d1086506045c0c5403d000001580c0e0358900f401589813240d0f0800220340c446100a104c041c00e000104503c02141013684180d40b00582041c0820701c00410b002c0700002c0120040c0310f00003000a0406c0303100103141001c030303011907190641803041d2403a581e800c00300001e01c2c00152030305400d40c0c029195500700c045c0b0 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 693825035 1250 693823785 693823789
    0x5031e010b0d051003020f100e0904121d091314100e21030411030a05120d0c03140a090201020f0d1d1002070605090f0d061401150801060323040c091109 67
    0x80210b41d176082380c43d030a22855030300040e28048050b41059500a000c04104820401546100d490298036a0307600ba6032000e040039030300480c10440a80c0355001000900059100f60441170595041d482412400d2202014050280c074103d040f04240308400d4486840c0780c00a0004c111314001e0300302c0c4501e170306400c02c420480140588400751024251030390350034096a054504102c03001200d80c0c0442140c826608102d60020310741c00c0040d84481c014100000000700300d129000e01c1001c0074810810310142d8a4566206005010318907080781580603180f0070340b025031070900c6030750401045902c0e200b0508000340d072624941c1c0c500030074243c8100200300300103c103142d0001780f4400352030890800d903944031040030020340d4250720b240e82154070103d1118440c081010a03040354910407412440c4403101d9880340c40700032803040884060310000700017400400c140b6100360400d4003140d00c0d004c08002c801038021138071206171408a0701500e40c55010002004042614410074802040c40e66002c0e090a89540c0 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 693826285 1250 693825035 693825049
    0x12030406050f100b0a2a030801320402070f20030c120309040b01051e04090c090815040f060501030b04050d11210409020a0f0e011e05031e010b0d05100302 68
    0x4590010042c5504050403a850001001d0025050b49010303405180d02e68600104034232000d0081c90054071401900d0a1303501c4c8070b202c44c110a090919042e5000034640c4040c44000d401c40c110580e500d015542c0940b020992a0f003240b00114903090f50140d00d40400408c0c50b00d42440000c030030340661180d02c0400e11520010054a02c04802103c01250b034400f480012a4140039002d03141100030b80c9000c8101341005448001c00460342c803180305006541d01c6010551707580c10740b4460402c0e60340151300710f04c0c01c543c0b9810542e030340203204900807000506252907079011120700b40c00444134451818140024440c04000c04140a11617140c008135070010b41c040e403034035001c0840200d124000b0140d2010740022014007540c0151001181c00c5490300301c0c6080c000d29080200040741d01140f18680d144c8503a51048843d8401d01c0d000004040c928850384400316003680c0000c0180070250800740480d4158000b10380c0c42d0340200b0500030b030b0782d440f0b840980042046070000741c4a1200301001100030001a101e400e = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 693827535 1250 693826285 693826297
    0x70201050f1c15030314040b040620071419260a0b1317030c04060509061e090f0a1a09031e100516021e12030406050f100b 54
    0x700c1d8603900c079501689800d0010010300b0200c12441d081c01d0141115410104440007140d001c0d0b503d4100303011014850102c0c9200e24010b000d0132420070401401100c0c0074140ca003030169124101540202420406c6604207001c54002e8001c00c0c4003880251001e2500840e42c1580407203881202800c1d6240c100070760f0b201c41c401d07180140014142c2010842c0305905000440155030025415440da2800070803111500c1c010070350440c3c4440b101c10301429440180e90980b0712a440c100c0c801c40c50300341000420b650175000003104a070301a01c10003600200d40d22010f640045150003107040f40d00d50200c581000540b01340e1080b02409408248404c000302c1580018580a251030400c14950340c481202c0428100079000c01c0b100c800d040c0034611342030286000101c28204d468802e00420841d140c41c046907070f958908407036440050340b0a041180402a4000c0341240c003a03481c004131507480c0c25450450703940e900111002ea8990b642e44c81007040c0e410300c1d0040c45a1003265680d40d5035000303081031941c6803207020710 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 693828785 1250 693827535 693827557
    0x515040506220b061803061e070315030f05070501030605040b01050409020a050c03040806070e0105030106020a02010f032003090709050405030706110403020919060801271109090f0d0507020105 85
    0x45107410400c06059480440f502d1400b8000030340c2c6907001d1011555411004a1140c020700c2540d000070b082052480444603140851068546652a02c580c03ca0141c9125070122070210304500c0000002981003047d80080e510501c0a82100e6262100140845e60141c1c0107a01960900c4201005a070b400804c0324181c46a07040016212240910211090702032004c208180380b100080c04100b4010025207035200310f4903541c07640341150400e001102c041c00f00b8411280503912410a40c00158000d010701d00c4205040d203400145010080010031011102522450b510000007040c05854103090016501402c0e4280082c45581440c0e038449a883c4100b080c0034203519030b5614052a5400500200c40017141c0040c0790380703000d003000008405090204c071551640c607441c02d080012000c406004544444800101c80c880c1000c45c41000c5141000801c0202c4229034808450841d40c3e03101c240b0a030003004400c0082540c04452039505280441645d9a441070290510041300141e0740030f011900e004a00c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 693830035 1250 693828785 693828829
    0x90606120a0b0604180b0a23130f150512030a050c0a050106062c1e01030f05010303090510080912070f02090106111203060303070f0f05060a0515040506 67
    0x502201c0200a12006070030a078002030001c1e00080c2c0304002914411208a040410840f8a00c0038080044080e050320071002d0760107040880120f0a8881511194501800f500702d40c1d80d5461044020100c0b907100101030441c80da030300c0c20529240c4882c10011b0240c6000e4500d810081c0b04045030543d079020341004001001350018032400e154a05010300414240c0c040000d011076511030034040c09507540096001202100c030800e030f11500c19516600040d013400034120116070300e80002040e506880e1300031058141515984814a41d0b6034a11403036000310f0080e641d0b807107054244010030080384404210b40c020000b0920511501d0b132008201c40c1160003c0382c05d50b40d540e44452804580d55405043e0184d40203803485c00000707401d40c001c400032043ca10380c1001d1f52000d901800c041050741c042625040d030554001d22089000802d6044140e0825010712245031221b80c0355541c003450120110341416105845a003441b080c0d405200228400d600115024410740c0780c01004600f10401a0f00c661440c449 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 693831285 1250 693830035 693830041
    0x140301090507020f03191209021f03200d0509240a0608010e010603031b03080105060f071e03080f0f0f0a0f0903090e0901051003120e0d1103010b09060612 68
    0x1008000c4c94010030002c1c020b07242c660201d840c0d041c9107135044c020004040780c19404c03010110f0341a8400e440e02c0760f5004280825079081c0e144500e1000d01300404050505903620501c5214503411412054000c0d1a46021070340ea900d4026601d0903070b07801625000c02d40e4800011b800d6410700b04030114881c43c0760000e0000c140d507540124800a40265881701c40c69510b0101459031007103040d0001015a4000d4488070b005030021480e28000c0c00f01420064002000000180907501d030480082c5240e0824044060402406803200c0100b003151088422200503004114000c15401c8100719a104503c010042c00501d4a8002030000e408001d008400d224580c900042a00b9020342c06020f40c45c40050040000da00300d881e020b80071014600a041a07960f01c04009120302e18140915031250100f0706d50b004009145680c0c01c500c41410140c0364090000c8020340403819141c01c1501000a8007914500d02c03407051200600d4210307000c07200018040c01c049000c0000c20f441e00011540298031764028015159 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 693832535 1250 693831285 693831287
    0xd020616061401150906050c0312090109060606090905010b070b151813020427033f050a0603021c29040b010b03160e01050904060312020706140301090507 68
    0x705841c45280e0031540c1e0b4000b064000304075a0204100000340c484441e03c40d105c00d07042c0c48078020b4240701880c46c2e01c00c1041d000500c1c50460310700e8002020000118900b13002d41c1c0c52005660340354020a0000c1d211117003c0080c55154090b0500606044164900d0329086443c1c0354215000185181e5581200d92610401c94136040015800310014048804407410b040f0b080c440c01945400f0107900c00c034140408250f05042d000d020418411b82c2d03140030002810b01e0740d003c0e1041400c106002c4441d10184c0140c4414005100e40265520101c07454103404299000c400d07412504041c0400703001c6031030b1440070b0006840d8070b840002d200d900d029540324200090302c1e10340003c000100b80700c0b090004031200e0484002007880d505004901c18000080a81c2c0c035410003082a010484030100030317900d02c2c1c400c2e04040e409480501045401890b00c98504a56080460140e0383c00340d00031142e8800105078110a2a8107002c020042c05e211704c2d00d0f0340c1590a1380d1034900c041c0018040c403012a56100d003c01d8680e = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 693833785 1250 693832535 693832541
    0x9150207030e0904033b1909021201090e0a0507050105030606040305032701110712232b0801050906010201021204081e0301081c030f0905030c0c0d02061606 69
    0xc2c0c10000c000550381e24240c41c0061500111402c2070038201014801c010495010315a8001d40000c000390a4824421000c20000c060059036900c040c120b91100d0b001c0f0749803c460005010700c481145140030306503d0908604211144100e0042d00c1d0b40000721440001903000c90400201c0c1c0c070910385680c480d141c00340083e00f1486607620060440c4400905003000c0e4054419600c043d98500703003510b030710758a55001524402e400f82030003d110340204005104652607554403a0a4900614a580c04600940010000e00201901d070341d00744e900100d000300f403104002c03c081c1c1615604800440c841504c0b0240030b0007140301030142c20320520b031280008019074801d41c15035036031100c4102c1c0c4030101d0900e41000c500542c064900701c051080d2000011804c065042d00300d90403210b000f00103007150b20b00e65200c10055007115044000b01a21a801503040303404500818007a10700540c003543e0b440004201c0d40c1d02c3c02c3e0841c0c3c0c40340d0061030644004409683c80310282c42da0085511000b454440d464640b40d401 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 693835035 1250 693833785 693833807
    0x10302180d061508150603010b01090b03070e2e031503170c010513060c080415051503060910060e040c0302061e0301090603050c0d21020304030204230a0915020703 72
    0x31048403c00c0001d5001e000250750302c51a614140300c80701c20788a0406160a0f14152051203000c5550b10404000c66800300c001194010745914218009070b503c140058401c00f0300c4546d03408805031a00c800c000740c0c036114910608420181c01d040000629030070a50390050101c0c030000c3c00c03000396007082c6196500302c00200d42c4145c0c841402080705292540030302458402d045020784501d45010700041c4180d008626090180c0c2e0801c0c1d488000103140641070b009030100500481d907416080a644206d507e0812100b406140319401a100c42d60390307840c0030012542c0c00d0b0300c18009a103c20381072201040e2140b18001c01d407034041c0c600c5075075071111440c113000300261a8507686520354004000146001035a0006050f07a01c5502650391819911082110041d2020006443d5180c425610344284a900c10784030501803440c01500d04140e503e400160880b505201c2444450344000c3c0c0c1d21001e13107442405035503c580b80c2101089030420340c0c1c0322403551510100240b40d40a6000405105241c050020090 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 693836285 1250 693835035 693835061
    0x10e190c08070602060702100911132c0d08011811041715010905040b0a0b0f090a050109110c0709200c070801230a09231b010302180d06 60
    0x1d540d81c409000b0344d1544121b400e20014016184010072401c440e02034484140e03042a480c03202a0080800c0004000380c045a0310180c030360301d03101d6810f10100c00a800041e203046520402c12078140317502450800412260b028108a040030050050804003105120452440c20700050003000000ca1384801b031146400500740034008035a42c0780d1601e400933080b20b49030030240140e074145c2d90310350200c2d081d944d00740c9000300b07010030050000300384400f11707880020b08000083c4414640044c2c2d4010900c0d2600a07101240704136101c00c01444203110a000301509181c4007000203103822652004262906810701400c02d45c41d8686010004003025032151903114002e4004103942c2e00489808103030713190801e20614586508112000154241904110010420a81c0800c056645d00c02d00070008000c295802c90704038140040280d6000c500c540711003000c0f141c0e40c5c000d140c40d6041e1380b52a10030700070030f02910341050300411100d112840b0f441c014030003040d01a90370442e250080d1071b045000c0e00400c5a414 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 693837535 1250 693836285 693836293
    0xf05070314100c0516022209031205100302030a06090f140102031f0501090905060d0f0804240519120e0705040510060503072109080912010e190c08 65
    0x980d03440460034841d00a06403a040103d200d03049810398a9000300c41d20784c4002c0d50b8144940c005424400c2144242d0007c0d14000000740200c0114941111a103401c02d0f40020740300c0075001c0305091203121791508400c0120440e103070f071450750313001954030380440c2d00c000c00060300d0708a03035000c0203800150041c2441e80214216052000b0307a141031700035082200d08142c92440794040c1c042c0e00200100c001d0a40780103959030007800b0300304468007000e418054050346c1c00414110700003000c501c041d0401079105d84600c12442d40c4500c0c10b90381c0c40340381e142820844121003441c07241c04840c0750000225540852488003400e441a1442003e6a140d10705052142e01380c1e0408554400c40c0c5008902c0c401510740807501042240c82d8075041c082d00342e01900507400490010030200b8801402202d08002040448800c840c1c482d200e96504000c0c2c1d40f0002c07040380c40e010086803190b0586000344121200c502c0c00002046841c0801d0b5149030765201356200141c0b080c0050105500384000380c4103010160500c14129 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 693838785 1250 693837535 693837563
    0xf03230d08071d03030426030c0c12070b1602220f0c02060408030a050c16030302031e3d0806100510021c0e040c0c020112180f050703 59
    0x942040340032030b99000028801c40c1200c8100c2c0d0500705120703418001400071070410f800c044a00303c8400101c90308000c05c43d51040144102d15082004041c15510031010f0441c144d070b0042445903850305614400b105070010003061050301d510394246d40c1d92450343c1055840940030360000c102c810300d80c031181d111503510400c0c005d9076502c5550001401e20000b41010050070030f4104040741c0307500742500c0003000010108003085100318103400a507040408601001d290011100c03a650b0071403039110084002c00d0300030040081d400d011b60441d00e0b40d2165400720f0b4003070745046040991403102038a000303071540002d02046c0d154120310f041c2200381403035400c1d28a100c041d200ca1080e40e4501e0200d808017070001201c41c0200d580c3c140101d21072014102074008000ac102d54007503038007544251059000401030844000000e90351076001d8600c250925032111084046680001001d80c03070b403160801e60290804011038400c5101d590385c4a400380d00003103140013200ca50700e40b60381000c4182e8230180c92150ba980304 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 693840035 1250 693838785 693838787
    0x50a050115050406021b0a0e070305040b0a0618090314120405010c02010b010f08150409080307081621020403170301060e0f0906010c0f24150f03230d 66
    0x4024103031000000440d10080d07221004030b64a00c958000c0e68016045454080900301d42c050340400380500040142000e191100c3d64514260000c40d00700001a880b441407205001460380110341003050501300340055030a01c0d03590b444100065110f2a8002d030380304052028140724483c0c0c0d44030074264001555952440204100170010103590035941546000e6400c0e40710307401482000000d80c8103071035075001c80500e02801d0711007201c000c0050307a0703e050144070080725681c1c510461800ea40f042200d10b4a906044400404090000b0704032900346d140c40d0300c07071420103030845400309400000c030030b408902c90264221403020380156030000b4105001c142031101f06508030000743d4140c0310f45030b80c0c0711440c2d0302d43e500704034101c0c1c03003e01410341008641f800b249180d4400d036589107510313010341000d0843c4d518a555100d845260b02008007150401d076004400020298080c2d0007a002c0140a42041d2600700a2034560b4904180b100600464811068820b01c202550028140b00102c3c0240c1e03c003102c4043c0 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 693841285 1250 693840035 693840041
    0x150306090f0105130f0206031305030708030718061d060c01060801021c060b0708090418140706030204030b0708070c050706170a090b011707091a210a170706050a 71
    0x2060341d64550a000000b4558800d0700240e0b81c0c0c9030b0300a40030705200805a0248400c5601c0a8010450b03030581400180226001b00020300c00284620301c0280d40b0b00d08418000d01c0c203820000c2d10454048113440c200b01840e0b000f0146030094120300c0141c140300b000000020700da441001c241c011554203020300000e100b1410350280400f001c6024040c3d1b42c40440d44038170800c441032030040b0f242c004401e205001c08181e548018060b003c40180c00059880e030b03200480c4d10290040765040780d0b25a8280d28a40d64000240300b15802810b1a0600f54101421643c80e071550384c1c001400749003046442c0c000250110310855240307800030303009001d40c2d01d51070325503000078505080c905290701d034210f512002c203142c108180306a00d04e20350130410304c900907401c041004200d107415255040e403a1041031408564031039948500741c50404041320003484501800c091298502c0601d0b01003040d00218402c8182c601e20110f4907500d583ea015890042c040c2c0c41d158283c9641c000c1c441e016000d41d29000c10410319420b154 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 693842535 1250 693841285 693841303
    0x72f0a09150510020d030513150f0e2b17091606111c270504140403080708071206060e03010e030a0e120f0307031e0206011401050315030609 62
    0x50300301040ea282c2050000f00040000f44100680c060020502070a202c1c0e401316400000322000f00c40c0410043d1101a451907071800d41c000580c0c0d41d242d207002806c040d4400c0a1fa82585040500000e80c08005031051000104580022001e40c4000400003680300701c520301401c3c05007034a80c01d21810400e05190341d52504000c00b0440020070308000c55024020f04d91034003828050802440240446441d10310040e4200c0d07042010f00a08403000c54010b0a035140c0140241c1442c0c8002200602d010304000030349a0905141d40c07420300300707130034840402d41c04045242c0c003d0880c14540030944a948040f02c0070002160302c51071441c40c1034008a8020303448084695000c03003c5001744141001042c4c600e413a80f007002d9407507010918901400d50282024003020a02810002c2982c6601d1b14800c0040d066070303c085030480c0080c4a008006010350b41c3c401310b4000f4940540700506041d07043c080061103205020a070b1034184540400020402e100f01e4044d01e0541c0c202409231009030801054040ea01c2c9408 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 693843785 1250 693842535 693842561
    0x604050606220b0102120c0d02070b030c042102060301060e030d02060708160302040905100609080a020f041a030d0203030702150c0703031e060b1e072f0a09 69
    0x80d001041c440d28054561045003000c40d000e042103001e0600c4084001c10501c04803034194011802c80401c55500c84014200100403480030340941034510100a00f0550940c01406000030103009005600076020103540541e1031040b000d017070030100c04240380081c249040e002517114600100210b111540304400041100c0b055044604905180805985030b0300111041030000e00c400300040c40c0200c40c03000f07601101a141c04c00600e4562a5001001550b2080b20604200601c2c41c004000c00ca0340410480014440d107801307080070500c0c642c0042c0402e6490003040703200d01e0f100c000500000c140c0c8903851150560081c01c07141c04142c1090040c0d00c0e80c1044410202501440d8031030588156641074007403090f01c100a03298640f181c6c50f036080e00201140340861442c0352042a03080f60160301807003180081c1019441b15601d980c002407a0030003580052900c18146034051152100142d0052260342401b4043c5144984100c1407807a01d00f007269055031b66540c0b040c600c00c00018046010307406003000c0054 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 693845035 1250 693843785 693843793
    0xb0903030d0e01020706050f06010e09420a0b040909020109080a0506040b0a0c0c08031e01080f0c0406031a0a021c020c07090c12020c0715110d091d061203070302060405 74
    0x1201107c423070458044501c18042120030001000e11300c1c0c00d9070f000340e01820f03100460000002c2d11aa40d8040384440d01d040a9500348100d9464640c291310088244c1c5c010308840381003003141001108051405940b196045654680d5240002c40e8000c880c0700001d40392038011542058002e00b0003540c1c6103401d98041c0d80070f02a150100e6444200780c011540554503646030013070304960b40c3c0c0d00c43c06035130700c010700c034540104050940d00c0c1c400341550103290090034180001d1440030650700c500c904004044100c2842540b91480c100001100c1810380c81d00c821080408050b950b8640103494081c2c40f94035507107030800303900048a043c14001a0b002e05440b405d040104c031820ba03150280003048030050001032001c241c6010300c444540580703400801c146c0400f04180c6080594070526070095400110304440840d2248101503000c6600304070007210700c0400e1a00810340b91801d000f89a13000e100c4445d6880c441300010019403240c40d800245401c060136842202d54840c00307414000d49440094404a0313140c05 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 693846285 1250 693845035 693845041
    0x5060108010b2d19090e0a0204180c0306150215011d0c1c15060201050702070b030106050c0a1a01030b18030d050901090c030308010602010f020c070b0903030d0e0102070605 76
    0x1184080c0e414003109200c01002000c0649100a003d11420111040020080004031419800c124200746080307241d80350510542d01702691040c440e44d0003480d43c0c0000307105000c2009420003030001d841801c2020344000a4001c0c0500e012009070080da0004441c00c1d10b115405510682e000a69803447d03902c4401000882e40c0341d01c2454030605101d02402c0d29258113030041740300100904000c0050300c00c80180222100440c4110ac0155000d190900700c800704000c004002194081c02a141d0005592010702a558200200c0e08050701040c0030b24001c0050124001e46c01c0701d42002950305180d0000f855001e21a4640000f88c800e0380240011199201d400010501c480c88560b440480025114055410610300c1000c120040c1001040c86010b90b4036900c4110110350070180b080d001e503000f5070703800c0310715818410701900b513a076070101c2590f446204006080c24441c01184007420b03110440000c580c0c8902e07840000e891409201c000340c1819103080307001d400307801d015402499014416103051060369 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 693847535 1250 693846285 693846299
    0x5010909092604080601030c05100e030715052b180804060c06180b091b060d1a120706140403021c050f0f10060b09180a0b0d05010506010801 62
    0xe215200c0107200d01e26022102d41480c030584540300012248075121800c1c036588021507868000283e100b60344180b140b240500003400c18080c5081c25590600349150912a001e01090750303400c00e8410ba840f420408100d58550134440e0b4121840700010414542030741d0070140000c200d205500040501041c82d0403401121554001c9000d15440d0b000300c0344a081c1031600b001074680d01a5010101c4000c1d5541400110300303000c034600400c419005a2604c5145d10340124403d04c2c04003881200d8820308196a5219403035501c00d000c880c0709070b041503c0842c070b00c024000764407648200341400310b03809076100115901905001500300e04070750556951000c220030340c000c40c080700d2249020294000210241108041401c0303003502c082e19204a08645e90025000e01880c20103400c00c80314030746c03500002855981800b46000300d01c05401c0d1051050f251503000b0000810100319008000b444403100310004102e000c02e03074000101e600780913211142c40c0e5481d185c518000c09003100e171301e07000c034812000100b040 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 693848785 1250 693847535 693847541
    0xe0c03031b07060f0909020d14070e01080f090d0c050a121215050a0311010e0402040f05030606030d0e1c02090103080301031a0103050d03020f0f0d060503240a231005010909 76
    0x14010315114185c0050400c0e071400080e6200b8040006050303100e40031900c20b440f00341c60592042d1030581d1b4403010940a076000514003880a800c01c001c0e114034005002c0c1c2c280c004200f10a90400c02c0c2452600076549262144c103000c4044005401e007032442c40a0308540d074014140c081000c80b008420440300b400c501e00040b00503034038068076070402c0200e54240001143c0c2e482011030b80205040c80d4040444803c0004c0c1039a01a0b0040340d254900b01000300400e0804100c400c1e000441103002e84103050800c1d1004024104000c80ca1384181c90b80200041101c55855503c08444c0d0041c1030350000e0f40e145d04001e50944e00070f2008540c42101104079800325102282568140c0e0f82c03002c06480318101c0c44100300c010390402d8407025400001001171040da0440c5100074540c118240001060b6036103040105424624102c64549402c040d000781005041c01c161030450b4000070140c4001a4644030b0321245410f0b640c200c0314080c13401034003401e00096010122412041742c00981c0c51071210790300c4800e06015 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 693850035 1250 693848785 693848807
    0x8040b190c050d052d0d0b01031802010302072102060f0601020a0c0303120b0616021206041a180a0606051509061c020c100c02060c0316030e0c03031b0706 68
    0x24a400402c0304410f0203120700010107000b1788600710b00c40c652040202c1464801110441c44031003100c0010480e62007001809544004003090030f0810003c0c0c98800b00c0360300d5041140001341050b5000074443d081007154001013020068a9a40c0307001f43e4500c0c00040d5581009481e0b4040004031342001039829840040c802000552006100015a15555058446e50140ca111034900e40e15a5803811494030f85401030a1031440a45483d161140640140003000c50111602c00b9507402c0082000085031032401b40c01e10642d0124490b070481c1c0e640c05030211108103458040086c81c004c094071a030a00c01a5040102034650850380313545400c00307d104900c035621459100d182c1103001488440300000a1038145422602c0c14800586040b2030010003508002e45160100c0086a03036985030100180c0c10403034940d000101e07065461860401d100c0801002c0c42d9040345104064490700104501c882c10b0102007035208001d4212925070221202006501848610420791445052000034403a03200740b000400b = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 693851285 1250 693850035 693850043
    0x409050c041d0a021b030316181e1a07020a1410030e010b0a030503031b092b150e010b040507050301210f0b0604180c05011b08040b190c 60
    0x1030540c10740c194940c00c00003002c100070f036a03082c00100c0c001c803020042c0c5000b40d6000b0b409980e0700d141c07400c40342c0ea1068001501c030082101c08505d0381c070075500181000d0242ca00b1401501290301003410000b07455103417138110171104006102c0e16112200740d20003606a140c0300301c07402c0000c507031560103884e1010420a9041d40c0190101c150002c2c941c0640c0c05185a40c1c05180003180080180c1c020500312140c6a00850712a40300102308000881c007505041c11001682e000580703805040313000101c121100d4140c1803220001d0454614441d131060304000302099109088007103401d00006030000410b03075031011143e194204016904c0601c4c3c0744c0b02e403e108000c29240c481c10342c0d007407501071081700c0d41809aa07003c00c80640210404250385104034448140314400b2320040780381c41e02c00d10094440410340e201c503441c0c100344008006041c210705041030355003e107041401c5201c00002010000f0040902134240e40b400500400c130741c581d16008000d0004907010400844842d400b044801c2151810301070 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 693852535 1250 693851285 693851309
    0x105011e050412020a03080708090306100308090907030b0409030306080c01020c09010324110304030e0303121b071401020a0e0a030c0b0a35130312090609080c030409050c04 76
    0x801120040000c1c2030200d0b0024000b45c40d181c0d141e64405000394031103103040c0c0d0005000b080c24076192404201e0703240d0000c0c40450f400c1c0311600d107a540051900400195a10038402d000028980a11030341c402010144010014800385001d0304018004001d42d0150000c0340c0904407140c0415400019414060796000d44506041c1c3c3c6035440b10004190100000b032000315a20048011980d82409401e82d0809c20610250703803418079142c0a406440b11001147c001d4000f802224070341c031030b0070060503030160980f680709100e403a04c060003600754400c00c500100809c1c1b00c15020b02c843c1030154050049101203844599802000e00c0400000f503156100c002e10302e50500009000b81c2841c2030203083d0400c1d26042031007040050031650201c004041480c4403000d02412209000000b910350100e8002d074110303c4210030b44001d901c0c000c106414102c0030258a13a1101d1910081084940c05a185d0b25088214030703032103102c40303a81d9a03280c2d031040c0b003880c1216007032101082c04408000121011551412166 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 693853785 1250 693852535 693852539
    0x1314011a040e12040f05090a1a12071d010e07050403022409061b120307092606040c0f0b190c0c03080d0b011101053610050105011e0504 60
    0x1c050b02160750b20803003500446008040e070b011044040e10207418010250a2924113050500841f100000c100c4058079040c101c6100391000c0008150034035038802d440d0028080803d03017000385043d69940c4541c24074018035030440b40301d600d4485030505071161030300390400c191101c15080b5401c0c01b07980400782d840012140707440c03040e05000c1e8500e4101058400e80e03504000d0403c1c0042c19641000740038828086060140c080a05070a01a20300c504a04503242825814a500c001300000d000d4000d030034440e1807410102d141e501380c105d012a4684c080e80c088691503d02460203100382c1251b4841c0501c02c5d40800404a164a0780780e0954240c03000d01400c43c0580c00541904481603480a4030544a80311039860200104401000910303c80c0c200d418040b07000b840c00000100401120386001005902d0001480408900e0341500004040c5a121300503000c41104449115201a003a442c4440d1140f229146009541764002c241250300c03d8861510078034440600c3c84100702d12280d094000b650130002 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 693855035 1250 693853785 693853789
    0xa1e050f0d180f021003110904020d0204091b020601080a0f03031a0a030303020c0709291302040e01060809210d060329010b070c030b040201050904051314011a 70
    0x70302082000c41074003142c00c02d10b2108030a080c810404054980790004000a02541040e01c42c0c0040c8072a180703001c01c0060104810104540100c1e02001d00c030304d800007a501c6821700250184c0700600b82c6003d0800c500e4510212102014800c044c003500580100c0d40000f5203c0008654448195040000c14465200603542103005000c2200540c5a501f4400f040340352075290000c1210145202c1d48005030b80f0158841da42d898002142e0219100c9420403840c0d0240c108903034417942e589881200c081e40d51006a40000301540d160040791b0103010710110300064900704200074a8103c4000761644061900c1e410050b030748485941c2c01d0a629800d10500701050710000c6401419452030b141c02c00075030951250381e02000b960300c0501e07415440c41d0108410040704602d0840500504c510300000340340001d580e4442000102c18840541624038a000090559014100712140c18500400c108100e262600001c244010501d00681d00e02901059840c51070741c0500c615041c604413116656002d110102c1 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 693856285 1250 693855035 693855037
    0xc060c0703210c02011107050a020904030201060b18011e200c0a06120612030c03270e04050c040c0e090406020c0102042907030f03051305120a1e050f 66
    0x302181040b24840c00d481c1c420364408200048240e8420780403c15950a4000a00b901d0f903100c1c4200c9a604104942000644001442c52a080d41030310039182c60b5455080980c0148003940c00314071007807000260041d2401c008010b000c84d040d0309032100e00424094070280c03880d260810b00d149001c0b40c04062401071000c1818100300641d0b0510301110300c002030749008a101c820348d603800440861084080e010554a00740280c0005e8820f8000d103401580700c58070000c00e80091940041c00b446209204441450110070401c001c1c001102013105141d560f4610f40700b0800001c54064509028080e210aa80c0c45d007800344582c2701655a0390740d0380c41166a4100465032030068022034038154200310309002a40b013800503000500b010030070b000380210001000c000700078540d10860384101c000c11180001070707042014030701031b5010361030005103a54440040c00c421076001c0304090082c1c800c01e80144100350500c2c00030101182030b940c40c0369a40100c00080ca032001410102d200100b002405800400440d0300 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 693857535 1250 693856285 693856297
    0xe01030821040c140a0b0f04050a080616050f07020a030b0402030c0f0f060c03220312020f030f0901111204140301180b09070905151809060c0d0e190507050102030c060c 74
    0x1004d80d174000d0342c3c0d45074940007940444616940d424010404101038035202e4940f4009011217405040e180c9400c001e42c50700d01000851450a00c103021072901241d034041c5058a504a0380501805011034136406d000d464003004490880c468496120188005c1c10021000340e10000082c055003070100c69202000030b00d0b000044c100015200a01406c07040c1030141802104141c88801006515400d5003448101504200507002c1035510208a140129000000303e0f001e07410f841e00c04984034044000100c43e10480b04442510741c1c80345945645010713810b407000340120350480440b0414192000d040c1400d0303410302142e03403c001280850b00c0010440d8144440d074030502c1c1d0780c1681c406a4940380003a04660703082c0c03005050441402032580103030034011041d8034896401d010580041c90047c0f440d554402000b402030003061800304600d100904250810074280e0154400d681c012007000c0095050024003076004d0725107210301080041c0035400803080f01d0380c1c010301c030b0050501651101507215440d4404 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 693858785 1250 693857535 693857539
    0x5090c07020406090615110318060f0307110f0f060604270308070806090402030c0d0302070b040603090611040b03010e0603070b0c010c1e02030a11070e01030821040c14 74
    0x10032103280180d60714415071014080d80c010008035203040c10380e0014041e904056003010310900300b551014648000055400c6144800d070032441b44c2c416580031038800e01454406494103c404000d0000b026000792500d1843c0703015030104e4190220350001107a41c0c0121020301980c0d03405c4500891468145a000207885070202d5041e042e140240c1b81542036a8000c1c150103900045007807044c40b140a41c800c0c003064001d40110b40040c06801c150b00000e4440c030414001510600c07241d0000000c160080c0b21060041646a60007a22559142c0024000d4841d081003241d14505c3c00c0e00c52540f45007500b0503201940c0d006100c0c21704613801d0015904400700041c1c41e29526100b034003800250158610000e105046507407001203160b0052040144c5021081e400000c1c840041018040d60350345d0005c103581d90031200b0328044080040d2300710580d061400c1900130400c0030040a0006c41031000000042c14460110079203046051a41047d8809000342650020070170b013080b050030000d01a000100c51400080 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 693860035 1250 693858785 693858787
    0x303100b0d0b03070b04151707030c0c21080906040c0b0c030405041503020f0906060d0b0402160308040c0f08070620060a050a06050423040f2a0602031305090c 70
    0x102e2000a071a20540350700414000c200080d0038402c802041d41e02c819284403d0400d5451656138050310b024502000380140c08260341d5520200c0483e115060521010390840e0401c00703c03445d00c82c24020a403441c042c051000c10550404a280c0c0c00d400500035128517023254040c80c41c203003410401d108070741c0503801c0d444083c8018400807805594900c03880e404440750080c040551841c500c18441940380708002c00b80324048520070001c036500c44d0401c4602c1c1c0010707040001141c03203c00c40058024080c84c221488600000d402c0d000030144c100d0046c500841c001c00714100d031540e0720078045442448c11b000d8018103400103102044114082d801c0d820f01c2e4000c80000c880e40079541009646040c1c802c403000d408081d2520140450303a60780d40f05500160005450900042e2196100509501800001008030717101c204006000d01c51200c2106c441207600c0b03d001c10030000109110b0154036101c4440400c0c403000c4010014120b8000821100305501d00344c02221514074002c10024040c0c0c00404c0e4010000c0 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 693861285 1250 693860035 693860051
    0x10e150c04031e0b151e0108040b1017010c1403010f060c03030e010c0207060e030304061403060f06210109060e3607090b10170c0708120906090303100b0d 68
    0x2514000038171841c0705201c058129403050040210410629012071b000c0000100184440e0740d00c83c1c0c905500c0742d00f150050344180c864410104400100b503001e50b19120440c107500320ba520042d000540c0100450703a03512043c40b1a211181e445200a1046410310081c10380100f0500307004488840e0918020304000a4803409014818259544010300e00c00580154109200aa42108042e80000401d60040d81000e00340400034160204503034101c2d20280c0080001100ca40d2107003001c802505000c1c0c1556150010b0004280d07145004175041c160a140b88800031918108520901046807181405d184040d102c07030b406030400000d4903030b24211050141e05800200c801034210220225082d000808240e0b10300800b002c103d900c15514984270340850a030300080346512080300d8007082d044200d07445658a03032101403106440742c0c0030010702c0b94002240006511104031602442110b0710784c243c6609507100b10b2610f40f80d1200f02c50f02072168440140c14080c2c2c5803a01d0282440059101000900300 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 693862535 1250 693861285 693861293
    0xc0b2a03090607062003070906140d0e0601060305060f010801050105070c030b101e08030306060d150b0c1509120c01140901061a04271508010e150c04031e 68
    0xd80f010a0540b20300e82c40340d085600d20503070594100d0750441c06078215800e41c204190010b00d003031803502c501c0040181c161002e950074602c210441340c1040340700d174040046002ea44d202da5140d80c0240319820119281900080440c180a0428098044141e540705010381c2040019101a040290280d410001c00305000c4000342c8950030460183c844401e8064070340b480d000540c10407403580d400103841c5c4810007a040080c1ca00020599030404c40c200d40403519400310700500c000a0110280303008240ca880e41000607152070803c01050124006401d4032640c24100c140d40d00079140c1900e000307229a20942000b820700c00d10358003078040d052a50001050b003560030881e040100c04183d07400035859558034000c0004080d8182414078040720701443c1c0d03040c18546031001c00040c1c0850256000704545100d103c0919400ba840208074400580c0d80c04091903e40030031074020701258114403107a1045003042400040b1380707254588110410f51000d80f8060075076990912001c10341010305980940e40403020009 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 693863785 1250 693862535 693862537
    0xc090310020306031902330d090201031d060708060f1f110604030c0210050f0d0e061506040b070201031d16050105120403030e0c04020703020a0c0b2a030906 69
    0x50040d00168903818980200741c01e00100280c40c50640ea0200a0b010051310340358140000310004201100791314070304084440303200e05c040e403d0b1082c01100156a0003221015032060316254001e0342c040115051344c068490881103882500c41d81d6a01540020703144911828880307a02071000740903051800701c3c81e40442d100c05107440c0b12034840f1280c080c1a0401c0c2da40541c00c4e058000c0d0f50401000ca5050944008d4001d4440c1c440c0a4080d89908a4010f00e00e400b0300b0032120070300d030400c0040f03a0341c2408500507030080c00040c04a0a83d4000c0c080450b011043c10841c0034500e050007001145454503004240c2d0341e03648541c81c203c0c181501d03201001700b0b440350140e0f07100c6040c15181c0a844240100901042440c0a0fa0401e9040c000140014a000c0da40e41d0155a1300c82c1d4541400280c0c140c0c0f41c126245481000b080700b582c0103000049500c201680481c20002c41442107900d00b59241d1682280b001c1c0f40902c0343c0411612000fa14050801c2528020b880e00781d20b210410b6a2519008074040740d81 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 693865035 1250 693863785 693863803
    0x3041e150915110304080a0c0201020a140a1a011406070c0510080405011808030a020705071509090b0f0612040303110424020a020108160905060a081006030c090e0c0903 74
    0x7030600510700c9441003451070241c910340e5020620f155107980f90582d581c1c415405812400d070108400c000300d00c0d046900800000741c5198209c0611450008089c602c9a610000b02c40204c2d00c20030b0070420074800b5500598018107a036081085508181d084506004481d0400c0006484a8180b0b2200054944403440401c9217013009a5490312280703481c2c14030f03a0a4400e048818803401100011000c0410721802c1070344c2e0010240c10000d41c1c0d851940c18034914203840f540207003030590298600540d83c29001030110007110032080301403025048a10402095400040500e50444000c1020541c3c44458102d129440751081c11b000a446941c3c059500c0950041d40013207010005040741d036054908412404080c5041c1480204056020b0354002081500c020309035683c0552034254556240e40105c0f8034101401001e003810b511100600320051007160240c54484680200000200d030b6107120703000f25106203c0544544915038a4440c4c14401c4180c01041c50500c1241808510380c079550502503510 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 693866285 1250 693865035 693865043
    0xa060e0f1306060e0a0e0c07150b1302091201051605030403020f0609010b0913230703060e060a060503070803030f2508150f03070b0a0c020612010e070503041e1509 72
    0x100040076041030118440b4146c11022078000c0351804c002686050000701c0b83c00301e43c0aa00c1484134070510040030040e01480102c582e1104000c055003e652002c1d03400b070800204215100c003c4031020b0354010b4200d900554188482e904940c1030b020300140508000c50708107111b44122010010001225403c228003030341c2806517651100c080765a0307071904504039a00400028018105100c591f80c1d0450513100300303414541c80c1040e898500315001ca05100d400b0007150000414410800311420329a16504111000300209240050101d8103080c0041d4241c2560442ca00071461502e5080148130b450344010207500840000880818000280a5444881d80d20750b486a40c020705000080d002c5088152844a003d403034004004060341e070300010550111f50340403021903a1103045c030504480510315043c006e50010310000700d8802509207001e46c1030403503000e2001021162036009080750144416600a007200c1760740c00141d05081041901c0c10040c912a42c200462592500f12441c251030309030700161 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 693867535 1250 693866285 693866297
    0x50309210d0801060801170307031409060d09020a0f050607030813020d080a02062d040203012a03050a020f04090b030f100e12040503032b020d0603110a060e0f130606 73
    0x4c40e558000001601400030700801021210048a2881d80e0b800f4450b001f40800c50035011948201000c142102c04424001d000742c0d985d00e60646910303002c0c1010b40d4040340074061451001403505801901c130300981d00010700303070b43c5006095141200e11020281c284640c52074105c80820060742c44c0d608941c0000d22500040303031038101c16800039040800041000108e002c5150b0400d006007070203480784c40c0c60316801c00011142d80b21800800c0c01058880060901c4030715009070b202254086201040c18007800e03940034401030341d8030000a01a030143c40c1035049500c40038031043c00008502e40006400031030250844100c00750310038029240c08403010928091650303c103010041003034140600e604003462809140d10b05450440402d40c0c0b40306100145c103030194420041d00c4806d1210010001403c2040700c15074035080840102802084c0c942300440d0400401d00d201041d038205011038000315030903511585461108541445044100c59556030307032021a1203801031102280384160400340c10290313942 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 693868785 1250 693867535 693867539
    0x8030f0f0c0102073e011112030703060e0106030b0904020f0d240c020c1e12030a0801181505040c050d051003120c050607030b06040902070b061c050309210d0801 71
    0x2907a105003149110311000c00c1802100305c070b040340101c0e000c1e80d19032003071a100740403445414a0b64200f42100001540700c8200006110920758190084016035640351207134a403999a0790700030303801c8a41d0b44055981103401d1400150261a000e0401c00c0695400f07805c02c0342400a035541e00e40d0034401c210881401d00d0b00d00004810604040c400e80c1c50100c000d00040010b0b003080000101c00c1308400308520352081ca40c44440c1805c0d10380c16000240c580f050011680c032503c02c01030140c002e1400340107500030b801c0038512402c9029594000e01142140c1c442e001d0780744500701310500000e0440c60341c070710003444000c20004d00030001c07074840c0074460030244100303540c514114a403810346440c0950148040000a20901003c0781001c00e95641011013814002031072100c010204815000d50791150355024404a0340300305000511130041d105d100b00302c401c0280201c10410300140380a0000d0060a982d105208100103818002c401e00d0204140c0d001d580d2801003140c1d2580c0c42c01c02c2123a910000500b40d1001 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 693870035 1250 693868785 693868823
    0xb0313120207080a020603061801060923010c020907090f030507080f0d1d0307030204141503030a0903110604090e0d02010b1c02091b16140708030f0f0c010207 70
    0x8000c011032001d09066441d181643d41c0c0c620032800701030f20440e40040400c20564440302d0b14405000d007000c110310300d907944034000b40642016205551100b121082102c0458480d4541c12800e40b1058543c802c4144840d005c0c0401c080c1d0040c20001880078060000c11415403211030761004501c03580040c0185800d0012080c14074260442c454140e600208a10f0788444d0000790a0414403519000c58807000f45101c002407800d0266480650007528040c0100c04041411590500c5007200700804081d0400c050b061660f07038441d002004002580303107041400021140301d050070b01202d004011904140e00ca032400001c64280001804599100e01d080c1e51640d0303028001c100441c43d040395144400f40c06402401c08103d881a4000d00c00c0d000c01000030a10b001c0700c45c003032441c241d00c500d0396600c4401819001980c0c504121090364101c1072604058201c100c002034280503035900700041c40c101111501005600c0c1c026110141d2103c4092220860303060b401d00c00361082c05d0264160308880c000c0c10031 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 693871285 1250 693870035 693870053
    0x9260405040f020301060c080c070302060d02190f2c03150405060a1404031b0c0f1805011a0723070603141003110301090609080d06061d04090c0b0313 66
    0x1019010b418010b20040000700e0700100d06100890b007012400d50369030303a10a00d85041250580000350b0041e00418903030311281c02c2b5805092103100c006c1e00c4800d012000807055032400b680075000d2000440741d02c25010740350f12900803a21104040501503130003404400009081211240c2140f205041c81c10400041c000e081040540048044030304011323500300880342c00344001004201400380041100d01c1c41d81d03440608002c082e107603044078050804580720190501c0501036441040c401d540c04c1d0215030041090351013154100c0f0044041c0c0c2e0185c00c90706210102c0c80c1c204d48016035400015251042250003100303440c40380c01583e00d0140c0034090400c1c030058202c900c09402c05c3c1c000c042190170003c001008131806010f0b02d801501c411524800840064003400e01d131100205040d0403c81078000b008032082c0507005400144c0000e0001c03035102e11003125101d6464891a4103103a0b8580554242d04003a070140183c98007811188411503103402c02d10010341c0c0241d07443c05840005569840034062410303 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 693872535 1250 693871285 693871301
    0x15090a0b060d1505100b070b090106051e0405180706020601050307061d0108250e03060601050a080c031e0108030d0f050c040515040806010b0d0b0d0b0a0926040504 72
    0xc07201d4240e6080c42d00c0340943c010810746180601544c500205041e81010359040b001040e40110855480010f0b180200e1002d5054998041c550f0a1250210783ca1405d0388c40a62159032619181c1c030a40245410072002e40f07806441c2a00b8080c0d0120500380c541c109011000260030309030020000c6514001c00e143c50400d05070300080401502c12013007085030b10202c01e0000d440d02c003440c1c602d150762070323507940f0f00c3c004511001ca80c0c8200e088078031003001440c1c2107030f5015520ba0b4110103a0b20281d55010041d14240315007019000002c1c1890000740f8a0075038440615000340c24030040d420101c0b6200103000c50341c907007a00b05c4070b5580e00128440d250300465000d40500708c1801081071006092102002d0094081ca00429100d50070030000c40e9081a151000c0d03a000300410005c0340e02e9543d40b80d80e115401c0d4096180c201070325080034040307403441c1010641081aa03a02403140c0c0300913513400b906075008141400085451a041800940204001075400e892603070481e0199650740345814100800c83d5259 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 693873785 1250 693872535 693872539
    0x6040b060f2113060f0b060a090509010b04030f120c060c0e0f0406060e120f100519050702070306020304050c0301060303200f060103020f0d08070c0f05060c0a02040e15090a0b06 78
    0x3002000f842c003a060081020b4030744e0101c00400c000c42840040b0000d084c011070219088080031407000c1c1010391100c0c15000b180c1c41034400c00481c0c0d80769032940030349115600024201c01c1000610000242030342c150043c80400e03038605000d0042c010341c0c0303e100340e8503500a0301c1c00140600c14029130b9032031710915411420074115010800185040000b07441940303200c0155101d03c1c8d0201043d1549403050100c0f00c101e045180998850381591003404c8000c1106413480400003100e80024084c0c81142d2140c103008d026107400402280b8030710f54844029500c01130088816005408002c80c6a0b2001d01424010314420303140d4503c8109220217001c1001c240d00e070a8001580069410090361002140300d506582d010340c1c14219034084c5078085155510310a0005014034000110382086c808001c25250955151042030600fa5642d4010440c0c140030f00201001d0640000f000c0c2401450907074800b0815041c20815640b012800b650748800a0380110b4801c11113401c01c44a01c010061075508490b070203e41 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 693875035 1250 693873785 693873847
    0xb07060c0e0123070b041505130c121104020a0801061407020913050a05121c09050d031d030412021908071a09060a1205071407020906040b060f 63
    0x4240d0009000d1076140e0fa582c101c081020001c1800060080b08031540140c0000924900b801c0529041c030485900e10758000721a40341001050605038003044030540107400030390300399105050000d8003941070282c81044440d59041c98040401da1168005403042d60320a0b1035403c070541c503164005d460048068030380208440100130150044e80d07640d180942103e801042e00d44188403d180462806000350800350091141c0d031807080b030301d040301c400801c01c615042400f16800324110704c00c0400c0e2500e144c0e0050058000b034090b1540703d07220360706c000c00441300c01c0c4944014990400382e017811035119400040c01070426182e00c60650401d000c5503142c858035001c00030561840c1003410343d102c041e94058049080d214a645000c0002d922040c0e6184290040007580c0d6035050a102501600e1080d0700c50081c0c609141c00604e20702c2c0a0032813035078a091890001481c01d40c441e07003004150400100010b42c05a82d8040c101c0c1c454139294054440c0c4806002481d564590100c00c03140c0351900760100b00c521104e = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 693876285 1250 693875035 693875057
    0x120308070306170a080c161e080d170603120a090515040509040821070e03060a0605010503130203010f020318060a050705120a090212010204091d0c06160b010b07060c 73
    0x800213882c0515903045003ca036200c900b8196820705040000e4014030040c451110f01061800141400100c0c281040c15010100d0380e0b981b0f10f082d00d41d41500380500115500e83e500e081c02e103c060000d154003076802000e480d1050350048017a601030300310b8201e020001e58064014000c1e410002c0c04078010410039000305081525000c0083d2420200400003042c0103404196502c10714504102c050000c1e070008002c8003140f411000c02091180480c0c802ea2080c4a00404a002c114051040c00140e401c10b031350b0140313180c0e030304444122b41080701c0e01c0482e0503640e902c55180740002a84080c6020b00c050084001162040602107480c200001cbc14182100b4945004d01490070f4201d411500000d8406c2ca0000495030303070264240040c00c51b604065081411001e48071540345041d80240195000304038100812200420005410a041100810680c0c4a9080c0c259245800e1018025020200860810f000000e55500b200fa85003a401003c2e12100403400c0800c0202c1030007440c60500943c50034048c001 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 693877535 1250 693876285 693876329
    0x60c0604080f0f0f033103111203090a03020d0813112e020601080a0f020d081306050d11030f04020d0c1517060613061107120308070306 60
    0x28202030310081510000040c510384a440c82010386101038080024191a0311044a400034a03601c2140c00300400c0014540d00e0362450620610410603889012a4000300c0040d030b40d0981d600000010220740f14407404910801c2d07950f100004502c20400d1602610055103513280103480c0c040f4181c81071050042c0d0100300075080b05014521503241da0400403a0307460b030203090045001d01c080ca464030300c40f045100504e0002c80003038a40e0500036003119800c5480c3c580e0f0700c8a4132616007a81181c001c110045480032140546032021000c000349004001c42480e11058804d14615103505503c1003000c90004203420b40c02141e2032103850f540302c40801403245940380103441143c0307010340100003c0c0704000c00402e50301881002d01c540c0c4054103840d9075603540706000d80700c098524a0000003c0719460600400940141440002d03640300244815500c0302003400c105c8185c4d002c6011340c40ca81014400d41d000041d0862951311032001550180c0c59010311400d11102c02410b13151142c00460f00c401000125034448 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 693878785 1250 693877535 693877543
    0x703060e16060f05130f030503030403080903040b0f07050f07031b0f0b0d1d0d1d0d02060a11150a0c030b010206101206060504060f17010c020303040605130210030b01030605060c 78
    0x148032918100399651174180e207203400901c1c4d40d0081410904000c0300441003010010055000310300a4840c071904c0c1d554403103203560701c1c0b245005820321aa0140702c010760b10750448003c0c2c40c0180c40f96081c0c0c2c0100d002908582c0c507105061f8015580c4c0c0b001815400154140840d02038003038140c42101031030729420220418503501ca100d00c807d030710075501c200b1300c0c0742c504a00c0d030394006071201c2c0d130285c0d150017003d03000c0101704d07000301c1c0d41d5035031201c1c99459054254034100324000c0510342d0103007a0302e0601c04070000c10340d03003100b081c10015100d026910b6145c803d60061000315108101c80000001c0b444513401c1c004040391008400241554401c3c2d00b0302c900601c80f01c0c09001100c1c0a2190718480c02d03482d1600707001510b030b182d2000760864105a40442d095104034460401d441c01448803507090500340c5600c9003039924810000004d60010408036020a44503003000b40e02000c0c0444400781180c840e80865007644112091f100020760300e20508140b980d01d03004d000b0090004a0744c0c0c07030404698410858035 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 693880035 1250 693878785 693878807
    0x6012301090540110c280804080a210903150213081c050304030c02040504110d0b06010315050102150a150806060102010b011119080c0703060e1606 65
    0xc00d0600ca60301440b840385800040320800c5180038000300c20140c07115152100c1d081c2c88190054142080b4840191300d1182c0c0654040354203140050211681c1c02d4010021414440155844071349820002d4000c1114800140004c0420400802c0e030f00e086420442903008014000e01c050019030003121000560100c0481e0076290030009064414410000c40c00c000e100d90054000c031003090500001e5054404a140c6100100078400c03c184078020202c121030512088800801044240c03105002504055021941c0b00e4820402413280c0341a080001d01441d07032114007240c41070380c080c0c03c000c401d5903d40540b204452014a000110605010002c0d40baa03602d1000c0e084251030403030006036120740d150803403000d001c403619900e5001a125607609440e5030f030484009026600340340c100c641d25442074440007641c0000ca0082d0000d1090f0141810340030080060940e00c603035081c000018980d105107c4200194411a8001803c55003100b4903130034035a180d99494200001020208034154010101c060 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 693881285 1250 693880035 693880039
    0x702030a080601031506200d05040603090f06240503060603100b0a050909031305010806220f18030306090902010f0f02120f09040b0d05070b16060905060123010905 72
    0x481d520140101c00a003604540005c42409442c00010400e821205611a02140c14180102c0c003030241081359840a40c0071599001034010071040090a10940c860f22140d4804d895180c03c203103054079982c0598200d10114460035803210380083c16240c4912081c070091030250054103091505600080d1103402c401e031824445501d0780c0b402221076442c42e1000d00074141c0109958924286041c00703d65a4002243d8030241c45001c4030040380c0c1c0c5d8000c80400d40701d0403000340303034114045481034070880c1c00010349031156803151100a00c40b0410700ca8000c240e42e038144200c200c80004401e040007400c0d0745590b48030101e114504413280b40540da00014000903810f29080040a94400c42c804071302d07101004c12550f102c040c0c0454017045110740d01c4000c10640e5030440703051002003ca14100300101100d000300400b16844845c08010005c40d050251640c142c0783c110121004446840d1001901c001d036108550a8100304014088030b10321011564036000503e4075281c180d6013400c0003030b009401c5c0d401524 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 693882535 1250 693881285 693881297
    0xf02030904020d0e010c020102090319120f031d0c0a0902040302060d1518060e0c120a0f0204030602130602061b072010030506030d020321060409050601031104050f0702030a 76
    0x346507496034004100e1000c404c2c00801010342c5280703000b0300039000030030041d102e400703130242c00080e8001d65842c00e03640c00c0d04505e86240e00c00303041c00b0540b80020105d0702a4240364072841d40740160604549803001e244080c001408100c8421020020643d9aa0b000441000d105210500140e141e0788145c4640c09407030b0301d00140c149440c1c50a0001d00d6000d5100c0288aa0050b00010040c103040e00000102c0c0c8000e807020380c0d0768842c0c1d0452580d500840645000603c940000500e0450725504001c00511004000524046e100d4590070140e90115039411404403404a0401010b0f41c1000429401901c81c0b007400d4a08480080e55034152040d808040c0101c44200640303541e504421458020408001b00244803400030070380003801510b401c0baa4107100740180c010300074002d0700103c212202e80e041000044070303d02260541004c500e00150406030031941e00d61510700020b80401c1524040c2d8000ca502d221020b1410303042200b500d100600b54a41a5000014030010036000000d81d200d40600342014 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 693883785 1250 693882535 693882547
    0x8100902010e09010902090f090408032a0703081816090f0f18020a080c060a0809030706140f07090b09011d04060b0c01050907032114030114100f0203090402 69
    0x100c90003810301d851a0303400f210200000074040419401031600040507103200d85a00100b0041001004c0d0464000d01018020400a10a0070041c42d040a02026440081c1e1550f14003454000940e005800201d0103c1c41c041c4c240030462110740307801502c0240795070041042a40d260400000b00c1058440c05c400d058a441402241f901706401001c600000c0500400c101441114040741844080c002640603480c0e0000200c4c01f0013000c41c1d000340240300079003075034078007103030154102d0300103030001c0c1003036020b0106018046c000b50b440e0042401e03180303180a01e40c0440c01c0c03200c0086061503000e031408050002131700c02008100c1c0360b4420b8940e00f000c2400c0c02142e42071643c0c0a644070560100030f44e64002e01c0c02c1000314662141c02c025000504441008001303030750300c0e070305125900c070103500000d06103480d66440035940d218420071030030346c6118600e01600f07031002d410a400c0c6281c00070380003c00f0941568842e00903034140065030020044d89490491007060540102944a1180c4035609004540000d42c03 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 693884892 1107 693883785 693883787
    0xd1b08010e0c07020a0513060812030f16120c030225080409020306120d02150f070e091b0d020d051003030e010e012601030209090102040810090201 65
    0x1150015150032000c44903d4200420803070303200c190814003080c81d4860101340301821b441e104001c100603007000c0203141010400c1252a9061170184104000702d51507220302d43d0054043c2190114134100032004650008034448004400350a1010312410315515600610140d520024000c1348c11180d00c001407035900003440d02811038201404140041901c640c025a00300000134030280f0022950a10141408080044000542c000821920b085002030423101c3e48132141c092a4405c0e80740c080d001a00890f80807256601500c2d1210001b84101d0303500b00b00340c10b500d40d4014181c1d2282d604e84049800f0b0f40c0008581c4801c2030078600494240c14000d00d440302a80e60685400c201c4400c507e004640b005201c24010341004117104801c0c0b1818101c2c00300700781045000c40c0c0c840751503045006001407458050320304440c0341c1c4100002c0200c2070010541d146540700b01c81c070110b034107a05d40c00 = true := by decide +kernel

theorem cover : BRFrame.Cov 693705035 693884892 := by
  have h0 := BRFrame.cov_init 693705035
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693705035 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693705035 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693705035 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693705035 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693705035 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693705035 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693705035 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693705035 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693705035 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693705035 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693705035 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693705035 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693705035 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693705035 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693705035 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693705035 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693705035 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693705035 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693705035 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693705035 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693705035 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693705035 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693705035 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693705035 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693705035 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693705035 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693705035 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693705035 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693705035 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693705035 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693705035 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693705035 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693705035 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693705035 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693705035 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693705035 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693705035 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693705035 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693705035 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693705035 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693705035 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693705035 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693705035 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693705035 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693705035 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693705035 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693705035 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693705035 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693705035 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693705035 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693705035 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693705035 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693705035 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693705035 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693705035 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693705035 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693705035 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693705035 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693705035 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693705035 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693705035 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693705035 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693705035 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693705035 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693705035 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693705035 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693705035 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693705035 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693705035 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693705035 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693705035 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693705035 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693705035 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693705035 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693705035 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693705035 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693705035 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693705035 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693705035 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693705035 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693705035 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693705035 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693705035 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693705035 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693705035 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693705035 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693705035 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693705035 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693705035 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693705035 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693705035 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693705035 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693705035 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693705035 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693705035 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693705035 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693705035 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693705035 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693705035 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693705035 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693705035 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693705035 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693705035 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693705035 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693705035 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693705035 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693705035 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693705035 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693705035 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693705035 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693705035 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693705035 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693705035 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693705035 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693705035 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693705035 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693705035 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693705035 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693705035 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693705035 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693705035 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693705035 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693705035 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693705035 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693705035 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693705035 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693705035 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693705035 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693705035 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693705035 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693705035 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693705035 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693705035 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693705035 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693705035 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693705035 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693705035 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693705035 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693705035 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693705035 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693705035 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693705035 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693705035 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 693705035 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 693705035 ≤ n) (h2 : n < 693884892) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
