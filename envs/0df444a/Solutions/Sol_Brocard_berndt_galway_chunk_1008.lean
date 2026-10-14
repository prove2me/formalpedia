-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1008
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T00:48:18.35036+00:00
-- url     : https://prove2.me/submissions/968e59a9-4eac-49f9-a1a8-deb6c4ce7e42

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 181115107 ≤ n < 181294964 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 181116357 1250 181115107 181115159
    0x80c01030501080601061407021309080a02070801060f18060f1e0b090d030810080a0c030b09070b0912030d0203100602070603090507030f050c090c0d20030a1104080f07 74
    0x8905100602086001f8525100d4072200066903030440d65000005608601c1c800c0d010004150907140c054001d9012100740740c01b41c4107400f8006206581406101c0a03640c80303144a00032940f0b400c04c03035404540b08500d401c0c0c07a1134079400c01080c43d8030800841d0006005210f44808200d0218150302445000c40e0130445001031b0402c24040580ca640c21075810f07580c2d252600e0f11132a40e41c128130b0700c440c48503504412121300981440205001041c01c050043c0c07402042141c100c2d8880e2140e00703680d030a09214502e610b50091203007030f5683c030309601d1b660910448103081e6450042003820b40000ca03801250001d0108100c8182441a41e1741040a40c01a01d800d007000c000700001134940548c0c0d00311a210080109071410b06850130000c05205040f094140645088001e00340106101d1315500b1410007421810f01e482003521081c10420880b608680d0408499499500c5281341200500ba030807100300c2100310108400611048200b00d2030006040000c060711078542402070061803483e5204050351088 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 181117607 1250 181116357 181116359
    0x20d0e0103061401180801050705031801051302090c0d02041706010b040f0e07030906140f0601020a151a030f07030515010305031611030102040608060a090e03180a0e01080c01030501080601 83
    0xf20265030608500409003000042240a80504142d400864001c204a9401e00c1d05021001d504000698003c4501800034000b402c113070581079003210401c480c100e190704284800036015007008041c0700c0c4c204080403175040c07404090b510030300d041e0f0b80b2950146a140d4140001e80b00348420130300600c3d014051102c50586020b02d84081800248064041d200788109035a01081545000798030a603202e55003c9000e101d8442c3c81c203804011140c3c1200d2329030007086110001546584081140f46030103500002401d000300c02005c0a00050403450000c01e0308071001380a0800d03c1da4108540c20301280100300600000307003185001420300000c810844a40c0802d00c0040c40018000300684e5080004d44403640e0034a00c4a08007034140341410030416401d544000b6011803160751050030203100713940a95003540d129640314001c10071a20b00940102d400e800a10100a02c1038092031240c4443c2c100520b98044aa21201d0b2011605020b900160880e4049140e6880e1960180292401404400c001c0c010f82c0d = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 181118857 1250 181117607 181117619
    0x4050108070b0711030a020a03030c02031203090a081608040f14030a0309030303020d0b0a15081b0915040e07080a1a0a05060f0c03070602040602280b07020a12020d0e010306 76
    0x24002c0c403d00074034108945005614640701040401c2c01640c008180d12561541e0741000382c540c140425003130340170b03000c0c1c1d45070a065041e05c0005c4038082c0d0200e03001800129510b8942d010b207a0002c0308000c0540007206808808501441c01400c045c140341d03c2240080340c0341c800400020085200074500a400000f40c03000401d0f0001c4c4942c00b00c0b60581005a81e0314041d85d41440241075204216511100b00c4030301280c440c00100d040c044003d419210007070140c6501010700c03072030080480b23484449902000305945a0800d0102154801d003954203035030404c0d46032614040d074500d0441d4004005210f02c0c08000d0800c03824091401c0035a40510300e8000340000f45e011070600c82260003424020103000070201030120f0110202d80d400714900c802e5a850307030041d1810358040c1d03205114103401446100c1c80c1040340703619030f4039107907000c0741c004548400305c0304640e5941c1c100c90300140200250f0264038511008141018031540f812462940a0203125840402c080c00d40d01003002d1580c10903180040500507 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 181120107 1250 181118857 181118879
    0x10b12010e0606060c0c030a080a0201150e01050f010908010906150e040312020f09030a290906060409150e01060608090304081e1f1509020f03062215050405010807 72
    0x1503c150f40d496598050215054070f00b1411841c095058414511000300307129184010b040f0350042c950080c428182c20751200c443e65241805110380703651249004100c5807404100095014a040c100a55815520b034191400c584a0b400c0c140c0c0c200d921090809680c5800d04e015801626220740400458140790310014000b00c521544075045540c002001081049480156407940000400701c80e00b154452805403c14402c9202c0c2d8140c2e6101981c02c100c8007031481c10014424040c0380c0081840d55108000c001c080c00d5108401d0302d0b442c4803114604206061801403011b03280340c1e0000490407900c6d080000b01402130052590040d82c00c18403050081c99804180c118038601140400889200c1c021095401c24034814642c00200a00b91020720100c042030700b054446818ac0803007400101d075980070341030681c400d1030318242c6180c0c0d041000584924143c07226144082c0030350049034149500703041c0c0c18110b4524480380100d800c400310041100c0d144c180a05400340c2082b001501c5001c1c508100816 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 181121357 1250 181120107 181120111
    0x30804060504060e030403050f10050417090d060f021903150303030908040b03041a09010b010c06150f060e030c0d050a1203090b070903051b060a030b0f0402030405010b12010e06 78
    0xa035519940440c041c000190001103601003580240c80c0c2d21581e80c41c05035540c54521561500900035104060300484a5104843c0304a13003003008050804a105000f950702d0340204030f003a61100c40100c40c00085141c40c0f0a142c80d001814900581d40e0340c5400e644050130b503614481030101410a1405101109500700540c11607034541408124117580d860900003a01840e000200311410110421003440742c0002c14903146200b000e01c038195601c8903501c0b41d003603680f16000e43d400300300c08041003000034a495000f0202110811078111a186d10b40103288500180b6078000400601c2c180e10f0401c00f4a1700340b02e561380000302190002c1c055000c81d950359840380c6a400d0040c000c00d6036a080c44000764000e4002c0c40e04240e10010f9003a00d841e040388054002c081900003079600d41318000d061015411080d000070b003001e00052110741017140da01b4080300078041000500d90419165500f03081e0540341c030f00155018074800c000100e01c2426075000d004c001c02c2840c100b807400ba0b05103181c0440491000c540740d9 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 181122607 1250 181121357 181121363
    0x90d05041710150f060801050604032301090606090b0103050603060a02071a0403090e090d021b0315040b04060b090705071514040c03020102011a090c0702030a0b010b04050f040603030804 82
    0x700d0300c9124400414144499495101061403e0080078103c0c00c0100000c08140c030901d21280d22002d84036641200d4580d4240101e6400803c20003040c00419140440d9100c403580703240d40e09001e002c14484290a5907420401215104d85070002405000a14000c0c0c4080603800c1c80c04104925040d00040c0c1d85110151000300f046900040700c0c0180448880040c0d02d04401c41c00c0d98685041038074004001c07201c07070710881c0c844d1110705c408030303562200101e800c84a44240342d0003840401c021020511500707190500300d40e07041c8602d241805070b10310100e8415104074028100004d03646841c0c1080001e5a91240c6090f110786160000c010380e294001d4140c03299907070481189140800081d00030313001081415039a2440d215441c0401007000b032925100d4003030b24801c0c1d0090140e20140c03120003520308a000005a84415201c0002d0414a0580c01901d0312900040440381624816140c2e012001800e8001c0524044006800d0155082100806c070000d0025502007000c149582c4000301030580c00781c801 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 181123857 1250 181122607 181122629
    0xd170306060909010e09070e040203060718121b12020913020607150f0c0315060503040614010f030507080303010b030a0e0a0b09030904051621060b04060c0506090d0504 74
    0x20039020740324042600c9030000042c01014007941c40d9003a4840091007100ca1220521030100d0120b41d894003002080e001e1540039000300030945400106075042440c1180581080388040740001e242154050311403201c50194200020200c02101e26100b1024190013483d44003001e202c3c4080140c80707002e452940110121400c0d030780e0b82001c0c03000070f19600c6500e0b4040d1003000700030006000710100f6805900210100d9404208007203450400f9001d450701017010000181d80c07003508105880c092802140d100b846454001400084013940711400d16081e00103018000103010180308019040105002801440000310708640c546036a6500d603100003040708480c2c5482d84042c00d543c00c8104181c01c1030b180c4c400d003000604d140c440d202c107544c1c2c0c0240740308a1082d401e11020038000501403010130303001e0003269985105800d8041140910110b003040702c04909070340d41d400080e00c0e0f4601c0040c001070982070392045211140d40c10300c1d034900400501040345d240c10002000340761540241c12542150044911 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 181125107 1250 181123857 181123861
    0x20130e1b180a0906090b0a0e0106050a0c080c06090f06011a0c0c1807030f0e03030f0c0706051501030e19060b03030d05010e2502030f03060a270b0d1703 67
    0x1050540140158440b500100c8862001c10401c80940140c01500e0f0714250800a1030079110070441154590f22500c0d01454004005000781071041c4010000402c0c50f013021803540c0c030350390340f14151a40320188019180e0050801e2062044051000026442841004004550418200c20444561050f5446044c0320006040503d218180010305449000030200c2055004c032100380c600c4040d003154a10700091920340c07000f1015419109a280e0040100015420b5030ba840844e075583d00000b0704141e44041040c088031000810b00c0c041c00f44103031200310161b100143c10314005070980c1d01c410b8079803120b608040300c0c032404000c2410004140f140c100380046801c1d25040e01280c00c51080c810f0425032141020700108118904003281c900520540000748112030305103401c01c0301003101520950050f001044004d000403a4040a99000356004103001070701a40c030b00360801e48022481c3c45103000c0c644030007074048518403442800c100f20012355515035401000e694840c1b2824418131405805940440 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 181126357 1250 181125107 181125127
    0x6091c0c08030a05010905060102010c050d0b0a0b0a0306030b070c1101080a0e0d0c051b09191d1507080907030204090c0b220602010612020f030120130e1b 68
    0xd45405181c20010450b500d0624440e4800945024011010050304020204003654070512a468070782c00701ea90f0301403c01c4c80c0340141e0005440080c00e1180c0c400702503000407070345c1c1d98600018091700d0500c0c2c4001890f60300c1e500d405604018001c01c03a1060085600d10a00415000c0d030801c4155102481d0000b43c80e5500a9118000c0660403a004101d00ca144144461a600005420500b502480844064541c201c0d607128844003c1100150031481041c046000c543c1c1180084150729900000456188500c8a00b0002035998004071000c03580035040500c0c0399642c0012842e080202403510311803614000080340e80d00c0130380303202c000c1c02196280314502c1441951480e04d00503040c4405000e66601c0f03804001144060b0f410864440c6642001c400501c0746d0052142004407181c610000701c030000980c080212403121240010303055521903000c0000c010220130403a454a052001070340d200c601541d00004014040d400c0744007405c0328101413000c01070007038540c820103900c03502100d0b6803440500 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 181127607 1250 181126357 181126367
    0xb0a090603090c12060e07140f0405010803040e04140a0c170c0a1509260d03020310150507050d0503011e03021f0c0f1505061c03110307080301032306091c 68
    0x86d1011190094240120303001c80004000303802c01e00125021201c1480302003c12007210b2007132103140741c1c40d4010041084070903004110143c4c0503000b1030b008107458281460090038101d000004031460070100b4002e010b0000301800d84410a1f01d03001c010320f82c03d40c1400c049400040180581c10341a000040d44004071481101441d020f00741820325000b21008505002c05100c1c04031003a0b1041d8041c00100018681c404c0c0f09407842040d4102503400040c1c030b40303001c224114881c000000100001000341d8808a0810804040c100d01c0d00c0d901c140da0380d0f00d4041c02403c01e83c04100c0c80117901464090801c050b83d103100c080d00c5907266098004c4140c0e100080c05440c100d002c0b10004142c0320203240d030070080c0442d0401ca801980103501c02404030303560300410062580701d13241c1b003140041c80e001090400300b40324050b40c0c2503114004007241c0c5425001d407600d68464100f41c2c03048503900c1c216000326007400e136103103041c055070a4080014401e500700110b601c0c2d00e5000ca44110076000600c0c21407010610310030 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 181128857 1250 181127607 181127621
    0xc0d06140a060c1208270102030405120a020d0f12050f0603070510080609061c1415070c0f0804081603050c010f0914041812080702160902220b0a090603090c1206 71
    0x5001e428042151491b4030700d001c0c3d00700b110141e49030b001d2444042d40c03080481003212400c0b100c40c1d01600007900445400d50f405031002c5c183c101001100b4000d28641c8209100382e50140e407860300000310760300c0c15038201803600c2c0650300603600034842040d84000164002c0150b030381000c4100d4000e1020f54070340780410351190300e03107148803c0f0201c844204014001c242410080a082103020b403880c42801c081081d00c4c004040d143e5000103485040124045004a00050031052048031343c0c1c0d161a9550f06850714004141a10400220306128204100701c0c04020b40b180503c028203020400145084001c0c02140c040e200b0443d205001030300e10761300c6645a40c8940b5183c030408102c01580004c0d41008141c80004c01121004904200081406c05000041c0111401d1070804040080307030519003050040e401052003c5001c4c00300c00303009910046010341160190447d8a070517a181c52000e98010001400e503803121040c140380500d884080754011001e18190780304080411800c0d0741c00d2410000810348 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 181130107 1250 181128857 181128901
    0x203030301030f061b090303030c0215090f10060e16120c11160302030606060904060b03070215070906050f09031e01061403150703050c0d06140a060c1208 68
    0x40000040100221183c030416a036020303100400210744140c451641400f485000f10300030462a00c4200f0000e40310350826056a000c0f441961800382900418402241003510120b40c0c5800100c2131804405040003803ca2020000909000c1d80c3c2c942024060501c0d00a0101c0160018a90f122024240581c40420000c070801d0406c1140e0744081c01d0042c140d003060410310780c640c0507103912540280740c04110300042d82d8005024042c903440304d01c00c110039603100c040c010341c1154540d100010b6182280c4091440382140380c0280500400d00688084004801480074092040101041c4040d55101054403084240d00c0c84207036403040440002441d1420840141804031845050035104010640204003203400c0402d6040c0462040d60404d0b884070702c2c0e80c1084003148c2044000901407840ad40000f504203600b410f030710340750003030352841541511b400ea08100d0440d078038012404150b0900d182264003e000d41c1c580102c072011a03544041491000b084000d0403c00c1e9080464920701c803010786040c08a203 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 181131357 1250 181130107 181130113
    0x5091308040602010b0f040b031f0e120c0712050a020907030e0105071101061203080c070204060e07020f06010501090803030f060118060e13020306060d020c010b0925050f120a090203 80
    0x19450728020302030031917940041d009030b04a00002d10306003800d0003501c1e843d10004000d082c4010341c0281c2301120041d01c07140c880400c0d4a45500419040d001c0c0006010500e00c042025902d560b080905031820009034803d41100b600c20040c08003068002c10848111541203548404072349a00304d00304d015107241d20031003405510348010301c01c5550304040003542a084c2035000340001d540d81d421140708008040400750210700000c1c0001c2e294032200004200c514801400040e009885054030b18144404640200140c0d100c41c0f22825075010421000d801030601340f800c05141814803100c00d84900000e800020441d41c0113000c14072a0f80903a042d15000ea031604001c003140ca40d10f807001403400409810582c007a00807070a14206224640c000c403440349002600642c6440c03011800700b4020361090341449031030b550b20050812103a89007001d60307024010189000c084c418008091a0401d00298180028400c040292110b00f460340806d0b600d4a0000c940384581c00d5030fa400761314005c0c02150000a5141c0 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 181132607 1250 181131357 181131359
    0xf272d010314010e07120506010203040612020d06030c0911190e030f25080102040609060804050c1518181b070c080607020f0d0c15021b01020d0b0105040f0509130804 73
    0x14107803445540b080e05c4a07941c811130010307058082c034100c076001d4490fa80181c00c02c0105024140c001c181010404090b014018944000386501000312084c6401c11140858072440170020000c890254402540c1081601850505c81d5000c3d11a0226160401010308c00d403295403041c03540d4144503004a91640c00140c9039401d8259003104800d540d5108440300381d854080e0040b44285051080d81c2c15511140c940b00d54039414601c0559503a08001c1c0b046070144031768041447c0785c1e150704e0241401041c510600d41d172a0b0140f00d040900254101e41c419004000c10b0300440c0e000780079400c2d80750b000b509002440b4282030426042c148a0304c200ca101070b00b50840000001483d0800084140c8641f00c5a07007a5503980c07480c40d03000c40e20343c801e54640b0800941c1100714080400c45692403420005035103080145000c20048208034800041c010301043c5950124014030819028000c00c0b4102c0402d103011850b0604140036007a0f660b4080c043c10380181480030025500d03840d01c260b84440d064010100503103507 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 181133857 1250 181132607 181132619
    0x501021201141305010b090108180a080a0306061706151e0a03050730020702130c0905010c020a0311030309090a0c090e07080a09080f272d01031401 65
    0x2c85040d208140030f1441e081a524545045204082c160b815443c149460f02e80b150004558440000d010b07140583c0140301d487c0c81990f03080040e4442d251040c2099612003c4400014048540f143d109809000950442403412815404040d9001401b21440655190b02020058280c0910f0081c005c010080206007104080204007420f412a00b6a80034411543da02c04220749003881200148038241c100400c041070044071440009054076801c00060030705403190001050146107643d0400c0d80c0740c0d0b450280e2807040d801401d25010b01020f081900c2000c0d1a81d01151100b24180300251600c82c00c42814000365500340101d4a00642c0200300449030700b0100d4541c002030030a5a00100400e02c0307582c0c000380000d4200d020b24031a5100e0784403502c0c0760380c558403902c0282440360000c0b1450041000a00e0411074480c010300000d44008810700c00c403d8030b42c04030a0b1007888800050384100e0a81c1010040840003c244101080203403102d0f0210812440041e0b001d840c0c8680c003a240b0b003070090300128030 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 181135107 1250 181133857 181133879
    0x1051c05250509060312030c030703110409020c0c0102120f07020a05060f0c10050408161407060504080601092d0923060a150506070f06050708011a030108190501021201 74
    0x90b9501110b0401c099100c450070150340741109901c45c40b161105000180403040c1c2207001c0c5a21403401e04010800119101c155480c030f501c140c1040c0c90099004c6411240034008020040044c0d10a0004010760030200d0382604444c00b07050042840341034002400811921100062401058081c1801d91500748141486d22260050301c2485417a00c52240304406485403409401e02036500301c3d000740d2030489041602d800806912900399894844480c0311050700d00104060002440c885d51020703240e81c00e000c00282080d6060380314000003824a0064000c09401032a50301c0b61a80c0d050784074208401041601000c2c080011015150360300c2d09030003880e40d41c0f10405a50002082c54290313041590f605410750221110302c3c800c82c4080707002c0d107000d002904104000b44011030040807210034120f8242d2b42d48082d64801c417135080004249000400c0b05200f0007900158176a0b40020460942d0704090380650780c0c819280400e00200c05038407803402404020340c1224469540c0d203110003001c1d80c580380d100d50 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 181136357 1250 181135107 181135109
    0x140f090307150215060a030206030c07020306040b01050f240a0908100c08010b130303050f0702040f09020a12031403040606030f0c0509060301060e0103022b052401051c0525 76
    0x20250042c540321845010260f11190300c0351780d0042c03030400154203540034440990002400383e08504400c001d1040542e9040192a100703a1086080135442e40c1003a0600210408980c007881c0a600807000d20014948101e0110304a000c6004245403280e00f600c0080340d60820340d501c80d20b010300440f41003420604498114000711074003a16a50710301e990314280c070180d5104003140011703181101081480040c0c0324a0041003074510b420b01041c14007101c1c0d00028101c40c140d144989076180c3d900011011070914200070001490b5020009070911503c4e20050125003c01030707291f1079014000009010080070f94051009142c1051000c1740503010382c43c000358040b1150141610406035030b00000c0c500d1030140198001e40c4d0b0380c400040041e0f460750b801d0101540c4c550044000020741d200d02100007051030049141124040c0d8018072500310510883c41e2040c0313080c505a0240280b00e0300500090b1900a26140140040ca43d00c8a0401d10360900b2800e00030000c0e00402e2494450f503c8072a4542d10941e220 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 181137607 1250 181136357 181136399
    0x60a0b0721080603030913240e09030a02060f04021306030503032707090207060204050402030c1b0313061809050705070c050402130b180301050103080706051501140f090307 76
    0x2030307103203a0303412810344044104440c6183d150344204108035030340c140107600083d01c4201940200350000c210003d4900c8030300f429601c5406083c2603404001c500817081640307400c10024806107140c602101d030700949611000b4001c5400351000000314046480c2d03040e01138000f0312355200030040107440303140c0380b6100d902c02c3c0c42c07850840e44074240d01c0c2c64141407480952404100c2d50001c003001031800c80660082c1d08220300548207281d00348400101925140000e5204039071103042196a0103851188140d000b170307901031856003503006002000ca4030115260000a071802030502e00c01d4403602c8880c0e90f0103e421034100d501810b0a00302030181d05034001020304a024400c0000304081070715030082c841240a405000854070207200410443c0007554401800040f129654103000802c1c043c003c82d0a40d0b4003a40308443d10140000d201007031203020700c1010303003103207000310070484004414000800c1d13103401c00000000b04c00b00085120300e03d09504102d136048003014081d2030315156200d041d10703003038404841c0403 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 181138857 1250 181137607 181137653
    0x30105030c010809100b0406050a08060712090506040822230108160305071106040308270604020f0a0e0108030a0206010602030f0307050702040e010f050405010608030a021203060a0b07 81
    0x6081c190300030111203210300b4202d0000d14035104504c1859003c0d0088004094000741d032844041042c1c1c80b29071582010340901c4005252a08080358020075000c540003003244800d24000e0f40400054011600c40c0e0880d4002440c1038840c414400b100500d400f00b0304082074240b8160400160038034058016490500205044c030704a46942001034a41440031038591030366501d01c25681c1c000754003940c0540e401550354903042410410000c0203601d41103007a070b4154007140342c2c1d1007000303c807e150014420756954001103a4400d07003014440c1c0f9685000240009100b400e03d400c0c502c0494440300b68400c003c10503440030b00c01c156075441c0455104c1d4403115044005006560000c980e090001086880e9101003e42052441c0e848800482d082d401c070120884c0c1c0140c4609201d540b48009004d0048044441e2500040700c2c1000e14005003150616400741039070b6003007840310388109a00032401110440326080f03213660301e60301c94001443c511800c0d00181889400400e042d2306004204c64800c07003101d41c030001 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 181140107 1250 181138857 181138873
    0xf2205030c03030c031b07030515060a0603090f020d020123040e060a030f0311011b020c0103140106090909150c02060a050f060f06070501060b0d0e0c041401030b0403111203010503 79
    0x18180c0700c4c8205000c010b4281c0c400c200032950410b1802c80c903041044120244c5a46580382e503240c1e406e00b0042421a10308680c441c05021641c40c140480c1801040d85080070060704401f82c0e03400c00f00c102c5040010f8410000b604096040da4001c2950403110319174200703109c2251a8004000006801c14010700e9a0043c070540001c0c3d5606044491f44140d9422201030b281c0044582d804482824414441c2ca0680d500e4813403c10021014480309040c0409540244c401120172364001000c071244082100400904800100900c079044490181954890301000ca01c00c00307542030084900340e90140d882c0b000782c5024100e00703455502040c154016410b8460070f00a40c0c841000100d10072500341e40003941324000c2d030f1b41c100d174914051006081c03485c807410010686996810130044941c002c80c0038208250748407018044002c1d000e0040d6a20010215010040288151a0325106c2c60301404000c0102154031301207010725003c2d41e82c0da0005d0900e0001c41d0584c1104140004c03240d0401e21540c0d00a00c18086 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 181141357 1250 181140107 181140109
    0x2010f020a2304030f080d09020a0f061e0e060703140f03072318010c21140c0a060903090b0f07060509031611040e0f0105040b0c030c07080f2205030c 66
    0x22078080740d4105108a44128003600ca491040d40020011f080c61a40c17a800c480060b01c605034040020800c69802d8140285069005000c3d01d2040c1c2540a046203600829201a5040030003042221402d50300280ca603001da160690382600c940034110300701180859508924412503004601c46d041e290381d202c0791260b407030300c00079800c003554204491400c80510000d000c0081c00d44044190020500d0080c0e1961074540b91021442248000c1000716414800d03103070788540c0c00002c0b90040c0000c10300024a81070115551648843d01c45000501580e00c0782e8540c03007070510444011000d4041e015071030341d0b9410700240d1182240c0c040041110b9960410b0001600b400021081c1e84000300c14241075904421107030385187c244007005918030b51184d078034110144059010031481484600d01c40c00081c40342054100810516801020701c01c004d00c08204010781602c0800a450805601007602030710349446030184000d80c000c44c40ba45034980781442c44e00440c0d041d012940801c0311030540550340a110890 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 181142607 1250 181141357 181141427
    0x100b01090608040807110d060603050105180a0b0a0212010602070302030c0414041b0b0408060f100803040b030912030408070c0603050c0405060702030a050a03180e0f0c090102010f020a 81
    0x1200e10350100b10100001400b20b1000e00082007114070030702000d04a00103010015070240b032969001c3da002941d4600610070484244541900080020b03150f814007a16034403030681d10500c0f00b90084c0303500f12000c0420b681c074945030141ca280340c1410210b000d640d81c4503c002940e4002502c020381c460b10420b9008030080c1420f04c0381030854010f0000d1910166907944528103100b064980c0b51010500803180095004640d2000c0c101800047e4080e041504050559640d0804003800d403c00c50103640000304a0300c2c1c0b00000b10b40849004220050306e80d900c02171440d08044240d02624070030003000042004010581009210310b0303201c0d00e002030100703883c3c40b0118101c90007102c5103111410f00300320070300c41840e00c0f8018240140c40101103c02103c0e80ea9942410480018004c07404140c1c1d80b1040400c810b2050000e2015001c604081282031a08000d82140040c01604520840714005140d000f564800c0d00300710390b00002018155a83c03000c0d0440145200d1684448034818100d004400c00781c04000 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 181143857 1250 181142607 181142609
    0x122d25030f090b03010e0601090509070c0308090708031b3c010506060301090e0c100801031221020711151e032403031c020702091e07140702060408100b0109 69
    0xc40f0181c116800e05600081040014081d0703070500811000c00549a82c488078030a126050650f1881601070052030b001c0c2000c04083e0505040c0c0d082541c0074071403484c1c00010364480d0101ca9070030415101030030341c400e410480140061212a0040e450341c82120680d013142d82d00101c10705920450891004050608986040d24504d40c46001040104071150750380e00500b243d44004000ea45120a00e480060090514000c00c040460215801002406044610f0b900c0e10034903410510b16820042c8081140c10100010185c0308944c0441ca40061295403040000e401c18098503206805080c070b2020103141c0c00c9881751159190140703544c514107006034429203001d40d21280007c101d01d203403107800148481d2008a03c035014401403200e82c0303110360090800704008401482c01a500e00302c5006100d41da141c0100801e025252080240b031080c02d4644141b90301c01ca943c5000241e11907481000815440b0303001004e98000c901280c003262280700800c00003003086054008229000390000150f650701c1036 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 181145107 1250 181143857 181143869
    0x1407020102030f0601050a0908011a03070e0103050601030b0c0702100228020a0b0d0e030f0a02010f0c05030a110d09060b100c02220f0e030c122d25030f09 68
    0x5203c0895200d5001d00f014100c40d006030b050171150b880d29200128211940b01c603a021191010051141107410180300d15405080c00040f2440c175581140c962030f64800c4184401000d0289290020300c940e413400068503041a4000c08020034403205800c000c0d6039204a07002950b1400c5c140d00d0450025a9060024022030f0f030207000ca0f0591403600c500e8038102e4100d994045030040e11800f4149030000d090006003101c0844c02d03d00b0f61261000c160080c00c680348444a00282840c042c28149415002410b8a5104042010200340c0c80054088455180560700520305920700b000d000104001d00c50b0000c2084070b5055516400f040c1e2100011504084d9028019412110541c03080d40c0400c1c0c610608010301140300300c081100020384000b04202d54130b150502030a5000031591061040d824000c00f119904007001d41820031030a41d0000586000000764010741e88588814500a420441c00b43c0d000000c0340304c0e40942014800c0c101c020304816100c0100d001618101000c0c2100340035812120a40c0c01c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 181146357 1250 181145107 181145131
    0x60e060d021302070c03050a050607050307141803070f08061e0606031b072a080c01031e090506010608162a0c080f010c030225140106030303140702010203 68
    0x816400b800004040c0800c0950b0054003040380c400840c00302221400111302c00e400600c02002036041c040e04080307000d4960400c0040c20001c0c00f03c50b581c80a2040980281c0c0d16a00f0b594184001d03c0601d000d0b0f0640702c40f078050240540008405080311032400440d00c4250a865656a40705004030031b58803218000c0081c07840660200d020380c14044080c560082e10b4030550810f8136112417811185030446403040720000340044056007034201c06082d440c42040c00e0340101c44000d00300000c0c2512803038429000c60416681eaa04085e00d800c041285040b0750400020030011052142085a101c0409000e40030205050002240040c0d044d44e60301031b401140c1d503a4003080c0141d9400280c2500c1900105d4100700404080603401146481d0586401003c2100043c010726245150190035696912281e8040c54410f001150648030071410900644040c0c400c3c0c20418006841c207030b0494192050410620740c642140841003640550041600345801c40c080201030f600c04100300d0a130f100403501800185 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 181147607 1250 181146357 181146379
    0xe0105040e0f06061e09010f0e090a0c0513030507090e0607080a020313050303090606010e031204090b0406080d0503010305010b090c120c16110a050d051e0102070606030302060a060e06 81
    0x11100302c00b00b900b21100820081c9040040600e4009028042002071411000041c12940641c1c0092440c001107074079060100c042d840704800600006001400806159101c01d012800b0078480c2045451450100905589164480c101607a882c03100c1e000394802d240c54170b000c0246081001402d0b901c21003581e42c07241100d41d04c0341d101002940010380924558160081400300091041c0040c511415a8100500303103854164001402d60480c4144140607400004040e5421000704003150705481d80e2001c0825000903500100d00140b481e903104003058050340d403d25020541c080000c1d4103c034082c40003442a10407101c20804518420b6500124544041101c00032580f4024100f5500400710501541044032207055800e4601c12820100c8a136040c0f074041c00c0c480c0c80c0c41c01c9440701a20050b21000140c903407a82d1266600c811a5002404c07404454440c2210300000350125a582540a801032110560300d14020303580350800d503180681076051280c0410f00e401202c1980d4403c02c1c004183d41c40304 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 181148857 1250 181147607 181147621
    0x10c170c09100e0d061109030714061b0c1203071208060d06050402010c061d0712020108070c050a06020f090f01021f0b040f1b1101021e090d050d030c0e0105040e 71
    0x1d9083e48486a400140c600265000329084e80b00f03055138020059807043ea59181c500c105418880260407030b00c0380a045507003850312610703500c02307440310303411105884000780c42139800300c0b0710741a41840050380c000f41941d0304800d07020703001c4081d05059104201e1903071010340100d41036030b081000712440c2d500507030000e01110118120381c022641090041c106841d80780165150f40c1d00383c03000e0003000d64440131320504080b50b085081000b80700500500d10519000c00c49940001d16001000e082c0c10100400d240141c0d040c8001800f900808980c0312404554440c1e503c55803245540007440c6c280e101c5c0c41404003440241d400030440c45100261001c1e50748904910300a400020510011034580080c2d56021a000034842480b03084200e82c060340618025190000000704400403000c0da40200303074018041400c1c0d0a039040009000340030310803c22a220400fa00c042aa030301045a80236241c0c0c8a050103c81403150154020703010340400d50342d0f03030340800070f03250040d030b10b901c2184110800c03d00c101e0009503030 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 181150107 1250 181148857 181148867
    0x40210122013080703350a03090c05090f0406020307020c04091a100b0f07150c0f08012c06040e0330010e040f05030c010c170c0910 58
    0x1400a05940058207038059501d15861068840503007451010000700000c149010300d5026000341880c000801d0300c90b040da03072201c80d0650050602c1c202079001e48600342000d0a075011000700e082041c0c41d040c3d25000c0c42c0b0310050140003001c0040e11801c80c9507402094908150700794503c28a00d04003480c0041c1c56650741c60b002503100400410844c022800b00c4281b83d61240112401180203402c549200d440742c4840600c0d40c50060220b078840d0134070304410400620703080140c91b9100000c281d11500c50801c1e09010b42a00d0010380000441460502801c0c1050b40000414201101e10358424601c3d8de200e850741c03100b07803c569420115105411000346504520107401e240e20400c080d0012440c00c1c164004e0916542100300e4000540d289481c8e50f100c07161110031003002020301c49010403115490103041c03103151380001c1d1000e00b01880c0c15955400384082041155810f440550081004c070201500c02002e1546100c03144444000e40c5000ca24803110540942d0b0400c0300080003001c5002c0340c0241950303 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 181151357 1250 181150107 181150127
    0xa090b070305160c020f0a080304090b010201150603150e0c0a020706030b030a0b060a05061308010c0905090c09011707090e09030c1c12020a0e0f03060403020723030f010b01080906040210 82
    0x203801b5805105954290b100c64200354000c2c03442c0c4004507151030a0014150685282482c800d045a00d0721203000e58500310020003200715085410005444c0c041e410081d0540141d40c0c1040e443c1c110030038144040c001c6400c0040120000a90075182103a48400049050310090a1415403580c4035450b41000b08400030788117900048014818800c081da60340108407103821100170583e100501c41c45c100b10040d802e004075600665603191201c803190801d40003407118040541400b035100300c00314201785241d0049801d4000301a02c2e104843c07140c60207100080092100340038410140800c5000f01d6054107000040d54001260303000507100d19908035213911840c1c02c204d503211040107aa19800e40c0c00c0c00c4148000d00c40000d00360b54001040c02e050b401d020307007190704c80581c50080d8061801c120100350301081001c182c846035010f440c00082044030400c0000581c007070b8203501d07000d00350301d41d801c0c0310056104403075407034080c2c8507100107a448402e026142d14007190042e4108000c2c24145c031500c1d00c0303900070702 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 181152607 1250 181151357 181151359
    0x305090f04060905070504030c15090b1803070306050105130203010f030b06011209060b010e03150109051008070b07061b080f040f1406010501023c030c060a090b070305160c02 77
    0x2011a51004420144d60040e102c01000c207a000030180144050312851a0140580c1c02c08040d102d074200c20010416040381c0f040c00b540301070101d1905101c0c0022101d10240b10360040c1201c508640328240000101400c0c4034440c031038180b150340c5c1d298508060003900d04881c0400b8604c2b6a0310303e152117286a030310307005001e00e04002d1080401d0405c1141071107242180ea005d500c00003004645003002411641d0301d2144244264402e458000c040b1503075112090545000440228454444508801c40c542107074024a07200e004404003c43e4080740300001c2c000d11070058005020030304000c04020036042241c4445130006140800192410649c0380e101a04144602c0c0c2030000080140c45403600200c02010400d02e80d00403c004100c15a4100143c41178010444111034000014000c1c6500464280c0840e040300303529803d07040821032027032054403c100c448605941c001c2c034107080464000c2400d041d084540d00c141c0e101180e07100d40b291089920400d042c0d00300c0d400c0c04104003020f45d00b48000030700403 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 181153857 1250 181152607 181152611
    0x5040b0a090506030406090302010c0815010c1e030e030610050904031803060c0c060c030e0712080c070e0a0c0f1b06060f1403071e0303080711030f0c06060406030305090f04 76
    0x5410340f540c00041d40300328000e2100003141541c03850024290b400ca401c00340200b1240d00c051204c03641155841072006034007400c041702d8003d203e00d0100d032420741c032100050003a400ea400d08010b040d00203800c04014001101170356403960724103031001c0d0b041c8102d00400350041154000a80000d00615461202c6020300d811a140c860b5640e80b01c500307960440025030700264507800f0003810022240942151454281810300030700c6000c3c4803140e17071104288a03c0740b0844403620384800707000000041b155140740040035160000d458030400050280f0507514420707031a00d010221850280309400c03400280216991b41d002d441c0c08900c3c3c20008004a6000396151955240300041c00c00780032210030000c190900396886000c807014105810304044e50b2124100c800407100444035a00d100041505503541420319214a0700c0d1500c085542d100c404010504078800082c0008040399a50058030200402c5011580170ba5103a005000c240e83e02440010b002c11010304c818a41340c6000c00301624107000c09480 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 181155107 1250 181153857 181153859
    0xd0204050a0b0405091005130c0e12010c09060914040905100e0105060a05030a05060408030403090e01120b0a020a0f120b09151503070c02010e010306030206070b090f0c0105040b0a09 80
    0x41d00505140d4800c0b00c4a600009081040b4200f0700281c07540849003400d03019840d0b25100c04511094420510b001c9066520880c00001c10302580c410480c50002030721000307142480150090003001c0f4035194201044014900294091251804100b03032960100f81140c413003a080107000c0a01589082102c0a006544000c94441c1e40e0b0710a1100c0240e0000020a19081c00001c0c807101a100782c0029009410401c00380010803000169070340c106503c1860195641c0d2941400c580741d403c10303000303082e8035403003031000084407002414165800c2c2e018419070502511039802e0f000481c0b2a207009170000c00d1841b000301c0009400317898526040c011582c40801d0002803100083d19084089602d4640c0a1290511000905000340322000ca01c004501062860901c940301030408420b2410013410415201c5d400c0803107034400d070041c0d0010b5501a00d195200e401074a8010440b200c2283c00c0500d501c0b41d500001c04c2d070741d0002580c108800040e140d1524090500400460561080c0c407900d09006070301d24 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 181156357 1250 181155107 181155109
    0x170709111c051603090201081303180b030103021c0209060d051f1d120412051207050d0f081306090c0528050604050109050d110312070c05090106080c0d020405 70
    0x32401c4145030a03460000b07103454511107025561034140156000c161601c96201c0061360012440e43d004120064101000c507501e00d02110b02900900243e2005001d0200020700c1010030000385060b64402c44100301e08000411002c2d4a518142e000a58800d60380c0340402c0c080e0038810220b840f098040c1061b40d04010704030300103442c00c0340c42c200e200c109660303544580c03900088070300d0403c500c040058014019440700c1d1349031100d845c003840c0200c1804500702550b14080207801c220f1170842a04020020782c0322807050030318640b500102d031000000704406040c1e20401503c60b0003102c1c4a800e40d60311607400e400e4183c6a44008001912045034002151b06001c141592100300810042071041e48200790142c0010100021f2001a40142e014003814402881b00e40e810a151405071002601c000c0141e19090401e20b4294044901641c0c15000c1c1c00c1c1c2c1c0c0540c842c02d01e0020900c9600854001d5041569482030044000c4248a400c0014154102080ea1542480c0c0288010b0f0807000001d810203450300 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 181157607 1250 181156357 181156387
    0x11211040513032d0f0302130e0103060528020d0209030a0b190212070e0303070215030a0c0207030b0406020a1110021209010207030e011101060e0406050403030617070911 75
    0x7030b914114031858003a41c1010158840d2074600b00c4400e004521110b05540c44092070301c0e00b001d14044061100c8400404009446681500c2d2000d1030f04540c1c565003640e4200d040b54606085c0015941c0700c1c10314000841e40c4401c1100e0041810341007001c0c14000d05000450b00094020394001355440d80c007040b00d00d58a82d401c01c185591a400741d00301041c1c0d0f060402200052200b018200e0003903030f0061000400084a60010680c852000c0c20b00202d60203a01d40000d00310310940c1d030000d610180844480304000b20302c0c0d0103981706442c1c42c4020020a184000207170307610040361100170000b4070318a00080000f00c49401404184000b41000358a21482510447c104100380c0f0005421035400f0a600b03480401da040210b4221100000840c03504005440003080b50020559050602a50000750030041000b5400040280300c0160603030a14106441c000d000b9140c2a00c00303800103810000d000c00d1010041807500440c40800c0e0082c2101d0340b422400d9030107054102090010800c0c10b0210200702c4d4100 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 181158857 1250 181157607 181157611
    0xc03100911031806072a0605150a080102040b07080706021306030905060f04080d2007140d14030112030302160f0c0b0301050102030a110307051c0311120112110405 72
    0xd011150320381c80d00b162801819076070600242072a5111324180310b0595001542101d03c0320b81da1b401a0b0740e520380307030510307242e50500084010b0141d480c20082001090b20801300400101003101c05040240da14190203081c1e0045028034600400300f0442640000c030444000c1c544035200308400344c20f2048644d00c0200308070440d802a00480e499070680410481d040c04080e80c40aaa0711050300d8904084e01d40d010507005030b001c1042000d5940e01180214049030507d07a14141c081241e0940c0c500740b9250600405e00c41c2024060030b441010f5000c2c103114010942c24101c24081c014440c150380c40c1030862604000122800d40c02d25900b002440051b030342407600304845078021103121902e4035540c500040240455840342c11559001c1c4014001aa404421036130840194235000b499800400b00090035845041c1d0007c00a104030a01072101c1c51160800e00d070009944c1e2810031820307400c0541c1075114860441c0085128005100610101900c1600d074081c4901490180008102d00c001240c222542 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 181160107 1250 181158857 181158881
    0x90405101e0608031905030a0906050717010807140112060e0106080603060709030b0712150305011509060f030308090c0d060b0f0d0503030105042d06050a0b09090c031009 75
    0x3124104a0006200e0b01940004059010080d45041300c4c0e00c410b0141c4141d454036441c208040040815101c1605802c00d208054000108211314245500d018204190790b01401540c02c2480e00005102207002c11118200c5100030300d842048460300b00116100d840b5880b8455044c1d0390b40d000400c031915188201400780596444040ca2414501d0405240180003081c000400110080030b00000f0801c1080300e03008001d50a2010902484080307802c081c2040d04504610300d01c030301c00000180041500b2030001201c81d0b8031003c2c103058980110700705654281c0916900300e10b40c3c034070810021f4803d0301c00c2d51340488010142c80701d43c9036103000120541d2060b041038690f580c0314410015a49840a200008100d04603000c00740c00609a45180d20780c003051140300e12450707451540c00707408601414150f100c036600040c40c00c444602c401500009102c030740100d6006405140c00801d040982e0070466506600044c800d0860381c2e20200140150307400245481c85070f6050300340c0010601d1260142031041c0f45 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 181161357 1250 181160107 181160141
    0x12020a170a14010203130213021e12010806010812030406240303020d09061718060907030614040b1605160302061b0f0f09010e090901140a150509040510 67
    0x2030400b040c00002a54051905902c10000e0104155012240d151001d5050301e200e0544150400034000a028000c1c00c0400042058080da04102d6550b00030319a8a4001c59180c801d41d032102c505582d00c40342405001c02d2584880c0640c140792a850b806036900c50310814010aa03d0001100c40b11606440d849005418000000500800d50188441407010602e8644401d401d407034003100038907203111a82d50340703000029400801c9400c03a9680a428180b06000c2c12540d040c103000102c075554400600c000e03170f0414980612031040f2082921624003a540202200030141c03207043c059070703c501c090091a82486020090300307003501c01070400000c2081c0250044d180710f242c00d2082000242110081c2480207008004680780300074070200380d400e49041d81d41c61540b070342d0a29005955584403a13601da0b500000707840400c01801c0781500300d4106004106040650703900c40064500135a0901c18401c40c00420400d82804241032044c08a54081e01440c103c4401003c0151200c04542150044d004095 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 181162607 1250 181161357 181161373
    0x60510020c03150705091e180412020a0201050f03071107090c1b050a1403040906090c02010c020d09050d052104080f03040b09060306131a010e061312020a17 69
    0x128003400550079604007440f640c0c0c12840c00200080141c40303004900c901c10021011402000074905010b43c109140140084500020000394010301a208407001c4505944c2c81d1107a0754039034400b0030f41103100c80d410385401e418240303105103815254000404a030200300c2000904c0030142000c0082100a20250a001403401c0d13045100070803001c0070440c1024181640680d501c00640000b64002c041034026a203401c111040e641507500358842c2c4c2d40721208150400d080410544220341c03010710301d282250020803009243c100c2c1640c03074450101c4004041189040104154100458208a0740d4400e405596a4440300400c1c50003a41c203203040c01d4400f02c000301c0e06001d411410807000401c403200000440c1051316200b40c0c81080d02c00d400515024520101c00308410f615581101020049448000d0144d4031441c4080220003180c004428001881c91449446904110084078000540104214076090500c440308103c2d204142040360051800c03c40054460b9610040d00340c0c40300c000001d803500c8 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 181163857 1250 181162607 181162609
    0x109060209120106051c080d23060102010911040e01020f030a02041401020609070323010c170105010302040506040306051503030a020d02060c1908071e080a0608010c170a060510020c 80
    0x42602d444100c02c26071401e00c040c4115030300d80d00010000c504a155180c2c500c421454690030500480400e0603a050501040e0403074000c911216100001040150290710355510004909031041090098144030420009103041d0502d900b00c080e408030810000751400b83c182c1d01174460b650003240da42d458250b0100701400f101c1c45105400120890900c000c084c0340c1481443c007600d405461000400c88004064400701070b075004c00d8194414900d0800030810312800d1030b400b501080442c0d1903100303101c00780340010400358042d109441c00d83d00007a04d40d9003130030b08580da40d800401001d0a01511380d01c4540500c41d0035a02040100480202c580c06400016009076010381f400a000d801e10842030400c0c014500d0b10340e8250a0b0141c0b00049103440525600c403500281d80c15115410304038a94441500c0c1c401d041d5421110090294032098070070481ca5650340c0595007200c1003400780c0c8001601c0b0700c89840030a240d0070f81c1160802d507414400945036a42e1782c0014682e868002c0304c00c0c0560040760b0200300d2 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 181165107 1250 181163857 181163869
    0xb040606020705090c030907050604150305060405070c060b240a020f011a0d0c261207030c0f031107060309050f2d070f09150b0c0c010302030411030109060209 70
    0x1444140020b00d03025042400040f04240b00400906956070301100189800d9001c000c00c500401015181d960340b551104001d00c42001c048451030040703030520700401c00500302031044900c55401d9555080441d411591400003a20300040415400b096001866200880d00c1a46014842040b942c0d0342c0e580c00c040401070708003200080d1580352645408a914200001d0816112850008641060300982c161400d84401609070304003d2000d5002e005034640503c035098200c0c0c103819901c1c11070391004882d06140c0b075144506a00100042c200d030520a000482c00f00071203524a2080c208129100c010056042c036003999036201d5400a40c554141d0020300005119140c8030a82c0b12000c2c1ca0101c1d04d0556641c1e40c41d00c03804000c400321141c501c0609181d02c0520002024180c68140414050b82c0c40722841c01074006c03580814941e6802c9030001401c0c4510400700d900390154600a800c030180c0c000019802174200610944640c070060340c019140760707030038452109010700c01c070070042e00d6200d443d0501c80 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 181166357 1250 181165107 181165109
    0x80f0a180603020c0d140d05191d0f0a0503041703210403080705091e04150e01051512010b0a0c0212060103060510082d060f04060f0209090a11040b0a030b0406 70
    0x209000c0525411000740041000300c3e01c85060541001c00c081e120b4501401007a00345069135000c107460411042e02e5012107040b060881c2009108032f40aa5801d200b1068542151482c02032459104000c101310481e4040d0005074501c000f0010f690920103000c06040c1070300d40c14035101100114000070441050b400c100074580001c03103440c0007400d299511010070800150f84a18100b142c05e00002c080c1295206d400c1468171610004922101756641e26500901082c00e000c1c66200b400700d50b540c076400143e00c1003600e10301810318580c6031240c0d180c01c807100c1c903a921184c0500104040c0541346005a29202184141c01e0b00040081550307614608214040303a00c080d08081c1e1742030884000f0020f0050024401c4400054840002d106410701c0b501d801e40f032801c0100b1140c143c001c0c0400c10107507480c0351203128891800b0b04030a0140040c1c102d075100480c4106000c41e644030010b00081410000d140e880305c0103402e6135074859403800b0f8175030403890314503004020341000194640da8041142e040c1401010 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 181167607 1250 181166357 181166383
    0x3090203101b0c2003190507080d020109050601030609020f09090607080114180a020c06160e0a030c03080702030a05070b0720030303040807060615031d0604080f0a180603020c 77
    0x34036415039281e0001c00d000b002d0b1440d800c404c51481210907070b0148404158184081c0607060103440d1803410701d0f1110000e12613401507010320301d04445070f80d006000d1564141d51120207004c060b82180c0d9640020301000c0e00903030b0403402840300246185c41e04042a8000c440040c02050246010030000344181c0051700b00701038204800008810585403101d103c4a01a0411074400d0030b81d0320244100d009002e54401d8001038401d1006104400015410030800302a666888140e000d00d100c00340070308050f44c1d03c0002c120104440041021400c498050b040091005055a03100d20312511801e1a19603140c002c41c1100100203034010410810103000e840302200c10045048607400c50b00000e0b200e02000340060b051040015060341001541c0d40180041c0440111000c405c0083d14401002800402e00341800041d680c601d681350a070000030b083341f00b00d600c00f01487c500700640c03032440085d130030100c1c0b90380500c01c01d52414255080b82c6181840034100903540141c5030011030540302c1c42c0c08400b941d40 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 181168857 1250 181167607 181167617
    0x20d2019030b07112d010603060c020717100c03150303020d022b050702011404030804030201030f09020307030204020a0e04110306090106050a0801050d0f12030504050705040c0e0f0103090203101b 86
    0xc108010200e6082c0100e0000803524417100041415005603044610740c58200d9441e00d50044100314456002c00c0152206034200e0342c804ad1036110000d460b0f00c41c20701c1c241d4036610030946200240c1007034200740844003046c5070220300c4440f00c0400b022003d117250012005a04043d0101d408113504001000f1f55908400052010800c00520707000c1001588046038100000024828250b901910700031014268150190750b44a58a041c03210042c1c1240c0022070001e810000d15504521080c0030360929150004c001d408103030328603400c02c00254000070b200011700568a540881079540c0748a540a240f00c0c0111981d074901d0204200207004105800c400180441402400515a030000d540c606540c01601d4068401d41e003400d00d0700307107030039480c00080065494104485031258150406ca0086100301c085640058680040006030340c980c2d0101000100e01c0e500428052a00340003002414a06040015496109402181c1070150b100ca1031540c10f03445110880780381c10181e5640150004078500 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 181170107 1250 181168857 181168877
    0xc090b060715051902090604032a0902030708060109050f0904240902030c0103050907060c03090b0c100b0604081005060a0308041508060f06030a090c0503030a120b040207020d2019030b07 82
    0xb47d41c2c1d006a01001d441201540c1c41c074145030b05460030b0350610318258100c01c0b400503075445004d0b000c0e601c12a039080005039003030003080c2c03294000ea0324102500c2d00148001007024048040c01041c0c0f400a1054a45510000c0b840100788040070344032035214080b80c0f020a00361968014586814020b8806904042c504030401800c00d0002c0741140a070f81180c81c0403000c180e21401e0071030f2180040c2d0011030351000005003503102070000203424420240306800500200d00440108812802036210702c0000d038000108020005025500c115401400100b5480c1901e4880d120564035801c1030300b207482000e4803d1941e20082d600b00a016500030022038203403480303c3c41d05010a0329408040c08242910b03840e2140c850070420b10440e0040501000703000c881c1c51b80341c042401888000d41c2c0b415401c0f8589031100d0a101c9080600840302e40c9500a02074207030441d034581e81c104d00080846510408076105681010041c1d641d07000000038401200d405140407821402c1103103000c0c00151000090010250f1 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 181171357 1250 181170107 181170109
    0x70203120708070f050f1b090f0403020d0c0c081c140403050c09040524011502071202060c030409050f01031101030e0d0e040605090a050f01120c090b06071505190209 73
    0x104440800d9070040340404c4082031071038128074007610301c201d0741d10703900551803211444220b45031501d03031401040381d00400300d440d10107013080c40000a88002e00160800550407012394000e0a00520b1107200b0b04034101603036540d00c001810031800b60500700c3c000c44c0440300070807041c0d440552070040048a0307507060300d0145035a447d160340320f400b003801c035005061500009050210500400080204000c1038440c50360000f031314541001000d0150301003140440300100342c0c1d00c2c80000c5c1c1100380c1e04601400324500045408000c2c00b6005401040910700c010800070070071003540d0048501513180c120f1840119410340c40d103041424100009141050703e0101c089220800c000390703001ca15002c9040002c941d4a00201140c081c015a070000342d080507210302800150107055024500c00d0902582903c1c032a40c8800b104110050f402d007000c0d20f4411846001d009080d800c0d8401030300044002c1060703107446a95602c0010340060144505030b00d5a4600410802c103016001c180f000e86e1001c1e00861411646070 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 181172607 1250 181171357 181171373
    0x907240f0c0305160b2211131b030f062c0606040b04120c080a02030304150504050a12060c08192003090a12020307030c031b12050702031207 62
    0x2060380400141c036849400781401001202c1c1c131011056086602d50701d0700d0401c070740b0020060b290040c4510020074210044280007041500042e488018410229203c0c4100583e511012620010f11680c0340c50081a000d0380403000d1540700f0f0345403404a507145d40000400c04440d0b550307000d03105401d00031900e00130740c0d00c8056007495441c03c1081880000d031190000329070707180034075046289100c0d00010b01181c1d0311280400100403030700c66880d0021403030312402c40725292490010002e4155105001c1844040c0f460700011a550200c1d04e40541400e030340e03100050104080b61f01030b2500100c45101c0c0c105014160281c902d41d194541040c0d01141804031030359440a0003810300d4840c003070f501c0c00014000420011b6107002c50080442468036030030043e05c4c1a45440c00008200c0d245070311030a9400c030090003c4185d5240d680c254070780c1c0c030108940340c03000e41e180340405c4100410382500c01c9403040000c0c140400360b1411076160303a509444401502c10b241ca000503115003125513020500c50f080c0003600f00 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 181173857 1250 181172607 181172627
    0x806010f0303080c030901090212030915090109030209070210090b060414150d020103020408120418050622091b06030c03020405150f041a0304020a090b130b0d0803090724 75
    0x14101315030341d58401701802e00401c046000203510802078404140941000000b07000c581b1000c60ba4090182076601c22540b40b440741c80c0c001070105c0d0940b00b040000d89400d615580c0e2012039030042d0b0383c0e42001c0403504000c03240e0300300049030103001d407505100d842c1c102440f9194101003101e80d800f0480c14076595145441c070000300c54503c602c0100010b03508591103601510001d0031800201c40f042d640d02941000150454040e81108030b1981401c640c0d010398034020280106005407450156800591500e006001d0160101c4103858847d0350f07280020396000750035161090030b002e1644009090000080c00d036041c0d0b1761400d0400d130052209100c00d0703aa00441000c80340b406011140d40b00030151200440b40a5940103442c41050400400c1d03d0680410045204034402c507010501c0d036840b070000360112011981314a4201150700455078002109034018910054000d102002c0c4440507685d0014540c0201c03100d6202d900060030801034054400300d0003505000d50964050580341144000b00130f400b030 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 181175107 1250 181173857 181173871
    0xe09060f060307051c05040203210304020915030d02011a0406060503060d1a0901020702030c011b020910051309141207030e13020d0506100801050a06121d070806010f030308 76
    0x10002c041105140074400b01c0c1c1e018a40526050300c5144511141d4000301002c48050f800307806124040c48111003028100d40100c00e845c01e101d81592200e801b401420080140000c080d0b01c0009550542130760104a40c00524042d40c1c0003084030b00c1e1105100c2944911200001e00503800c000f01400a1900403068942c080c0b020344006404040da401c01003900440070070342c440c801043c40207000110106400924031b40c3d0007502210b01042d40440115041d46401103185160441c001403540107183c4041603d412400c00c122108c101502c80300003a0010980303a01c003400096803a2194810800d46503c00006480154058903e0b54250482d5070f0551250300b20003010856460311805080d52480c036200d0480000d64000c41d15941642c4d600310060801b50380f981d1103103404845c0201c5443c46426031a05940d8098500356081e0b00d0300c0410b946600c0078803102100980c44901c028a22a11078440450f1460b8003002804002d24254145040c80f6060b04101c2d07160542c54024001b0079000405d00e90400301c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 181176357 1250 181175107 181175119
    0x1e0501030f0b0a06080a060807050d020f030106051c021e031507111e01053106090f05071a07030c0308250e03070906080a020405190c0201050103030e09060f 69
    0x500c01ca00c80000306408040103910031060203010600e40d901150941c03184a0b0131404100c001c0d281c000700340c2c1e25003c502c6140c2c0c4c0182d01208050040c140800404034543c005000816a41d49641c0080c00304451106141c44055104907140e0541c03810b0f80d5850280780030320b1310407522800000d0109072681a55544140d140600802094415200d085081c40a06155043d10920112240881d0070240320001504d1150b0070030b030204203c50041c40c080390056168400140e0100e114103070b031403845c242900050312800c1d52618442e0121b00c41072900c0d00068490409406034500b000300e4020005e43d400f140b1000f0a400740321a00000f900200200740070354040c1410301603592001d03421128000a0190400c1c0b040032070f00d0081d15650030050a032000a03044043d5501580c94081070360131030390300d40310740201030380450030308400340c1040e41c4003940114521200416480310385081c0401d030340c2c0070708106d401070b0755a000401c14150b1200b40d442a41c074048a800055041c001c5c005003406061074000c903c125 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 181177607 1250 181176357 181176371
    0xf15051c0e010504020a0501030e0d0809010204080604051005010602060403080402091b121501020c011d010c08131802030603030d110c010905071809170a02030405090c07020a1e050103 81
    0x54900400300a600c4000c207100c00c1d003484903464064042a94100d01030609490046415070090050001c0c1040c03100c003e041002c10102c04840322400504130310308556007000003203403400d428405903100da801307035004042150300541d4900c1110416844081150011000e0000296110702d43c5500203030111540103658427020203d001801c9100184010984000b440c20001c80258065a201e600c1c2d102a014010a041c4010390b107948599440500040c1041100006202c8040040d0fa02500624000d401e6003515500c03c000c44c1c3c0001000c030030b15840d00c40100203102c15014070f000031030301c42c0704150300754100702004c81d80d00d00902c20105141c0b03486180f402001c01d0f030300c030075100c0481821000b88210305460405503201c1e251402075a42d00105220b028441b610107015102115a001c9580c2890b54110300311080c050b001440100c007140810000040c2590720100da45004810104000c0e41e100f841e4410040054030310307407015041220b20f003c880140f8103002c208908444080c200803900e0 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 181178857 1250 181177607 181177627
    0x30a050702010e220e07050d0308150909070e13030c0f020d02150405040b03060c07020118030204050f0601080a060803160f0813030506070e15160c0602060702070f1505 74
    0xd982500d03003ca4001d291400020725881032105042821444042c040240070400c0e000c05860ba00b0720300555030032410050a00000910a50780198060000301c490b501d01c60307007000020f402000c265050710fa00d0344155410302c052841c800307506030080e0320b80b00fa46c06a0844ca40d0702910034034140c0700207032912681b00890700645d159280350300d41d91781c1c0c010b1840d4202005400200b000d81c0143c0986400f55143ca15088803d04002900303500403079141c4c581c0c0c0e00302116540110390003000321359111072407800c091340040161120300a0310300540c0d040001c80e00516051000420702000240025501d504082c0108002d0f0004800c941c404100c0e50408520031000c1d00b4440f0107100841b200030005e01c400201500500105054001540d12481c15505280c85204044070130b02401e00e01254040c01c01158400740c4038102c00200039509240050600d111402d84609540e14001e80c820310140c2c10140812400d00c1e41402040d01400e444026450310a081003058501c10301c0e450866014010000b80d19050 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 181180107 1250 181178857 181178867
    0x90e091e0c19060f0903021c02030a0b090318010f0c110411070503040e0708040b010b0912100e0601050105040b161a0103050a0c090504030e010f030b0d030905031608030a05070201 79
    0xd80354003411407116009881e01010640040f80b0800300007030303d501c1c860340145105041e03c1040340d03002031015041402c1d1090314100b500300d40004990500c200a0407600084110000c4e6200301ca00c00083c60f1100444468006a042012106070401c6880a2078010841d0000e144155241c1c0000381d10710410905004240100307104e01c0c404107560b10214001040042c000024416a840c1e028180c4d91600c1b41c8000b903e080c64183e400920340c2c40c0d1800103014101c0c291010704810f060061102403820750300300d0310500341924032110361041a12441c01c004151020810f40d40100003e10f003141c80c280c68840884540c0c050080b880145015041140050016130103152903181c0451000c038210796901c0c07800310354034ac03009442110181100200010b4448140c8101803003103400d512031280c0c2e140d0903001141e0382040b000c060818590b4074a492189521021351440d2950700c0703131b03c851800d641071504141c600b11080140c41203000050360140701038580071055684402d0300b03040050b2a07070320510060f90307 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 181181357 1250 181180107 181180123
    0xe030a11160806041505010b040e071b05030909070f2c0306100608010801110a21020c01021e0a0c0210050c01020f0912010c0503190609050115090e091e 67
    0x92a0780000700b84030a01080341c0340140e1043d51341d4140800242400420743d0400d10402241c2441404104400e2403035202c46944020b0914000101045810448440001c501d1040d18aa4800709604240342402c070443c580082d00c41c244466064014000185040d889400780103a400c54041000729070141d1501c41c2421403c01400e03660b0604d0310400801c6034100510404001507044000001c030380006100d850f1880b000c52070030506c0c00002c03c20907649c501013a11211131510181c0c450032540b0980d071010340810010340340003503669000701003001c0680044550360310b001b20040100c0040702e80c0001c003003084554140ca900806240140d4251407074054801500c8140d4000503107451410408802410000c1040b94140144180c003900d05003210b004450311130114030100301103607094a0303581a03070398401018800414291780b0340001c1004d07524281d002c086560901040104456040503116010700032074549040c00c0e24001100a41d00d9100c050b041444214030083c80e40b0303d0341c091215007 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 181182607 1250 181181357 181181383
    0xf040c0201091502250c030314220f05010905030706110a0506070801181a040e07080a06020406030e12071113050f090d052b090b07080103050d030e030a11 68
    0x180060a4008440000e0b61004c1c0002c80c49034003050305c1d0280452500120811240c010103120159405d540e0143c03038402104082104c90078080c00482140a25041c40c11124903070b02d00c44036045482c040a02e040403225810050620070055014400c0f906c00290309412940c152400589445140c901c1c0c5082840d0700c80050420b00800c4108140e9540103401e042c1280c541d076403403625024920842104480080540c00212a414680342c2c10b01d21345604042c1191a00d8020340705104d543e503018515002643c0c204a40407600458108100d86d010b1244441c10649000038000c5505042c1c80090a0f03c134004004214800780041001c15860f0790305851001891000100554103007421154107001c401c51300c001d018843d01041d07881051044080d00c801d50040040392440a903a000060301d003804c03011207850205d41d01c0000e90046490482d26601401c0700da01c44800d55410341c14108c2c00c00044101e64014903050a54402d0103000c00400c4403000005480d258458601c0556490305007840b800700d107 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 181183857 1250 181182607 181182623
    0x6050102032104031b08030402150702010f080414030403110a09020f03010306022a0a050c01030c021513050105100f0b2109010e0303011707050a0503060403050705010b100c0b0f04020f040c020109 86
    0x100100108000118000c9002b240c80d12a1078940c0041c1d20024805e00340c000740084c10001c031001c2031134024070a0701c0c0c00500c2030909540012061404510350303003059000703540715602407a1110950620311100b001a0030003d406515210001640002901c41888003c000c0c0c0d030300140d1072800410000c06014070b4107145140b0104aa41113082a503140c0355803a05407034038041e03c4484032240d8041d1060180d1081e868010b003071444215444a02c03064002040109070038443d110030400030b032080c46014841d034980925480440c1c2000c0c51110008900e4000401c115410803031246444001e841400540091009100803561092080d502400540550415501c0b0220020584107104143c60b8841c4ca1100b04417554166581c080000c0440d25120340d5815412450114021a100b00c00134900180240d001107aa4a41080450f00d1240003015135000110403580c0d410800003403c20315908106c807061001c200b401e0940020304910702c2c00014030f11540e039131420011894002c3d0003280c010758205e801c07 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 181185107 1250 181183857 181183907
    0x509012112080105010305180c06090117040605040b0127090305221d01030807020409030203370518012001060e09070b04030515130219090605010203210403 69
    0x81d02d41d034020300440380805d00700030000395600e4840b01c914891003c00e00042c82c012003218140401544031000242c108003c1c03100d101c1d035500320030043d10700852203401c00080074505030803c1c0c2020001038100c0440c42c1034481c810600c09566a10714014035000810008113000c1600d003e441500c2000a070040c98610389134801003090407038400d407044074216080303864195090036007021481002d00004111030801c2c8100009420181c0c8610b06061090040324507204068000c001e5141d07206111030454440f4100902c00401c3d820008210754500f82002824600c0c40da109040c00710103020503e04100000180f401d14500136005150003103030a000030010242c640c00224255401202c00072801c0c414410005041c15404040b541200d070080043d00141c103041d605207042c842d02074400404844101c44100241e6540c90024030b06110005455a160b458880342d03209480b02030307205038103541090015044013100c41c0610b42d0720303100c1c4202001c007035501d078902074a15030342c1221600490021400 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 181186357 1250 181185107 181185143
    0xa1706121f060602010207080f0a0e0604030b090c0103020405033d0905070806040201090605030a020d0606050310150e0d05010f020c0a03090902041202093103030e030405090121 78
    0x185903440c440c0c4901c24012281c80d854103078240d100b4800c00800034142004103c480055280c042d2070982500c0c60000e00000700c00c00003c0050b00242c2040d41c3c552921824031070200000c10084850709020300341541030901d0580041c0e00c072039403940100d100000307084417a544c94005800110703c04a1444a0400c12080c2e04038140050204100c00c0f5043d10650310003090301600061070902c1958140d4480700010b060040884407604054044260343d0303000d001c140d16407105809000c01600c0c4a5403030b140c40b45000b190701c104030390282d84a10804440040444521070f40002c010030031280980d480b1007040c0d020300e84103005210803500652107601c08200a07540600101f610180c2901a44e1003402c06c40d2a8107058040f44268460b6144644980402c039005007042c0014503407007800070282d0301c2c040321320405414480b0600d592000c203d84425070783d041019054070442c1040500c1100941c20281031501140c00480103000720000400310094401d4180006403001c01c0681d40000e05c4801c02204113 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 181187607 1250 181186357 181186393
    0x20702010c0b071124012c07120b04060302010e102a0b090d0509040903050918160305160c140d020307030e0405041a1009060b0904060602030a170612 66
    0x40c2c2c0300103140143c42d030356000440310700a4000745d0300c0c00e0300c1410f100f85d20b41000039240c1e0f000c048650000b803400c0c0361112684904a02041e01c242c2d003a8540248018010240504a4401c1411a031040f480c0080500250343e001c030000c01d400c4400d4440301105d13a10304a003a200300c6030050380c07820480a420100072800003d0005500f46a208510560b41c3d03484000c82c194075140084410800228140040101460a03800100b1500d020b814050b00c1c0594a81c04100400581c0d011018000841c20a000c81310204041c0d0b04400c1842c0d2070204058101606100c1b250740d0190100f4040010f600710010074030113002083d400d0714885c1412a02e0700e400d81c03a40607440703410061054010031803200c5d083c009824540217841c8209c0d40803010341145903000f40c2c04a62031320080d040d00610ba000c90408904049540b1809002c2d000071002203454000c017204006c01d88465411031000c642081c8003101207160042d02003012042181010b0180d592008040b444020311201d2081c0c480c4900c1031840d00b052121 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 181188857 1250 181187607 181187627
    0x5061303080f071b0501080c0304030f051e0a0801031401060e0604020c0304080a0302062208070201080a06090204140a0902040b120a110f190e061b100606020d081005090604020702010c0b07 83
    0xa8a800400d40e81e48108d000050000711b5015000c10fa030a450940c9491141001344171404009840141140e0030361f0f908a155004000078801207075a580052040c014507803455542c0301c0541009101090a01d030a100c96010003a1009005e031b500869600020202030045d02c0141002d034045460003145410004d6840105452051001614040600b03944032510510a2556002110300389411580d50044030f003480000c00144200360785440c00314401040d0f00041008007040740a1620b0503807080100850022070b075200055070340c4104020421100d82e04259000800c2c0d800007150b640c1d41e8200c40001400500f14000319201c0d0009840000b4810407020f041c0c40015101149011007060105440315503a10800c0d0354000e8082c81007100044011016202d0101807000741d07910b800e00150010140da510760010b10240e041600b851908a510100c00c44c1d202240500c0341030903901d03010115031082400b03083c0c2030207075400040e02c03402e590141e10019845d41e40f010700c12403a4035180744020203103002 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 181190107 1250 181188857 181188859
    0xc0a1a0c030912071a0906030103080a0e090108070e090d020706180302090c0c0f0c03191103160e130f0201030c0215010b0d0e0a0803060405090a080d0c0905061303080f071b05 77
    0x10704845c5038029052605564043c50082c0c1034502c0e603400e40e190b10303440c0d400c1903000078200f06640001c05400c2e15590703030a5000b054034800910300e40c3d00b044c1400708010002040150300d40e004e0252441c40b141c1c00501903045032410304140b011020307420340f0021102815080a900150308100b80a004905d600042082c050150156100709002e880da5540360402c5a1500d41e01d07a0022810003501140d443c0c4c0d603005907114400c8000303400f0851001c6424005222114201c640f4242c908009010086c00060307842021003503640d0030b404070340d9500c8085810945000c0d04042c1c1c0c84051041150003001442e0a8030801d80040c2642e40c0d440307910a1140d800170308401c0403e0f00f80820031036810707c00102c0f1200c050b444010103007503176611014000100b0b001004540f00c0e109050449000c901040010304e22110310f00c0b4003043c00b070354041015049111075404203000704410080a00000100344107481035a07401030400ea07541c0d40c4240700c211280503608010301a5110524020700080080f841d2000f2518 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 181191357 1250 181190107 181190129
    0x60d06020309100c112d060a15122406260123040f020303120a050105090f040503071205040b0c06010816080601060e011407060504050c0a1a0c03091207 67
    0x102c1c410803204181403000102c0d01d64001c0100d80c3d02200012030302e8000c5440092100320342551b807002030f032401800390703600303902c003584c0791206e100c440c03001d08002d4017522003c0340303428000f03103d941d0380c0c00500307950309014414129298240f819400140c008038010442ca05240c03100c4003054070f8448040240d01c008481c59803808200055071442c503402c40c11407200c1c001c84142c4a964949400c0e074291038031401203030300d40000c0001d550111400050140200701c0c3d80d00001e4190706200034440c1280d0080c0c0b00c10300110310f01e420000003800000c00c8809a9a1081c000b00c42d160308000d041d2200c2c00385804c11106c0c0321002c01c4024401d4000541c4d1812035001d9403c5500c80e00ea41e0060f100c10080b140504150341c1c20120050110301c0c09601341e5102c82c1c006240071044000c202010603241d411075201241e007280ca610500080c4002081030083e050340442d4652201407030040c201c210030f9006468400710042c0452803900c543d13014001d84030010b2000d80f8200c89600e141090300d44402540c0140c58000d4 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 181192607 1250 181191357 181191371
    0x5181c0b100e0702071a041a0403050d02061501030207020f0a1d0a0b0109031e0602030a06062d0e0102030904050a1509110f030c0702100302091005030f010b03060d0602030910 77
    0x182c41503141d140109000c0e006000503034108054078405103a404c1c10f460030701500300800140c5a2110f0020003440000d01e0402d911203046140c03890030000000d84040455100300140008160403034505017040c4401d090060369490244041000810300e0380303017285d00c02002e180004031041c0030062020030009a9021480603501c0050039800c0b5800040040d000510602003840007036050380c4d00449020b0400b900502c12401642da08050b40d10850746c54203115142c50042000681103503c20900c0300504480f0890103461802107541d4003a45421307038007084006444c10607264024030840e024080e000d40103008620b01012800094840340341d050090140e0801c00180340902840780003885400001c00301e00e0407000c2c10380c880c05034102419180d04c100e410808440165030704101350324440c0d955280943c41e140c0110030080c03020070520030901030000030020040399500e0504400e040d0740016858544030b403174031004180401c810002c000e14540c4000240081140c00007903c2400c5500c01400f40302d25 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 181193857 1250 181192607 181192619
    0x10c15050403020f19050a170c01020720060306010c20030a0f0b0f04031d04020d1a010f0c0206160302030c0a050714012f010b100302071403030705181c0b10 69
    0x40b03141d5417010b03009800034a00c510004003211003008031001d191400a041c4080c1c4d401d101e007207a12050b81203c00800165072045101c09030841001d5000d0700b2541141141307080000a00240618400200b4500c014405c003121100b00c2d5172510705d901e1024044400410141c904255001704541d030a560b0005814009804d0711010b1481501c516459130b100005000d442c4049102e50300c0040600b41c1c010b40a0141c07080e408110311a01240354007810800c803c03903103040001350580c0304088420042103c60052035015880b420204e80da1182c034415491344074040c40c20124114000d480145880e8000d2221920901000258103030998010000040e40710340408015181e142280081c071403030b00c02d40c2c1403036007c05090022020f40c900c401400030a294000c900010f99115000e1074110201c3d42c081005400e01c140c0b1056203800d2400a0b00452440c10542c901600314040e04041c41da4100c0a000e500c0e8460326a0300b4240c800c40c1c3d10410001001a080c6071801c6c59240c11030700701070b070384426580005035 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 181195107 1250 181193857 181193893
    0x6040e030406050708031b070b0a050906010f1406070c0f0603291c02060301060f1e02060f1506040902070218040c1707150906110a05030405010c15050403020f 70
    0x80700e03056299a49020342c156640f07440751b000101a02194040304000842149861004203010307485114044500c0c540b15003900c08490000d40710f07142d0365100310b00501030950341000c884103480c29245018049d0401c00d0005000e44580303038000340040c0e0701100c0081c510710000c8884c8291003580d2800c2c02202c03140c150b0382558080103207843d403003241229a51035443c10807882040c82e00311121004250b0b00d2050b000728800380d20a9104d00c002825a2500000f02e41d80700c10406030080c20a001d00d0706449080310025a110b2019000040043c03112000c140c024031050f5811207402c01c0034081e6612030f0360b40c460600007500000c1080e40101040d0408045c004c03052500705120f640d0180c00070b00a54144000c2c00000c0302800400031151081c60004200100515a01001e6001c4c40d40e458100e9030030050010000c9401c000303c040d5950001070113100290000c026030742551420302e07100041c00c2207400c10382980f095003403104145a01d458144801c1c141e0209184881e00004401c6520034030030100090070b = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 181196357 1250 181195107 181195109
    0x60303080f240105071704090e070807060809031e070308060d0b1801020d0501170d0903260409020c01090201110c010e060f040503160302040501090b010c1202030c120306040e0304 79
    0x40122104035071050101005400510800320615025040c8142581c07240100c28000304610460b00c000b0504000f10541c0c0e0090403604440310001e882b00c6860840780c50f9540c480c40c01403800f8002c0c0d450000e03a2409007042902e02040641c0814020805180318400d0258013859041d0000b0f01e01100103121030074455000e600042c2d001c610b80c0301c0c0b40e41d01091081100004042281e165400700200102c070001c0c2c1c0900b0303020700107400220200250313411803513203000e42100e11841170144601c402c002061802c0244104146841074228111042e08142c8885d4032640d00011001840441c090300c200c0c60540c0700032822807003030300e80302c01101e4044101541c8504116100d4005001da41d01d69986081103c05441120b52180c0c2d4141401c0d03c840000f030402c0c274811150305528201c0c510800552400e4000c0c9401003800140401c42c0c103440c0c0300002d100148203a401fa20700c0c003043c9030030901903108008a0704030204181c25a22440e00300042d40541c1e5100f92480f038407039410321210119180000c41118 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 181197607 1250 181196357 181196371
    0x10e060f071206140d060f0e070503060a0e031e130b0c100e031e0f0c0d0816140304050708032a010c020717030f120403020f070f060c080d0e01060303080f 68
    0x20344d0980d80003081004a090300030049a100c0e0f10b03200b056180710018091200070040d107002509159045c0028980f50081c000c0442410078100086100002001b2044030342400f002c2c0c100e0031101080340b55181c0c00d03114103060540507082990300042d0b06d103080000342c20503080110076150101141344a440545040c01c0400c0c0860b001000704906c030924034403903018042010101c3d80e050a08890550707c2c0b94100420407030369508a210380781652035010a00560181d030030060560801a440c8004101c48101d0b168034404510000204083c0030082043c140181124400c0365955441c4041c00c47c80c24110038100518801c001150265000c0180101030a8180c40e500815074540303888941030001c0c409100c00c0c04140810002d14000303144200003006d03507014068000c3c5081c10b1614000340f410300d03241c0c0d103014103070031040007440028107159180049889a141c80700d03c134005410028032a20034034860181486c038105114020040640044085074040e8692095503610804e41c0042c20001315051 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 181198857 1250 181197607 181197629
    0x42001140f090a03021f020d080f070c030e1e1305010b0f07020105250c0503030928080a05060106030c022b030204030b04062a05030c0a02010e060f071206 68
    0x80d5082910002d01801000244071020540c0c1c0c9401103102030300e90b602e80c220010210707055510000d0701001214408105881c082c2414030301141c00190401e405020b080412440000340400c2c180724005042c85c45c0001480c2c40030700641a4082440c16117030315900e6004151488600d8510300c0c1512030541240e102c802e5036403400c0021549410325500181c1c01b2414004284020000f0301421280c0c42c409101c603806d0a140b50703c40e4140348103000b145a0005201c3e0b441001003d520703482d02842255040c0703089082507800a041549240050103039040aa40d0384183c01e005000d10000050041c101c40b001c0d01c08001a54025504030303100c0052026045182e02403903821414510345410040d0a40080d1400505090b00d0340e561810304802a81c0a6035066203820211244c025549035510760900c43c1800142060090340016107140802022080e1101c4041081c0e2041030003900a4001d00a5441c241d031103900e4174080d004213042040c1d40000010391003400b100440070075886120700361000c000c12 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 181200107 1250 181198857 181198867
    0xb120112020105130b040e101503110d14060f040903090608060102030d06090207030e01020106080d0e040f0603050a152c0f060903220e04020909070b0304200114 71
    0x300030102104010101d04000e0304020341650b40304440120006401e1240b00d0583d2a407502200300e80c2490064075480580e07840c2c90003000115140549401250180e043c049289044a65a02ca05002d07030158a2140786c28403040d0611418452070540c80f5000c110351203424a01000c0500c4211009120001c0203c0c480070000e003c0c1c1401303848460f40c0824144105c07441c1000e00400c920690b442c41e0711960303241ea00440c6c004100750704445003030360300c01085c40200007075443c246241d541c603089100703030200348044440c0300ba42a4035540c0018901903042c003010b1100c9540d82c0b5102d583c690b10040b040c1d665140120701c1403940040c03401080d0301600361030560819403c07c443c0c0c0c10850304592109036403c0c4104818440e401c9001d2118501c10803076400076503103541001c46000c04d03c0c152207107a40c4018040e04000c0c8820040454887c2d003103901034130070406c0d03550750032801850280340d83c1080d0401d0001008100c10401171240100508500e031400322a0b0040b40c034010b54942d641844626007a07030701401b17 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 181201357 1250 181200107 181200119
    0x6050a05060c03191e031e09020a1520010203010f0317070209040809010210050606040b07020612041b0b0304230c061201030308010611030d09020103110d0609060b1201 74
    0x504050304400c2c2c152480c10f111820601400946007144402240502901074000b103006100490349912a0600340310804819500e80b503003900810702401120f0361a140b031029519482d2041000e0700388000c2261a1665480019090054084c018100064081040d05007001d060082c1d904880000311040301090540e6aa601c640d41c001c840340c07039104000d0100d42c016950b1807008500a5010784180b27590340f45070000082c2030242245440c1c403480d007440d0610007280c07070302c03003c94040b50110740c0c2003a143c60f124400903402d0300c5810032a120002e4110b09010038800d00750003d15521503090f41e4846081d03070ba03207011000380c0000c86014001031142e10085800800340c0c1a0100c2c0e50040c40252403441c0a544001862500440c04c42109200c01d607005000309600804490b016203448c3c00d1030440d80d050200b1441e81e07846502d26020f002601d40c100102164060341041c8601e4408101141c0c6486906e50354200414462043c4480f00b400d0010000303900b90b04004485090b84541c2c0c4d040d8280c1c1c01c6c01 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 181202607 1250 181201357 181201369
    0x602030604020d02070b06030607090303090302060d1409010f0f05040203031b07050409030c110102010e07180f1b0e0a050604120c050d03080106020f0c10030c12020d0b01090906050a05 81
    0x902403500301d0b40030095240040018401080c0f1607126085007040f03400c0500a042ca0880d000702004188002c0b03960030320110340c0207440c8000721396044500070b6591900d0100400a03001503003c10029507905c0d0103010b00f54106402041c000c6100c03030381c2001103064064070701056038001d880107501a0400c12403082150160840c041000c5044402c458802e5a141c000c60300710350200c402a0005005c00c0605401c010002c5500d5442c1c010900c024000e140058401c591941d509214512007484441001b000310301e801d410510007031481001c100992000c40c0101380705c18040c1c500c14000100031131210449484c14400343e90580d0009070180342000e09002c0860300c3d0984000c41030b01e640c514040c000804e60317222000b071001030380700e0354802c2820b52415102078607040c0000505145601704c03202520054460f4107084410708254540850ba500307481d401a0782440c890071030784141c140009642c8059051030b402a020380c0324203036104003840c0e035903241c010f08440c080c0c01040d0340040d00c2c0404001d070346425 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 181203857 1250 181202607 181202611
    0x70804090207140f012301060e1c0b28140c0c03090307031a01060504150305130f030f110a050d14210f0106170a180b0907150912060203 60
    0x248a00d03610f107042c0003004a1a0100102400d0240c1c4e4642c911803440990711403c1d00368518141d07021001c10350410002405c41540c118901d40113120001c0440b0055801c0401201072540210382d4201904240002071000c03d0308074030b0703949954124111440c030103815124078101100420075019460b04e843c40070108940c402c520f030f1035540c40140002c120b283d81c280007440085d4400c05d03040010340300c1c00d6066250707640c050f40090180700c800d00c405c00140c1d98256111401102c039103030021711641c0368000b500411013100005800f288084110604054000c031001c0244651510f80846c40f0303544801140d55280d83c2e0f07a0007044e68210750724980c0500e00450100600604640e0f10303e0900440722604244d803220148000c56402c60001032054000c1c0c1d1402c2c0c0350150041c0c0c83c110f81d80d800201f2154950074006030000101a944555031050b1004400708200c1e0075510a408000300d08003100c1066a4880500414041c24131107461080094002e81c1c40070120f46d100c00078198202220b0303c0380c00083d040 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 181205107 1250 181203857 181203863
    0x3120b030c031e100212062b08210a0f18020105041e1802040f0e01030b16030209060c03190203031303120b0a090c03050106050c0a060e01090c0e01080d0203070804090207 75
    0x406207410406944e500180130920080080e0020919060040004d2078403107100d0f00030416280f40c4402d02d0121a0501640c2290b0840c551a07607440200403444000318030412141d100c030000d581440000d007201d40102d040d08502c00c109002c10b1440c0001c00d40c0e281c40000001380490030030030041118105201c1d012030350100c2c070505000b44d81c1d540c164030a203030081e0920039030003180d002400780b1484400d000030030058410154004820b605542c1c82c21000c09001d030000da000d03451207403040c507000c0c0700350100c1c1c40000713003e400306448115a6007829580d402c00c03039401201288400e01120400e200000742c1c0d110342548000d045130840a40c0781544c41c00c3c095040200c80c1d984911780c03490360b5125218114024070381c076040051402100340d0020111b0f08181c1001c420000200841d074202e80c000035801c000d540e0040c000060380c090381542c072401851003460080c4580c401d60800540c00c00300034001c0b41201c2c20340043d1285002c005500302d032603110f04240107001107800c0c001404503c90a90103044050300c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 181206357 1250 181205107 181205113
    0xc0406020d110106120305040f0e0601050403021e030d0905090a02070b0f07020715111902030c0111070302130c0f0201020307080f07110f010b0307060302040308030606071b0303120b030c031e 84
    0x51142002c2a4512171005c080d030101d0000641000050001c10302c5200600f16100340006508218000131310a00c11840b019100b100c0101d240c401098068440c01e000c400010300f10707038000e00e407944040c10b10500c0788216482540c10b50001004410940211402260f1000c44004260b540ca14928040e0901628100441c424a1808551082d400c10200e410004035140c0340c44964010703801901d04200d10210b0401c1304000103040e4010b880000d4060707220102401c1116038200d010000d0b51810400b9031000e58400d4000404008415250303021601410302592102c0c0909480c600036400e0f480159111750009d03598000256540907020031540d000a080e01d004512a100c1001c1d040ca01000303403034900401c0e550390300c2d054480d2070104521802006603060950a0500e0368451000300c0c00014181c600520340043c0410812481c89024100246400b0240c0401626414000c01c030807031813400d00c43c0745450710030740c0702c290b160005e441c1200c0c0b00000c005104400d031059241420700140481030a440c4 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 181207607 1250 181206357 181206359
    0x6060906160611070b06041e0e1009060e060603060f040f0f060905060708130201170703091e11010c0510110c150412030c02060c0f0405060307050d050c0406020d110106 74
    0x2d03980d000f030700c05041e1211425a12210f83d81005410008041c0505124130b00d010b40c1e03003040c2c11051000c62007118407403d0028002826409403814043d4189110055524080400c000c121407503010305040c0d04550100d841c1c030780e42c0da0281559850250b444110741800310002500240350080e980d030b080d5114801120000749a507072684261801c0340e004072081d4100e00308110515070706c00000780c0c1c494010f242c5401c0d0308900ba000a0f1100017818141401d800c0a4800252001c1c020f4004e000e04d2544260b0a00000100394450424103130714820445040c4901000c020b525032003100041802c5808c42c0203070204059100d211740041217060380c022410341c0c05101c40c0c851101c0900140000c09584600589246803c0c80c1c031030040e120580d441414140b820f000b10b51125800070f09154804101980b955440d01409515080ca0145c0e60055510000000130844450b5009010349140d0381c0903601031040b504c1e8083c120348207004a0041a0043c0d108503144541d040c440ea4601440e019894000501d00d = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 181208857 1250 181207607 181207613
    0x12020a2606040e0106060c060b030c1804030e0a14010c05010b060408071d040c06080c0706020a03020910020a11150904020c010c02060709080d050c150a0c020705010302030606090616 80
    0x100300241409100540864100045400c180c0101100c1150035802040114200503000d04441c032522000313082a50780d003401d82c01d47d0300c04000e400a00341c4005d003010081c0c6490100d88446c54000c40e800c800003046650440b0150034010700c0c00080d02c0c02c8201c101d0808250400460714210340b02c030266055902c0385c003202620f480d010010400b070800c00010b00009410700307000310380a9a8401080303803003d22210801c00481c0d007408c181c805941e030134a070892940c0c580102d490000d00840c5406800390344002800c1c144650580d00415080000350f038171464034451070200382e03200c00c1041409002c0300c44421b50b0103047e00d03102000b98480c12014440c0340c103103250300c00420101d030003c5040d004e00382e54420f030011605404000c055841a51803910641d034074100f412854649003440300030030034010045001d010643c030a00000034501500d00d2501d60350714006140c1c1e00034109d102c2050000d03019403540410654400d0085034401c0303801a00a9107812100028840d0990008820f0312458410070300c41400 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 181210107 1250 181208857 181208897
    0x106050a141204051e07030f060c02120a020318100815031e0a02030106051210020d090b1e0a0c080105100c0507030f060f0204080613020f0a06110106080d12020a 71
    0x281d000b000140800b42102c090182c0d817010702101c00e01160f101890803c0010001119424559481400401e24150b0700105038940241003400ca0780c81c030310104104140d50760000203400347e81c2c11a10b02c902e006500005121440106c09045000144050300240034010050550110b01d02d018040301c031070000942078519000e418082c0103c007500a46503490551409000322805030400b21a000003c8481c0d400781c42e90391092200180c150b940102d4640814100d075801000c1a5030441e100308090700e40b4003d2200415081c007004811560102c020540000052082a01c03101d0305e601c803002941d0900c070403c08440945169201040b00c450300400020707106100b1a001540302e44a090f20b007040d60324189042d07420314404165030030b1040c88104100840080c2c20783d0000c600100c40b5001c03041d0340c00030404e986890661240c1010b105c4400044003544488071004010b168002000b001e92210451612003120740139840020f0a5025241b003031408650050848036400e06141220b01810740200c41c0c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 181211357 1250 181210107 181210111
    0x50412031d0a06090f0e1e0901020d0f0b01140a1b0c080a080417190204020a18060c020f040b010f08070c060f0203041208010f1422020309150106050a1412 68
    0x38181312010000030703100500820241800418800741031514a000e40c45034113424009a00b02d41800c070106582c0b100a604880b402c1c0c41c00d007000d010000c40d0216050107040e0020001e0700240d451040c03625079400190685d00c2e5400039685503000410310841403d0b420303002d401c05442200304c81d440003810300000c00281148510a41c3c01507102ca18245895414100340f4001c1c800b0743d00302c428031036a003008041c21895159030403940161a078844820455050010032001e60009022036408108641c0050170007060783d00c204d0b0881201d54240c0280000cae036141c1c075280c90100f501d420264040c0790041c10015400105840c00e09080303d46615440e003076038088181000001d900000340800d1140d54411441c3d00241d030708220909514244030f007036180b0144e1242c148941900c40503801c00b81c0d540840b1050026600c605034540d2031400700b4960086d4010740300000ca03407140340000068200e00034982d034121001c50302d4841c1405200c2c1400c0e580d184c1079500c080d6400b04208210800310042d002c400c0c0c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 181212607 1250 181211357 181211369
    0x18060d0203090717070501140a0201020903070b0405034c02041511010207030906050904090501060806270303060405060a03050a030f0305090309090a0f11040605090907050412031d0a 80
    0x1030359500e0304c18100310741d007456042c08800e41c000f0403040c0600c1c0d800c07100c0d042120340320a00095031001d00c00000ca0081c0034603600690b01d030103011000500c0103500c10291060766000c400744c07003081400c103240811a15000005d1a664088000305680100029000c2616480250b0b0311140000c0c400400004982c0a07800c4101440d20001d00805407640c007070401c00382c050005008600d80841c03500d01800e8002c641c4070f040f00700000004d0004040d1141d40100c1420381e440030081c40305a450744030303544d164407040705c400c2c0240c40c211044001000c0040a0050f828500101452a42d1103400501010700001003005801240c038180020010b4001c01004941c02c1c00307079485104a0079850401401d5480c00340101d0650b07481402040c4040c0c1e55010001e41003080a000025940201610140541148404101903241c0402d0004d00325401500424207004111596061962101000d54803030041c2e0203035080341102c1c224140000b90046c0312100291528228070701449030540c00040140b03526403c40 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 181213857 1250 181212607 181212613
    0x130e07021612060b06090f22020d06150306060c15060b0d02030403020607030b0a05011206030501050c180d0305040b03060f0301020c010209011206080a030c11030331060518060d020309 81
    0x40c80a11001d80b140711800b80c1c08a907101e00c0e10005400140350100c4035040188a20323005400e032074400922521510300411040020754a0f0010081c0501c01400c10f8071414040065504110002074800e10400c4181c52440e212a00d5601c1e46480e42003090440b030f5146a01555585408103440d44104007401307003000581805039491415180c0242018805401001818204111421580d440010f50000c1d20b8003841e00030350310b16a411004001d050180d03c007030700c0b03035191205200307217610a84000c060b0210400c00780c118282e100800d210a00240c0c040240015506000911035181c005000b941c20403401000035550214110000742240c0c410305202809039400903c0c8030031540c00c0807000e0010a04204100500307490f1401e49034448038034250040410111101550400412026045410102070100d94039819214441a6106001814001005600c00700143c1d0041e00480e200c0541746103503500c42c20b003d8200c00118086104545a90384007806025295010f00c26101852081c0c0c115801 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 181215107 1250 181213857 181213889
    0x31507020a0606091b08010806131a07030e0d140a05090f03061f0503010603380114011119080a0e030109060b0a0806072708191205130e070216 63
    0x41c000c0e85aa01241e090148001c1500401c007000009c1131140c0e0002c3c0300c10700301e403540c0001c1c60160611406949100c1d40f0051000510007015450f6000ea43c071851800d042318913074822003009482400c8408910f2121003030400c40500841c0c070640c0a88a5024040d0405005942480c00282403c0b001c4500c0003441c0160145920a5283c0203c51001014150000c01180782113846040c207441020900c010144003201000440b407510941e031542c9044094900d003d10350319208412015000060040c1c00034200103031206016034081244145014140e00a960105907036a40c00308d250400f032031190a00001226420040c0c40a025005010b441880c0029844c2c80302d808002000c0c0d065000040140d01c810700b00070701c03241c1081d00488803100780d200080c05155940802d92030300d0010b41045020f4054240c80400ac0c104510203400024414400710503070148107481111503015908000c813141400d1072041240c815244415a0808003030f01c15120550701c0541c03100b49000d6954800c280c04102d44507 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 181216357 1250 181215107 181215131
    0xf03090e1503120c060a050601050903031209120c19060204092408030a0203030c0c19060906050108011a010c060204150906080c040302060d050a060302090a02090a0503030306031507020a060609 85
    0x300c0c0450918101c42c1504062503490805da4865008181d48a2660b0b40c501042c1203a01403401d84828440c0181240d41d03550036110398442d0782e0810303108400b8034402c00b81190416401c01c015501210a80c6c0d00410941049a501c5e039124008540140c1d035156003000041041685030040c8a50030405c45c0070f2480300c0c111b40f8002c041d9012103a00003503061300706106104c0413541c04800c898000c1c05ca007401c680c80e506071132921410b102101381c2e07401a402c402038410040007400e4015007174050044c0f40401c481d17030b40c0348081c03401d9070744030400d009040c000e4203800086580502c0844035101d0003203600504050303c070351b020350403031001d440105c1c04917004400401610340c2c02640b4540c088801000c250070a89503601241040c011100d5000c02c554607070380011540700c9558041401150001c0c20340c1d640d81442014880254000d402050140c1c42c00703280420030b03050000860b4000c01010380204500300c1340c240d81407c0f4000150504046000380c003038420214045000d8400030342401180080e401074445 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 181217607 1250 181216357 181216363
    0x1d0706030914070e1612051306050f060102060a111201060c120203090f060a050c100506030f07030215070c0b120a0624052a07050405010e090601030f03090e1503 71
    0x110462245a00c802010b005004c2120200c075001a24050801d05ca400300001c281d4106610051018076107290904001008601c03940c00307a00c20340207501c10040364807243c41800710b8410807039400f0b0269200c1008076923400074030ba10001d224000c05942e2070030003207914082c040990083e44100c00250f0343c030b041003080c004264600448140c15000071450510728001180b1500b001039480c5115000c00704007114041c0c014800c451107812140207407000c401303c01883c1c030010705081d6002e502904c503001c0003060010001a00c038040c2da800504580c4800300805100800f980004000c4034140524000050190351400192205a5144200320014500400500225016a403003040d546c01040c440c0c400340350f101d1003921040d50782d500d03201d5640d5149010f45030200e044440100c002000c640c0b80081130583c045210400e41e20129400e10031030740c0e00c008103a6118003d403030110322500100300410000b01840140f241061103170804a500a41e55803100144090486480d05854048441e07000c00713140034 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 181218857 1250 181217607 181217633
    0x1091809201c0c0302061b34180213120609060c140306010c1e0c050306010609270f320112170906070804030606050603060607061d07060309 62
    0x2c00c0c21030000c485039443e009550150361001038054807000800091014039440d000c2c0704546c1e448101c0b41c0c181010030b110107032640751072094600300703c1c0c88081c210004400c541c0e02084804983d5070005a8001c502820025800304030340d41504580180000f84080c20316818003115030240d80c7c0000c154030581400004e903410000c0342c80401c207200e454040111100000d0f82d411810a1078038014200d041e141201c030f890f03e050b0041c81680035001080003041310805046058400580035500c2d82c0c2d90782c071016903080510f4000d070bc0b040d080501740d080c50392a025068210b02a880c9401091b52021100440110f40c450302a01822801c4000c01220b4410358070080d44550803081003e14446d0300d04140c8000210030880c0c001e00f03000300c81c25890382c2c48100c007059a07200000101340c1030b5282180e2074240051390140c031040343d11900b80b4400140918042c4156441a1005002e4030716150995403988000c150703035400c000e00f850211908a0074000d0800200000d082c03242c40c0081c03a00d08905120b2820402 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 181220107 1250 181218857 181218889
    0x711010605090103030507030c0b150316080309151603031a0901051f18060503010602070602010c14030c2701030b09250c0506090607030c0309020109180920 69
    0x1451010403882d16601402c504517074240c075115456800d13602c2c0440c1ca100080b480039004511120500816034450142160a908218110b0703200300c40c00c1d0034910840005110700310483d0030074000c074072460800c0c8010149071100000024500000c018040c54200300070310301900003d903a581d644080b14000c002d04074081c0c60845030b00c40c040d89418001102c8048160000708000f00d0341544082c000d000301100d21200303031b1110050345510303100c0344024250b40003481050014810075100149280c01032041040111f0b80790740305001064140d0700e12480740c0c0050b09094440004000c00620028100d902c40304800d85030308020514084c44000505946e40e40700709a100b0402882400040d9103030030700c1810159851b07000c403603028440c0642980c0351000d0501c0500980106420442c4ac40c0011945500ca224640c0301008010365440080341203418203c0000e010840c241000d01c00600304070300c84441c10300a901d010131000f0321030381c411120040c061807401ca640800c1e0b00e6040d507440c20341d43e50307920981 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 181221357 1250 181220107 181220111
    0x204060314190b03070306060b0c160b12180f1e0d0801030b04020a0302220606050a1706150a0201021804050615071104060e1b03150118090e0303071101 67
    0x4212548010410390b600c1682002543d0384035402040c1c4017442050000d68100a00b000055559241c1882c03681c4400107000180c0900c0030100340d0402aa08a0700582d00380111090406420b41c0c111480a04c1c0907000008a070920103040100c40e42c100444400121308030042d100c00392160041c00c0d0300312100c0281c14110341080165489030303640402c4d0f250450790400b40c20700060301c0e68008600b80b8079030384e00041e40110103894030000300e0344488510385070350760020005c0180c0790b0b580d6000c41d41e5000b04443e01c3d00092903d9800395540300d0100c03086420100c0148520b41d1042000701d514180d5200e04081360150350003180c800594402c045d103815198405650505c458607110000a994005080844030101408640c40050003c0640c2049030440c0180007000520b032074040480703a1030022119501004034202c01d2900601c1c215054a0080c02450b08890900019800655820803880b0031541d414650b46c10004080f000383c061840040740e40c0010303584d40c0c01c3ca0040102040903043c440b4007141c1c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 181222607 1250 181221357 181221361
    0x307030206250e1f09030b0c1e0705010b030303190b060408150a150905010302090702150105010f02030c0106090212100302010e0906040e060103050d030c080609060f0d0501050a0204060314 83
    0x403042d0a681824081600e000300c8446411000640100c2c070b4400030410407a2400914404641c0103408141940d0007071400c000155500000202c1610a8020042c2101c461210080d100722042000d0b1012a01c02c0d40045505501c0c6408280785800440362402c214011848100070360f0400c4c0300d1400084000e545280c506401c115405981c1c5090b41c0280b5203104200001400e4280c8641c055071401810b002500d00803507076442544090002808240e1103032a03d03c0c00b0400c81c50001907085030100911141c0c840c00e80ca00310041d110b595007080d410040d400100200c02002c0402c0c81074002400485e2001602d601118003180c0710300f040105188c0c5c0591306c8d0502840580c2e0015081c0b08940012a0b03048000e60301c7c00d0106020b41552082e155040c0f14040020082040200316002e4208299030104150760100300c1c2211106400d0b40e0040e04044d01201080700d80c1031004501580c400054051451080305664840c00c403441105e0161815501040c1172000c00c0d45802000700f580c420081c41c1800d4 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 181223857 1250 181222607 181222651
    0x30310051f05030c040806040312050108060403080c090103091401091101020303010803031f090e0d2709050c070203070e0105090109061d101205060a18051903030f0606020307030206 80
    0x8160a5500103051201c084006040b01031103c01721400f0707003002c000340e601e80d0403d85005041541d0456240c81c24500700300c0042007000d00043c066100d25003542c0d584480b900c91000403001c1d6072042c1d01080c10142c8410241000c0390034241104080d07131920000080040460501c0c1c401e140c000f590190440d002080100314100e000000c0d2900014040d181c01410040018030380c07024007465000d8500241041e01c15418601c01040056014071b25031510500020212411410702007416401410f00000f2601486644030b2540010782c0710103c002c8a5207001e465800280ca413800940c030820304507942100500403400d2040f00a4010042d001042c441c090a210050060701d10031071310a034450121704001881104503080c01e500600060004a02c242500e0403d180ca92408844000e456400d080f07c402807043c48101840a03c0d8221000d40350401d08460550880c0100e000150101600d032a42c00300c08200d03e1154600801e02a00116595200d525001c3e007444c0000385101c1001c0840721214400c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 181225107 1250 181223857 181223899
    0x40605030d020a110118030b0a0f0c0f080613110315060f030a1a040510080f030a090b0d110412021c030f141210030201021005070e040203130203010e03031005 70
    0x444d884102c100ca4241070744012202081c0e1904511500034604100000b8401d40c1280d00d8040d2100580c1030000381580d1864030182c490007195640011660350803244094411920260481c000900d4800068450700c141426200d551800000c222030000c14800009200c6651403001c1409840320350a00704a1903407800c113400001e2040c0311603a111500450000b507910310848a00c0340040c41003149040c036440c0c0003003840403070084003500d12980400401d000030003c29107480c9142a5102507002c0e04101c01840c007500007001820b83d1387e4032212000e04e00c00c0c02c90b020b04007801644031034181c40c4001e03004000c2e44070302d20203503941c044600d14140702c04283d00000402d01c0340400c1c1880c2000c4054034200800d580728490302c40240310030002c00c1c0030540c007406c1481e0003124000d0f4201c80039490b6101003141140c0741561540080340441883da00d031401c0607005190701a05250355a20a02225000f203030954101c010002215000001000f070703503003200000c2c80054402500c034100d56036910420411 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 181226357 1250 181225107 181225123
    0xa0f060f0306060c020f012006160504032a15020a0209070302031003080919120b010501081015030608030a080a0608030903030d05060a030210050408100203150d03050c070f05040605030d02 83
    0x801042c5105c804000c0f41d000b40d8885030f2010030306003100941a854081103403a96002c9d1250360500191921001205100d141070f13306403600000d4840e85201d00c11800c041740081c1d05d4200e942c01211080001c0d0902e00300c19900307600226074000c0c1c00507030002d1040140f080001804042414414020300020920300e1014100303a81d4800c580c542e44114000c00622452200c1d8580030340700000c2c113408a031404450f07000e1407050707200d05481030701662290011b446d180011651014124445c9908001c0d5102d820201424403419080010700c1d5a1500d42681c210b500c20001040400d00c40024000c1d0032000d4401c4400419944024604260008000a03141e10403622442c507501c0e10b54001c07036800d5480110140c000d660060003804501030b400380103465500648035129890040c8400720005410301c0c021644600040b0b1480408040b00d40b0801c452010030038030a80800c201400030003942e81d000c00050000d07041356403642100d44c1c6031008110aa86a5410460081d00140d10010030301e500007910703076 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 181227607 1250 181226357 181226359
    0xd0f0e1005040506070614060405221b06050c07170a020108150409150c020102090d120309050303010f0f08010908041701092019141e0a0f060f0306060c02 68
    0x180203219410011a070381e00468100603400400041c1d4181080f0003940050f84030364084d01a403c0726a20752003040f00300c6804880b00340078400319448400500c0005981804000d1003080742086800c100f140141310301040350000400304070700184078201440700304044401030942c9014280103881c0c243e0390703d840d140d400c0030082c148580e44000c1030803503440c020000499940640b0800660185042c8004154100c0000a404900d08144030f4510342c4180203c44a5410250000c1040d040075038454654000c615156030070942c1c0c5a000000040040c00118020300b80710b10340b01c00850601040e00c02d04940345e806003000703030b14200d00c220000d0030345401e66044440c2d5550a8680c45d00d05840c51780549010304000301061080d090300303000d0f10404400a05500c0065030350745141441301070b0a84640c1d40900690004c5207002c03da082162400064149040d1114080e200359015910042420f80d0001d401c00e00011031001014414680e001c5d1361500003c01910b02407100515200000d44012244e440203 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 181228857 1250 181227607 181227619
    0x904120311190c1205040503070303050c0a1a06031213050105090604080a05031315080f06010e0405010e0619060503040204020d3e0c100506210f0d0f0e 67
    0x200c144001c00801d8600155040410076070001d07808000412480b0100001c0358400801819100c1280c8240c06403800c0d1803024000380700d85411a141aa0030341c1200c4800c2100e48600c1a20350000f694416481e2255100300d1094134080c1000010141401c0345003018840c40307101072000300001030750059078004440003808d11660380c44428000c10701605c91500300c01a81d2144000342d00410100000070485806c0070284803440c071751078068504070500c11000003400140164007055401410025003500510141040188041c0318404103064480903072214a01001401c104182820489403100240e014019a0030300c4278240003019060340005040070b07010313507404903100f1710405880c0e0101001440084d48074242c0d44e07218041c2101000b0b1002130030000c3d541d0240b5110411480c1054a040c841c3e030401600c1c08040242c442d00013003c00a0103940e102140404828148007100b611a500303005d0031015064003108802c00302d2804101c0401e45041042c95114201903c0d405150900c18900071140 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 181230107 1250 181228857 181228871
    0xc050309090c130e0708060105040605030402040f0f06060203040914061f0302040e0a0e07090501050a1205070512030703020705012d021e0a210519020f0102121509041203 75
    0x407000e001d025441a001ca11104410013280406225100911920303c968403c2d04594680c0011101da024034805c8502260b400c0c40800c0040c585030300005607055408000040e00c401041d5010203481c01c070344c85400560800902806071080c0c6000b0311310000c5071003108030113a05140780401c807501c0e208020500050081115034007080e200b501160020310300048001032600b0083c4501c002040040c89103111403080d042c000034552894040c084c1240d4005041400491030310302c0700200240d0b80c0d00d04a980740200032001c40c29546100303c040c01641004015a1110f419140c06480c1c110310350003481c103005880055000c00d0015440c450303c03907051944020741c00300340180c0130f91501c40029038a803100c160a403520084036000050b80c1c3c059601803403400a0f1005400303620004000a0029a800506c042007046541200500b992061041610449645030040482142240c1048403082c800020400500004184000316140c0e64203040b20003a00c242081c1e03660a5000050500360401c0c1601c0d016 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 181231357 1250 181230107 181230121
    0x15201809190614030c03070f051002010902030304030309030c090203010f03060f021207080610080105060f0a021204060e040c022a0117041506121e0809060c0a02100c05030909 77
    0x441c0d042000c1d03022030240481c0e0f46481480300f1490024410750301900c6100c2624055280016030360088881c1d0040721080a42042d0071300c018516607064001c2599250101072006031801c1004200441c002d80d103400110341540b400f0004000680e000320701c007030f00500040c80440400b091520840394401c5001684901c804038810181c040d05020703a2806502008100070280c010f00c2c824400e02c006c0386c4c40006010500400c1d5822a028000c07140c0021703040c410820681e621034020501c01c40980101ca584a8400b10340010030f51058001e00d00045401d40d10080c141000d006188000b00700d4005000d010303809203081450043c4a05000703c0240140305008041e9004943c460b14014040c0d4850003d89403d04119080c007882c2c105030700811b03140400016150030291000340c0415407056003285806686a030b90100003207941c0f0142c035004801c112a920a130358000080c030701c3c030ba941e001a058030f2700180100100d074000321200c0000e1240c40ba9034240081c4001c401c440361510200c40e004030f19100e8003 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 181232607 1250 181231357 181231381
    0x11120a1203090c0e0a090203010e03180f03030c0706021b060c062701020a0507051b090a0207030207050409140705060a1202030907030b0403080f150a09021615201809 73
    0xa13201c0329218080350107101c034001e029046444480c1c001e83c000e024111215200e00d070703284581c184040201170070042c042403502e4007040c900304800c0020203c0341846041c030072a90400e4041d07405940568858004502c404a403081407804104045a9060501c0b03110010680c032150010120b1846185a807540e41c403400e07425000c0b80002501800854031240c51103809845035200e0038094900d0300c0344848030348000084505003207003c18060003909007034070781c88400b4004c1c3d0808081142580621200810303261200e10030556201d01031211680006c0c0c04010690070101f607504410f0054008100c003410803030b00203540e903c03131050481c80180c1e00d80d20000782c40d080c0990341e000100400c000c04140010b1541c4005810301980c1110017241d101c0d1030f45410b1291600310489126001030168400300b0205d01c2d00d5002e0164699020240000c030b282541d00c0044540400c0f40140c1e0040e940c000880f51302450026201d000d0900052440c50020703803600b0707900b280751410100c501c280303640350018440030054 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 181233857 1250 181232607 181232609
    0xa0f02070807080a060e0601031101050708091f1706011b0201020c040f020c060c0a08040b04021809030406020c010503131101021006181a0901140d080711120a1203090c 74
    0x180c8240d4800c603403078480d02c3d40c507070103580025071350039082c41031491080c1c2c2e000c1046e90407640d0000042810782c942400640f450740007203006407003c0009204041d560340711035241488103c928501c594101618200242c0090187c0d0106410b80c07000d0406c100d40c5036001081c000070055180c92001d03040f401440103d113070504e64210b0300e8216050814010818291742c002c1c220354082201580c02c243d594007150b000703a0040312000e400050011011401140503045040d82060010b082881e01a03050030811081d00c20907203158446500c0007504111190b81480015107121091034410b02c1c2d4144070349481c5800a0006010700925011800008180e00030820249200d0042d5001e0001031b50b50220403d10700c4403500340840440c10550424200031103103401001504d4000c00644181c0d0074490301c5403003482d5510038241c0102130380410101140f110300c054007040b0310510340e0040c00e141210070300007090303d2040c8030300081e400411010005422514000005101458009080d62150900010030546 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 181235107 1250 181233857 181233869
    0x80c0d0609020901030e030a02030406200f0606010e0d0b06091005130902030106050901030b13031211210c07080a030b0616121407081c02160302210a0f0207 69
    0x640303200021890740e550064410001c0980f8104070384502120b209483e845010008001a0030401c0140085800f0b410180700110005c0a82c06d9550380134142c0c0c900d4500c10b0031000f5802d03880041040301969201d5422200582c060b00c16980403446691401990840500040c0c41526000b0002d000341c1048135003880100b8000740720010122905040c28020031202c603050703019509220000c80c450410910880c102da5102d00305a21755514462400701c0604820f03011402c00040c4000c103001480caa020b070b540383c08003003107005545204812400305154558044018009003100c10001d82850306810390302e80b0381d000380e411070f03a03100c1810048008025941465501090200364801107a00d003107017a20410740309100d100da8011440200f0f840d0040303100c2c0d60725400c400070000140020f00407009801039a08105991401c9102c62031000241c1c0c22201103130b102c0135010603900042c90750400011b0307000c40050740101c50710282204004440d1050384140300902880c00c00100501e4400c101040080072 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 181236357 1250 181235107 181235111
    0x30f0a0b07030c210218040f1d07030503190306050a0902040303081018020a120906050403120207030503060f120a05010e07050105040f06180305010510061103030f0601080c0d 77
    0x15a500e090360300c0c050203581e298002441d00a800040c18001e0746035429800c1c1c07850124108001814110002e0b40c800940030520540c8051400c140342c8035070054148103869802c0203e000201c4040640c0c80840034100e441d619444240200046100402124841c50a04e032508038071040c00703e020b4014280d01d0384190742000414000145c42070b4140d0142c003d03607100f6030311941182c1350314804131031418250040c00051101814207007504000e50f8010107004c4c4c5141007181100e001e0014800403240e801d00e00b40c94035a1100c040004155000022284490110700218101101900c2c002c019000040c0624000c030a20040e41116540729600c403a0f41c5c51400c0200d600e843c080d40340481c00f0b0100c0341c034200b109219620010a04d0760007001034400303440d10481c8100045203002d50459444090f5041558448500c00001c001b2600a02410348180c00b40441206d0a03868a503004000703166403041c00d507040e0020300612500c003940e0524150411004d1901c141a40c0b207018a058480c842c40c411800701c18 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 181237607 1250 181236357 181236373
    0x206070803010b030601030c26070318050708010b010c1110111b090c040305030322021f0e04060806150f0409060b1503040b070311041505070b0a06081902030f 70
    0x70f0b100005511920307007aa018849002003800c00c1d2484400a0300d0020580070040b4560179070003c007200158030a0280c81c01240443c9061401c41c0001c0340c1140540f0b440d00446006d10610b20300340244684c408080c64003100c002d4094581c41d00c1e60b804440118403807160201c20200092003171104006070110030f0140c910045071804020081c4e03200e900220301403445c00e40040d400110510030b443c1280d8104000d5490740d41c0c0c034102220800d80442004054046454511025880c1c3e5018800400881d12144c410120043c8000d0080c04900d210a48218180802402160404105c55400c8240e461a0207030b07210a10300019107001070411595041840c01071803501303004d059003215000e814280c506611070b9065201c1300005110440300601401e42c10004909810b00c00e5219090166206e017040c0c0c03c4c40d496014650f80c04400310144400100c011480e407083c02750901c0c65503000801d084003080b8051a15880302d45442e086040b4800c0c201404207190103549040c000c0e070f41002c418500f51542a = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 181238857 1250 181237607 181237619
    0x71a0109020c0c040531121701050a05060d0203060a091107210e0d0f02060a0e1009152102040906080f010204050306040b0406090605010e090c0a21020607080301 71
    0xa410040402c82c030341c490052020001d0806204480c020306044c14032030520044030b400011044c0940c00c0280445514040c0320f004158200c03000c400e85075140d6a00f52300b022503040d8400b00548180c2045203c0c6902d440100826510301d000c48031170114440c00503849075a60300000318104501d5010480990606606a0701003003214020410284510240840524070840c0016101c85101012001c141180c400b0480c0d80703001d07010032451600c100c44189200d41a60f0100f0142d40188201f1008608a0107a1051902d052107008000380c01d280b8008032183e2400140902103030900408000303000900d2440d214500400c3e2042c0c5038011048001c2d0342e01ca50f00c07020380d070003041184200c03052401440201c5010720410f008540454038024000d184c140c80c1e41d00c86010055002d0000c0b141c2994171f196540008413140189070080107961012541c520702543d00c0390820710f10341982442011800720034000c0000908103030f1302c5140014080d00c0c60081510124410f0321500c02c0140c01e00402100000341 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 181240107 1250 181238857 181238861
    0x1218030201020418050c0f090307180504020108090c090a02030601180b030702070506271215070f020a0c0909050102071e020103061208090f01020102190903061103100605071a0109 79
    0x44510340200d44d0600c2001021100456070252501000c80d08100301420050b030a100c054007a514004040d5025269100100c0300b1143c614825034103003986440c10002550f030000303091a40180035501030300c4a4817071140060020080140044111903000c00450340f180d20800402a50009900200c107240e92510325096940c3c00032100070006208812010405051000030344500300e40007210240c454281184481b40010203440385904000000840095070004001f01c2c05c1c1c0c02120390030225281448007000b45007d01804000c8203660101805000050742044408100c40c3d9103603002904002900c6e0641c0a4414804050f043c4441244480300c280107451807020018400d0300c0070842140d642d02c88008180d000d83d4043c100400900100f81c140c2401e8200c030414000510006150280100c5100c0c0561904801000001c3d501c40c0103004000d101d204070382c025154103585900318034248a1007400c4400500945040120202d003034000c211170400088081e08a144048129607101d22120300 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 181241357 1250 181240107 181240109
    0x9180a06050a0f020c03181801030b04020f09270f010c0f1107050d11010908100f0e030403020a0b07080705340e0a090804081b0109060806030c0112180302010204 71
    0xa030314a00241c82c03d4030780c0d052084402c04000c0d4009141400e44080c3c8080903070a000801c281c104100841020b00c1c650000c40300350207584a00030191350360420780184101c0e8000c0b5011103003c1e0b03054409024040d40c0c2c14108103048035160909282002089410604051410202c0109982010a00c0c214036400c40410413050070941c0d160b40c540312400c00c107070341d80d4492072080d544c0004e414070703503240401c160a000b04001c840606048460b00d584901d82858000c840712901807850b42c2d6800000209024040d1507201c00428004505050451b000a550104203100c1d84040700700028403402000005004d80d01040c0c1c1040c01d64294400031101107009d04040006086a1148503203445034644044c4044016140e2100b020302d030170ba40e0036070600000c1ca206542518201001d000025061608004454105814030b41083c0380d8080d001c0007400c00100f98100da414400c04104001c0d00e91030000304200070320001d1901500301d0020300b0700d0400601c00c01d08104912079400240205240d01500188 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 181242607 1250 181241357 181241371
    0x60d02040501082211010c20040f020c0c0927060118021903020a030204030b040c060e03070e0a0209010509040c0206010e010b091e03250f060503070e09180a0605 71
    0x6815a03414201114602c9228811329200c840c40c450034000c5212402c91041c2c85006041c0040740d212161100c640d440e1800b980292801c01c1c01ca01d00009003442d0044000303000b61540298200411f20001f6516031110000041c081c1508e4400100e02d40c0820030070480b0101e00d1418014032242c0207503e0b5480d801c6c02d0061140141d1140080d0783c0218144c8211003541c101d2454624000c20300c958201e002e54070003050b0400b05030f024000440402c50303400c02d5901551140c0050b00c0031b14600030300039201036002003425200c0e80282e44100040c0201c48030080d40b024110304c0c016503407202d010050314540141142a50000d00c1c00030341010081c0c0009442d416602e110340090200d80ea074046e8201c60340b049030300c0c0342d8104240d482c98009a2008880c4030705031a00040a0710042c1020500c454203a12070301c0c0c8001d03081d0f020381c5c0d420024404101042000b904003460828a035241c0b01a0107002155071000d414000c4090303c000400090700c2035a0007000840c1442a40c486070214105080548800d613640c2c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 181243857 1250 181242607 181242617
    0x90e090328200607030c180b09040510060c0605040201051902010524030a02010c0c031b1401021204181104060c1407060807050711030601031a060906090a090c05060d02040501 77
    0x40e0071840ea4150104100b12100b40040003180c3d10100c04801611070700c5404001e00c000318110742440b0a8100f80e25014002c48080240c603044602c04000540c0d2000d0132049081060740c40501042d988044e1604119030003071000306103500c0320b1004032000e1080d80041003810180490500d08968103401c034600803c2c44041c1c4449040308010748a4001920085c03103175042d03000d9072085005501401d1400030301401528124000b680d02d07107030302c0e50a41d16800c0c1304c0724403142c00105220807284407003820400c031020300c020305020049240003072042c0b296026240d44080c0c421003512843c2d581e0780051910490388000c40340c54651300c120207044001d00c110221010004903c01c110340000004813002220701030343c0c03540056259030400b80c036107601404e4240e41080c180c52502c0c2440c0c5040000900035403064040050900c03810b6072000c000c84010700381e0743c815600802448600d603603002c2d9540d0010812540011800780c9862300240c5a40e00b030f131180313400041c0410040c20741c541030b50250048910a8980c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 181245107 1250 181243857 181243877
    0x80307030e01081008071203020a020d05010b1011120711100906030f0b03071707030f05060402090c0c0606010f11060f010509011a03042306100f0f06090e090328 71
    0x3c000c80082a85c0904401603110500801c030940007224070078006c5010740150b0b0f04401300342e00410649188004282d03026034440b060500103040c2030100c1200200f05180214240e0100300e0f0399500d4403000c0300c5000b4140c0004c50008180540000c0b40612030000403d08540c04080c0280600050418410003000c030b40b41c000900342514240c001c41440c2c4030b0080180c10120300f85080048040c1e40c40b50f4550183c45090b20101c0000d000b400c200001c140503030000c0800c0d1070144104102d1503030043c01c80440141c18064030006090000c1c0a6401c01400d007828007122038a4101280c400c2c5404080b40e581e446504103101160000011842c10790b01c003502d402400342e8a4180400810b159285001913010042000070040b489145525141074145040201c0d440240308001e4640380d070130384201d02c418401030401c1210080c5030351400010642c50001181180c6024409405100385102d5101100304000000e8070a40041c4119402d80b514403c144003c0500c07280401085000480d2a201003000d20f02 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 181246357 1250 181245107 181245121
    0x30a0e0c0a0b030c03041e08071209060c11120d23040303080408070206160302060f0108070b071b0b0703050a020c041505120f01050a021e04060801030b10080307030e0108 75
    0x4410380304015081441c544a201040308107500040040e2a01d0754400ca130248401e59a0407c0901076004000781e580b00c42c00c6003000700c00b0400d10300801003130180c1e003101041a15009012865107581140ea040a943d40c0c03400840d525644aa03032031485400307a0600034001301c4d008810074000c2c8410400d400b0300300d84500d00341d40f100d1155000150104182100003000100e005000345000b03440505464105178281000078031140341c40e01d007140075800800400c03070000e030300010443c01048810300501c900d603e40518048103100f000c0300030b40400c400c4800e283c0102400407051000304240400d49a50b40102c0c10f00800035003142c45030600502415001d05083c0c5401d000d80c0c5401400801d032410810318040420540941724081100d20703015a011190b54001d0078455288114000030000d83d9036003030860b82100107402d102d00c40c413890609100500585910620759410340e503009120f40c51613101e441800d001d4010035800145984000194003003019884004401008420f0701c852080da1a500 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 181247607 1250 181246357 181246369
    0x90524010e072304030203060f010314070509070e12060c1902060105211603030306050a0911070204021b0307030f030b030c0d030e0f0405011e05030f06151302030a0e0c 74
    0xd100c02c80041d1080760025000550040d030011031003e545569407400350380b54003007820010101c1c2d41d0300341c0118880040091084801140341102c00c54000b800e581c600302000241c5081020b00090200302c1e141c078581c1c070241c0311910400e210043d10800c0745c034145410030310000650321031000c1c00d80d400d6029001c810407500029038641a1040103209034035049200307207a910090000322a51ba101d00c141d800e00d026044e031401440004e907001c1c2c0d40c082580b074104020300015100942c00f034980c0c94507003034040003e01c05004c2540e0481e0b50444016a45100700c10210407070701154112601c0302d000000b000000c168001c0c18075505138505071001d100000b006010162140181c141c541d400802c2c1c2d002e00e000180c807a102c46220704800034810042001c05801060490740c00341c01800c210300d41758800c0c18200c05864010700003414124001c000c800050f8169030f8445002901680d042c0032304400350105541c5d01e0145408100d25040119164a0401285c8001d030a14803804400c0d401740f0b000c054210b003441 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 181248857 1250 181247607 181247611
    0x180b0415170112150f0609112a0a02030304080a0605060a0e060415080106060203040314030306060d021321060e07060c1401021e12241201090524010e 66
    0x1004a400190786083c1d1148400508060101ca03007000c9001c2c3c0d1900d80e070491095011840d480e050000c0c0380d07810905400201c1c1d9035003050b2980070005011080741d56004040d04641c00d603100300e1a21a82140401092501c207050354000e40c10302000c41c000c604441b000034094080e80c040e080074442911070105000d00e110f05030080c00820b50a890002d201c60505811081000038506d04031103200fa991b0f0722a0b42103034069003000c8016007001030100103100d8000681c11010b20900003451860801000080789c80c414480c030020829001706051041040340c5408030002d00c040740142c0c0003160b4101107500c071402004001c0354140e00d03041c0150a0194006400002c0d21656254505041c650b6250f40c2c060b582c0359130f41800d4070741d020414101068680c000380e03029000042007280c0c9441c0c1d401d01c0d03041405d00003050007040035941d9180c01020300300c000303550365000820f64004550342c0e000c0c82203c3c058a440b5101802501c03d0550780b03400d40c41d4490449244070094074035100f20382d03214202c8250440701 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 181250107 1250 181248857 181248887
    0x2303010513020306010c1202070e0c03010e0412020102090406030303060806180d030b0a080709020c0d0e0105090108040f140c0109053f010e0601050f03010c09090507180b0415 77
    0x8000d50a81e4840060b0b0300442d046501410300d102c206445960b4140008942480c010050301b00071400c005c650841d216450300542c00880e01425981405112003801800a001910308084c05400401160003076040f00c88030700700548107012841e241e007006400761a0310b20070460a840f980000600c00c028141c4250704681c42000500220101c075081100641130b81c0c04141c0d44068a8100000e144008115031401042c01550260716603103803440c1141898003400800052040d284036100c41d60707030701c00d04490000c5401d003411a601d0310b9500340141c5403000342d4801401d84080c02e02c0b14903c05000503900350a02000d0f43c40000c0c094a4000b800595203c08000d403514004189030845152a401c00c000800850303a4100c2100507100700c181825141411030803030a42d085880103015a0518894a101c0c600d8103074002d110601c1900c0000300078103000c0c0b10325990b542d940c1d0301183d2042e00c20721103a00c404612031180c800c0541c59182d041c0c0154080d10540401d604882c21000250780a69095042c00c58 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 181251357 1250 181250107 181250119
    0xc07032a150b010f1202090a080a061d03030609040317040f110109030218250e040b120604170c0f100f110a0309020d0206040e07121b0e0a05090723030105 68
    0x401c00005aa10b81000c5640745d20b1581c0a02c0b40f610503444403568800101100e400800c00c000040c10700b1002c1b80e01c0c3c2860f501c44c0000703e8440ca00c1c02000042100e41091050b00c0d0907256548074202103451207116204801100d940c44180000c1c08804c0c0441140b8900400c60b03002061582c3c401550050001d200c025004a02c08924001c0b9824901807560700c040840700d2441c24200c183c024010440c0c0c0c0b0f40c07240c00890040040c864a0303090600c42c003000c40400b13444080d41010400c80c41030340c801d40180010100181c0c100e403440082c0c65202520940c4d05030408880d086a00788120382d403034030304000c1b07403500d030380e02c0d089c4254410b01040c09143e0446d0b207411405071030100d00303060841c040c140941060740c1010b03020320b0460040c1c88110041c402000d561044450760f081c8908010107402400051a40c07403400c007000003000b41002c11000382642040c1c140b10300402c95100201c2d450f4040c82d44016408034880040150450304210a14589540c0000d000c40307152601201c49024003081c09402c1d0440c0d = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 181252607 1250 181251357 181251377
    0x50721060b0a030221010f020306010c020d030201140a020d0e03030709030b0a0b13090605070f0e1909060803130909121b02040c02030c0c01050306090c07032a150b01 73
    0xd259501c5000d41000240880c44065280e030007250050406441c940d141c008a52240c501480c000c3c4548110000030301c800350302e14103101000030141c00030382c54082e11502d1240e90341030405000350f1254002d1601d620401c242450124408002908840c581c44065401c01c11044014040441164030414032030301c4000e6114110340760403078401d4000b0415100d0740c0d624114414140e4400e20a5101c582180700e000c24011110716204085da900a004c42d4144075038031510401a40d0130030b0500c80074403002c3d80c000d015040305603403102c075418080d80104411031910001085d00f0b8400700080624559040301c42c0340d050f80e255241c01c1156501c402c058a0485400702c0e40ca0890300c290b40c2020003055140e1002c10300c0780c06800140884000e0b01c03205c2c1c0564000192182c2d05501401200c0044c00c0c2401d0450440c50104013280841100a0101d010200001290020140185407904107030f80481101d1880c002c03807600d580d070081c103120425140072030540081c040c4468540140d13898a00c041e5101c011003 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 181253857 1250 181252607 181252613
    0xc120a05071710060f1101090606150503060a030605280902030106080d050a0509150a030f0c1d0402091c030c02031203092e0c050301090506060c06010b090117040b04050721 76
    0x142100e103e445d08100e128201402e00704000d0240340b010602414001888510303260061259602c8080b40c80103014003402004516940c0915a00460ba0407079400305003507482200030b058008183c10b104401a41c15141d208a803500b9a001d00c01c0244241c2c02040102c2d1194111a561110580c020300000c0d410061580002c0c465005000c0300c0101030701003c141c2181d01c40c0c04000d81c1003200c921001030303542c845c036003115890b070b008594007007101c0d007002540b15603082a40d54080ba907405199000303580000c0c0f039441a86034038481c0510203003c070352002e0000392545002880080b4500341688a03200384503e0821801c03c0b04100c0b80104441d03c020040d10311000d41a402414103946a0101007070400100300c44828240124611104a82e4665959604042c062800c644018144a00501d401e000c111081c0c03c0c001a00c03415100301c2a4480d44070809400101c03103001d01c000010b551942344400f48002c114018207424000c0d88180203481500e0303103581203030080780e1460764103080c0d4102c032003000d8000c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 181255107 1250 181253857 181253867
    0x503012d1509200c0d050708120c030411030606090106081005061c150503031c0207120c060c03140106050a1713020310091a0c120a0507171006 63
    0x10303031840000818565405803107020484140d0744880c2e440ca45a00d041003070754040e140102a0001c2d02c0400b14107241502000315521643d00000000f409000076284050100710410345825428490300c80805203000035190007603810079902100d034034600d403035031041d80c0c6008140c40e8032648001d45041c0c0160701e44281100ea4140280080c5280440b845000c0f5103610f405004202030591401c4203144050051040400c135042c819400311003001071141400303183e03000320464003a07a400008081854502c3c64425000f403003510002482045808070001006400c0100d03d0350250040c0b1042000d81000c00094050b11520240d00c0021001180140040ca00880107420401c00b50f00d0702d200c80e0802c52140ca02c200c08140c075005203840d1420810b108515081200e14140318140174103010b07140455aa4942d540b00c0c0c1551503420200e1080000c0c0c503130072103c0c16501088643d0b80380c541d4a08081c24404010602981c034100059214031804803650303000b510450048610300200b40e852031401c5002c0712 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 181256357 1250 181255107 181255181
    0x1020714070302130b060d0c0801050a08061b0915070f0b0f060a0e150301020c0f061014060a030b0d0b04020420040308070317070905270a240b0c0601050301 69
    0x82d02100070310042c042107d01d03212322411000c0c40c0c0ca4410880d41805d04001d0010410760107201c05601c08010008400c8100e070712005075550340c0741c0780d5031900410f0000035040c105a01036100343c1c010224030541800315143c264000c0030300452680e803481e00e40681070361202008542042e002540810104640000c400e1007641c0b0088000b40740b0095000c00c0e002900ba84e00080c1804065803101104194500302441780540003944010214083c074076110007480b42c946e072602d0b004e01c54a0003003005010303d8004e400c01b001180380206800c0c2d0070601c82c50414801c0d8000d880c241d028514006480e0118012000b0800c440780900c1556804d01c0d241d6a1005a03d520804040702001820b8442050342c072210b01c40140224900d0b11000b080c1070600d401e20441c1d03201110303200007480070b101d60300d0b1143e0300114541ea009a410940802d0b010300c85203c0c20318404a1001e2280c01d2015908001103440c110000f4100903121501079540a076a104201401d80748001c92000200f12400700e440d6002c080e98160390 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 181257607 1250 181256357 181256359
    0x3020a0f06110d0204080d031515140a1d060a02190f0803070801090509071406030702011e020a02070b030103050c06130906030b040302160608310501020714070302130b 74
    0x400d0503442e070407120310307a0b81000c00107045443e0081010701800c802403080052103802c0d803404200c44211a613480c1d905450307610801c9001721003854101070451003410401c141c0c0040a074113a81c0c1c0d4401d40d01c001d2560454459404050141d150300a82d02c1c5000c10440302400354550043c07051500c0e5010540701100b031400304482c950040b00110b03000889074005940728400948a03c4002d40c50304503440c040d160f00520014440c0c0000b50107003d0481107050018015809a542035141d0303070342100903401842010090035920329200c031400210602500281001e1007542e0070b03244c1d0140c2d588a000032a020a00008150303070070030a903d0703030181440741c0a4020041211542d4135042d64503020f44044a03040d4006035034000300c220800041c59010824508c51428143c6110442c2d03182180c0101a82d07000f9264405c0009108070450720034440c5504030480c02d4055164400c03410301403070058000e501054044400740d0402c1d6001078040b101091680032640c0143c80500b5600f0054170307410041103200802 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 181258857 1250 181257607 181257611
    0x1101020403020d05030405030d050c060a09062a090501080108030a050c0a06050910060506070302060105010f030603020301150306050702031920302a1c0f09060c03020a0f06 76
    0x1d40e84541c3c46100c0039014101450740c41d800c4c40181414540e52400340c0d018058200104841c07040e0002e11160f0100c2d41c1440062a10304a01d00035000c2c1500445c2108006149142103812803800c010024240000e034a52450990307607040103440c080424800c51a03d030b01b003407080b041351a010340001c040407440e60007659149815130b45e0b960100d070003c4c1c403689120780c0202400003103c41c0c1889448081c00d0b04441c0ca508140007650300960fa044140030301410407400211940155019801c220040c0d030f03009000380450759040403101810110b82c802a66502d0501020564941c008002c45000d50b030094004010404202000d0303800c2c1d6410000020107441e46140c00040076020300c0142214101c1495481c2580341c000d450301d40c03006002d02110503089040290a00c0036091101020a80f0440b41100c00c3c10f8412407442400e1120010828030200c0090810001c01035200c5003c00c1ca50038643c986001c0145c680030b044400700d101c04130040159102c10758520110340417880c180e0869100f07802c0 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 181260107 1250 181258857 181258859
    0xd0807020904050d020106060306080606011404120b0910060302150901020703151b050307050a030902040e0609030c0f0601030210051e04170c030105040803190b04020f04033011010204 81
    0x116104541c111402d42e00f942000b061201c00c150b0a0040c50010007061409000c0b5a0604007241d4aa4202604180c140301c250036a16009030741100c00d42d0000e00c40c00780500b92032545820301207400101181c2110003030040c0e12010038490002e02c0307800140c0342c0150513200785604245c0103c103550320556082d03042d0b00c5405000000241c03403185c5140542032540c40443e002e032110b00383c18441660240c00d03c050040034400c100030715074000141c1d031031090185808100d001c001d002040003407030441e220400303601480c0100710170040000001c011040c140b00484660312521820252200390a000080d40301c40c100c19898201c0d88124081d00c00805020001021128880f66202c802d92203940401c80a40c441501001140d03420300452a02140950080c4a149003680e0783c20f4152000a0210903156a041181d080001c0c480c0d02018041c607000e403007107503034030725002424849030014841180c0c2d4030110124100e6081e00d02c400007000314103018104808a442c12400e4644504450440c4560340d401c0c84 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 181261357 1250 181260107 181260109
    0x30a05033606060d08030c090a0b071a13030903020f01050c160f06051309090521030a06051012050702160b03040b090d0c11010e0d060606030c020a0f020d080702 71
    0x41403000384014001c10070414200c50420308199004240d10301c55003c0140b0784d000f09040f4401c4961250042d0002070790381016070b0008182140070303001003200d4900410000e0401206030031007881074038000029034250f903d10121000601c020b80c03008000855100c030400040c10300b100200c821341d034141400ca081c003406603403003454041d05821400d100640804100080100a42d02c01c3c0075041c1454601c0c60a86101485503001c48944203640c03006564010180c24850244075841249001c2d080e40c1542c0c49a8841004a81d001521804400ea182150003321843c0c90007049100c0c0b0044d45800c210300c504640c5200081c900146928158003d0a548143c01244a00f81c04089e01d8401c030803689074181810000000d0708024403ca64903072100b5111081c142d04111001c0801340c1c0005615111050200100e03203082441c00d03000d4120103004294020441c498005206272074552703508021094440600301d1359a62056005001801035000c0d03980541000e0070304a02840c09001728900d840c403d64 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 181262607 1250 181261357 181261411
    0x7170c0405091b0616081801031811060304030507081804060608040b04170c030f030f010f050310020d0204050603090d0809010510050f0406050607050609010501080a0c060513080304090b0f04020c030a0503 90
    0x8486400001c00c1f450b02662075a01403140b41244041c1c3d611480707982d111a5a080c28031850350f0702d074910500004c0001420036202e0400c80d2419588415400d481e0064081942c1341c40c0a1010402d200f541003402c089420ba229180d0580f04d190011000c44c096152034881100740151a020300c2d040701010000b849140104000405c03400c0c01d1205141e0f600d2515030880010718206030425081841c0508003004103581c00540c904d04c90030a01ca006940f00015a42c10009100d0381c0e004542101000c000c03c040c09a012030782d0f0844103040d46034800c007542da040005080b100c00303c1e0607019401c50072406000504000d8146401201c010300001001d58407030b000510141c11480c400c4a2603402403003044120003080c02580d00400304d88006254010301995055449031090203508104a404a504d4084450760380c41040102818000e6941c1c03161030b41da04a02a00d0301060850060000202c1c080c000d0078030b03200300d42c00421410b000d51b0400c0a101c038122502d52000e404030000c010481c1d00e204502821b1 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 181263857 1250 181262607 181262617
    0x302031314100b030a0b010501080a020405101215062001090501061e0617060906030a0b010b131202030a0609031205090606090a051509070207170c0405091b061608 72
    0x210001e144444040b140d110550b01e040c400350740660007101c4410000748024580a0545000742064041544d4032030400d0001c0c01b890703020f1640311100000d000c1003240c0080a0502c81d0900d8042400b01107050750446405207414880c00b80016003101c608100b10701c2414401c0443c1080c1d40c000301c4e1f03802c80354480b41d0942e0b20a810049118030b020104403444120700c80c98800900f5030b403c1c456500b0000700c1031080003440c0205030070f004004070000540c06540900c82c01c0241640208146040d50310740350310074020b03001501114803218440c0380104480da041c1300d8601d80c00b64010028032820944c0d943d6000a80030345074044003440158580c4900c41000d078024184600302e403100178041072074034108001c00110301070018108146010b007805005440c601182e0002501607982811a17161007a00320b150131056070050f80c24250240c00802c0d1100d011070165005841110305100c00d44485547c552980d0400b44000d407664251005c0d80482d00301100a0550300c4400001082da00c0f0346611001d6040e400 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 181265107 1250 181263857 181263893
    0x603070201110f09010f23030c070218060f04180f080c100902040c2618010c02010b030705180103060b0303091018090b0d0b0402040219080f010e04030503010603020313 74
    0x8003240b40d421300c0d607020460310644079013842c000501030460800042d00b20031014000410382e00000c0051051920074003103d0302c00768090501c0e6445856001c8100c940802540c00c544903800c0d014600d0082d18150183c10741c1140710300702c441c806058603607070b08080c406c0d020812034082800340281c4142d15401d00400441b81480d00001c613080e4854810841152480c01581c400d22050710f508e4461124140502e40c0d161a400d00100c040e80c803401040100e050000340301c05200d42c00d0240010391154190003401c82e8072402d8040380c80c01c98803074040085a100c221108803105646100410110740300b900304858401003d0140c0e80b5011040c40030404101804e8801f8010076100700042c030f26101e001c5100e900620701c006c010401c0c0928000000c0541c8000d10300130b400b00400c0008601503503503a0b411104039040aa6108000100d00c81d40a0003200b001c0b0358520703c050008000151129000b10b60f20710640c0c0c56601d26142d0b0707003012002d5009400c05483c02d040c1011070320060002980000504c4001c110b = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 181266357 1250 181265107 181265137
    0x33d09140a050c1c0b0d0b0a06080d0e060702040905010f020403020a0b090f090703060305070312110109030e06070203240412110304091a03010c02010501090f1a0d020d080f03150103150302060307020111 89
    0x103001e804c423805482896006000662280d0b024803155035010307603012130006045912a030f032451540005000f0300a8180090130035442c3c0643c02002091640c001d0088030310a0b599124043c1e41d44520303000e00c0c044c85041035001031020f0205d40440c640075004543c0001c60f030500141c000d841e80c03601840d000c8580c01c1240d94001000070359031743e43c0d000400d1041070320340240248112035040d03a004100703812640d900c074010500465404210364081c4002002c000085000419180385908030401807001070f03806440c0202c241117891701c09440b9070a030366039800d05c0304021440c107403520b9080e200409103003580c0200d5802100860700709580030f000f40b414401d081d5001191550400f0300113411202d003809031000c11454003284e244584507240b21b0301028131048400303802402d2130740041581522800c800070482d0304002211003000031484040c5004030380e40d0042c88440010b2200641c122840c01c140c0031210400e83e0410401403802e0002958420030340d1001140d00503003c10000c0103030b0442c65985602007 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 181267607 1250 181266357 181266361
    0x20304140d0c0209161205090f06041208060d2607060216030807020c130b031c020312060103051e0a0b0604060c0215033d09140a050c1c0b0d0b 63
    0x80781000102d50080001c01c180f031744240c02480058280700e0810710b01c1c8081d5407070700006102c0301c5050000700789401d6040c0c00c1d101d640c5850f24090500b015032001c08404500d002300400d000e814004640c4031440c1d4480a5490103000040100c1d042c0701c2200b82250241c4030405c51000000d03154000f0f0001242c181950200446252802405182000b0115030440d030104031076401d81e56603604c0100b984400e4031400201c282000340400d08000d0320705643c4024040280690500c20303070000003032900f20f40c040000401516030a004509440c4152449007078007088100d41d0050b4080c21008540200302103070001280b000d48004100603400c903a010201143c2d02c0340c891410740c00c10081d80340d91090701840da50300c1c44c03074201d50004580c1d0a0030359040400da030040d0503d0f0302004051000803651102070402250a07a0f03120807801620700c4c40801030901c000d41001c10f0301312015018003802080f50500090a0034050403a80c00c07402e40481c007074908292112400149521000706044900c0d000d0701c4c04076418 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 181268857 1250 181267607 181267609
    0x618071205071a0c011d0d0302070c0302030715120209130b01182304020306010207030f03210b0f12030f0a14070302010b030d0507050d120e100204090b041509020304140d0c02 77
    0x54062071b40c80c0b502407403080c1e5110100311001c1001649000c8600b00140c4a40031410101c0350a02c6d50b800081d0144200e00c5c0114551002120b201414200796907582c0e104468010000d0681c0610200140c01c00004880c041e2295103640010240380818034100f18158080808000a000903500150700211068007941d02c000300a0a200d8a18a0a413000c1d8614145100005c8d80c580b030511010380010594035007402050b201d60f01014408003a0000b4881d082c0982e0744140003410207506180c850451144108858107003003004541d26696100038508188540c0201821644400081420400000c0540c2c0c60303d0a034002510803d4000d0b8000116260030505041c076000345141d2072800c5c8803081c008800080c2000801c0c0070307000003602e080b0ba113540880c0c544601400f088001c1500500030041660310a802a40c041c00031a601030301c007030001c00d0000c0180001c03100c958007000008444010284030b09c0c2c032a82c0085420922a802d000c1d21445000702d01814220107010040c00160a401d000041d = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 181270107 1250 181268857 181268861
    0x1d030a060617030304082b050403080708090a051c03060b13031b080c1003020706090f020a05060c1209031e100f0e0d0c0501020c01060b03090618071205071a0c01 71
    0x802c541c4001503241d0304080e100c0d00ca15000701541c05204400171044e8071480c980e40f800341144030500311030a0020b400c2074030740a41606021a4a2400511040001030040c0d0000a403281002c0d002030141c0b00d00354590a40c0c0b2151000405001c0904d51500e400250711030403600145050a82d46558020741811442e2047d041248400c8001c50310100040901404402060811000030200ca12601124900b08240c0180c060004040c0840d0310341b02c488001d110114041c100413520884200c0000d41e1100104103403801120b00510641e80074a80207003800c01c141c00206043d0034024121012484004400840b038400354422642c41c3c0c120501940b03800e6a20700851381e144000003010301001d90840780c4140d4500c01680f400f01040402003081003480001c1d4110b0300e036522448000d104542d1542021811039209554003ca140729410000300f8481c40790140442c0c03052808081d00405150060412420003a0300c41544c0d20302801d41d00082c0d8812509600c5c82175042082410b44890f83c1303001940c2 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 181271357 1250 181270107 181270139
    0x4030e400504020105040b0306040605061b010b010212040302040506060d0921030218330403140703050a0311012912060613020708040e04080306090a09030801061d030a0606 76
    0x8450341007200707000050382c1000950b41a1b80e0511903507500c90f03a942d000200603002d00d600064000c0750008111001c51402c900410900048070001d002d401c50140049030b4030403041c2d00143d445003041c0300920061400e600041e4201d50300030843d50074840020801c0c1e045650883c0201c0ba070303c00362150a104003098a02c440e66500480c2011803e00004000d00c8004241486410b13228086401c040e00c08554001c1d01110798840a548482c040c1f0700d1205031509030351240c0801d9450007501880e0351202c120000303e84d03003940d6101d4041c082408031940d09403507080c82800650340c5552a001280c1c0300742da902c1f000400c61404050501c500d40e07404414408043c0908000d0366094002004202e0303d6215811071070002541780078010f83e903110a051104460040b60421504a8075070001c0c84140300c110f0000d140601c00c1111502d8064452030300d91421100451b500502048440c0e00401443d40035071300210144105211001d900c0c00307818002411b10010101c1102c1030b56840b03005200781640c4801f088 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 181272607 1250 181271357 181271479
    0x212040309060203040f06030c050705010f020a02010b1c031112030901060e01050402120114010306181d0d0806010f0302090405190509010b0102030d09050312010e0603060606070b04030e 82
    0x519141c00c6c85900c0c0702117000341c01841c3c181601c980381182091301c10000c603640190083c00801c101c03000700700444007a5015010f007600640c00e007000c4600c20300d0900c1e5008811078184020102c40e00302c0350741c180d0f01a60b041a8110084c05a550030640221384003006500c2111882c00000360706003081d0b00c4040312401a00460f010f60300c1446a48128564105000c0c159024800100080c1c3d01c401300403005444203420038800142c0354602200c03000c1c1c070b0b5042407108001445800e020710320140c407081c2d40c0f11111407140c400170707448501041940d40104180d060440581c5400340c50807a03c440841c0c25603005841460341108603108218821001c1e03c521904a496880280862101c26000039680d009100b0300c02140d5130b54503a140c00b00581041200e07204128148058507969617040c00108401085954a000f1b00404002401d20701c1c0080454050035400003407452a51a00d07181196180d030080029500580e00d5002415021012050000010b2908a0a0300740107540742030311030319001c1c100c0c0f08 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 181273857 1250 181272607 181272613
    0xb090609100b030d030b061b0616020a05030a080a0603061802040b01050a140d06031b0303030f110a0315030803012c060102060f0a0623010e01080103020f040903020705030102120403090602 83
    0x1856901083c401907143d139624010550395070f50303800180c1034416034503041400c40312658805a40200031175458400c8141a100303030034901e80d8260598803a07203c508010000e400800a455589000b00311042c0c00410301800002c8654a95079001c04446128400b511704144600c2514214034160084041d90300c000e1a01c54103044401c0d1000d0708181c02d0a01610004001040c1e64100d01c1d8140c0c080300040d504540758056085d034078201c001d4492421b0105a000030b0900e82e580d04400864010f41c2c02c1c07000300302006481c040700848110018506d071402c8041800b03035002c0000c0031540c468080d5003c1c103c11102d008489200d0340104000341100701d8501040340000e01000300c03681c3c0105010794084040340401c0d00319a1045034400081803d500b100e8203041c0e2450700501344442428081401c1c0000b038841d60700950f403040c0151082c00003403100035030220301040070f00f80d01e0610b60003004d8214842e00445600c2500c5000182c01c0ea00b04101d9012240b07119005c0006142c3d0041810300144042d00103 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 181275107 1250 181273857 181273871
    0x60b0909130b01060c06020f1813022a0a0c030302060621030f03040f1703061e0906060d0906020d05040c23100903050312040506090c010903020405060303070b09060910 74
    0x1403003209072414844d140502184070858024009140c04603801000103680b80d65030340f860860440b02103041104094003403a00e01c84041c01c10400742c803c0310340c4125410345035200c0342f03081e5400720810210466860310501a500320039001401110340180910f04c02c0d00980801e141c0401070110b00190003a91010328111650f125003800700101c2200d444c1c6502c1008113681c1da0752420312518103000110000d000d24186041d00c1c61001100c1c01460180d0340c200c980302058042005a200d500d100210403070f0b4800e45490100d00c1e1454054000d10035803421143c040350a160b65102d00d8226003210124100071615801080104181c1071500e1000c0d000e0b40d49800c90a000031011214481c6000080d6402004821039400046000c0c00c1143c0023158414110f036078440202000002c1e4403025070f811606480b481000c43e080f11008034000c84401810f9455485481c030355002c11000e010050a6584c1500040101802040c12000076510401083c40200018144105040c1c9080803600c1180b01c1da03442c100b6 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 181276357 1250 181275107 181275113
    0x1a190e010b0a09021308030c0102040614070203150612030a0203030118020c1b1804140706030615030207110d0f110105030c040320040203070f0207080a020303070b19060b090913 78
    0x100d00b0703095038204140162a0035010041d440c00b203140c1d40100d0300b54800840c0c41040b46405400601c142c6071940d40b0309030408802a61078810b8003440c00c0095040e004241000709903c01c129103286d01c050300504480c00c460358480f440d402c640c05441d043c801078000200521000140c00707580702002440c02004c500c5e00b28801c0c25a516403500360440d0398401d4504803038a115a4a25420643c8040f81c81c600d0442c03401c1900d4414440003555450044c5802450000114280640300b0241190340c82440c082c48090004811030007036100302011112004c2000c81640592500010300b22082d1141440c00010005400c0c104040d00341d0040050400104104001c103850107402500e080b00d6100c502030b02ca0002c1e40c10305802e6420015816030304644044200b0500b264090400c4803070390060340039100311170344881d407281d214902e0302006034061f8820019103000925103138406510841582c0356014501060301d094040d60b040394485c2c241c044020400444a1400039000f42e003001345014001e0001480765 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 181277607 1250 181276357 181276369
    0x21020a0306080f07030b0105010f02030c0d0c021e0a0b13030f1b0b0f07121b24140c03070c050d020d0306060e0307051525060b090403020a06091a190e010b 68
    0x409039a040214035082b600c001402001034607540742a00c41038851059490748014141400808242d106028501400420196449003d20001400b4000d40855804c0402060f0b407540b12030344002c0002a620070000105109110008405210710079644070342101c2104484544400e400c10444a05d040060a400302c91000840d400940e11082ea0210012035031001d490140480302d0310104100e580079040304120541035040c10b00085020b107829480d159058450032140c00301c030303503410317680c0b168000c1100281000c01465002c0e0703041c0b8001d807444240703541d40741c1021200810a00076074032000440101c2034050060300060710700d5241c601c01d84281d0138002951048c20340310701c6003c0c08241c5c0301e42c004031080c2411100c0b10f910845101300303040f219591440300003c1110b02540c020340ba0080015440c6042d650007806150103500510042d20581c4a000040c045100c1c1111030804008100782c500600c1a02e991103440040c1000290062010303a02c0d041d10310520300781d5026450860101c1c440c1da030752 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 181278857 1250 181277607 181277609
    0x10602070312050f1308070b04050f120a1a0402010201050610080a0915110c010501050306010b120c12150906011407060e030d06080d0f09031221020a0306080f07030b01 74
    0x40031000c00300084001c02d49903403203040c0440700107810001780c41a10200b12040b1104030340000c011036408075516074084000380254021281e1001d60045200382d1403800d440d940312902a0300e030540d100b00c081c5954801d000c04015a662180e50000000c00c000d641e02032140035489034094455204c9030003410802422400000c200140031a551018801440007101c40355181403258001000240400700c0b01800b02d070403460b200b00c0c0d00c1d82801c00100c0c06003004111641220b030740c0c148103030500101e040001300654008090109816040c440415680304002500e8050402505042005160340c42480b0303403100f00808032418406100d111800d516485400c4030740d015081240040d5074009960064258461a4a40c807107250600801040c03010002c0307000081074000c0d442d010002d0041100a8501010a10000c1c01d408803107404a00494044e05440c9400045400c61000c513001140e015001ca8000001c6000000d6454006000c2180c08004a0139800c0300b03a001411202d1035507654080c2c580301 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 181280107 1250 181278857 181278863
    0x303160503100302031617150412030207020a12060507030902062502090a051012020a0501030504030e0910150206220c0e010303030b01120c0e010e12070b041d0106020703 75
    0x400030004499910b624160005958020151103113401004c6c1540e400c51a5405264941c884a44d070280005400140004e45010303a03000740c440c2603455032280c40c2da182c4011080c4061540801c00d60300141e85030501c81014100514001d600102c0b181000001c6540080c146c406040c585142c0a0250b03035a40c0a035182d11042480d100055041110240080e00c90950300940296502c0f06020139a11181c118605c034162601081c424a9a13610011031080345e0003101a4005400040031700242d44a0341060750b1103800781c00c1004511002901150915000322803001c03240c50b80341c0b001e1107982640c88042d200f0007105c0c4006c1110f410710950380c0c1c00058412281c03c0e200d4059250703050400c00e04510740380082580c0701030a0865030752030030b0180103400a10041ca001070000c040320a0b1030721303c51080e40750f24069540c3e0258400c1c0f005005640340c41d90400b07801c1d88020f241c4105e940f82101000351001400280d410107454610703210780001d03491100d07004900984041c00c0140003042d4000381c44021260 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 181281357 1250 181280107 181280117
    0x12030e060903100e0a0501020315010e1801090903050c031605060a0207030503010b030a0b0d030522240207080316050d05030103050a0f08270109090c09050103021b03030106021e030316 81
    0x134001400529262005d83c0c010403c2d40080200400012125641020414281c803000f402420790b01c100010080280004445600f10304014005100700f9400b5405061203424007602d0440030850707462854101440c106a060b600e486480100101406a40e0300442010000d5040c0304040d50040e045000500030070500b620b02100041001460742c0040d0503c8201400b84c00506c0268100189a40c0c4509003003e400202101c0b000d5030a03040b507070702c0e108850344140a111049060b07504103222080900039001144110b09021a00d4041407000344058503000a10010b550501e00d421b6007081396241046090280920040020601c045558290366a0148403440e12900e50b140444080c011944581702c1801041c2d40ca90b80c20700308103507500906000762541e1100300d030388454000a031692561108001210706204201c15400390700a07121a100c0f0240c06101200c84256140c61034000760720000c010391142c100c505c0701118043c100541e10583d100654550300e04061420200b409030224041081 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 181282607 1250 181281357 181281371
    0x1b0303040b091315090e0a0201122004150810031e0302030f07140606030d121a040905061b0a020706080705070506190b1f0507020a0f12030e06090310 66
    0xa0360b00001c0500808071620100400c80004c010340110076000e005414101d4540560744481140010301e4440b41c590503582d480c18001c0a1060502926404d4004004000c18403001c07000c940c038084c0030304013909440e03c4440c01e900c00010001d00007034001d070502d9802c60a1800900200b0703513420350038548005182040501020520b0100d1841c0324099042c0350018001c1419020815149440442e00300c3c0d51007280d06607114802019100d010202103800425a441140206d05001340c11002d40c0c81d0020b085100920007883c00706080d24100e038800c0754107800270010083d0400c0c0400c0e001c030a00c00100d202a06104111030040d644051034041e407414880c14400240c41244110115905a40e2040c1900c05500f05207104505c2a124042c40e00d90103400d0a40700140e80c10030318403001c0724502504480000440518056400340c0c0030840680e08060b00c0c03c4086460014403c0200041c0081a08443d0a08150400400240841c020a48a48401c101307071010399800140344e60f152600c0e0700000900c4 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 181283857 1250 181282607 181282609
    0x3030601030507090e1302040516080615070f1a1e010902090a03020613030302070b070f0204050a09020603071805040509030901030b0f040608010b150f032e080a0201021b0303040b09 80
    0x4195512a118080e0741e5006c00110104034a50f030000d07103101356028041a110503100066030400c081d07013800004da00c140003a044c0d15101a48403510700b03040058516040042e110310900fa6580d801c00d880300700d82c05802e1580c50b610350300a180c0c000700103040400400c603026000e0000e9801846540402034000c10803c51b1aa9402041002507900074189699240600080039807805140701c10703405800707201400035401d481001262504c0703a000c1842000a00c0075070821004010140030700142654a510803001602c0b944011401608640ca55202c500e099407403600000e0f1443d00003c0c001c0c1d0411060141c0c8140005c00d842e4080000d08000ca0085546400b1400700384902030344a50050400c0b00015880d44194002d0080040c10744a40344485142c0601036a20302c00c1603a05a050001040040c440c000b0043d415041c1400718005001001414150803103d00c140341c220740059003011410000310368040160486079072500300f9203d1000381075000030303449004a1080c8190b03090001118202 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 181285107 1250 181283857 181283867
    0x30504170706270c0b090d1401020409020f13270b031005100f1502030a180302030706050d051003030e0d0501152601020310050609040e060412030f0e03030601030507 73
    0x1410345000e0444410fa0120101d842d148800c02566030b02c842034004240c604014040720383c543c00c041c080c210000025079818001c54400c20f4481c0440d5400c0c40040344890183c0010020041c141000c2502d070340d801d03451481003074090303400814110724000524601000d0003124403c03401c101c000c006000026180440c0c20030102d441600d60180c900001c00c0740b0b82214107809d0041d64114020b04252548519002c610354105e1000c40d00075034414081c1c8660140315180310403800307901d0408580f20580d80d90200b880d00388145c2141010500c00718205480100d1813040c0d0703070b0040304d05010080f018510788019060341d15031019540035400f2030002c481130001c00d40000c2c0b0320400b0751860900059541d420a0851054406401e25210400100070506001402603a0180307925402c407451480c5400c08120b000d6209050301d41d00580c40702ea40e6125545d052041c54803540c000c205c5081c844400c400024116002c8100c4580118038003c1400403074034002040d00c0e48910b080c01c00181a44070300d0005e9034 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 181286357 1250 181285107 181285121
    0x2802030406021c06140607170901090308070803061e1003050705270f060a02060a09060902090406090311070e010504020c0a02120d021e06060103090c05040c03060510030504170706 79
    0x10032003082e50b0803c150043c194007000841c0c011032009520002c100c0b0400030148100c1d100600308480c59140303801d44403065802007500d408141030400d89281d4980d514403554111540035a1035240100c10800281409000c2e400310448020b2242820340d0010005035591074090320740030825035900300082490b170186049504c0f1440401c21085482c00841e4000006c0d010016030342c0c0502018070f860410342c14800266041e00ca02600509159034424004800070880001c054a03441c0e125100700001d40c0b6442c0c650340c000c0e80110004524484242800341001c0700c038215000d65580b00b00400c0140740c0128000a054681c201c0300540d0310070840d440c8628000b004140654007509011002010300c0c00003480426900c0d03541c0a42d00985105151810305100e039000584540e0840302c0011034640c440e510401c145881500ea5a400f192508046002c541c090410040860f0307480e1010b200f903103024120030b8030158061501f48201e180039510800d2031152030174901c00020000c103a070402c124490308501 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 181287607 1250 181286357 181286377
    0x1e01090906030501020702040b03030906040608070203040e010602150114030a1104090c0b180307050906010e0d050106060c060b040e21090303030a020304061503050309152709280203040602 83
    0x4041d2030380700e050141c000d601c0035100300d220f0303440c2c009605110704003c025210f01d244002c20880c2041e2400800340c0d8941401401c1d4011030008010101e000200807004034041d1400d42d00802c10140e0035944003c0107281a08803c02140481c95034000700da0300090014410355004500440c10b03c803201c00300d0081c102d80c100080c000300030078401040c2c04840c3d0740984804600210740107124a04442819144d28080c054250010130113000507001d940140c5402500c45005804210080380f99110355003120b280b40c01078070000b2000c9041c0030900c51540507000049004550411840c042103502030359626031176145800c502d074800c0c09070b41454401000e84500b84800750589a4910b00701d034298000f54004c5400300c032420301d02800000c076003c060840a0941c0d5101e001140303498009001c01c14444900904c400702e000707081144c03403042e00400540e08481d9202c0249407050030300c40000c20010000050600c0445400c80107159803200300342035410303c05255034500507903d8689007000b04c080d02c905c144071 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 181288857 1250 181287607 181287611
    0x20619020a0c0f050c130506090106030902030c0a030b06010e030f070e070903050a0305040f08010c0c230114010509010b030c0f09180f0603070f030f1509050f060714091e010909 78
    0x7800f8804045004403105d24210b8592080c0c40500603c0d10403500161a00f0340c1180d094001031061500a610000d000c43c001000c075107070440c860001500c1e100e0250400c903080391940d000e00445507080b06503003414010890181c8045e070004a107040e6105070f00d01ca4a00c50010990101e09118086c403c914041c5802c44151006000c40e030902a08a034800d200c0c5070450080e801d4006650901032103503c0d41007681d075907807182c0e048158840c01484240190b2076200300c41904211741c04400d00340b240e0407189020b0700c0809070300d40c9400104103108805a00107810303494104204a42c0340212012554081c2800c1d10703454031440d411021600c82071600429251a03280c547c28071041d012109856072040904500703c45006840b252602c0b210301940c400100800030140d406070014291f02c6912017800102000082c1c1003015454a03403414901500307098003600f00f40240040a6401120080200611a0303414501204440418001181c42ca98108005150800c000a0380e00c1840c400300105200901 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 181290107 1250 181288857 181288883
    0xf05161101090b0408010b030601090204050102100b010e060c06090105070503040308040b07050d06090504060e07080c0103020309010b09010b03100609051f120c030b130527010204030501020f0702010f020619020a0c 94
    0x17264000d000381a076891080c4940d100024100f2224000c64090341c1c41179014005218200e0b5504028015a03940141404000820507940b51101400303403031080d0807900109180e040486065003198006050081040420410000401d4104411540041d4005401b0305145c2c1e410b40d01b1155800b4200c42d080d141e600f000d200041c210031642166000c0c0b4010401081100d00303100540e40d540c0311920413108543c01400101d601c83d8001d0380659442302812002148010310030b00043c0b8200001d030000d00102e0808010b0200d00d01d50505081b001e8200380c241900018105800601c004040c491341b45c03d024030055400505502c101a22021b212918400340071141208074050040c02c0030398034a502030814051400d400549a000d9175008103240180c645001c1e054490042103c00d110700e100480399000c02c0000300048091006040400381d82160540300c0c2c40501c0010b201100c51140d000c210b40c0940c0500c58141c82c029055203c1300c101e0900180c0d101c0c9122001e80710024036500c0502041e0744030701 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 181291357 1250 181290107 181290119
    0x50d0b0303160b100e13021201020301030503070c0b030c1e07021207090c05181903153207110f03030a092102030a030507090b030a0c0f05161101090b04 67
    0x1900b00e84511580544200350b54400f00040d0303500b00c0d48600c090440010000ca03100b4651a507050305410f0025001a50542c1c0340558036080ea402a4004c864990000642809204800d107440001e09000d1454519504003100c0440f541c0c0112030301d640140100700c58036000d080b46001120201070b8040c0030440f141500a00060319001a8031403002d519060101c4030b220503101d0760480300300111440d607003000701d03040b90305101c0d821a908003400d050300b54a50010001c2000c1400c2c0003241c18400401042440b0180d1030840c0440c5509040941710540c19010064821890038030707035100e00b040c80d00308030106e420b4043c0c601d0000d4400d441d140e90b0000005210500405800205515015610002c031400c1a4003980c4032580245140c680141c1050202044881c0320341c000580041040c5081180d29444103000c80b00740c0d1003030b030760054055649d000103400c0a410002450641c60f082c1415410b00391580c2d901c480c6240c11010040c03604e5044020b442e0300b0380c020081c03407003d009090540c03506d403030300c0b070f0 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 181292607 1250 181291357 181291387
    0x1003030c1113090c0905061008130201050c06090a03030b0f0d02010315090e150601020d0903082115090a0b010e040f1d0609190812070207051f08010e040c06050d0b0303 74
    0x4040c1030105d608080000d001800c20318402500504079613a1130081e6900d28010304d0b1007101a40049040180400900002400401a0324092600480680352500d01032502404a0b8443e0748124000c0019944030484c0340d40c0c0b6080034203071035020708020542040c4500010010b0700250080040f2600d41184003480350400118404655801e1000e956151a6a4010b9075140d90400314000000d58146080c0b0000c4c0302280a01080d00b42040114020001116144140c1d00101d944007140c2030210041401840d0000307401d80c0141309040204040300d0f00c100020a0700442ca0038644c002c5496034641c0008000302c0c1d01c540140382481104c84403501203402c5071521485c0581c1c04442c140705400d5203020101060043d003542551068010349403c852810001c041c400007419042907020300701c80020f05440b0b21003404050243c800da2744031017090040f8046c00c1d1080c103030000e145045102c03040000040e071225000c0103540e8641000b60b1609890f16103031029044265425400d800041030300c3c40f03c07458407 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 181293857 1250 181292607 181292609
    0x40b0402030907170303010308040b0c0a0609080d1a0307210209040309050a0b090904140118030f0306170a02010e2b060e06040302060a1d011e051003030c1113090c 72
    0x20304450326581102c44d2480d9a83c0000c0c040078100c0941000204802c01941000301856107040040d11060700d2941c840c801280c0004030103450201c40010a400380e4181e134400e00d00700c07243e00ca00c4240c85105050200781d0342c4129004603014586048004803008140b401004080d9900400024080c5440d02d00202004039500c1014010312a180e07002c50f03600d02450a0b50010f0320040c10145103030f40c654440030f03803440c01b40d000b1401039540c3d6403d0038100c420405007500c04601075110429100b003811402412200c15502509030703021407402443c2c0c500d501141e0304805540900e0640c1e0650391110010700614002801d0360002c074603210f1040e40426074003243e42c80003400b8090800034820300140154a4540c02c540003401604401b00140c1024110b0384050f51840c0002e1148101c030a806010030b0840780c2e000e40c411502c100540e040780007010b45000d10f43e440700501065078855032031582c010b041700600c018000d2610005011701c4120b901e40e885002e560381c42030b60045c4145805400c14005910385 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 181294964 1107 181293857 181293869
    0x20307031d0d0b150a060f1202030c0408101b052104060605030d0905031c02150703090c0b0a0f05160f05030c010c181a0414040b0402030907 62
    0xb040c104076445043c468900110000f4003204005840c0c2c001e9001b041008030000c500240f0a03480018801c4e42d46620700050f03126250100c0ca500f1601841d0000d2045115107015070f1014400f40d0410078500c005c000c01648140b1078251b003115070707101300040007000c03040040d4041d0701e10388400c220fa54814016000054050384520010b81002c0d280205940004c800e44400d014034901804042011541360b40544c2c1454540302e00691200240000140040044000280a58000d800c60701005510000c4541c2d410b442d48030780405500a0100e840010790341542c18000140034a080340d242e0310481c0e0b000915181030344c2d281c0c00c0c5c01043c980100c440b80405e2000da130306072909024042510f0362a0310752201101003d82d424500381c0c095401800040307452000005a200d0903c100da080d540142c0d25000c903882d544e000318001d8a07207800e21580080c030020410450130804101402a189 = true := by decide +kernel

theorem cover : BRFrame.Cov 181115107 181294964 := by
  have h0 := BRFrame.cov_init 181115107
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181115107 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181115107 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181115107 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181115107 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181115107 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181115107 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181115107 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181115107 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181115107 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181115107 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181115107 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181115107 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181115107 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181115107 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181115107 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181115107 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181115107 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181115107 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181115107 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181115107 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181115107 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181115107 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181115107 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181115107 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181115107 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181115107 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181115107 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181115107 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181115107 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181115107 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181115107 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181115107 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181115107 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181115107 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181115107 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181115107 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181115107 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181115107 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181115107 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181115107 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181115107 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181115107 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181115107 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181115107 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181115107 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181115107 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181115107 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181115107 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181115107 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181115107 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181115107 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181115107 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181115107 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181115107 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181115107 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181115107 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181115107 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181115107 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181115107 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181115107 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181115107 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181115107 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181115107 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181115107 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181115107 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181115107 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181115107 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181115107 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181115107 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181115107 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181115107 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181115107 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181115107 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181115107 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181115107 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181115107 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181115107 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181115107 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181115107 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181115107 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181115107 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181115107 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181115107 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181115107 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181115107 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181115107 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181115107 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181115107 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181115107 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181115107 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181115107 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181115107 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181115107 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181115107 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181115107 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181115107 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181115107 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181115107 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181115107 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181115107 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181115107 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181115107 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181115107 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181115107 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181115107 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181115107 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181115107 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181115107 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181115107 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181115107 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181115107 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181115107 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181115107 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181115107 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181115107 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181115107 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181115107 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181115107 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181115107 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181115107 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181115107 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181115107 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181115107 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181115107 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181115107 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181115107 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181115107 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181115107 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181115107 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181115107 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181115107 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181115107 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181115107 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181115107 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181115107 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181115107 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181115107 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181115107 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181115107 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181115107 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181115107 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181115107 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181115107 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181115107 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 181115107 ≤ n) (h2 : n < 181294964) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
