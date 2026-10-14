-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3340
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:22:16.215981+00:00
-- url     : https://prove2.me/submissions/4e334c4d-5260-4ceb-9d86-43792a39d30b

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 600539568 ≤ n < 600719424 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 600540818 1250 600539568 600539573
    0x70807051312021005041206090227041e20040f02180a0e0c031b07080301032415170309090901090b0a0e1002032d0a0e190611040e04 59
    0x544030b180c090b841142c0b0710850040d0140903030211003d480d00c00540506642043e1240380c0900401003081b60091085040c8013905180c010b244013000d01d1564041840f810a400e2550400c5201030182c00050080c049440010b00c00e08952804241180c001d0100d40744c600c00020001c1c603000d6071b5440741d9800019010019042820900d01d080c07c03c0724081c0103d5100d00364201990307021513514041043c00c101080f180c2c0d0100716011015005016058034101450742d0744a802e4001f81e0045452100801010301c400280202585203c00d088078104540c2004d00190020329010f80300d50003451036080a6000001028400c031203030103401414502c05800c10b20080c034001c00400c1e0f4141c0707600e00c0c0c2c10045010b541c20b600851207030941c010018111030007401042d000a5001030f15185049089164440c812802040400c4601c151076030310303018524241c40d07047c1c207941400c0b41191a9400c00b0441d82074600d80a030410ba8904d80001000130311a482011030b03009445290051101d211320070b0104000c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 600542068 1250 600540818 600540839
    0x501020303040b0a1d1c1d041e0f05060f040c1d030312090c0301050117030a1206090f05151801030803040f050f100c090302090612010b0406120203010513030203030708070513 77
    0x1c5039504040c003100550100c0746c12115401c00341c80c14541c1c12000e4482281c1c0e4501500f0080104a0356401301103050f030038107903200459000da00600b1065855104000162170041c035840d11600040e281407054400422008100380c526400340603411480c110040031644040040e100c090301241c0c40c3d03c110341416102e4554411209104c0d034420741c20329001044a01641181008480904004500303241c4004010f9a18180e00c5203400206581d4090014100001d03014101c17008940c040c000850382001240303d168807039100405401500300f004580400b0072001000703411241c00080032a1251940e103801001c000400c080a841481141400c8110510104240c40549144c1c0d170100116040100103036442d116a120180d40021003000040d091304140c41c00b031880540d0840000780c820178010000e0115107089d0840012a807010444504506092140e0760700024604001c040380407003960000d560340300051507031040000b8040440c184c60302810903108449012500318400a84a400440 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 600543318 1250 600542068 600542083
    0x30b03190b090c0619120c0305090c1c0f02030c032d070311280801060f0b131e09090b07080a05063102180a0f0501020303040b0a1d 58
    0x200d641c010103011580881000880c2009118040c00d460b0400048240751070b0402e490020074014089040090001c400c0c861080d41078104851f01d0015481c1001010715103041c011254483c0200c010070705202024441c545c0040182c1e6010300e81d100c0142051010078280152406415014824011400100d0607a10541560704401c9014800054805100140d03900000d100c040d02094441e49050050305040090802042c168030f0010b0704502244103903e1105010750104841740d54600c41440110601e802c024000c0855125190500c107100b135880b1084200c902c59882684d11040a101c00f200c828180800282100481003103042000c1c146824000c204451a0300090001000940b03584a1480f846005e0340025280c3d4554501542c50141d0b901d961003e040e0010852255501d80400d00340002c280c401d03802c02445003000c10400c2805140fa145410040a41102090922150f64000152580030350890541c0c0030356204c9406682c01001c40600c801710f00011007170040c542050025550 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 600544568 1250 600543318 600543323
    0x115080d11010504150b0d0209040503040603060501030213091d01050703021b03072d140102040305010e030f0313080408190201020f0c0303030c0d0b10030603110103140412030b0319 80
    0x1003107044484000542202c0c0100c60080003103074038026015040049600c8800341c0040904140c10300d407419000100d8051045070b00f29800e6000047c1801010307458016500101000e003800d505052040662003192a89802030b4012196100b601d10343d8010b04a000c40004208040200a81e00705050014069480380104600040080c141c4500554000040760403e5400c07440850003146003124030130030402c200f404000c5051500180030045402e684252150006081c00103075140d19625096083d00c1d40400710345640e03003050002d03142a0381494100c84d480000b50201401c40781c5540340100c40c502403500007a03030034800c50001080c0b40300e4007d02c2c81032141c002d80071070b86071010700d0b00b540342d546409a215517019001400410002041d00f0043c040e0301c0c1c140403021504d040c0c00e40100d00802ca03c0c0001d1400240c5600040040c0f0004c41040c8203905402e1030184644a00780700603d142040c00760008004041104040e91000e10950100b040040014182c5000780807501e5101d079241e0800500313 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 600545818 1250 600544568 600544577
    0x1c0201080109020f041d0f0c0c032b0c03050402030c03060108060a1e0f0203190b0609060f0c0f0d0909060608130f0b0c0c060c0406022a0d0b150f010e120115080d 71
    0xb0030323022400002590464480b031002940b5000381b00c040344202e4030400c0c1110455696001580d00c1c0c426550084c0c0004044556000440f89042e0042618219140618600070340108006102c1028003040e41c951203d0440d070041845010018002844403030f4008046444e4078200d011010205290000d500611001482520100003410001e003160695140c6940c0001c00300800103150401c02c003d0010140414001c41c00c110a40c41d10504000003074024900b903412000e251407881d90400400d8014150000003003000c1b5060100142c2018000380c480c1c15607801070305101040000d40c0410b10340032a4084001910745c01c101800b4062904041c41e1601240259400104e6074542501030341d04413600c2d40d004000242c2e43c1c8100c004160400e40780221500034041c14420151180f84901000610882540c0c0c2e442c5045004003001c01c00b000080c0340b0075201048191850b81e4485900c903064042110b580d94403214807100d81d8014442d06001000c400d012000006031044007050f600c0c0c0b2050107448 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 600547068 1250 600545818 600545821
    0x501050f3d110c1509010f11030a0c12020c240c010f020a030b06090a12020310240504050601080408030c1e04030b07051c09141501051c0201080109020f041d0f 70
    0x20031401030542d13080950030724030034892140c0c2c540c4070b040501c400b49202d041502c6200c020308032030f90555015440e1306010444041c0100c0400c0080601120301070103903c0680244000100000c0203800c0d0080c0c03100100a08000ea01e98070f14440085608902010b07000300030b80140c407810348019421100c2400082407900b034001d41c03142454070442d0300440006001001107420204071246075524070038180e800d0302c0340314a140e282c4c0c21b561141002e007450301c003025501400e03140c0003151425280e401c503038041d5041105000c0c50341d80186a2580140d88082c00f20744a98910ba500da14500842c0141900ba1801d01c40400d40d010041c070060003a60301400d0701c2807269484000179581031040c0b95046c81c0500c200c54400301000070b05d0340260401c0b44151500c615070f06442100900d4041d080d910742c2000c1c50314000402040c580340d02d03400c0c42d442da00c0b81e007069061070540004c1d00901d4148500c80106030001500304100c14000f0885000d001c8a403980200c4038030000d0f0008401d40100c9810180090610 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 600548318 1250 600547068 600547093
    0x607211809090510050c09120610050a0e040311010e161a1617040302040501090e010605090601020307020f041404140106120c03020d0501140117010501050f3d11 71
    0x1601107180d000383c024843c0c0803051003000000c00c0010920184000140503508195944c4e81001c013445245000406c000d041c844908941c51019501081c440d005a407000c0100364001d491050b445505800d0100186071004407071400741070000c0000155008281c0100201d800c40800c10007540c15503080800842450040400781c0d116001d07201d1900315810307142d00001904000c1c24242d05041c24811402e0555a034045401e984017a002045000c0d00c03841a1410100309105640c000d100466642c4100d00306000041d450340305500001e401016035200105403905e071500014000301c083d2550b45803600e001c9c10400b10880e14194820055420480001510503c4c9444a031126070015041d8080c2440d503420401e14200d050001c50700f5540700c400d4800b03440b84c0c21030380c00d0081828800007140044462613990841310142c220610a84007040300348204e84903070002111203d000c02118441b01400322004000504014020002006502424a0980e40054540f011900210846803a4407508 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 600549568 1250 600548318 600548321
    0x61107060804082101060801081b01050a12020408120c0709060e070f030b1207080c061201050d02240918070c1506050d110a12110607211809 62
    0x244200310019070350740041800314164200805001c00140541ca19510071040803980840b4260701283c00b00b0841c5c0c0041003226402d204014036481d94800d03148000d0a43c1001910078001c1c1e5034207004000c02212030303241c0c81e040c035412900506102d4084807801c5000311100c1070700303034880a04540c00e40034140c4005040c0d040c0d03000b01420b40303600d805800d034942e8070787c071781100c805410010f0042015202d08580b01d103511905800c0941c11903032001b40010300d09000115141516101d070f510702480c801c000c50000003544020ac2c3e4151032007200d001422100500000b600c40c440c0790402a400b202c405c00e00e0b9508c02c25080101a402400c2d1040206081005030146d0005401caa0503808104074401704000105601d51050501c05c1c1030400103651900c98010540d04806030908481c106150082c6841c1840d110340d001004040c2c0303142c00c1005410942c0c4100780343e401c40400c940a044040340c004100550079001c1c5030611038080d01e403840066400f43c001e04035200c1c42100d5a8032181c2580114650815 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 600550818 1250 600549568 600549583
    0x60309030301060e180403093f0501060e1008010f0608150603330c0403150905031c051e060d03080c040504110a090803070b010b0a09051002070611 65
    0x28051400c1d03030710b89482a24082811a45694003014141d0100082072100d00e03c14001c6000350303202400a030401c1c844007207450303a04201c640c0071001038209462a8009990101400d007000b070b50915142c000d46400390160605420550104040e101001000303241d151107402203941440080c054007419156510440b005802580c46580011999504140003a2011604000003030704a9210740034101c8040b1580c0248030b00420201c030810303c0030094003030115241d07401400c1e00138201e00c1c0034a147c0d500402c00702e0916074140c1c0551582c07810801d00005000b5100e0500071034100010b54440e00e01104000c017070495110f000510a60944130300140b40440c003900c10000a00090128400e42d00c0c2034580c088010040d10f4400f0781003001050300d8489018074080740b1100400310340c0b0340300d09040280010b502c5410041c0341d80d0007844510f0102d0700359088241141d50440425984094000c801c55030b11a0607044580c105801e04503e00c2e403240d00050300803c607030140d540e502d0a80303100d69865449401 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 600552068 1250 600550818 600550831
    0x1c0c03060b04050613030803091609060f061d0603151c08090f030309060d0c09080303130809042c07060504050d0b0c122d0f0c030a020c01020301230603 67
    0x405000034401800c24200a000f179880500d01c13020351030344d00d07907480c0b4140d40103c441d075407150014964901d440b0b03c00c00403c1c002c3c2107070702824030499083ca006004405594800e010802c102410b4502c40d428032000b803000d015201416040d0390385814054441102a841c401c18001d00c80e190307401000040740320046562035400b074165403400d068a0100140c4940f40240c1940c103000030801070b0b003982d90340801001244044080801c140d6403200c0080c0401c201640401841c0e0010010448603001c032604800784e02e9401120651035200043c00b19006103403402c440e22901c602907000c0e85004642e01c0e410580003d0960448080c2c40e216801100d641c0183c0c4920742c0c0100440e4103910000d0343c150a000e5100b5001004141001400c002d202031103103003540c01a9690409a100307111f8618110f01c11154001c4002151306070f41089581140221070051807076406a01c0130000c2000c2c4003a50301110014000d010003903440b961a40e01e0007035036040d214070403440d800780f10074190f2071400c180050f13911070f00 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 600553318 1250 600552068 600552089
    0x50a0b180a030e0f04140610051801032d060801151a0906071e05100b13090516081614100503040807060c120e010203090a03120f021c0c0306 62
    0x50075650030342d500c0b640c0c211455030006100c0c00450b0703076454034030070022480c02080c44015242080740902030707502079910a08040040812090285030070085407203001900a00e40003c1c044040441e404240c4900420403107407800003048a07070031014640050082e180c03500020015004c942d5403001106070184a440706551000c0400b002c200204000344c9040c8c9006002c4500c4c2201e2561010010541804091418250340300000e080c480704124191000012503c1001030000020000d01d0740e51040e1035800216803105002c0d01088404d0020b1820607002450310403e030b5855100440c2c654001600c64201c00d00030320130018010426000c90351141501500415032003030f2481048420b903000070310640342c1403420000c3c030380010950700c0f901d0503032445907803102030b411207110b1454240d07045140c8040e0076078018414414031010220380c000a00e68076040180ca49101144080c01501e4030318030881041d80b003c16225404100000c40004c5c1a1b00ba0a040000c2701c00c8010039411141a4081c0d440f058 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 600554568 1250 600553318 600553333
    0x605010306120f060608030307020a0317101e080f0c011d090f07110d0f020c0d020f04020d0b0307060c021002070815130b04050102211501140c0703050a0b18 69
    0x203061140d41110f214001d41c00422443d448201191070b560040d42c8620045c0d00c070100007070a15620021107504001054000072085c200a29841c0c01c02c030150040c421180750081090200c114202005401040494240c941100e0303441c5a40c0d4644e01350440503808245c3c00c10f0b41c03c1c03400303401103404c03040a02c00501d2956552504842036150005c01407481d4140911050754407030b2403c080000b0000f5145696070072003103820f0380400074200340820003500d0282184007000030041e074844080021481c0182c81c0103880c0c41e550030b51400034211002400d1780601031704070b01003407607540a00828134240c000d0b1000c0c04a00d03003540c02241d60b560688580a0306400100e894410f41145110190f0041c00c42c52680b01450324030740f105070804078141c0381211640c0d030025072512004800d180c120b05c010007685200303c1d1490304448081c00c409040e00700e1410415107000c0700c0141d034080010355500000700310444031095101c2c682160756070407001003903410f50306510014001e6141d02111244041c40701016083c0c030b = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 600555818 1250 600554568 600554573
    0x819050702061206030708030d021305040b0d08030604140901060503070503030a0203041208040312020c03070501090803120a110409061a2a01110d021e09030316020a090f0c03060501030612 83
    0x150301c0e010303113503076403501a10781e00007000c40c0c0400140101c1d041ca4a40141e80d00b884000c1310004103100e6002300e008901b80107031089590345103c0f035a0307081c54014185965940d2030754000380041104003c000c1c2e0607410300c42445206601540008180c0304254120380c0f0103625071301055501e025102807a00180e000300424030411110001321900944504039241c1013a80301d90362611200c54590100c001603101c50591440c030703d420015a00148800c0c2014000e25040c5441103403284180c80000e0301c02ca249070003003115025180d0100c04011005448079469546809921014040703500c6503c0c02444e982c046952110703922402ca40c070b24007035000c1442c035100711401941241c0e03801301d42e6403005550301c8030500d03040b01c43d00c0002d240711421140b005a0714101c0050318014038586030801c0d0014031090000c1c240544000048885042ca12a000c039180c0b415840064102c41454006040041c28030030f001c032003000c0ca078010810b01e203107544041c0591f680f50303401101110f240b44507001400700707a942214003 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 600557068 1250 600555818 600555847
    0x10f030f0809040902040906050703110c0325050f0604060b04110318100203091e0a03051209120403030504030b1308040510051308030304120f020709020f16081905070206 75
    0x216240c2c054808202100290000b030f04550f8000e000355032050300c94042101403581881544d041c0d81092122605201654140c140d4a00503076491092805c1003000949060502d0318400000302c0d40402140c540c10f0010342c0c030f2519404152800c0300c103d4142030200c034052805004010a010044103440d0070740d079034101003000c0c8000d95a0b9a14040c004e0030b08202e60f03148a40000c522403e0300b800145200022400802d10483d0340b80580786581e00041030100000e41d004007103034a001d00f61144c22106480c0c02902030305142c03584980040004000400004140c0c1003c003420441340280b10031401545c9290600e0401404120300601d040d104100c1804a0b05c1c00c030030481501c203045d20b401401d02010b5160003010382c0f400e41040b4095400402000704104000f034002d5004103a5140540c40005581c074080d5403076000b4094410f40a80200307070344510fa00100c00307540c00c00c01c041882c8010400c26081182440d403042465080710f980c4844042400c0303008804643c2c2681e03014190a151005900135005c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 600558318 1250 600557068 600557077
    0xa050702010c06140c030115020c06090d0804080d030c030507020c030619021614010b010c030206011a1c05190207031215080601060513050108130303051b0708070605010f030f08 78
    0x155030b01d556601880c0400510041c11703200d02103d0003820740d6941005a91520034848080d08801c660003422036101584070282030b103c03106401c0d151240c00407542d00c2d1000c003500031504000000d00c80c9810301110340d503040d0003100d40140d00380c0301080a519070348801c03a112036020700c1c881d4143e0b0040021aa040070400c107002480c61800c5070060504188440c0041500e03151241940c080c02c07842d060900b40304003072045031180c89003400c0c110784903032681d40c002c0d448180512540815515644811070103181c00c4080fa200111a5441110200c2d0094204401072806582c0f1542d160352031140c9030300c0c142c040c1c82103540550701900c0d0160f10041c9107029401401340e01e41510072813030380d0100c0001c03c41030400078503020f007409131159529070088003180218031550b0b50000e4100070b60801400a242d0100e03000c400d040760189004612075450400314400001e65145824183c0d60005801050040b06806065814483c1000f8480c90b40d890828198942090202900100d281c0c0c0160000804100040 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 600559568 1250 600558318 600558323
    0x80901020d020703030b041d060705031b07030206040b01080d05090402160204020a020a03030b1e011b0b130b01080607140c0a051902121c030f0603150219050a050702010c 75
    0x5440c1c044034002140581c0c20084084012a40740d00e0190f21038901030103200c020610250b00d090007000780302c40850f030350310000e099501440800400306038280498014a4280150940c0c0599240034500e0020742e1400c0c1181c0a4804a10341c10011400e614080340704950381080b5a00c1c2403c00326030303400b0070009512008003449100010b003011001600c4900160840c0a5660040d040503011400c01070269010111020f11400c14024680c0368542e041c2d542c00c0c901d400a00c0c254a440d10b444125071501c0b4101503001c1d194919540c1048a040c0e20500000c5070184075090304642039036140d01003980c0e08419120351700460444c04203188903c200c4c9010340f1a543c0144200c1c3c05841043c0c86035420402200401c1560f4800d4032203078010b5003040d044403000800001d00034030003210640703189003c240030115500d08260301c07049035850039140b03500154095900090602554602641c05034000c0d807250440e42c0590020a41e0701245500903400c0e5100e0380340f9621411304e07201ba65401110300b2030103082d04 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 600560818 1250 600559568 600559571
    0xa0501260109022212030507030507060e0d020c0306040507030f020d06060f06030e2e020f0f032d0705131211120a230703080307020102090a050111030a080901 70
    0xc5514a0100420080c0201112000141c2c4c5001c2d4100407920040500d034888038410044508200400d061100c805074540c0510740a51101220b140440c1d50340f0800601502c01400c1c40d8418190f201e01094003070305038a454089a20b42901d12080c15100c03e42210064000e40001c642000070450803849032070b22903c002c2c12008184640da07520000c440486e0402c05098079940d40c00d01420343c042c4906510b600c81c0038010091800b401c01d0008081b0b804904c00d014440c2d415803449802142601a240740315480c2107142e0f125403004840340b1058008540788803d0300d030f42c80c56140384042100c00c18031402c6205001400309550300c3c0400e4a02d61b01500c0c1c01b000814a201c1d00040c2d54525256203101c0303034810380030b070162030f85100c04101c000c030001190b1090741d40060800500042114880c41071800200d00d030510314240110500b418018103500143c149003001080200c581c0d81075000304142e5900301e80a0019544038030044a0091488181c107400303910400034040024020b0a403640d010220000 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 600562068 1250 600560818 600560867
    0x5120313091401050d0b07110c040903080609100503060a0207150504051509030405011b0206250c09051905180706050a03061205070302061c110403030e010e0a0501 72
    0x8003034803001103903401014640d68522281d608182c500c20200d005000c2241c1e00a0b1120b195214080100000340c0440140503421000c1c4048800501c43d000c1030745001030041007034070100d003009820039a045521030300c144425000220810140780700b19054070409001400c040d50382886e40320003548a15015202e540040803240f410030824040d0511462269024106120076400a10400d405c054200f0304140c00c1480103001070f0741c1c07101c0c446504c020130007a0322950405034004031380203210701280026544481414190301e614440840c04a0f1803184404001c034580d103203502000c541080e50142d0308111100410b045800c2c59401071034201141d542c09445400d80c0d81c024038500f5140c3d90020303003c03410104541d5503858061007010018444030301e86019104c004e582c0e2549030b6010780802840361380042348505070b100c40a1360440c05442044c0d000c0041002c181d1342200380b60030130311048000424030b00c5040724a500c140681c030424003000c0c0007203000d20f0400340151412007000030f400000090307614 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 600563318 1250 600562068 600562087
    0x12030509030a030e090f070e010509010306080312090f0a0515090c0406090f0e0c09041b08030a090906050316051e090c04150c150b0a0306150e100f051203 68
    0x70702c45024840d46402e00590350280500403108401003100103105070302800c201d0403a802c10702000c80104246042c5030b0f24070055005900900b400d4002505921011500c55207280a100145003d0007000085907179603226600f1450781c0e4201424010180e41101580c966001d0801104c0f41e002030b6070303105442210100c5e2010904440e666400030303162030f480d145803c3c0e400d038861246d0910103680788054060700c0301b0ba1011400c904030252000700794401002401c040c2d4a413a078401c03c050000d55007a03070303681ca00d404401043d03106280a20b14174180340030000115444c000841341c404a201d222034140303907071a26003041010111000303080c2102c0707083c40145607182d0310440b0452043c851006281d440d0390400909145a40c2111440020701014101c098081a03c408030030b040c07648038a03408104403e007076001c1048070400d948003e108038103007041001114501b0b5081000d48a040b042c3c001c543d60b07003007400703200d825180c842c410040d02c0c8041d00784150f0070488403c0600500c204101c0b40b0344151070 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 600564568 1250 600563318 600563323
    0x5270402040e0319140403050c090408070209070905031b0d030c060b061204170408030f0310050a0308073012200c0705370e0108030901120c091203050903 68
    0x1154000f04d544014100b441c2650704052a82c52404d4140d0409043c54103582e00c8075660f43c15224500c6c03151102100003003c010003802118411a8050200406410408005082100b003801751a1084c02014500e000c41d180104032000001e80040078003000c004141c8013650f404e0800b0790141d42030b40d1141224040354a42d14024180805428401d003c145002c5c01e1044c0900220a42081405c904000c204040000002070b03610b4032020340075442d40c0b80c032148554443d484141c1e2241d60002103050001041c00852009000141c0c02138210082143e085202c41621084140720700c10206460300c2040b030183c0c480c000d01e00380e0a40645002034152110854100f4010440343c200c60031040010b01d901c0b01a070240041c8005040075664508051544084000305c0045540d50f58140e402000119800715030500e04030740203103540d00700e07102175503100c407107098982e40b2104015012402600503906030390400c1c070400000c1a400e646d2805c155049c01020030914548000603001c119041c40040b4095900b07 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 600565818 1250 600564568 600564577
    0xb13060213090f050c03011a210a0b04050403120e01022703100b0609040c05071401060510050418020307020f16211a090a050601120c05270402040e03 66
    0x541500040c0740c540350010003598600c00075480c8940c1000284003001ca008401d480c10b5030761401d501c08400040004c400d50300e000701400d1004200309617048943c803c0c030480f0050701070502a041444008070240c1404203442041d40c00070006900d189050148a0319940984540b1207004009031a2108100060810310b82242601075030004090803403040e0314003040614010341c8135034400e10050610a0002d46e0b24012424524001c54481c0c11803010390b8800c1d4200d07242c1c140e00940da50150305000d12054003c091a008050041c08102e940000d0075000d44141e604a030340f0754034500c400013001d91417031019400141815003035200709a901d1780d0340001442000b8074001d00f65844c007440d07840e104602d00103100301568080f880901003011008611106802c80c110600115684540d40381d0948980c9028401c0c00c01500030b000b03640c00850070041700c0c8205c203402070203820401e0080e62079400300f01404000165074030171243c006503e0032501d44628042d030750040c0010310000300b440d41c9a40355425a4031 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 600567068 1250 600565818 600565837
    0xa08180f0a02040e100e0c01081b03070c020a09050f040506010623210403121401060f0c170c0c130e060103060504030507060905030a030606020c01170c070606030309060e010f08040b130602 83
    0x1f140b04181c0041d40c1c4480c0c80c0d03a1001030004001c0040025020000301840b000d000b0408000c44420300c02d0a54594239014002000c1c1070000b08201e00d4012110200354809840803110303800350034000119039106441402c281d8120f1609048503c024070000c661a501c90740c0586034003100616060710304c0030149400f62060307001e80c5585100c0b628011145084035002000c0d20301c41c50000006000d911b40c02000074002050600b0440c418840c241400c58400d8903041c000c525101d400681601607110100b21002c245c41c1c1541c20003c0c422030281040141d4511500038411540b0003001080410b005410040c0c1244c040e08003645400020744810342a121603043c19519a031000403043d055583c1840350a005106600c09424003c080000007450706507841c42d00707103a001007580407480240d2000c1c00c44e181d0f2035015804029041d964900601030b850316106800110b4415040c00040c4c2d4040c9140d030410004641c1c0b00700c0e09a41c0d694881d00400780140600c8441039010003401c00042d50392008090482 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 600568318 1250 600567068 600567073
    0x10050d0f06090f0b070201050126010f1104030209154b030f2a041509050105090117030901030207050a0b040302010e120c060f0603120a08180f0a02040e100e 69
    0x50684c00c014401314000b5003d8011a03140c04010021451050800b46000307922460b520800313082561450301400740710ba07010b0005403601c5403410800b60868018405c90303100343d55641090780d03900d03181c414000340030480b681c000580384041e0131032080c040703418880d443e01e0906600e43c1702c000302d03070350194440c3c10510380c121034251100380380461800f041102d4040d44090001d0003002010241419000c05080c14050b0b907106c3c03110140c0b141c0e0f4646c1c2110706180c941c803020703034136541c6d40c0c4001c40080e02083c4946402040c8000000c100c4030203120042070b00b103001340015490040713001c00441c0254416070301500c050003400340181c0080c18038103c25004070f000c0e5001040da105c5405a00b400c2662111201581e2242000300c51030045000c1b40140d48034000c0c0c401c0141366600c210200e41000d80030b040700e400030b04000a60420a0303030030108550041c4c1400705055503c4400103240d41e43c41e1110044010381e903110101100c010700d4540c20429401d031810303065070301d82848414800165800f0ba641d0000c0381c0c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 600569568 1250 600568318 600568343
    0x180f0c0a12050a1a1005060901270e040b071b0f0314040b1c0f0903080105191e06020714030c0f0a0f0602011d03160b09120307030507110610050d0f0609 67
    0x400c00c10320480c0181001f11092841e00e486000062300d0706a0000d00500b409040992150a481000c500d0038020031044d49040d05e28502403a11001d480012214580031440d000e0701c10020310b044002c412821540320614031120001510b081d203034123000c04198501c003101040040b40500002d0050000380c3c03844049030110b01d0100c1c030500b0598a00000d0f0440b034a240a00401c04650300c40702c1c5604562042d92005554403007100401d200c1d4120307401110f9841c418908203c10183d8030900c10741281c4560b400d0340e22581d240c48120a5803400300442c41d40c540d2001ca40c2820b05e152040c2c4012691100a0960080030303580c00c40f40071200710607400140940d6403560941e40902210202100c001c108002451618015440040d4502a00b00c0d025040208901c000fa03000e20042085450200c1d40c500f886441e4980300e60b005025080c1200c0610005652144103241d5020000c0c1a07409a03401c800b20060a500f0030050000c040b424510688020f4209000c100101d4402d10a80408a02032110801503 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 600570818 1250 600569568 600569581
    0xf13030f0302010b03160e0c04030503120103110108100905070201091e0b0f040b04080a0311070c1508040c2d08160e19020a050909180f0c0a12050a1a 66
    0x21544134186039400f030f802c00b01c5498041401840300006840c031030b05080d100da8642c0481e03008c4500454000906c3ca10000135690341072100ca000b000d040f20711845105110348009401158020802d986610a001d0540c6007030000e03203103580116038041082d01c000200005552181903040800748a0300064014481404040c024601c414035480065080c0c0e6410504080c4e42c0c0c40c101c40d00c010006010448045083c45449110350401841c40540d01034050700e50300c0b1030a000f5114629440f0b0540f04800c0d400d13622401d20f02a0240c0f920aa0300400d41c03030f540c28540300c11a0009059160450f01138035a107001542512070154880d00074029250003014003140c07140c0c80290240f22074108107050b22a100820011002ca150006d038204418800580c440c18514400d41303d038061015041e034004107071001c208840c00002d018407160820b40c01104c40c002c0903014083d07284c41d0320031186600301080c818148120590312401003803140c401c078111240517809446400c50110030f580143c11046045060091 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 600572068 1250 600570818 600570821
    0x1508040605040f05100c0f0513030f05240708060f0a0303210e01050a150305060a0b01031e050f1f050d030908030412060f05150f0a08070e04021002070305060c0f13030f030201 77
    0x841812408e04034a01604040305180142d0075100045c048202190700703d080000c00c2c80f0107641d100d480c1b4140d86803400c1506401301940c204030341a00c009800540000e4551904082c0c0b03101030b00000d031891100d1400d540341256a16641803400d199080310414245042c01d0501c1801c1a00940100000311400c1403000d044c02d4039011100358101c00d1120f2014800b003040840c14941025580d1400a00c20008000603000380001d95050340c02281c14080701d0040d254690403031841403101851090007940c50208401c28284100e40e200c03030408000c50140414140580c1c00030455000f4142005501c1e07448000c0761856108d038010340b281800c1c462044081050500800340c54200002042c021441e014542c0c1c000c09000850300c51042c0c6050b81c03070006a4440e074a4042c040c140b00e0303096440041c3c80e90580c0e600c50f8415641240210b01c02810101e5a41c8003007100c1c03045c1c0390300501400481e100c03004140c120ba04a1800d045216500300f00e103481d1480700e890180000c51007940344003040a1141800390 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 600573318 1250 600572068 600572087
    0x40812040302030106080d02060a0c140c0c210c090c07050106150806031c0309020f0907020d1106060a1502010f092301110406120608010c0302070c1508040605040f05100c 75
    0xc50340c0001c9440c500148c000c01d40a0740044101d1001610441040c0102ca01849109008400402c0010760400421001c54000d42125050701c503000780d0040d0300003042031407034041c04102d00754104003007c4000d86042240d282d0043d1030308141c6400c0c5060340e15010b007103c005a0202c01515460b0f42207030034594004c04100d80c0524210054011645290300740b00b9007000c000d07048801c02d079403101100c086542c0c03200081c0c2d4a900c0540215401e1410341d001a548000c0018403c1c081740340101e0000e0302580000348c90b40b01d0807020700609052850007000301216031014403454195500e032003403203900300b0030703840b039000c0181c02000c41020100707a12201c0e1801c42c05c88071182032664103242e031102c60313075541e2001c55040310102c0c40c1c02c1e240c6048010440740103208580250381c00b94200003c00500b1503058001c1c1000c0c1d4028540c3c04100b9950b0400810080034414200000ca001e140000d030114460341c1c00141d10501440742501d40e03040703035a142410058004018045141d03180c0d1103040b101d0f8840070f03a1 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 600574568 1250 600573318 600573329
    0xe041502030c1b240123060703030b0a08010509070302010e0d110603091f0b04060b180913020619020d0e010203041e3602070b1902040812040302030106 67
    0x2189903050000410b09030303200d840c01c1c03290084050304102d0402c290070040300340603d540895040006042030400d0340c040ca028403030500c4501482c9030702d07055200b907200c448200b0b0400601c90780c0f0780700c0e091360150702500464101542c0102007840c002003a06087c0039861043c0a0388019010103400e510014081c00807100702c10f170180360324441d204005030b401c24100142d42422607a107620399491507010b0b8500100b200304010301c00c003500c0032980220900c2c0c04c40c4500b075004035400c0c011151a2001003601c0e0040c1c540c0305000c04c442e411441c12600f40210915001001c1d01316a5440110603008280c4643c400540c1160050b042c0b103400150550600c0a00d040e0f075190300d0940c95141807000000d41d05e0085004503155200c1801c1c0050705140381651501c01000806d440311000001c403508985100c0140300702c18205070a09460300034050f003504c00c480100c0ea0064900060351144542a25035144468022050660800012640e0401001235000440c0c3d060b80282d40d442c00c1d4414542500c40c0d59005 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 600575818 1250 600574568 600574571
    0x106091d061b090a42140c15090d031b0f0207050d26031302060306040b040603052a100302090112020d060302180408091306050a090e0f0a1203090f06060e0415 70
    0x640315012417148040244150900d4200000c82c21207156280034420b0107d80030081c443c1103865030040034401c09992049000070107681103401401d00a4095401034102c0c030710510021884801900e00907003411482d16994811122001e45400110701c09001c40003050341ea5035801c14071280c40403a43d08008003840403500b611400c600f4076190806998000030700c020b206031404000282c1c0c94403207611103a90000300400a000d01c6940b07081a0f42c80c0d0703034444c012006045d0f50519404203e15140180000c064016103807440f14071750b0704011002500212001410002501040c403880707041c500243c0240d15000710b0004840c1e14610400c103180b45504096040c3d00301c0e05003000081108039054400c09001a60801c2d00390818200c1c0100600351500002d901074400c50020a1a90359a0b00001c1039000b21303012030303c44103081500c07241c0e960300030320000b040d0440340345003c442c0c070388641c000c249414400c20405503518201d83d10700003655441d401c6100c3c501c101e00204802d020070b001c40e5a9054491100 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 600577068 1250 600575818 600575909
    0x80a0c02010c0206010b1c110a0f050408060c070501090b16031a13021b010513020a0914011e08060a1a010c080d1d0607020106091d061b090a 62
    0x80181d21200140b00354599146c020070f01401e06821020345410200541c0402c000f807843c3d035400350808c0d4201d8100500000c01100219404902030170403141a00c800c54000c1c485695014401c4090394401c0c82c04841c0ba5417140c40c501b001902400c282406032891301d820800c0e00100b040000d04070f81e40704140070b4244855042c18003861b241ca806600c1200c07111040944e4800e03c1c0000020710042400d2000015864902007082001c48000854169442120411403180d0b40340d8001069610f82d002c40304480b05100010800e4001e100c564451440c00c810034428440e554401d5981440c4040b00e07925009926200c80c0605100c0340c90040d040b040c001d0800800a21090b06c420fa140d0242c070900f0796400796645921a51120901520040c04c88a070049580515154400034040d2040e0b2141c010124144039030040500004c090700c030802388008000b03110b03c1c0e54541d1a00301492089003218841e207010400d0085513120315443c000540640c540751829081442060b0b00d500f05504240c114000d812030 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 600578318 1250 600577068 600577091
    0x60312050f03011a0c0d0c06050f01080c09040c120b0a061e09020a02031c021c060503030f03100f0303021b0406061b0c0f08070603060b280903050102040303080a0c0201 74
    0x307003541c1c192403001103010100020031340060140d10601e01011141d22803c0000300120b6405550521081d2040701c1c28441512042881801048280900030080d00184000c28003400c2140005910500035003800681d142d076610411034100304010151001c820580c10010f0303010290113035a00504814105208010140c8107141800106000d102040c9400044040c4100c1c8200180c400c000c0180100c0d0162000c6818500c00a5008c0b10a004074040c071103d0751142411144298002c40e4801b5001c2c5240010014810038dc9610080882c0d0380c0e002c07000d1010030061319460b1240065807080c1c000300150080c0d00300039500310a244015512690810100b8801b17240d1102000e800c0a10b0b0f84a4030300415010316011401d01520b0300a0204040b400b103000a810300300007007020403591f964408022b880e0700c4024107481881480c00c42d40300365001c1e101081180e0821100300100381c03044d28120100c1910f03640d480e07007a60700682c420b90005035801c0621900000394031420000e510140000c122840451 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 600579568 1250 600578318 600578347
    0x30f0e070302030f07141009030b16020f2d0102160f0b0a200d0e0d030c1106040f0210120c02160b0304030903110607051606030605060f0d09110402070606031205 71
    0x300501380580451b1081c01f04035030007480c8a602440c0c0c400b402e240e0b41e1070011024400702c5400b03018100140b14540700159005400f0814108003450350f500703050304030354901d40502003480d95100c003011903600b04209001c4419080300142100e00c515001e0401d600c3e1411700d40d04959020f00b00e15030705440c1181c840001102004018040c101c1d0410107521903110949423402403400408040f0f1502174044401907451385a07210381c2c520042e82e02e40b00c2160581c01d040a81d145005c4800034406500c003806200035182014660b62048103928211100322403d41d004001e0711080200003000d40d020311a180c00e404e2020000c06c01801c4642541411f44ca001d44000300700042a120144c51640d50300c00402d1551100c4c0c045814040c0c2102c102c1e003100d5217061b0005041ca88504c10f4400080c60008081a00c1c680070044409031015075058908042c0c003002e800c0300410032080122440032a074541034945441d50300141880030300407140000d145165062044007007804100300c1041010070003480b100e80204 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 600580818 1250 600579568 600579599
    0x30301090e030f1909051021020f0913090203162417090c0613030506060102070303050d050721020703080f0c04170a1a011a090d020f01030f0e070302030f07 69
    0x46051032a44e1540c00f055a10780b90303075000180c01084007402010000e4110300c040d01da02d200c0004050384101c8520b803c04c100d00500050706c50041003041103500e41d1400b02c281c07642e503a1040d8030001b0780c45082d9000910340500204801c035002400f6608002100340d9410f05e0094101d0000c50002c40c10020000406141e40d0382e240c60402052040403804246082100444021f00076051664a0a180c2004600c90400d4402181d451203004000354413544041004802c580c1c1c9500c43e1414204070f400c00c4030190000600b20300401c551710b48001b4240348035042c44015807900b00c9006030385107001d040c01045150000c054001c0c04004000703102c2d9000071202214100d515401e1081000d0805214040c14004420700140000a4540d00704040b20b000b0303d040303130488914a07610340c1e10f502a1121f01100f801284081c0d58490640003042000d802e14010189842c40c0500d8000740c014409010079080711260808000c0a0f40401c07024021400c04007e00b94203e05030350001c0066034649070958a14211 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 600582068 1250 600580818 600580837
    0x90109021803010c02031b0d0f0c0317010603020a0e010e090c0702030316050f1902060334020f1009020906042c010504150504030f030b0f040905030301090e030f 71
    0x340081c100000106001604a580d64000c000303010316805140025629005070785600c080514015161250300030019407481110b0580d15015100c034040320382650b803038207289015000c1c0042c02c009407483c1c1243c185018043d00d0340c1c5d1401a10356402420081130329848107840e0741405140303940e140ba150b0ba0510f4481e800608036070f0080d51400c146c40031a04501548814544805c002d50400c402c201d408501c06600500c08400c41c4d1814800c3c5800401103d45028040c0d00010100b01190a00b07111120070b50703102d040c0c48124400d000c03944508080802e258281030700180c026802d0b5035000c1e1014040841c0f81c43e44054240f00c008803640000703030b80315005401584690fa45166036407401e01885081d40c504400300d2805205500b120304200d02902045404171000240c0c400a0112082180f048030301803500360341d400a240110038001e40040c0b40480e01103a03c0050b43c00102c0c00c95445007d480040d9100c2d502954695140c40b85490a0314020349440c0001e402c148502d54801c850681610b080300b0 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 600583318 1250 600582068 600582071
    0xf1416060513140d0b0406020301080d0203030c220e090106030b091f05070c020604031a070503070e040b0307050415050f2e1403070f080c090d02010c1401021620090109 74
    0x203240e0001313071421448180040025202100300410710009a025604079185013003a91070019204604903140d10046400b070b22a08001d2201b5800c0c40280189883c00c981080c900001040d21a149d02c000c4040469900c512070391160028001c000c50441300a030400d01e04002012010000d00c014a09104000506d215065441000039145031280018040d000d8000d044513a40302d0302ea05205003c15124603182d1a440030010128a0230361080c01168824401d039684c1001081d414000c00028242e203098140e0b052043c81008140da548500c10013402c1005030704d18418051404043c0703c0d486040750440c2e40302e400d41c00e5100d044042c034051366600300f40c0d804d50b90751114813483c04140c807150700c80021604800804420858000e400880c9200d00781119143c481e1a03544900840c400b81c883c3e002e1950300040c0e44006031005502407071284694030b00c0b61501d4401c444040c50302c94220f810281d0610140e01c2000150028007000d180c03c81c1038411010b8450700d0b00d20310500400d0015006100700080760303 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 600584568 1250 600583318 600583349
    0x1815180e0309151306020c010912060e0316030e030606010c0b0a020f19120902150d0b0303181302040b18030309090108160f14010c0f1416060513 64
    0x44405000300e03541501d004000c42400480783c0381d07040107508800440900e0344c0080101181690001039000c0702c2c980d0503510801c00c2c0d03003007850020190040358812161103840320010001e4840501c06072194020311000d0048801041c00c000300105c0910f201917003e82c114200b408410b9030300c5000d0b0315580750000b000079459160084040028410302a296580010110303402d104072000710504021523a840d0b449009500981d01d05008071804268029481040b09480350b0080030401d003c2d10150002170300018203207001002203070459000c410400040011b4501d84074441c07500700b1500c20f00e248581c80c1103040906100e03441c600e81c440e00844404076442503040c1549580c0810440e403120300042d01090003540c1d240000c07680e50400404408100c101c40300007251748400340040d070089401c500070428620b0090f000546080c14200000c0d80d030b000240006c40d0100d00f45200b41c501c0b4007201e200404140608681c40c0c003c1d040d85801945c10000d04008540041e240340052909132071400d82c050050b07 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 600585818 1250 600584568 600584591
    0x30b01110d080406060503010203070906030b1909050103050601080d020304090b12010f140c070f0206030a021201030807020918061501121a0f0a05090f04020f0a181518 74
    0x8551001400411071040c2801c08031542d03408540d80c3c0c001c600c940300c1888810b454004041c242d0204544902c005040528208182803180c0c218050350708028000c050480490b0005001c80d035002c0c2c10290b000303a10340b4010001c06c07008010240c01000384c2c00192080c0301c50400c0003074881c82a44a5040c00c941c40e8840d00c1100c1e0346603030000100b0305160000f048003400316075080018203030112802ca041000071000607100c101d03540484a2045d841260720310a07400aa003002000d030000380c104003115509000302c3c0c0032070785100900c030301035402405520b80b41c0c951441000b03003a0100520b051200a82800d403401100000500e1581000e001942c0d440703082c124400485441f40c46200004065007030618000241806004416000c8400d48000c03011803015024005801e0040c0b10b800d0304000000009040c00116100c030b5a000b03407000301003849102707040c00050382c007000325040401e05180803030001000105c18801c3ea10b1941900d099916210704e8000b421051010825180ea241c83d11a1b844820 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 600587068 1250 600585818 600585827
    0x6041211040f020c060a0b060405030307150603050312040c05010c0209010501052b0b1206071b06061e060e0d0203100903020307050706090806011703190e0307061d0609030a03030b01 80
    0x240703003002260464848041a130b0860f41c501d010381d4214000c0e46400100002424500c0440d0203403100980214901410f030f80d1222070302c1e84800340460070f00383d550b64080b000680c10701c000c2c0707203504881c04c0d001e413a402c081c14200b04085140d440307503041c007088042c494016180c280340303e07046030b00908085071280d40c0c0100400701d030300d25003a1462070f94000c0c0202c80186130980e0321142146000307558104582c1d03204d00510356502810754011002c1151030211880f6a62140d404802051051601240c140c0e03942008801c1c0381d035020000c0c1c040c0d14140c070003400f8a035480030891411810864900c0000c43c06500440c0d1202150b0303003040c4c121502c1c0c07880c04050500800444000b154400201c45a0f01d80c1e40c1c0005000511500500e0054002c4000004841d491684080400902540910b1034500c090a0001140d14400c0d500404e1102e8408034100958051000340002e0101c1d0711481c1411214001c91740410031404155841003801b4411304040761800a0894800c41e458100000d500400c2ca0041c6c5 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 600588318 1250 600587068 600587081
    0xc0c1401150b04080106050909070905130804090c03241806050a0308030f06060309070e04021503090f010b101b0c030f120e01030c050a0f0509060d09110604121104 72
    0xc5603207a522000902c8442440c001d100310b03580900200040c946560810040360001d88100500e548403140502405078243d001035000348554441e1039040c182559811101d41042c2d00140c4496a120795076005d01d5014007a1480c01d1000c841c0b419140b200c5002a4801c0300a5402000064043c0c4440c40c00c4181661f032060002c4c000041503101116501e00d09520640d000303da59400c1c03c07440314040b03045400c0074015a40203d00c284003600d03060341080400d050743c0750b00030000e9078060715945100d5229400d0400450081c8000c101400442c0412015a402e40e02c01000d07660040c40ca000a101d400347c0d0143ca41002610000801071502100342840440c91400d80c00250800492012860404c45482e0741c450340c140b80d54a60f00a11420a00158100c1e0341101d07002c40403c130300f00900004c0600c5001040c43c05070b4281000c9003400c1d03203500440e4954100d14009820a80c0e100048000d02031400034242035000c0480310180341034184821304c490070240440040207140003110341031880e980c40e000364 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 600589568 1250 600588318 600588341
    0xc070b09061b0f160504061d040f021c0303150b180603040c270509150a020a0921050f070501050a2d0e09073e121b010c0c1401 56
    0x11061161113109040000c801441070038800d9207000d40c000340c042c8540d0b018000714815550300c80c0042d030360345c0c4550346c40c860000350480e80b0500d150b100a008114a0700b02e560010301036600020020a0074010034544c06090300610300c070950a0007684040c0e801a8842c030070020042e01c2070340e00c0f0345580c60719537a10706d05034104a2194580190800112030322204058000d0041c41050105031a403041142c0c5400d00140c2c220140c5204900150f8a880a9002860380b000e003482d010040b01da44800d0f00c3c51403055020002000311040580b942032007010400e03050103107040400303089098a8880041c1151041c20001400d10980506805451540711015101e03054000134440e524044850014105d41e9003060441c410017038000031400c04c600c20400070b03d905010705d0100b00c0042d002e040030900c41400c0c0c261800000110b8800c0038401c0c03800c1c81510080c06488400d81d44503400701c441107a104922511101d4070360314141d08007054070351200046658a4001c050000d140300300c0d052643c0035010311002d1 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 600590818 1250 600589568 600589573
    0x70e210639070602030a0c140c0304090c0e100518010216030f030207080d02070501031805060403050d330e100e0703060830090901050909011b050c070b09061b0f 71
    0x40004402c5030f0341100c0c94107d035669a444a1421a4030b10001a0190003840c0126600901003400305200c00c0d8400007258041e81048160b03d2a24000241d121003002420000600301280c5018041d001154200b803003107090001d0442c1c911780d2001801c0304100c910024000f207002084000506000340007050151401000391400000214006507a603440c920410b40000d11b030030843d0007288010505032420350342c400c3c068400c945032500c003100c00d50001c00d4003034602903507000300390702c1a140c0820b05421110501c041906e500400080b00700160015405402480743c15001c1000080b0490350700d1040c2c4400c08000d00640e214040110020041a080750282e8072403490405160751600f581164150040c045000b882000c281d00050341e0b0103100d252030b400c040c49100500480c5860790845500c200500000911072031041e20b4404407030440740010000c6500020f40550341d803411702912028004803180e0514105013030010403a28403803014003419510315288a0701c6100f609000030060241038404 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 600592068 1250 600590818 600590821
    0xf040b04151508060a0303080f0c090307030b010f0918060509071502030d0c021207020105090d0605132108043002030c0c030a0206040e070e21063907060203 69
    0x1c1d0700a0120b106144008030b100344000680501c0c01358800d50a030382e032541e034504031a120018802003000f400b5100c684c00e00c0c0c1c284844070051702c003005440000d6010f400c0001c00303175141a00c5001109180d4202d040344d2402c0c50184d90384006003196106000ea40110300151940e54441900d003020000d4000c1d03103a800c64150307130700b600aa000003e8100c0028400c010089948490002e0341d96801c0301c23151049402d020b11400c00950b014402801c172210f0090044e4510301031550354407048500031190380354940580c05c00181844030308080e0104202c1188802c0d4903004901d00c0140c0031a90040004020420b07400c0c0783e88030074401100900355820013041417000400e030200069141c0d000740142080a20907441440300c10300c0c2c0068074040300307900602002d29182c00c4c0440d40b500f00400810f00400e024002002c999182c0b959011003040c000c5506801e8450074111580c113040c1030700680301124072000315410a5800000c007800030003406c000052607901c550b1040103000c1a0043c1907004d0103040c400710 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 600593318 1250 600592068 600592079
    0x30b0d060506040506040e0d0e041e020424080117031209010b1903080406052505150915010519091a010206060102060408040e0a02281d0f040b0415 65
    0x300054007800b0229000c2c032803541c819042c081107440c2c0360b049010b554060300c0c154002c54012401402510740103040800c401c4c810a144500d911100b0810744509035000404100c00902034a03040001e40c40201070101e0850408001440080180161060540180000070651101300300f00e804500c0c1c048141003440c501003410038001d018507003205000314100c05104181038040e0704107005a96011507128101824010120f0303c81d000340a0030b0218000703100708030700c52040c001e403c8408544604002c0543c00c4d10205080e00c52078014200143e203521040541c5040345400f181e00c0d0640354281c072008001d246031a04010030480c0c1c1d510810030035191860007154540d503074140e005540c02c00e8003100d64a484000049a44030380486e03028005100921040c0181400c100b51142c018842c800007604054185c03801071940c12a0300c4404820a1f07400c142200103c3e00407040300c40c10202c000e041ca0844040300042040c21045580701449145d486c158060196100d03404002c50701401025501c000d901e90 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 600594568 1250 600593318 600593321
    0x21b0d0f020d03020d0e0639030406050406200703120501050306070c170f031e060303070f03020106030206120f0703020315040902030114040c090b04110706180b09100b100507030f030b0d06 83
    0x140966009806610001040507260070b81111021054011076255a58603100c003002860090005c0f149140c481c607072440e540d14000e2305c0e00f6900d0310fc6420320341d544035075182c05002d458101340c03a0601503041c10300412859070042803459104101e0700b4034100000851a20111246250f06c0c2c05843c5140801c0c1c0d46038880c07018011b184555209024490a05940132241c401c105003290b0960741544200420000200c55811800000d442400003107030303083d242d038001040c0b908425110300c0c0c00c0442d4000c0181c00003070501e141c1d421641d030381821455030400c4400c001a00418000442c0a26100e8950401310349095008982c003d1860055501c1070800740f8201140c2c086911840301c00d1800d00369003211500c2c1901c640300d1118520407509203031403040e0b69603002401d4541080c10b644c4200c0d8407402c0c08102400c0000d4031507030140e4081c00302039101c3c881070b40860746842d100303901a010400068003066000b00441700c080780c25042c90405600f20703c4045024249014407160411407880e030030782c1041500e = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 600595818 1250 600594568 600594601
    0x80c1e0a02010e0a05090103031412070804021f050a0f17010f0503060f070503040b04080d0911041a06040303210c08041e0203100b06070204021b0d0f020d03020d0e06 73
    0x766100244001207108001c44c0b03201c140141c6510a1103a001080028001d082482d0500c01c80d2910340e041103400c0c822031880c00b0003164110003203444041003000718075154150f2134102c0e000441c11040c0c41c04020f00100300380140000303001404440c0c40325880007801900c070300452004002c1d047c07207190786842c3d01000781d026610a05000c1d00c51003003c14402030030000814854802c541d1030500715690303901c0c1e503034207504050000c6e40d00d200c04126004040c4064003c00d007045004240403080c05914000340000c4596002002d00d10310a0382d03d01405680e03800c402c8400f16501481c3c01c0035882e1807150b0710b1140324018000406d5844c941540c0000c000d0704074108500c15405464a641a4520490910f851001130341000794181c108046800d0701c0d00180d44090181e2034060005410b0080306c1c4d02117003c99100490800c941c043c006031480108000700a055400b4a240c50b0044421182c1000030b5500c0124410803001d260b000309042410003500c3d440004c109174184202c0f1924213240b5180c8488109 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 600597068 1250 600595818 600595823
    0x1201140406081504150902060d1407021209040903110a051006060e100809121b07051507030c0807080a030e010b011b02040504110306250912080c1e0a 66
    0x246180020581400f16a11a4603904590504101d03074555982d1035030501c0841100024582c0c40d4142409615504080c0c11b404004501c002100a14100500f15405004000e0300440d4041280740c20324103c80c0c400e031103502501740c07004204013410340350030b0b00c102451141c400d1aa100352442c030b800340400020300341c014000a100c1048819102c0c0d0044881122161000c0d03000101d44191000c0140b00e00710b003030392001d800d02c1901e56182802c2100080d5034880c0c04650421001103d401c1c1e4091070600500006000403142e43d52a0900c0c010f000b6268000d4a02c081c0501164034440c8062000700701c2116105a4416402907030389204041c0035008003500c200041c1c60351b10b009104001ca5004211107501c0d144080e549012400003507007044090200100304560794030401c80c0c0002191400c01100340602400750324000e07200900070b5140349904d1001e000004201d501c1004004803c801043c06881c141c00c100240d554501d400c40e101e1920102d4004401210380038890381d0107801001c114803213240e2 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 600598318 1250 600597068 600597071
    0x6050d0f030f080c03060904170f07020111030414190803071a0906010602100b010e040f06060f0302040b0a0e010509091006110f03040923010f140301020a2312011404 73
    0x42c81050464a001c42140c1403240c4035010808034003145802c1101d950300c24802c8040d9899407800e54032603078094200019540d031001004c54100215078002c03001140010082008500b0949070041002c02008034080341c0740250003100d00c03800741d103110960000c090060601141d503284414640184d4040d000822401350040c2840481c802550202e115412108140d0091402810000141000f0145020b4144c1402402a1414180d84550040300e44000300c00000280a5240582c050840f4051401690030540b04000900401d103240c002c5e01c2c2c0340025407030f0010500c642d1000594442c0718403e13480344c1c03000c0035804006201e10711080500688000303640792078400c41340054a5135594018500940743e078000f400140844000c0d070340400c1d000340100280c030306040d000d40f4030580150390030b800100100c410104c040c002001b107103086101d5088198002c515141c4201401049415800e5403c0000c00c0815405910510310b2010380e1070641e507079080e83c1000e5940e5080311008801c0c0f04a6940180e = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 600599568 1250 600598318 600598337
    0x30b0601020c0906011218060603030e0102030a0c080901090e040b1510090302100c0c08060105090610051903110408032109070b0904140114130c02120d06050d0f03 72
    0x154070101d005000c042c00500980301a03202d01c00155588045901281d80095651004540081c803600c0c407090403601400002034914110305004240904101e60b0074103650003040700501c6e0380d034410042c00d0b0554014114544074085070004a0b002501e030350202500100020a01c018801440f4140740070300c0042500c000c00003400410f010440c2c510b580e100380450750220082015080410042c0c03414a180d10300518500c409a503610391600f0903420032480355200c200144402c0c02d0200344181c1040341169561164031039500c00514603c00c1c0300740288103a0155529042d003500075084036444c04003040c03078a42c40380e0300ca1a0382d0380c0d650811400d4040095825006020b1405503d01050044442d280605a4075040410b240401c2d40b051020036080b6980301d10802401d4452a00103001c0d020021002c40c14250711402c0094041d00c90441c0d11540307107080c00b840358040d000110148506002034880340c54604244400c0e000344900c0e8030164011682240c0c04d400c102100714240f0b4810303c21b45501603403 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 600600818 1250 600599568 600599581
    0x3140a0e10151e0302030a0b0708060607080d150504020d020703140702150304170d060302031507120f0f02040806010501080c0937031203060b1e0f04030c0b04030b 72
    0x30ba4242ca1100006220308000501100c0341d41c030b6000494102482d50001c0b100d60342e40c08a45403620944042d1960850f800c288101c0b1680000d6441e0041000c0305c003281002031684a000d41441660043c5825684c3c0d644229002c4034000400402003100500c11520307a042c0028102c041e40c8040411000240e0039909100040302d80c10640d0300385900945003640c040402440c41002da80041e0042c1c1d02006014075940035500160300502003045454030200d4128a180305241c82c250103d01e4040071408501e0070080041da10100d809604807a698000c102e940c50344c5021001001c1c01d80141d80c980d800040d0114000d60001404e6040318400e0741e07070b05455a24003d1404c10760080030600c9078084520801c500c0c140d44005408005003400180c000b41a28400c041400010095032044401c845c20458013081260540300f5a402001d00300d101c40c0c54900c100b1907140800d40c3d0315000c103640301400308819060744085402e0714040c6500052003645280c0306c10003006250403074401181c21f4803815001a08 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 600602068 1250 600600818 600600821
    0x301060305070e06011b0501020d0c05211503011103072319090905040c0315020403170d060f090608010f180f060b030102212d0703140a0e10 62
    0x86039003000141c00150b04181091094030000760040d410400d40400c040c8903131b640c0c040c050103c03e11402c001a51911801400c500b561110101c55040c00b00a002c8880401741080310004181201c81201780203a0303030740108459071824103101c50340540ca041130310002e1500c401b008600a041c42d4a52100e40c042c00c00c5a04039024000540800002c82404403241407000f08105d00c4c1483c9460400c0040e00d601c4080c0d01080310000c907019164000080350410600c185100203c251400b030280940c5020f0030342d195440e0310303680c07503181d046880e400185070076440f480c95101c1e0016006420080e0350f119035400c40d440203020349014a809951904c00c0c40031035a030a80c400d0420b180b0201924400040885e02c8a0700c0601c070002007a50910b490355007074684c2c2d40e003c1c4010f10385480e030030b9540034000c160b001035815082e10042c0714080b403103510401108140440024429241c907100100039243d62208802c8028142050342c1c44918540b6a05010030080d00d80c2002c42800200804c8480450a401e0b0030300 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 600603318 1250 600602068 600602081
    0x21100506070507060f0c0215030a0506040615270f1401170a18151a0a0609050d0609060c0908010c080121030c08070305090901090b03120334030b0301 66
    0x2e00d03541c0070303150401802d0301814000045900c41e051500742914150080303042031074100080d101d8031b00b00000b084807240c405d10800e42c000c241500c0404c01c2c0c0e403c2144e92003e040a8035414001d200b22900d40c0d92902c40800110070f01d00070000300e04031186949a50b0400fa40d0300300e005050391405011440410f0394401e520001d4981c148011144094132000805401011404240603500440f002810007058203241c5a0800d11103071113000075600b0001d03082030426820880b58511504080320108007065009450a05444041f00d04130800155850110028881c0301d80052901c0e0811100c04807454025041000700d440c1c09000f40a011060101210b4242d0240280c0403600200800a180204240c41b000c0c4560310070300300041482c0c110b440c1d261141d004450114002100000c01a51500380140a58018010300d00c09002514000300025110016983e4040c412280840001c0700c001c00101d5103440302441c0004034030040711342c440ba64490080b010010000c02d08043c0e042e11507040510460 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 600604568 1250 600603318 600603323
    0x180f0f04021309050c120705030706021908130f03050c09060f010818031201090b040e06011a0d110c06071107050a03020d030203190207050a05040507120e01022110050607 75
    0x410105070500403140205952002550344d40729181504c072041c0c9600040a1b41e408103030004214482c604010540b420301c40d9005442190082d0000c188014829840100141c0d1302015442d00c600f0400c1e48002c1c80d10309a4030110b0031014030038002061080200c0d465112160030744d0b05d18038561b03d440900c0003034071201c01018005040e410004e500181c1040c01494540c080d6420780c0c4c54401044c0188915540a8010562250340c55244c00c0172860a846104c0d150b10b8a04040c3c0029803600300c1b801c1208448135030315202210b00003500003400c415940a01105d00d40c0b00401c07611105030420159444500f100e0060103c0c00481d80b403800842c0000f860011198020500d40d50b441c10744d401d104056080c0d00c012002c1d80300c188595100314440c40703c000e0b0034545035402000040e2412082007071148150f44018041c41c60003050080d90799004404d80561102010003103050198406920300a1013030b030408555950400049081c0303007079420340690261815001d1030706603544640403c40184101d1000 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 600605818 1250 600604568 600604579
    0x13020d0326060d0b07020f0102040303200f100506010e040606120b03030408030a0c1e120305010e370515130c0e010f0320030414010b01020c0d0c05180f0f0402 70
    0x55800165006680e5648178202c1d1040c3c17445c03000d800c01d9050990308160401c41c04603030001c0d548803952070320400c0310204c081650000c1211280790300386180c0b180c03045800041d141d92034200254a903401075100c3c90030132201a20801c13169035202c8006041004c4900c9010803d81020f41150071450000250b60070360f407d50380690300d0702c1c0c00c000b819a0390100c546002c036010b4290ba0710301c0070980010002c03c0141401602c411103101e401a070300900301c5205030401310282c4c0002052080e02042c0c1510105182d503661665941030f00441000c140e03404003c0005d108080c2814100810200151005a800300c01543e4969081d80302075150000c0e03c1904600e20b001070b6100d041040b0701e61280c5240c0071420100d00b400101107582959900c1d0301e041164240079021400003c0c0b01c10445682d580600b012645002004a1414500000c0d01c804e00003a1b41132084640f007150406100c41d106900004110051a151a0005030b140d120314150048407040041c40e90079000074081c02c1090600340c03181d94010700 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 600607068 1250 600605818 600605839
    0x6090109080a030b0a050613031209120305071a16110f03030f060d0b070f1215051009120606060905090c04030f150c0e040c0c0308010e13020d032606 66
    0xc800401c4000d030b21a85c000c0a044000500303807184001000c40c01c140b0441c00000a086050011039030301505226000c000f1103120800101c00755000c4004819454034000342d81c0d915508000600305031089151050814500c280500e85440b0071207100403540545035025040c0020710350588440e2014100003440c3c104100051000b01142e450070384c8454002c00320740c1c010305a0340f103d01a4103411504000407405600040008e190481e4803c040c016001205100309510981d48101103501403040078041c94100d030000c0304d150300404150028200300c292156940c40103042841c060540c500c0b480000c12510300340400d150800c243d5403481001061b0459150500e10780d501a486480d96105603204160b180303009a034090180902c00304091503070303501e2031110041000c11045400c00e07a0b0150a202003032180c103001035040320403607044440388845507409503199502000c0dc00742d0700b58001c0d0710240c2081440b04241d040030380b2188148803401c10014115460226400d209002c2e81c00c0c980c841040ca0 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 600608318 1250 600607068 600607087
    0x6090e0604050c0c060a090b13020f0f040b040c050d06080706050f0c01090f03120f0221090c03031c05010f1404020d1e0b01080f0f040201200a080301080609010908 72
    0x40100f03401901c0e400c1c040d490100b504800c1c500f852030945d0300f6000304d5101c00d10781c400d0201e40c001e0160002003a40c01c1c10303030020840d030004180d802d17028029805960306003140d40c0c0c1e0342d4a42c1d20140c5044000703001401004120700c4000d00c1940300c1078a2124081c60302601003000c4c000000c42400750b440700d44410340360403420403050400b50400040321040790340b0361005500103140c00712070b8800c15210741c03160210003e4415903031043c0c5980e007200c0410944148581c0c81881e0b000c2250700405001503002d801d294a602040d80d082c400b59240072a014440040c0038058281c44902d6034100009010301041540d0b200e02c0c1082ca8030f6241d100e00c47d040700300f40364a00240d00d0b00e03500030024078103500d00004000300d0398000991616801c40c416150b00345c1d982c201c1c10295820021a550001216206605529002c4120000994044d2010f4100b003040600a120062100020000d85511008551142440d032800d8040c3e031744240a5030303d0a026120200764105014003c04214540c0066128200100c0c50b = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 600609568 1250 600608318 600608321
    0x20307062321091f0204062003030114040b0a320607061d0d0306060908010203100b0a200a140d211e0c03050c03040b070c0807060e0703030906090e0604 67
    0x6080c007943c40c001c1a10070504160218610340c0040501800540c9403031a1003005881e40c0c112158140c2406000030000081500101c2168155084101c0341d01090346900c000c10010300c00202c1542e00202e07541000708070008004d003261103040c003400c0c07040e01c51118dd03000800e880142c1020150420018000800002c115070400d01c0f010a145802d456140c10043c43c0620f400320b4080c0300008250360702c409104403507025610f0b00150090000a5245050008003000f1982140c801c1481c1403001103954090203118500c0c0c2c8216400034010b040205011030748031500c0d80075001b070803148800011031403101140049202e0310300714496100c0c0108410303a60400d11855413142e900c0c2d41110342d9038400c0320304038008528400800d456002d00190018448101038100c40019088401c0311109104000000d400d2001441d80414a0300c4c01942c2c02a061402c80302501608000510090034011a02416034000843c035084034040d990b01e254003951100c00f6100600640103040c18040c41100003001030420723 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 600610818 1250 600609568 600609571
    0xa06050a02190f18050108010311060c03120a0b091501030522050a05010506060702060a0c0c030b090309030706050a020c040e1608030a02061006080a18020307062321 73
    0x240c2009850820b40c82c10200c0c0301511040c088000c103181e1990a140c0503440301c141551184c4030842000c80c01e04103030000e4544401440001e01d00407045100c20300e543c441106440102032541c0440e80c8800b01c01d407103060340b40c074200c2e40c803c0300624040c07000525150100a0354050f5201e146401700c2c1c00c08103401103026000040110701c5203d401050040040360710300a010f00c1c507000700090f1071040d45a03d801400e6810242100c0d00c1034506000c0240940c2d0380340c0889629401c0c03402d001d180f48419281450401c0c1c4254009003444440c00c1c01c200c07640300007000508040c0c1c4101d0580b0300440c2c9270201034980d40a50208600164000c90f06240d160a1661144428400d00401c540c1800782d4070300544030251554000c80380e1074002180382c000c025010000c81e0780095242c44000b180c5c0d07041a00003400d4510040120030055101e800112200c150341341c040300301c1a0060182c4030320725120701c00500b0803052041000c406240c1710320700c1f008a00481090b101c0131050801400c0c3c0990f540c94641042010 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 600612068 1250 600610818 600610831
    0x15090e070e0402040f0e060c1206040c0f0807230c01051b0910020c0310020a0f0806030d050d1503030305060a0e0408070b040201020f03040603050f0601020a030905090901020c0f0114090304080a0605 87
    0x240c4410340e161251003004641e12903405520031a5a0322027452207114500d6010700700c0c41c0940e00304624800416041803000e080201149041c07015980c030184110b40d8111280300000003101c0ea407240307221441c5190010a03402107071100034070058540b004203480c0c60070001740d060b2002c001444100c40b9854602d10101c000c001600c11112403d007080006410700d0742880348030681680c002046040c2da500521031702d24503001c605059405103007450109840c1c0c074500c0d0a2204108000490401d4200980d20540b00c00f0101a03035524000e840340b601500400050320900e1041d41c8018000848488800402d03104a91000240b800e1500a544480e2170110261049040d40980144403054090810262004000981d0007007a5400e02c0d4507909502072000d440b450440d00718001c0c041c0400c0d003003001c02040b00e0041c0d41040641d61504210b6009007d80e0354000040c0c0500b1094041a0005403c041c50760b941d404609082c2c0c0d00c60801150f0390344954800c01003184c10241408002c9609030344015030040b03 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 600613318 1250 600612068 600612071
    0x1202090a0f0e1509090307020402070215030f09010617070b0a030605060c03070308060d0305031b13031103010e241905040305031806060d080d020d15090e070e0402040f 74
    0x9481e00306048025095400c52003224070032500b045407a09009500600f41d0400399144003050800744100e54680c0305818001c0c2c0203680004400045480d500000030180000d884007076140d09080b0300340d080100c0d042d41c604044d5800c0c0724000c503003145041c1c54009102406002011414a41108009140c100044e140c05041e564207001500c1d0311100000c1900b0380340c00014607503d000526000c0c2c15040068a036034080d2031190403200000381c0040c2180d400200440c482c0e0702d511b034000b040820303c0c4101300c035400541244100000801a80a08004603200d04800034401c8040307003014260344000c40121680c035400344c80c1c2102600282d9241ca01d801181640c00200301c0004403861609640c0199401c90000d4000400c015203907007150b5070405070605040140030181481000031f40312081c101c001401401000902d114201c20365030458805034481c810502659000c01510040f4590a00ca00309030503050465412480c83c0c0403400d001600c0c4414040001d50320b8980a0100070b02c050800084043d = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 600614568 1250 600613318 600613339
    0x190b0c0904020a0f030e031204080c10110a140a300606050711040e0c0f030a0f05011e06030308070c151514040603020603010329040b070816120209 65
    0x103807114002000c0c81400364950000340002c03180024102d400055401000d90800e0101e000c2d08038218042c150415002801030741c80d40d2800e8011170030309180b60440203000c2d18100f1900240d818280c00b0304042d035090b40f5081c01c8007607603c1e29215103103d01c1c1024000580842c040048100700480e0701101e05407610040b004144200b801d0b8400c986440c1c0081010a81c00f04c0e080c3c0410218540d0b400b0741580958082c040c00e001c10301440d540d294219149482070f4562291003000e52401c01c034070840c868101d2800380e02c1440609103d402017281c0c0b0703406035086d00d83c007039850901001e42c001e803006c482e49640e40308a41d9503100c0045400f0414a0412a1042184182140103075001e002e0000442e1080c1c02d0700c502070f0300d00400b040003584000581c1d8084da00308082040960b5465003541d04486d0024010000b803c80c0005440145180480300029001020107010a11041c080103e2080c00203807070703a0381283c46000801c03815503000c01c150000503100c030112030704500f810f802402c14204d000e400c100c41e0 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 600615818 1250 600614568 600614587
    0x150e030606041d1f050c070507060e0f1c05010507080702100b0f0d0b060f0319110d0506090102040e0f06033c0a02030c01030b060703030e070302220c02190b0c 70
    0xc28400503030851042503444900c100c3d1020324442d05c0d030841417101100789407001c581d40302500c0d004140706038014001c0e0420201c83c01c0d2034503100c10080070740041c0045901040c00211003400d00401c00295550b42c81c00000401d564040c1800a01410035034004040e10282d240b0303040040d02c1c000b02c000350011562021001943c44809040d2181c51055040306514a03044003886084501103402601c05e9100d003000b04190130328850103880b0075800071081d01c03411030b6006c0820017000944000402d1441048200842d286043d4090000c0d1a07207450114420307110b0112004004800307541403507054014a12330052100616086107250304000882500c4945241800041c410121a000f030f0503040011510110700d01070212040b0a4024242003000c42c040c8404141d49000300a070050515a0319405104032900811112005590043c14122100386003105645074080c0240c5108915080c440c3c0d0039030b81c500204500f940310100007524210900242c0301c88803d0040038154819641c010084c1092 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 600617068 1250 600615818 600615823
    0x30c270306050a23130602030c0405060f07060b040207020901090216141510150c0611070807021c17090a03021e031507020601060f180609150e030606041d 68
    0x1180d4100c21000588907000c81442d5540a0141c1c1070703480c3c5824210405c02c1300d8508032100246a6044207005883e9030710340482800611441d0060340e48544040341c0382c03074081002d00040403564800d4000384000002101400103902402500a501c065000c00600c2802401d901901d0844109880e40c91a2034854a419210f101525042d421079001451040d415400c81d102060b08003541d684000380c41e601e0b00380c1e00010340c1100100c40b410042c6200c03850f82800090340049000c40000080030f0354400b218a41540746078000d4600328000e0385a0440c040c44030460302d024000c1180c1046015425080d860ba02580315070100c03200075400740c804100403000da01c6071240079559108041041c2d13140c0c9a00f408051a15050070b030010b80c400e04160401c0b03551940491490f04483c0c043c1007405030a5900402078502a81c0101e8420018002c4040060781c03903401403511007107401c079451080c011242001308581c6000c00300390f440d8255100c500400e8090816601801c269909805a011b8241e0681c80701030 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 600618318 1250 600617068 600617071
    0xc1c090b0f090c0603060a050d0206190e0a0501051e090409050106080706112e091209030c121e02060408070e09010506100c03121116050607030c27030605 68
    0x40c030041070038080100c510010800c0c3c407000c2e90200c1c0c3c0c80b400c500e0048001813103504140074036402100c1c224420b070110f407a01400d0f551020008588155008003140004140c1d03171512140521a100392752002a681d40a00c084800002c081241040385000040a560b5103074415540c06401075a41c1003103402150080c821980a40380d606c0140c170400c0d261200c0141401100041960740d0f400030000c0107503a21003040d05d40e501d03800b03000c2890f030303514110184e0070002d2a403003c029003580c04266203941881c2c0d00058006c1a039119400c1c2ca17111070744510120f621200300036002800e12100300303058106401481000324109100034410b514040d03c40107d2400c21020f648a646000f0700c0c2011b011f400d402c2030240740e50001c01624400c0c0f00a1000d07000038400081590041c00380700b030b043c14100100f51160041d6407000700d400d4103941e643c4064000e00d03c090700c85c4d00c400d481c9401000f000c01c0426200b8029100c0c00111503030750041c4224080803089070b5180030007106c0115600c00c0b5001000541c40e0041c203 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 600619568 1250 600618318 600618331
    0x30a05270a0209150d0f0f0803010945020427060608011b030f0603120f03050c3405100f050f010b25020d0f0314030c1c090b 55
    0x1030051901ca40306008180c000902503000000811081c20396907125800e41d401c81c41d4001200c02c100b8146420306405141c06540040e080b4130740040040380d0400d042d003140108116251008012980350b082c04120b80d0000c80641c00b90310a181a00c0342030007100e48001002c180020000501103000c540215039040440c4044003214614611500501190303201b42d000a2400301c1c000e100f40c101002071819100d0b642001d94041c5036460000c544408030725400388015540c00480c8200ca03d40349040541b13810000c2054600103420880001ea807450380405031281c8400c49010300c00050402401e64103040c45000300100b00718800c003090300108070104010507181030817000008940305a400d03400c069600062248004600300c000420a120316101100c9800f281500005003103500302c6200800e02104410213503100b61000d50050510001164483d285440381c0c9400c142d180500c3d031300316882d01084903041c280200500c080d0a04109592a00c851000c05500000703102506036030b03500d07003000d054070103 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 600620818 1250 600619568 600619573
    0xf0616050105061e01021f140705031906031a072a150b0307031103010608010e0c1c0305041203120e15060d0803012903070302070203160803030a0527 66
    0x9110850410301001c0e103512110b8881910718405020006c3d5503100040d0124001c03800340305601913609040d134004400c082482c0d5501c03515003042403005100350004c0e2000782d100c81c420300140020070040d100340d00480b41d1002d165426042d4500d40f0344001a002881d10060010403010240091326240c061907034001c9075490b24010071031608100c3c45402c12400d08031070440ca80700d44e00b02250750016100046035481a46048a100301102203400f6045942c4104117560a25084d2004140003003844541d850f42030701c0ca1444184540c02449042e07080b41d1010f000b151007044140070075213056004032100c600900300104207484d80440401215034548402840340c112204841c4c0e800c41000d4500c0c0c2242c42210440003100c02030b244d0f001c1c1c3d0303c810f01ca1001020410058441c3d8598010026011200740310046034903880c0480015003e50322000b8200d110b80141d540581407120000d07120003c1d50f4000e402182150703603585070000141406000c000011407002c0001c110300026000b5840b074207a02001 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 600622068 1250 600620818 600620821
    0x1211070306020714071d062706042009090a20220b0c0d0203130b16060903080a0e06040807030507051606110106080604080a05070305040e04060c120b010e0f0616050105 74
    0x201d685803006072130304e4403070708c0c03500702c07502d51139007040010140d40707103101d844035805c1c1c85060000300100b10101e0400103003a400740d6104911751180e800751a148100b503a4403040da98a00c1c2d4044c048a035003000380d00104402c038000b442d01942e02406000fa400e00f920b10001219a1541240725208182e48400790350800000c000c2028032060208078010340181c0019814240c500e1081003000e2094083c06400f10400311380c05170119070b03400446650036000301e070810204000d07083c0200002c00442d0703992106814003100004042d0001045442070f41c02040050038841d8640d0100c80d194000301f001e0710244901e12012086400383d074043c00c0244000d4071010342d1a20500413135402c6d038115070320183c00e60700300c081040003017a80303c01203600300c00302480d10315980c00340d9280540380c038040c6800c41ca2489151a04010400c5510340c04910320f040691075032042e80c882d600114042e1101482000d00203000003181d112282003010040c070302a41c005040f141400880001c2000075001c00100340c403240c0d100e60 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 600623318 1250 600622068 600622109
    0xa06050f040606080105010c0512030f010503070b0a02210c060f15120319140a03021b0610090b031e07030c2903100306090c03121107030602071407 65
    0xd4601060320169424808149424006091403a051203130905000e4420801c2041200600001501c038900402203622030a03d00001d0400900034041d0342e01a00c41c845010441445080076280304142950080100c034141c0480d00c10fa40c404003c1c466a0890140f0083c0724041e424405588140b00c461b01c079103080e18011200415800c0d404007a45e001e625820946080248040304440600001090009080292080840f42280644861035442001007107102001e81e00d50005c2030501d03006140c0c1d0300c2c00b84001c003140791503200507200c000ca114011182000220280d4002a03c0d0180080594601c0100c400c4030030182024001d0030042c0d60000702c818070400440594000c080c00c1c18100780700d4032548034002a004c1d0401005503004d07801d40400000d15001c4100d04203805964000710a011021651070040c4c0b60901c0c83c001190707030007045140507103000e10400007020500c10039001072800b0351541e10b610b00290701c81c1400b5034207400c0c1c461140d00c0d5200704000150040003886003004034504242c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 600624568 1250 600623318 600623329
    0x14010504121b0f0206090a030f0b0405071403430f060305011d13021201050f07030507090512031638060108180d0e01091203081b0904050a0605 63
    0x90b1000c0941c00014141c100c04034400d030916410496044da685d07039482504000046c00b1189030740c4001c0003c200d400d0f49030200110194850f02541c443d40c00c90360482d45424030019510b4840c11304507059070100d48103240d900607900200e2440800c0c00d0015240624103d2800e43d401340001d1031294001c49008100000c1291001410040c1080c1c54200302950400640c4801c2210500c0c0d0135050404100104030900300c41d02000b0141c5034000d1154800c044203060301070107000b08503040c00c4040c50407400200b619010f4060940710b03150f19036814850f50300b00400c00c07510501c0c805a1200c1c0d0700c400d00800090300d42c40b980160845000d60b01003030851041114180c00700d0a04078803050122501a04224100465411650407050900749260195612a200c10a0a1440c0b140020328401d00c5605a4803035001079076514a10804c1c7d80b00380085854044811201004c580001d00140d244400100d5100701102c05c000c81c41c245010329450410070304002000e07600305891002e20a41c0d6a482007001d40b501 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 600625818 1250 600624568 600624587
    0x2011e03151502060f100807090b040b01030e030a0f050408070306021b0a031e11010f02030a06051206071b05031917040f0b06030c03030408010902091003050d03091401050412 77
    0x82c2c0e00209016032400c40b00075103c100190240076850ba503000070410085000701c2c840e02428541c000c40791b0055481d18284050010300d91002e0089140c0700000010354800d000c0c1000c01502d101c000c51501e01d032585e08881c9508074202200030418140070224940748103010440065014040141c2c903185419030304551906c80d61001e8245038448034a450010f900090000c10403482c1088504c01c851011209030b9900e110000c00ca840c0e940303402c460a103100c0040e03010314020b040800c0c04000003511081440401c40c1d0240b4110800c5e407001c000195802d1040d5400c0c1d44401030360003145840724503a0348951030b41d00044038007a514843c171a000401d0940c407481c003e116522584802d0071604054544a0b41d400c902c400207443d00311040001115a01c08102c060b24940002d01100c3d6500d42d151541402001c00d078030122310844212000c40c0041840b03500d10b100303803500280a0100c454590038241d00404405070119801c0311441031909042d2420301c182882a400b41c42800300b800200c1d00f009108600c0f = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 600627068 1250 600625818 600625829
    0x2d0618040b0a06081b040b04090b0f150a0b03161e020f0d050304020d03030c020c1309020f01050c06070c0c093e160812090d080c120c0702011e0315 65
    0x1c07007000c000505c22072142c0521031040590740018250036820116018051010b00a0503089014003441450800110054811120442c00240001c00b071403c001900e01e0390310400b0b48418062012402101303501400d00c0e1408140c1c00c0440e04044601110352001b607070302d581caa015801c030505101c0342c070f102072086130091200e51a0603031551400f640028608245000d000d001c042d80cdc0c21075800918001c00c000381c0021401400a2642c071402e40061001d4180440c04030700845000c040900e155015100785c1c0d40d98803085000c0c01d030320780e141c51045130300e0601e01005944056980e8130025103450588a0024650101004107000b02541c4110308010246c17000c1a0019010300b41e8980405d020903029104c84040450030503c1005250814200030f0003181c00700c491045001042c40100f000008810200050729200d2031581da846400c0444140100d400d00000102c411b0001103030600c00e00028a01c0324414140004c00302c02c0a40251407407100300e1904408a680c1d0718280400282c420030351401040c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 600628318 1250 600627068 600627073
    0x60a09052d0f0108150423011121040b0f0405030f031905130201080a15170604021c020607030503060619030501051c081912020a030209092d0618040b0a0608 69
    0x720901d17080000c21008001401c5001c1e849540c1844041c1814020900c41c40d80009100011008400440c2d136440800c40d1020681ca410b072030381143c203900d03400138809c0e0341000c4250031076036441c50590354076280288200c4040c081040707004c00c98a01c0401441c003900c14021a02c1e0b13215541a900385c102d5101400b04421030741003010990040c0e0780f1035043d551000e400304000c1000390b401415491840b58541185140c5010a000d4003a40940000c0b5184524000c17602c80540c56400340040140a203001000783d00641e081020700d0110340254025500108017508031803070040303950b1014546c030000010100009071244010059840c0400c180503080700326100200300c100440da60340c145803156940c507a25820340050080030290007540c0510040c40494000d43d5900d90b10a0000d00a51240410511500a000100e00420800d1807030545542540d444c00c008410541682450800018000d40e44840c10f00300d03041114609608030b81c0202e200e6000018942426000c56098400c1504803100301c0c2e = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 600629568 1250 600628318 600628333
    0x10e071b1209030206070614100605180105090d0507090608030f0d0b010905090c03010905010b091008040213060306052d160314090a0302010b030303060a09052d0f0108 74
    0x200c1510303004000340e65000e180c90060344000c480c15900807100364006940b0000c08107400b414040c094000d9410700342c00c40a001c40755500d2094100c0041b215001ea4000100e050001d15280180e40c0040440080c05040c03681c10901c072031000540840014604076107a07000f54008201070011401800c002e0049100518280300c08a240309030742d400764096102c4441d0315a000d081807640034100820161901401d8200e103032605001d944540c0d8001e00c00d0b1460185050700000d0601460030a8400f1344500916031205200b0100080715840780140050f07070b0200729500c00342401080352080030029407084101150502d0100d031510b00c1d041003400d1804141c46480401c44525003008505a031016002040350b0340541c00b210104c001b230001c4860020301001a4050029805c1c0009080501f41c3c402e900a1049944000905450303020540f0500d800c0702010106105c810440d8001c1a40610303d002d0050507050034001001e103942c00c07603207a080d2048216091010811031020414003518180c1c1c002c7c07050 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 600630818 1250 600629568 600629597
    0x1b0c100c05031e04020409120810060503040c03150b0301020a090501090e0105030d0c0f020315090d1706010f1202071a0f010602120a030e1c110601081e030403150203010e07 76
    0x40c50030f00700001514281100090840d9200e510214010760400d030a045d20240144002c1c0400390305580901c1e1507800150b00090152240c0c08032841135a1100c00c00d00b503207103140d81c0e00b000807203465090042e041d01c4248401c0151001d1024210140c83c0b0364423140c04038608400586a4407040d009943d22050b0340005001507240011820f010990780c1ca82181d21409174104482461a84c4100a50600a074242d905424031003800e80c0780074170b2200d13013681c0e810810041c09403080180301c0346001030302c0307440400214258004d11040401600c18181703101803e01a5059408981c840c0d007080741d04540350b143e904000300030f4440f0b90b64442c0d654002e240103035050410195940c0c40366040b25074201c1d0001801d1041600c2900140442c070702d04411030741e80c0c80341000f44c0d001d018050b0a14200051108582201c44040041d45a040314110310280a44103170340c00006078401304c0780001c0145480100400000540d119002c01400005980c0050b204d505042007034041f860060b142c1c0742009402e9040140 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 600632068 1250 600630818 600630841
    0x3090f060a0606120b100f1b06021b0a030c02100516153606020904180203010b1c0209060a0b0f0301050102210901110c060a050d0f090c030b1b0c100c0503 68
    0xe1203010381031080081001c03a0040f00c00342031049000c01d2004100a0203c1000b45075006054840d5064bd03400a1001c1081c81040e40c507a1034083c0074000071031045014015091243c428065120207160242c40d05901005038501c2c0d16281c41c0403a0303070840800e01c0310301064207441141c450106414024003c54601203960401d40101c0140d80b00000030f010080f01000b0242d41211101d460141007400b1180e07540c60065030030300c03411509900950030191250040e1809808078a0759441c4016040f03070203c0075800740a09c01c5030050880703402c43c0600300c000c0f0744201480061b1036108181010140c0c1c960400e800203060840ea142c4482480c043c450707680310030769054010703a0850071080c6040b001c1e00031807804591400b00045001c82e0402800998040728650210003060790101e10241408101c101583d2503040303a0450b4000740c0440311400c8107000050184803481d07003010207081c8a4030b0001901d03130040480e612a8035044180e91101e00d00060003550781c001d4450340080c5c7d007001411450102e90288 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 600633318 1250 600632068 600632089
    0x206090606090621010f0e0d030605010e060703030207020d020301020c070f0f0b0f0903070f15030e16060809101d0d08010510050a090f0b0309061003031403090f060a0606120b 77
    0x1071046001c03c1c1144004d034025800100720f11501c010600002c00500e0003a80c80c1c140c2011500002410024013182c00d5000301286808244064035803880c00d0f6054904070000c0d0031020040341e10048403031000e40540c0d800d0019010f8554901c002d40701c910304d001c3c0c2001e0380c05046ea1121070714902c00328003040b80d0b91901080e030300d407811100c03d4a0382d1468003000290410280b90040441d40c0394160780429010380c000c490a4031910b113a02c041014410f0124010b0f0303101034540813108040d03441c03403051101e684184600c41d00001c0c01e804440e000c86040c1d03a01c00644081036810a040089102150302c080d400700000412044503042c8020756505107000300f581c000e900340c40c44050000005981c1103407842074240000826071140c0c0b8080b419110130a8002680c03054880e10000e2003a00f022982c4500442044011030794036448188006c4016001e80880b6080141510700f5030081c01e5155003900424405903102c0c0749004400281a03041c48805001c81c2d04c48003c024011303180682002d00c603212441c980 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 600634568 1250 600633318 600633349
    0x17060a0c05120c090406090219210f0203160c02030601050f130509030714030a080a0f0e0114060909010c0210050a0b0d08070c0e07052b0c02060906060906 68
    0x115140110410a8601e4412000790b9000c500192080003c1100c0540162845000c115801c3c8245507580388584181e0291041502d0f100c1d01d50107803080c0341400b40e12a20106825a2a241882280c610a0500b101c1500111920a0350004100011010241309001112040d030400849079481e070b80219a9595050160034000c00102c886207145584118040f81006c1225100f8010381c5403c3c0c80301a00c1b500908401c54914021084403407800c04c002c000e46400c050300e40d90700c1e6242d5446ca14000094003401c010084410b076110030040c0c1043c8203004156441c1500e60315890b031410100107210f40d0f83c20041071080607900d009034861030540d02141c5032403840030541e03011400c3d48980c18094020305005012a612440041c035020070401c036500900080340c000c00c1c1d0000256900d440c0b80c180c91340221040c1000403410403192002c0c001355800d0070b00c03810300c124940c40100044e415840c201e0306030843c9403003d64411010440203800420505a03c0a02511001c030345040c03c80201c0c40258451418 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 600635818 1250 600634568 600634571
    0x2160b0d0b060c1c050f0c0106050a12150c1206150801081f020306060904060e04030215070e01110c0a0f03050106050d1128030b04030f020c01050a0302090123031017060a 75
    0x31041d852007101a01c40e122919050b040c1c3e141c1f0704a02d954001d22051041c5070043c03c0c3c0a00020b00c2c00d9490308003e40035034000009890303020f402c90310364009210840600c0180002c400c16441e102d003031071180308042c2000c41b00c07039550b140c48070340c010740a818140d00c10311281c0c0c8003880c1d40c007006000f00008280c20306401005030326a00c9140014030b440c0078580303419801a1070004005140d00a080c1001d00940c066020341700c0102d0022409140355504656250100e2010b03460a2110751040004c00d030000c0201043c4c894595410f00000e10024442d40300c0924554844e00a04c2400000e104240052800311803c40e851103241e6a507800c2000c0e01031345d01d482400c401c3c105281070152208401944007407001509a200d807280740244200c001590f064000a80410881c030042d400028140c40c100016100c060030310708514021800703980f050704840c0c104400d071040300c01c11110000840024000d00300c0c4494587c40e08078030000c0b440646602c0440c40240901d0343d007a010b24085403058000201200 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 600637068 1250 600635818 600635863
    0x15090207080910091a0a09051c060f021b1b1507060c0f0909152309130b1b0403020607060204031b06090503072402160b0d0b060c 57
    0xa01d030010380030314100e03070f80c0088410000a1540340e1020700081504c8040ca01103c0c0c0d82c6020703000e440680100390413040800c044440600503464240c1005481c00030080401c0d40e0142d40c0c1c0c3c0e80c1410303030750303018148002c454000c0fa80032680b202e812a1800001c98880c014003451114460020030102c185280d5801380f80034a010031084658002160740098200c1401d000381005a4401013184042001d00d000140040d540071500c48554016200c01302400d203250300d5181e0400500980c1c0038684207501c240740482c107518a141c0e4450384c0d5034600c5408481016200340441d410140300020005210042012420300081c5030008841c0035201581d8054560b684c4524007443e10200903c6aa0005804000501c0c400b0010f6940e10181c0340c20f4078440e98403400115500c805059030755816010301015084860800d50341ca030501c884061032020113204603000300034115403001050720f103074110b4203418400041c0c0742c8054646000c2d0040c2c03900280c40c0749160420f410503241d21a010754880000c4000c42c0b41 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 600638318 1250 600637068 600637073
    0x41401020a050f0313050406051f1101110d060602190f1704090209040e28060b0d03110f0610091e05010b0403140c010206040212071208090f0415090207 67
    0x7104031000781e0300c02c0440c2c140d403401204241e41c0390010700f04403416080c11a4046050b003030602551003216805044440e004540600c1d0f80c02c0041d80d410198204190b222180000d200b0034007502ca40c46400401c0141c0d505040c00e482010b584e0a600103209561220f41940c054010504184081342e80215800c518400d23207140601d466150b007200f10f0203211000c0b402143e9113245900800360304101320740170010503010303440b031544880450042104e4180c60380060783d01c010380300c040e80106500c207510014101c0803080001d50340400e205002d40010b0201c2044c0c0703e070f43c502000300607030301c60030f0800812040c903014030f440c40c1340011400303107038407560700c40f001c4c8001045820400c500c0c01c869000184003660310f510380503010750802e00c81a25520340c0b42d4040c07602c181c00407921221100060b07016103002d680b55000d000c04d00020880e91400d078400c1440001d56640800484038400d803140c03602d182c0d01c0b0503a03420007910f1054668106e104a00c1d04c100c5090b180c2035204400100c130440c000c003586500d080e0 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 600639568 1250 600638318 600638323
    0x30109050718021c020405010e0904020919140c0a110a2301330f121106070b090606041a0a1e0f0308040602010617121b0f010e070503010c0504140102 66
    0x11030403c2441c0b111342214418180507070042c00c103840c82039032103c15020149040010f41c0000340c070301a4000003298085000d01c0c48a01c4841c1d9084990000410384458001070380e04010f204480c0c1c200302c1d09001c11080c0c1800d0b0300c0070703158041c015034100a2140c540d0a0304c4000507004d040c802c8200005129985030b0004200390070400000403800c181c40841170200d480140b240810040346442c1e607210b0940401d41984110450003076640c04103000a0300c80559031102c603200d0a03090780d542c0c0a00284007900010312142011407203245820b02400d0b89003044014041170f00c0040e41d01c10365110101c009400c103500c0308600c2074100ca000c2c8075040500304005ca000702041482d60000c40c03481c1020040803041c002d031000104204c0780d01f54002c201113035a032002940700620490b61011f903600101c4061030000341e8400039040c1000c80701040d040364504d1303450107840d0444103506c1c82110703516100b0303184140d18103000380c0c80107080075802808503e4a82000a216201e20f01412401c1030001c0d800d404164403c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 600640818 1250 600639568 600639577
    0x304031d18040b01061130091309111008040204090606051002071403010e070603091b03060e0609010c02151302100915030207121b08030a020408010b03010905071802 73
    0x41c201000202d0400e400c000415000c2400340768040350301310100c2052000001468480c50541c0303003403c0304001b6801005189480c8070709501c0c410840034400d4158030755900340000c1e40b070803119100103070140e070504c1d041c11010304100200b8440d0460b180381c01030654004684940c8258115000100341c032039490914020102d0380c1000d504801260804441075400003144004e032211419183c0000c48a8810507090f90074294860941e9084504100b0980c3d0003500724200c144d11805107015030201c0311005403c040c6684d8000d84850703032600c00c0f68188100601c035458000003950001d001c038404140c00a559442c416007801c00c2c0d02001400656a81c21402c41c0d6650307035034000c015030040400004024070f1540d04e402080e011010402a12004ca0f000744210b410032580030b103441155400408066071401009110790341c41824403a8000000343d080c0d00150b04c00c4500400045c2c40b10300b0442228211600710714214005d0f8508140e0718003141000648400302c40044060000010003600c084020303018 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 600642068 1250 600640818 600640849
    0x3051c0906120e010c0c110406120807030306051017060f0901140d02130b011701030c0b03070219060509100e0307080702060c0102120105121609020a2303010303030e030304031d 78
    0xe02017000c3c515aa100d080e4601031400b07040100c03480340e95101080129000c0d44120710407400c03030400341c400040c40c29000d843c4035802804d001403010342d1003001c980303c22140105040094115140ba15032041c141040f9500300c04155000c16101500c800869060340040c0174544807003a101898039281da407500d1595a0b11540607001d20b200e03401c0e03400c0c0f8801034800c050782c8a000c19a510004441c098000c41e030036049036040b510313242c2c01a1034414528040d5001911040441c01200c1c0401c1c0721128048012010508c208000200c41c9401d54050b81000b005900002d06681480242410504008240d810b80307500800704c19954056440010128403404c03801881da94008100000307000c034002c0c501c90417910280c074100301116007000c009440b0007070244180d4110404010500280d05c281e409010030003111305082c915644400402e00c8001d0605603480070007400080103200b0141d260050395402c5c00c5c400c0056007141000d5038042c041c02c64030743d101c0100680c25218002c0303603503494800c41c5461a = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 600643318 1250 600642068 600642071
    0xc0f040506120412080c0909060a120b0114010c1104020309031308011a0907080a0e0c031e01061e060302181c03020c0604050a0e1e07080103051c0906120e01 69
    0x10301071102d1440c80c460459050381c900484100c080304c03440c01418064030a05080c00403030300c1d00ca6140300b00581d40b8000b030003480c0c0004003400e0100f4802c1d0100b0401540c01e0003813451071169894080203100c0d80b685d2030102410424101150f00002d803802d0120301e4642d80440d03015072a0340e076541c280e40c510f00a20004038907003076248200140d140c0d419401080d40582d00c14980411003007480c14407800e5501078400800040c00c240000349616081e5120400d114002000e0341d2081d84502e001074507044885507104003500c12058000e4140400b44669001001035408543e408102102c044c504820030703115070024541c0015260316950015a0100340120000341004e4000c200300f1448107080320400e8044000d48103051081e80319181190590381100d0005000c0c400b40c90030701800081c84c0f81c026000c5117542c400d03071301d011981441c00e01c030a500c034007481e40d51142d01d50715500b000e40c5003056a54240c140720b44500c01d0402500c0c1d0240d80d0000341d4146061500c07060401580b03000003003c1035914440c4d6035 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 600644568 1250 600643318 600643327
    0x1b1704060b151306031a0904033b030d020a14100c110c0a080303060f010210020a0201230f060904031803060605010e0a1805040c0e0906012c0c0f040506 67
    0x496461001d084041803c00b20150385584401050741159001280e08041460720700601815140030315207141c0c894481e26101e100f141200101510030100d130001285180c1010304090803400c550140c440c5000c8003180100314425000320060348400c449000a019083c1c1c2030088a107611f000c001142c0c0c1c20421140c104401c81200d00e006040f50681080c10300c041c05141c2145500b840d14007241800c0e21a10006145551100308c200500400340c82d0025055005503031101c4000d10003072000c0d0410317603410780004c20b5511041e20800b414210380941445481061014009600480d100142c0d0259090300c15907282d0b00c0c1d0b4102034545640d040300c2c08007020300244010040100d150032036021100280c8504640705255010400c2000f102c1c0101845240c0030108446414080d4218a400a000320b07801c642468035070b1080122281c01710b03042125580220010402031801001c00710312050480541a0003007034181b031081440001a000700c0f6424404114400c0101984007200c00501d0001d00d00c41e0355 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 600645818 1250 600644568 600644599
    0x206130b0c06071103070c0611120f0301080c011b1e0b07090515070203030f0d06050603010906051e0108060d0309090e010b1008040203150a0f0204030501050405011b1704060b 77
    0x42ea641111210005414400241045072000050790190740e8826103420710103080100803100e280050504495034812425528005000b01004001c80c403414805a0b5072581080c0c00b280c500304141c00c0c0c5038100070025006160f00c0d006182e0004050390f1000a44c8417284030035022800d000c000d00005040600054203008110760000b4607201220801e664900320090b10040264403801403450294250b0010000c10030804200001041241031201d0f000038015201c40106034290026085403140035a01c0c14207000c14501401700e0b02c1004000c0203c02d40041c9a00002800f8803c09011980030380010210747c81014020408000580203c0c142009040d4200344400d0103808003018180c0031f02400c01340011042d22070b40e030581c85903030040c00038000d01300403c1e080f4140490003080c03120299620020041030f4000303800103000940c010400030403682414100300d800c40d81c038030700c0d403c0d2451502c01d01200c0c66034001c1400b4440424000d1955088ea0700c03818128060124000d004d41e018070507880400a = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 600647068 1250 600645818 600645823
    0x12f0a02062d0901050703211401031109100323010c09030b16020c10120203161205070e01050a0c021f140a1b02011704080306040c08130206130b0c 65
    0xe102100400c030304881c104900510000340f09003100d003070004404000c1903000c240110380c1c1c45107580f03040e0140584840120355800c01c84280e5180c501203601001d00400c14000c0080e200c10202c2c00840d000d0000703040c901d410319061003691100624180b244800080030810381e4004c1d18040b68803000038007120041c0080101107050394017040b580b2500c490081200603c00c4004599148001d4004041100140041220f00c20400c0002d03810461050082c103400b5005001450240d82c00c0c1e134100451032468040980a10105026070440529100030403510300c3d4001e403100c0e00c040082c20865600c2c000c00c44221000c058116000c0d4001d0800d081b03050100c04000c14088104a0955880b8280006403550150b1341c42003024a1000480d800e003050a407840100400c240f0510505000100741800c0e010880c25140441d820b5804200c04410092203003000c0c000d90390310220520702100c480c5020120203400141c1042d0190145401044a00c14481c40b0213422000e00300020f4030321b49030030340f800f10541d = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 600648318 1250 600647068 600647107
    0x17130b1c050717010e24060912070305240703020702030d030c0c050a0b042102060610050418050106090501050702090a090c030510090302190b040308092e0605012f0a0206 75
    0x10074603c2004000750080d1010785408103c220014807c914201000b0304129071002c207032211105c54060040004000748041050302c883e5010411005820313030941c1d4807082c010400034051400d1500410810005035400300b0020142034060400048200710080100c1d494111150020010312540410b6004d0044490f05c05124030300c9610f011014440018088044210400b07840e00940d1001c00419078070b01c0d1003a290202c4c80503914045050a50720b0b0b0301c6600e061384020280c1074659861005101e425071180b89170014040a0812a01d440c5059000c030308072030ba005041242e1566100d1082c0304000c24481d01400031034008044a071480b0706005901d000b072031121421000340c4280140c505c080f01d41c00c2ca000743c00c40e4005900003a180d49986064404e918001d080000e54041e200e0b9665418a80300701c040000308030340c2d14030701d00718048060602c1290015080a81400a44280085410001c10102d01d10380007483c0d007a054589078032055841d145100c0301c001d610200100c1c0e00907140f400f041409 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 600649568 1250 600648318 600648331
    0x706050409180503120c090627150a111504081206270a14010b070501050a0b0a1203020106050301050c0d05070c02090c070f17130b1c050717010e 64
    0xc010340c0250380840c128501c02c9010080c40364109000c210f0301d040c1000d0500f548a03a540709502d14000301400000c05580c00041015a0085400f5003400c043d000301300b4440804a081e24040220b001c60450180d0501440d1121b03030810092280004030795006002d02074403405c584e44113090f54241454000815081800004002405d1600007030380d9107811401000c100940c01003a6003030300010307040408100c0e40141b04941954807016051000f89001d00c10f82e0080107540c0c00c02d0b45400d0149401825110040d0562085900301665903086589900001c8110340700d01d66920310428075450213a01520060340480c0d072551031700040002e0240e07042e0060510030185882040581d6441609452445801201a400c0300501c0005600200c44e0402090420b00a8101711055015669815628406e4030207002200c50b0214480802c50743e5802c4150140810950b01410820f000c2070042c60400c00b191004a066101c2d40440c01560240580e00492140074070070851035078503081e110040d610180c07000c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 600650818 1250 600649568 600649571
    0x1e18080703020c01080c160b071106070807020f160506031e13030f0f0e0405191a0406290d020d09050703020307050a050603060906030309060d0608150124020705030706050409 77
    0x5500d1444078000c851f03c11008010b101903601c4251100b51807031400400740c0b41804201c42c1120003445c002c12049100d000303a592000450b14060200905040f201c02c2c0358141d91f0f00580f8030180070003014200d601520000c0e00d40540365654801e184400c51041140303000c0d10444001880781d185442c1646040c0c0d14020f440c0c005000075640803c8aa039541c0d0131600000617a00da030b1650a600d416000290000500000b429480716010b071803504440d224410802c80e540c5050380e1004500f01801a20024602c5c0448c19603030481814000f40311013091020748540c0325000551408a984541c1030b603025006404042016010a14001c0d640f0300171400160311030301c601d0303034006001d1070301d20300e0442607540241c0005c0c159201e0b80288503c1c954043c110766410300007801172007800d858030b8000d001800c0c2542008200701d450403402e641449091244c402041116000500454448440d05c0000d031f241c1c06400e1080108041d0100c0c2003040c50b0700180d9040c0680c840014034950b008010b0000c0e03e00307a110 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 600652068 1250 600650818 600650821
    0xb0306060a1d2701050402120c03030f0a0504030b04151a130b0303040e13120201050c18041b0c05070b0c0d0c0303061d090105060102011e18080703020c0108 69
    0x801200c5405480340000705180021003200d0321001c25806508102941056210200b845800f101c9408440c140701e4160b039503c0c0304110a503e4215109a40c0c00a0300015191001504010070f4407441f8480e244100c5520020b0320405143c4034a00725401035401c448140e40d1802c00d443d0046219001d5030140722000d05014900c403d03803560003d803d05450000300031218484456152001401c06035000c968140000d001c00240413054115003480390300e80a64050010400f8174100c2001c030400324805046a00d03140420204088103021901d002c2a0f0980c2040d58140242c000760240003904940400c462148070100c41e45c80e0400507148096108005813030310152600d0000700a409240402d020300d501400c1d189820314080c000900f80307203000c1c4c03a001c55010b8480d40454014055441e00d240604103450800c14004c030213204480c2c0000091000b131110080138084a00c0c031583c5d800520321301c12303596881ca0f8000070100801500c2c01d980895415182e0a590501945901e0036520040c00701e4500d00 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 600653318 1250 600652068 600652081
    0x3181a030703051e130507090606090501021903020303010308030613090302031317030405010807120501080a020906010c030e0f240702030114040804060e1302070c05030706030e03030606070501090b09010b0306 92
    0x1821314a006074841c291a0702d55600d02001c0b0036604607002640d0500070084045000503042c000c1c00c01409540e201d10740450301d407000083c980300c1e52000caa14050040090240083d50200403a411250040141c07910303134580c607000415001192407a44200e5207026410b17410150084003500e4001e000e00c003010000342d48d560000400407035a0f624402107030002c0109010a6008003907050304021180340622182d441003050004613076007038101c22010307071000400310110700e0015140c59000000f8a80140890050780e03020f0108080c400c1040e10986099404540035194075001c04102d0741c4821007030b500913801a51901c05584000d07010ba01950805071079400e031340c2c3d814224500455005401c02d292034a010310841c1c1a00c6614410313507001e109183c94000d9220f15001034050f0500844c01c01e04841e260608251074444140e01a00c28503040101008010201105a9a0040040d18150b9940515203040c1c1e005000641c402020041854240704140b0f80542c0700c2c11081d81c05504540c4ca40d190030 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 600654568 1250 600653318 600653341
    0xd030206010e0c0f09040c2a120306050915040b100c05070b0a02060f090109080a0f0e04050106050405040e0724020d0c120c0311070b090a090207020105030403181a03070305 76
    0x22220f110080d03108000002043c180713a0701035102c610062031305800d211714151010040b0b254004a012100600e190004103000e09050410210040760408010074cc0c41c050102d40c0d103040080142550080c10b601142c02d41e1115042000c0018000303104141101002d2801391a07039003100c2044d1800d2095a0021408d54262001c5920310496034000f8841da44d603c1d003036000e214200034040c034a955240d074440c1700010104c02c0a444040c8490b10b07040082c0120f110001e141c07040c0341c1701c403501c2142031500400541d5005001c0350269901600d0128050380c507d2040c61401e0307080e50103c800880d4031544401c4526201915007040c0901e642500d804111070901160148199140038008034411011405e5150003581080102c503c28100500e50a10a40c0d0090410a40b644070404040300001d09070b10b02d250044000003e050710300c1c800c6080c0150f5400007040c60200901c010144030740000111080000c00c03968100811204c2c242c0550301030382d01400b02c42d9400580705240803a00300404154150b401 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 600655818 1250 600654568 600654577
    0x904331d1204050d06060f03030c030305060910050d06020c030408030a110a020f0409050c100203041517181e0106090507050c0a02040209040209041b201504020f0d030206010e0c 78
    0x100d600076410305042504002182c21245002c884407503545e100004d0700114002c00e5401140a40c945800c641020305020303050307400007010b40d88142060f5081001032403202508005603041510128440174007494044028070848480e0136451001183c000b59004c00003004010303c0440707a451140e2030409072417160380d450700072100a501a48c418051b00d92801c043d44207a199a02460807128188010004100420f905407904c05c01600300080c24070548289001300120985980303801102e8034112140032043d142302501e00d901031049103200000d2008101b0090140c4040071245160300e08440300c400d8020400b0b4410b803031300141094001442503014005450002c103160000c1c02041549900f04402540030310ba80c9940182c1c244600681c1c0c2e102d92180189540182210780c0085451840190000c5080300803008110b000503c1d0284014011421000b1350030301c4145a06181c80300c1c0300003401c0c40b8003968019045510700c429002031550002da0541200e443d010f18085580300c2c1c8845541a114 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 600657068 1250 600655818 600655843
    0xf12090a1712161e08010305061308070b130b0c120c0a0f030e100911090105040b0a060806030703170306090601020705031b180103140d0302090904331d 67
    0x3910000504a550b07007001c00b943d0883c083c5048400b407485403801101021050010200280c0c00f20010300421404202d01604940503840c05007003c440c56842400c00c0c410010028010200880424001d80c9200c03078140543d58407e001d0301c40d03440d040302458442c3e0030440310003040784040e0000ca03038601440303021100c01c4c1c9290340c3c4d40d04143c1011002a8040c144401c0030000c40d00c0346443d00781e400e1400380729500f003e51261500d40710003035a5030100407140d203040e04003e1246150240e6044182e403242000000c50f480e50030444401d9680c40002810444980e05c043c2c040f082c009154511a649800214401c54044944003c01d4841000484e6120304502602c1e4240e44400c10501194112907401400c00400620102038240742142e00c0911810aa104071401e4280c440c0d41c030303403481050201203a10b40051408604041202d0001000d50070041c00141100b01400728580002580615045021043c0c42080714800340c4020600010200301c0342c0c055031320b03425462907054260301142c05030312000d = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 600658318 1250 600657068 600657097
    0x100c0309090b0904290c07061a0d0b07170c0a02160f1a0c0318100516030309020103140f060312190f1707080a0b0f150f12090a17 57
    0xba101d96036a00480060046040f00160385d6902d07074507000c14a180305101e40824000c4544800c0b25180200c280d400b84484a02504a601e0800d241c0f0b46890902e503030704030b0b000f200b242950380354088255206200c68484256506d4118200210701c03d03d0700041a9404507503080350400010586801c00400c03040c051000107100800082140c40d010244944401c80d68607a100d103404410076001c1d2450384440780141d019042c0caa075041c251720b0034405c13611280002e030428500e001410324000300e1105541c88014145503a5000c42401d5922030707489203101c11103240d0000000d0070003400c005004a0110340d0701d4441c2c40742c01d42c5000f20408140558500848080c890707081201c1c0d400c010380302541c2215844007080680f05130910305440c051203040c041c01051301d0780840340c00d00c081340100703942040d2100c41c0180d284c4e000d614600c9d296890114280d0a00224480d2500040b440b1030559100d269070701c55110b0020001d01044000214030030550b50f03c04c812481400c0c6110f440e0450724000c54074084682e1 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 600659568 1250 600658318 600658321
    0x23090a030e0406051206011502070303020c060711040e010b040b030a030206060f0f0d03030b041b020c100e06040806010905060907080c0c01060b040e040c050a050d1e02100c0309090b09 81
    0x68040e0206500455008102181403511613020400010310210900d01c0c40d80b0010042100f0751410302491040b020900c043e248c010b0568901940d6000c40c42c0303859004850005840041c0b000210460fa501c0000034400d10a5141600d84607000e05101444d5910176440c1004880782c5140000700d42c1807495164000d4800d030350f502c0303003080802d80c900303014550055001c2007412410356500d5035000700c880c030030b4030300150b42250074043c08122603c82d50000d5000484003e00c0e00d6030381e0001008000003070211019601c003505a0b00c11a1815030121401c0c0d013003800803038003007000000403607007070306072454104c00b088140e441c081003000c0e251040e0703490390104050703801142c1b805a04400905559680400200f1290380e90030030429154025400b0768003a0300b01c00180001c000d002500540204002c4660106090500c00001e510491031103004000b24070b8102c81412403408000301a0019400410b000080148403101a040d99500f81c4210002542c03458007045080403031240c0c07100d1a40c041c1c40311509 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 600660818 1250 600659568 600659573
    0x1080c010c1e06050f0f010b04050612131217060405130201080c0712030606120603080f070204060905090109140d050711040f060f0f1a0304020103020708070f0623090a 74
    0x1602c0749511502c21450301200c5000101c0d0303c60241600501c88803841d40f84514207051007240c46101070704100003a000c1004100040d554500c25215280c40c0c10001140c25101d61007255122188540000d00300c900004210341c18907013064440b410f01c080a018811b182d610002000102c400c200d0b40f121a411050040300050f5102c0c0c0003491744400b140d024280f41c03420fa5158510210007100001001036100c1c2e9042c07004075030088003a28004c2402d8018051542907030340340d50960084c05da08000c03012011031885c05642d96038001c18000c2041d1082040a07003840e0381c80ca030103070036840800c3d41e00511440440040050001d186142011a503407241e09101c0a0340d10441c9100300ca0441c103601031340f0791070145900e0b003135481640e00401340d00394000802454482280e03401d1119600c94a9042da946006589022056088031f03400303582441e0050350741910740341c0f8900c24024124054a5820010012030400003070380c2c41444401d1407112846040344640740d48030202d14048032141200c1d0080c540c00c000 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 600662068 1250 600660818 600660833
    0x62a040f060302130b0c0a03030b030a050709050c0922180c090b0a0b16030f181e0308160309050607020102250504110304060e1207121b05011401080c010c 68
    0x8100c80d841074134010282d9a00c460071182e8010040c2810590032900303100040542501c030320003d0b91000d90140c2400c8503036480300345c0c40d42402c0c410b09a840f0b84070030024050200002c11100ca95a000389102101c60902c1038140c44109040d0030406010b290607155003102d496100c94031000c42e03000c0c0c40205140c2c01c01200c0b002a0a000607400e401404c00d00000c1001088800588140d020040500d91942c8641c2002000d401c52030309500107000208141e010004c03000418507055070250b00c4280a01602c26040e01c84440495102905081002c00c06070b464003d040b1190b000c4900950340c118be00754844082141d64031034001c009001d41c0c000e030141d0341005802d00c4400e5554256440c3e9402d0740b43e45d0004141a03926002180440d040c000040104000c4240701301e0b0f0190854200501d0440d509114401e007600c120040902412104203408800c1c0f440340e203c2e104502020000904603030032900e001801707400540c808280c803c01c92400806c91010000d42040e0440c4141d407800d150200c152107442 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 600663318 1250 600662068 600662077
    0x110714031f060b04030609060609020408150c07142b0509130e07060c02280b030c0904060e07030e0d05030109020f04050301060b0c0d140f0912062a040f060302 70
    0x4080e0782c03620b10004006141c1c0c4058001140200700104030040d41c0d01d042c1d022520103402c1200e4051043c40148017028000802c400c4180406031071042d681c42d110080d24250140781401005503041c00c41d518405003021404100014500501103211480d242c00038580c090115180000583c080c8100422464100e0280300c100c07c09000000b256154550550708188039908000040f03222110340004504024242e110180034485144545c81d4103401c40c0e2012650030301c501250180080085079a11400c40d08030b5401950090041001995648000013613010031118080400d01c0e0481e031304040640410301e00803610443c1c1c6c80c2440e60f0b003070208000082d08030300c0d0321340c4800c0810f1002081a031000d00c20f40c00540341c4045007544071781816640318904003117460242c00700b0040000804400d06860140c520045001026a0300c070007022010810340d01e100480d01d07004d88940c000b0300c041c1c07420f241052a06c61305440c18a06003025400d1070b8440c3d03440303903200d00c5169000b00b01042203014072075400381 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 600664568 1250 600663318 600663373
    0x3031603110604060209030d090f030b061909060e0a050f010e2703040f0b0f030403031802030d0807030507020c010c0b04060b0d110112111206040e0d11071403 70
    0x601c030000e480301c0c518100c4100c80031100f155001800e20b480d0f24081210b20441d0303003213150056440d03007810103040f14400c1500c0b00400b540d05103008a0354994855066049003986030302250440d580c0e0300c040201400681c0b1035028840c56440c0814901c840b0790162600c54401c4500d40c80c0540d1a1a4515110100c003c4c0700001124841e14040301002894030b0040c1c50340c103000c0003182ca0b039080c4000b800702d409541d40b285d5140c03401003280601c2041600143d079445601400c0004441c000e030005418032111210313009500d400703101a054569034004a40b00d0040c24145e804100b9617498003002c0e40c2d14407068003900e020070641c40d5884000303403a06070b082ea4042d104900219000713078000007140d68112201400c80e82d00ca1280d01800155900040206002e40d256809020180554000c04500e10803e003012002d44101c00025506442e50740050300e250468100b200c42011480d000104111001010001103000300c02001034010b842140d4a00c0b40480140580001544000e0b19078080c02c01c3e9260 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 600665818 1250 600664568 600664577
    0x3180109050f1219050717070f0603020913022a030901020a0b091c0f12150506090a0b04181407020d1b0206040905091911040b0f1c020a0b0903031603 66
    0xa035694002481040140244900d0003407a21b1410420b0158104070028450029603111303000400c9200c0b0161221400c4544509006a5134a03040000c039141943d0700c0c0c850b170812800007908644a001c15080015807028028904a0b40006444000d80f03e1150026060041c4c0c0601828004100780d000d4051308040c00c80d0485002034024440016085250008000494841c1400200542e04a885202d282c030703074404100444044440385100600707250007124000e19010900c0b60381512404218005403501c1d42800c2d0701c4544c0c0700c450b5038100682c004070040b540d00302005000b6400c40e1201c41402001c1c542c016107031041c001201110641681c122070003c0900700d8080c0805600c03010004d03c044e0101c0d00f4007090b60b1500002e003e241c110703903031941100b89a81d014004041012080702643d410781c100d5000c954841c1040018503040c0c074102542d540b08110140d10412400b2042182c3d04e000e100396806640ba42e540c1d04100740a003c1d94039010740640003000103000460801da07454403d81c0c401c0c1007 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 600667068 1250 600665818 600665833
    0x903050f130e01060504051e0a0b09031608060916050609060306030a0602040303120624050309070b0d020712050f07060507090e040c030203120a231b03180109050f12 73
    0x140305200b0202030b8000c1d404034500050a0110742030003002882c04841007488100d903000d0340c0002c21081a42480b80405010021510490583d000d10001c1e0a01010b00d481000b40ba0711104401d46820041d92000300900c0f8603103801100c4802001010304070742005041e5400c1900c41e100f031158641c4010700050341401601c03038903c0003d150303102074409140680e5a9015641146851400300d44140c1c0001150314000c07852010045810726641070f41003510300d005526921001c60f114900703075a940144d4160200441d50400100d250386c00b034101680a8020748540400ba031000340c510340701d0100c0d01014400b08000c0d50b00802d07800c0e003000350085580d1a00406080d80c0304144200c03000140d038100c07802840e000040065185c100040340030240504425840c3c00e010040117800a0110401032654a1070301d0f44181d0362844820a50f0b03061403281c4460b000b0000210106902e0364080056400c01008002e58800b40f94400e03003900341030307130006410000320b05402020000004100d9050300c619201d00303074 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 600668318 1250 600667068 600667079
    0xb0102070b0a03140f010b0901030b040b1c050105181b0d020402120a06080615040f09050706090e073f0f14150108180a080a0806040c030903050f13 65
    0x70020554801c1566000804000c0002441100c0c1800760116015580210040c08031079600400c81f400c0300d409007030000b01c0d20000b50100e0090070030103111035030044e0540c40c418203e40158040c030302d680b440790001300310917501c901d00003001042100c1600702075400104015441100340003c2c0c101e0b00f02c020443c400c0003981b42e0010341a684840c4c403115140c1a40c0c23092210784a524000d1401030f00301400648510701d00a40707549408040702c45094410340c3c4802c440d01c40c0c0303034040d07015070405a00300007903403d601d4690300c001d000740e4010300c1a0060821080c000400309445401521a1035058880710345c40602c103102000d00c0002d04d100484681284980031a48000044c86440b61151b15864045080301c0c0c440000000008000d200c240b4103218000b501c08903a80c0159500e5200214100c0140c8244203181410701d490f12001008000c207600040c1c0034403142c1c0104000b0301c0303508110340c00d102003082c84500f2001c0d00c0031414000e0105030284082614100c042e0f01415652a0081c07200c1007881e42d49 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 600669568 1250 600668318 600668339
    0x7110304030b131203060305211b0c01410c060108100b010203070f0605041703130c080307020d06020307030b0d080a180e15010e130b10031104090b010207 68
    0x54540358106600e143c80001080014000c50801c42d180b400c08000841c40d6071107183d1542d14200110380030a1030441d00d280079410420549200c00343c0001d072000e03002d51304411641c0d680e041011003404101301d840a40f40a2200d425601c0403034224000b24500c68518280c249000c000850040500220500c000860030408200c1d1500034082c7e0801424103100352902ea50407100303070018860443d0410003641011074251040e84c2d0113a5031180300043d030340e075031802e15407401c04807a40c0e0f44541c000d0020501401503d012256802d960080084003241a07403000c0079980c030f01c0f525000941140c1d00d4004100460f1840d030207142d008450b4140442d07420310420020f07040a01c418811039aa500100d240e15801c4c2d808070000c0480d0117070401402c03910303062540c0a042c48500606030a05151100d19070209a48038128032001c214010b01150f0603080741c0c004482c090301101d1040c2c1e00941000441d030001e14441d0082815214128105520707160402c402100502402c00c03e0340c0c103600c1303207420000728030318603 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 600670818 1250 600669568 600669571
    0x180c09110d2c0c030303190e031b06060a06020a02010f1b0b0103051606050f030a0b040504060f054b040b101202130c11100b1504030b07110304030b 65
    0x140c0c0302d81c40b090104540384000c401d0001c22a030400e0b480a1100101c68030000708a903082000300d06050703102c45a454151010b08401d5048a00e1400085080ea4101101042c88001d44150406a87c0d050f0307100c40034040d4141d29449580b0040e0300c003494a80255010b0b203407440c9020b8003403501100b10221400c5440a0400c01101160540c01340d030010824000240700c4000d0008004249040c141d240c080300505500481c000c4507030f1a80e0000c04604440d045034000e000340d41028005201034601342c02e10000504191804a0840d0b0800000440d0480c204190201031010007021110704454407000e6400a54000100d48080041e45400310503052200381e07844c4201d2040c03001e07010310329052040664514640d8082400101e209041c07000580c2c410316010f084054850700095507045100d01102c1412100c18908030a000d580d5040740c00f0102034210405410702a80c0990803000e040d490020284201e02c0094112044900420801d520800a00300c400c2c0d0341c001203904040c0c60340c6400404240 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 600672068 1250 600670818 600670841
    0x909020a0f0c020307211e0b1b091f030c020604080d09050102040b0f07021509090c0c030702040f0c090e01050f090403021c180e0f070e060705100906180c09110d 71
    0x100e0f58886c4040180c0c49900079418401c0c0102000007079150740d600017180d08090300c410b406496000d07120142503a00d03415901803c1c4020280d0074421903d100b07800300e00ca240b00000d000282440b00b00d4094600000300c0301d001c1c1c2c1d480032009140c41c0c040070080009103107900c01101c142d5000c1000043c011008800307810092004009165100600d20401050005032045001145000c4c880e2210554540004035400400c0d00d0507503980390107030503043d41584224a00294080c2c9003485074041320015521541052030641c076008402c5884115005c8505400d2140c1940056200b1180300203003403540010740c10034481e00403a0100c42d6410034840103010b14262040c0018108180d42c00c076000105955002040100c2d4030b401e440c2030100441c0c0190034010b02000034403034004400312180e29a48215801c0941040c00d94020408204141c0040c00352201c040d960303542080388031070b003d14600d1945d18540b940840b18a13040c91900802d03801914a51410380780001d42800008010442d50044d000c0458 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 600673318 1250 600672068 600672119
    0x14060405060d0e07050d051015081507030609020c0a08070602041703070303050c090607020d0c05060c012a02060f0601090e131202060112020f1f0f0909020a0f0c020307 74
    0x103c514082840c11856a001d02c0c41808075010940201701c010414041d0445c0368580440c07128002c840311640c0201c203034401c2c5001d01c0713100c41c032a000c50244620f0038000c40840d80e0504c6855964140c15059000b01701d00000ea030341002d000000000d2a50000b40035882c410200981003680c0c0724151044500d0700d901e40c420175000054040105585449410361000305450000d0409040d8004120315029040000740512100c20f200801d100012885000401e0003c0000b507441c0f0108002138042c10b200086da4080110344108903060940110482060b02015402000c0390342d43c14141c0d42c2c028801402c0c482c148060b800010800c16082081c951013041e1801c60903800124515101d1144485480603e0464010000501a1100b030345518907449070100c0749140c0d03600d000310002c1e02c0c00300d425000344000786121455000d42c5410480202c40380c1a20b403110110103940300c480b90181e03c0707001141800502c803144d400091038000c2224030102e0740050101c80c07034591907000ca803e42c5000c60700743c1000314 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 600674568 1250 600673318 600673331
    0x807201e0d050f071d130c030602160611181203071b080d0819110a0507031b14060f04031b030302070c08031c090f0321110304020103050106030506090114060405060d 73
    0x2000702a185e95088002c68400c414041c0258807030f41c12401660000400940d000202446100e211250300044282c01c1034040200e11307114680ca0007243e204081103402c0f2400410384c6600c5280030004041c450100c0c0c80698640b404a503108001d40d002d4200300c211411448a000c2542c1d0b0b030800901c1c0c07105810761180d01850402c0c4c90030182c405001c04c132045c403460038240c0c00708402c2c1150301561001602d078140f032030720341101f85030a80e418907404214426484c0c2410107078050282a20b6060400b80c684d0060710b5441e1111010f0f9450b84500315070143c0441c040e43c070a0103820301c0840020a03240c0c064a00141001140d0b41d03012210340d415800040558004503042004006030440e080360420251000c0082d50b0103640c0740581e40d040c0010244c203000c0c074130700c0d50951003980d40303c0200300103220300c0c080100d00b03107404002c040da03041500c042c3c2c00a4500800030a4080c0640f1506004070801003495038540e10b4901c1d00400504410911908103005000000d09502d8903001742104d5101c200c1e002c0b808 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 600675818 1250 600674568 600674609
    0x4090201021c02031b010507090b16150609060519060f140310051002010b0d080706020405060408010e0c0a0e1503010e07080618071203080901090807201e0d050f07 72
    0x5e1060814000c06164504428002199002049036044a000d280c015884900801859102461030a0007030b100140060349019495a00c0d40803005a0780008001c00040e616107081c48040040c02e8013448441e44440c0c401d0247d00c2c011203030440015043e01d801d030000c5e07403414580368003500305807000501c200c0880c009108515015440c1300400740103200801426110600080d0300744590340380039007105e00010381c250600c80d00e50115800740030050840c5640350394030320490340207010202e03a1078514043c0e5040b085081c5400c44010b81155600002e418403601ea1005495054000d0030403258507640c2c0382c15401c01c0f10801d0024500a104100241000e8507200d0890000c50380844c00007002030300030040078044482e229101003003403a094500915150b1310120030038010000f42d400907110010208030002000060100c0001c801054442c2050300e1f4098800e01041e03510f815544503400b00111300090b064200101c081220f079000f03004030b070100d450022400d4141112500641c1c00104800200000e = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 600677068 1250 600675818 600675847
    0xa020c030111031911040b0c060103030912080a0305070c02030601120308060a08030f1305130b0111061005061309230906090d0309050a0209250e030c04090201021c0203 74
    0xa0150360b54041440e51800c1e102440d4101c2801501403801d9a0f2062415180c250890a450152003851140e5a990a02d0601035030340d604248412000507462400c003107400104004d00d91409607201c40322a00342040c0c00e03019000345c1030040113042045000c0c684800035a80400246000340f41c0b500005071480181d040c02024500b00414441c02481e404104200c0500c0000846000302250065035032903020381d00d0511002c3d20554041c039800300107508003107416511075000c210441b4090300c030030500c16110740825881d20422140c100c0c460801c44401c000c030b800d114004001001c5030900e1110319a890703015040840b151005005007a1041084503403c3c5ca00810019400c0b04508008000074074120911503a10107092030460101a11100100d080202c204003540407150f00405c500100e251010129018100340f880741c880c000c50303c0709980140fa000b50152a190392010340548400b822940500020f84098041207045100308440b12840080400d0407060bc4e1003242d002d15501c50103a52941c4 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 600678318 1250 600677068 600677081
    0x40b040f0204060212030c2a0109060b091303090302090a11040e01030302191709150a02010c0e0409020d020634060501061b03030e0f0f101a0604140f04020a020c0301 73
    0x8480b0035007001408000400582610155080e50316510380001c00300c23159a9014243e41d000c4a15503007410135410070481d0980101110ba41c084e00c200d50b8a03030b184035803880c00b0440850082c0100303034404410700150400c8001582e200c2c1c01c0141c040f40301100d07161808201c2d0310a41c000800148814014020154140442e0015503040203510480e008035846144420901c00f40c01c01c1c01c031000152400850302c4101030180c149003140801c5840e01c1001c900640a000c910710108006072015142c0f082c01e240c1803050060958020b002c04041640d00d60911441d6407103990150b04d1500c0d000500100710385134200014207012644244041891103240c010241d41e0103170808014445640c0d404c5200007100c40702a51640d416150225020308032803010350800301c0c801200c002d54090300742d40c4c3d0b04120001511a0f0100a07400d420082038540b05600504200c01300c09a13607205104100c10408051640b1000c820084c006240c0340804807480005812640160850b070050381141409502030f140038803506 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 600679568 1250 600678318 600678343
    0x30a0518100605030c060415110a080313020a0603050705160f0212150f0417070f0c0f031a1006052104210e150c010b06030f040c15050711040b040f02040602 69
    0x103505140c00d0000d403101002090008c1e000300301d2183c0c081c0d001d4000410144204541161840359641068603a071050b1000121040e80289a0010000b5a0a01c06c0c414503200301c86503070743c06050040040603684840d0281c3c034260740c0701d00b5000140015a40703030914544842000002080715512003841c61401e000014013822404804404000125008003180c1525249104d241a51642503181c03104500304850130280040c0f003030040204401100a4805003a00d014150510a00214403e07050305c8070411200c41e11020f030352900c10005240905c0182c1803a18440001d16038038030300000728a02c4050129010b454100140200410551005001015030802d518041020050000214a4a4502100d03040505030005003400d0144002c3d4046042c4c40d10081a0741e940742401d074141208104151000e41b0050081c0070300203815003c1c03002d20001071009403105401d105068880d201081c44084215800c15110390000d90103a88520030300716100c05003c001a01c035805d152009140c0648401a03 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 600680818 1250 600679568 600679579
    0x6020f0a0218061804150f06360f0203060f0102030307360806161b0602070c0803070c030b06010c0c12050c03060703020a0305060a0b030a0518100605030c 68
    0x8580260320340401d000c00740e20307840b40060070790f0f165500482d244c0c400d4030601381c049040e80420b1108010340d104070b0850040c0c03182c0c01401400044146841201c2c0c2510130141c00350303400240146010007104403074014500c214200204000714420003c20740715100c6000260550000800885e460a20350b406d107900c200707200850071850142000b9000d1b521921401c060805100154440e41c000c05001c4d4075203924406114011031341d44c503911030307843c10b0070340c0c000004c0040c0400e0400c4251040070907440100320410155180016910751800035848200c0039101200c1c82d0b50003066000c0b08000030082d141c801c254100e07206185040000314200c1c058482d42c10041c0c101500c40c0407030010807101055850034007843c0020307115440d101d880c1c040001c0718030741c041c090f5000300004242c0640c050102004a520700348a55030310758081140001081c06a0120700100f400400c04004076036100aa01c0540c400700d44222070b903c040041d14091020200401140c0c481c2070501241c00c0c24410035000d48401d980 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 600682068 1250 600680818 600680833
    0x905100519090b0711030409090b01030c0b120c0f091809150114120109061103090c0409210c080d06060e0301200a1416050d0c02030309100c0b010b0406020f 69
    0x1522070540001a01c140108410017800d2030b580d4500744111002041c1c108402c10101603a8945000001e50900c01520b420851640015061011004442c4424460101d040b83c80d40d403441400010340100d4441c0a82d4441444000307440d440f030000442041c45041803c071020f1511080c4170340781c11144400c0421200000c4010403400071001100003180d201100d000615400759200301d8010580484d001e45024206103804a0000110740154006c0c040481035800d4188054240000c1d00e04401000341b40b6452804071501da920b543e4129170440c00c103403078424400c1380c1c5034035010078540040e820280119903480041100581040d007031200030030107400a00400400c03440d0b05c640000e0700c1407c2508504005003144001e40f00c0c084c0010401000028180c1342e000501009401c83c0c1d060404403040d104400c1403084150107499480c0d03000c0d0380200110300d80507549046c860100090040b440c248200c1000c00d03400035402c0c030005806043c50b000500c1e01c0301c0c0b5000000703161054800c5070380e440742c00504 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 600683318 1250 600682068 600682073
    0x92301020c0f0310021206031203010b0711030a06050c0903010c110a0605091e1e0613060209010309061d070e0403020322050303180316050a031203090510051909 71
    0x58810510841202c0c203152421404020a00703202d01e01003150081403000400300f11982c903228106020b44002d41c200c81400300303124111007580c402809400e034040740901c1038000003003880308826200c1e44080c00340da04504465680300d090311410faa6010b04810007143d0079030282000d11445c4641000c1d890302100c0302c0040d08002ea00c1d00404500600307415150400586a03420420402446409008403441c00015100100c1d488420800a03540082d103000c0d8416180c11000034854003032900d103a080230040c041555440025400030745264141520382e1301200210361030b031161101c0381000082c0c14030340308030303c0c9646814800b154201901d161180410f01c4003199000059940c8980c0305040d980c40221a010030700c80c643d01c242d00843c0e0502c400200340c590f03a43c55280008042c2c0d401d800b29040c1d06880e9a0720a811130a9018440c0c010b405507808001044071450f60740d0011001d410300148a801e1600ea8500303003a0000209440d10740c45405102102d881080c0401c040b0841d041d04019003201603 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 600684568 1250 600683318 600683323
    0x403020f0904080910170c04050105090f040e030a230a080408030a0b0904240c0230071a0a0c051603140c150a060509040f0c0503070609230102 63
    0x4558640140d641c500041c041001d080221001850020502484150766181c010005e400380040a2299000040462400406281642c00340c6105868003800c00751448248094400c500412a50080d21108041d42003c0c05000920310084599180003401500700710460340a4200f4421340708141003001454265031344904451340250780004400e039641ca40340b40100c0902100d03e02d035907001c03105200340401c00c810440250748003400c4c600c05c00c00c012580c0d000c1f401240e014403496805078100d1b0103180c00d244d00180f01c03003007850301d400030101035001001c103e519503812458003103484000c40e001000e02c01e1801040c02e80d000560140602c00383e0030240f00205903001d040c0010701d215001121a808150091841c0d262a401c60056151034000c1d010146d90344110048d607400210034146c011921466040c001c61041d5540980380300340c20345031541d03424400f0b000000d080c3e9a5500f41d11003c515554140032034001807810f0341e03039064240e017070036000c4d4402c0c20140501e09200c0b0312080d0020b40c0b80d801 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 600685818 1250 600684568 600684589
    0x5060a0e12010b1e09090601240302131203090905040c030f0201120c0801061704170f2104020109050f03060a050726011502150c090a0806040606030b0c040302 70
    0x16285005040781c5032019034054043e404000341c0c032550000002400e00d140c0440001c800a00b1143c56603142c44e034007111610751b0003e004041c038045020000d050124001d1018110302c0032039180040c81c04007a914441d20301c010540004080c000402900d070185580800c2450140c001010100403505042d07550710441d50291100521a503803a01118040d68081c244040140c2d000700400c1c400031810b0a00100060024061580481c0800503600c00780e0300c4c100e1005214507804041c0010241c1000080c01c481d400942540d1000d090411127285241c0819680600902d034110381168282403500c0054a1074002da00898016510022034018581d4006050b58010000c4980024207850b2101d0807100200c0b00c45020b0303140302455020103210000c24400c14100e50408405250b070380c99022007262034007407081d0728641034889030000c203281510010041817581c10042c040b008481c1d54454041c1042011101541c1e41d81d41c0702000c10620240c241c10030b82c8901c1e180002c514041c02c5030300040319070f40f1 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 600687068 1250 600685818 600685847
    0x31a090f06011505040918060609020f180a03080d0c080a020f120402030304090920011e0e0a1205010e010c030b030a0f02040f050f070e040612080919060207030c05060a 74
    0x101401e0501414010070898000e011400c00601042180f908005d10051800708203c448c42e117004d0000524000c0c601c00c2c1d43c051006607035902d04c5c101052064420188801040d01e52000c620070002000660300001400340c1c0b5001c000c0130070440000e600181c0810002090088602d00401220150304a008101d4210641c0c1d00c6c02c48420341c60b00d0011924600503a081240e11a00e810542c0e0180a0003480309484882029580d0307464540c40b03001118286a062183c124414900c0c044010050281c8041410400003070100c14696a4a100f0f0107500142c08406803826595040d0002c3c40d03400038000c0a0324040141410300006080c580030a84e150140c1c1000340445200310303010411035640e034002c0b000b141e085071000c0c0700504040100c18243c02c1e05880c104041007150805450600b4113004842c02c1300c6400c007986031100300daa04d071224594011042180e0200320300388410f0307840c80c6088145024104c0c55008104441c114645020022195000540314030002d0001111507503001200b42c6c1c01d0300 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 600688318 1250 600687068 600687089
    0x15090b0307030b060c01020915121b2b152301030e0102210f09070509070e0909160f08070501050a0207031709040605090f0403050f0403020406031a090f0601 69
    0x1941d8000071002060300408890740040001002600c1000540140481c0703081261141c060085080b049806480b07000340c5607181602800014600080b400c40251501720505102071920f09852106a00080c800380d0b913074080041c101410803000190320542ca6101d000485040b00582003000c0c0b50003200c000084040442107034041106982d2280e04115524a0108000e54555501281c5002d8555400071680042d07203000c40000c0c051041c0349000d6000e50408800703803102e142072506020311810f005081e03030180001c000c10400c964488021041c4030309a140d001d08151240841101c0e009440c43d40f14410104079a1003d0200c068049214021a2000d0038a550740e02c0c4050303402c1c0d007488030590016000c0341e0007805007a03000c100400180141042241d0801082e80c03941c0c10082d964074260341d2089480e500c2c5001400003405440244281c481d84c0e250a801d15650368005419241e1980049802c82e811480c40b0782100000c5c10300603001a282c1002d00080d104062240e66110814882c2c02400d1 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 600689568 1250 600688318 600688321
    0x110c01020f0318060603250f03210c03093c0f271d16060e01050f1615060303030e060705040302030a030c0c0e0a05150103061805180703140715090b03 66
    0xc07c07945000b01c0050050341072005401d5601d082201809031021f8a10306825401650030241900c10508045544e44c10b80320140e406080408080d8004858000700000740c8134003d5412030044582600c400c810100340500e11500d0400d0349504900615034000740000700c005c0d000d48140f03072900184d40351b91014064005414038240200320550b00c03800c0d40b002e07864003500306100550300340040488180c03600c80d102c4004a0740c14000449241c891618290b4404606214110a940c0b0742c142c0400700f207008000540a610040b003c0c0b2046030000d510480c04641d440f402480721080c148180d603401685d0781400303400c0c1445c54000c01e4458001c01c600408100440b801001005030040343c400280540c0004001c8518140713600500504069891070741b0f08010498041c465032003401281c05a42c00d01c4d074074490407580c0d481d140d0050100a040c1d1000c150312502d904011401c10818600114015000f03001c1003040883c4650510a49400c480855400b0303107080200e0301c0e00541002c0480d08504415940d9 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 600690818 1250 600689568 600689623
    0x61403060406030602031608060d080304140c030111040f0b070503030708070c050303040f021206100510030f09121404050612041a0708010f061b06110c01020f0318060603 75
    0x4265a030001400184044144a8101da408410700410001c42d12008c8854a861042100e02002c0010040840744100006400940a51046030348607040070100c600010f0b0f4400000d0940741b000c0300d41c001c1008041001c2010941023414000141102c60b0018a80805c80c0c50385922484003d00480070b1101d5a008500440d208a8160b0103154008043c2d1340c5074240340c640741d48480c485e42000d03442000c2116200040080200c1d640b070007140d1030b99001c045940307440c0038480f05180307841d481005e05946011034402e81e1749034000c0c00001da1207102c1c05607010502120240811214411810351131405000c00d00c9a610348404454800c6031001d2101a00c2d95036141101d044e00c6014012070400e80b020040c8014960082e148605a8030b40000d840c83c2c2d9911442d084920f892210700301000580b1200800f07002c504194003800000d02c20482591a180d660800c090980e80400c1e807140d4201c100008109036109a81da50b000f0300040d44014140c58103000d0000303503030741750900107059807000060f0524a2 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 600692068 1250 600690818 600690821
    0x1c1e061e0b0604033216060e0a05011b0c030b010510090b030a0f020f07031e0e03070b0a1404080a1a0106120b0604050d14070e01030305040b130e240a0614030604 71
    0x61108440340d000d80f1480d100c1d01190b110540003c04507071030040301c1804921f180c09030344088045040a42005010344c9401f0046032032980501c0300c40110400010030710b0200f14000b101c04081d5001da600442903501d01801d20111902e9a14060100084904d043c40120780c0101140c1d040031409001203880b504840f07851000340710b881215188241c00040001c1016041050b10150082000c000b19540f01d000341d06681d202200036880b80d0580151000b03204407100100136103505280f40c60904034604075041d00001b1507200b504800c0350fa5008907030f00000c01058054904080c1e458540b02c4040e075140c0203001c1d00907940b50030401c241c161640910003880c0c46100a6400074803000300380b03c850060314106600d0103030041207840d61a01940e0804180807080103103a504880d415a122440c040c07421311031040c10b40000000203035405c500030340012602080c40d40b840c05254000d41c0203c1028546900d0000310446131314060260111300410041a034200b400c0952082d0400440317950381d0388910002e0b0 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 600693318 1250 600692068 600692123
    0x1716060b01120c08060a0b1312050111040305061519210503030a0b1f08060616051c11010c0509061803060f04120503061c1e061e0b060403 61
    0x2456603e0000540386043e03008001c24007407203041e0341804009132100c841c0462449052007400c4400c0c1e241e1810040c502041141c944050701500c000540d0a40c01c5820000c1a031041d8402c0d02c05a000600707010140400d044031030003556040f104106020a80c0403011400e40a0f84524010308544c0000300c0881e61a901640d5400b99101098964030301d000284103008101d150340d014060540c80340d080e26581000740000d01030031903a071034858183d510a0704200850707014100039010340a12004c6500010010002207150309025146040c110084110052040c40329040c0c95800382c0c1407408090b00e041d0454100c50401d0015640e041c0d44c0d44040160071182c10705803c04903010700c075a9080105140c001e045050246200300301500f403600742c1c48000c54203400207461a6070300030404c200301c100303070792151b030f010500240308159032240000380c0743d10041c444c0b003407040560395942c0303444c0c0004220b503c0201d038000120722503074100034001c601c2d404603070789000d14000241201d006049000c801050041c0b001e = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 600694568 1250 600693318 600693347
    0x7030c0c12050c071d16050c010608011a100827060f090c0901081b040e0109030e100c11062d0a02160e0406050c1c05041716060b01 58
    0xc80031641800700501c6a4440b60716265a4010002c011641c120050020316400860801c03030403003038480d000c142d80310007103181c05c08080c03080400172422002c8081c0542001000428000212a803007219511040c0d007115001900c2060004440e00e4000d81000e515134001c4d02c070a0f1603c05031080040305101040c2195104801031169204122090311004100c070f02c940c01a0080c0d40c140000d82040c841104020300610a0540012008100b0740a10500295126000a0012404a01d6088803600b12841d8982c1500010201000b05070b01d0b080403030000003884118500340daa5203c50b6114a01c010340720b01025841040001071894130302003001d45107a046041d5212280b0295041c83c042d01c1c42c0e51000341c2001c058000c0d01c1c02048101c4182900c102101c08820f45403c517940d503503483c5002000c006000b004200d00601148000031b112031414100388080fa4070000380c60a10b410160502022607402d000b181804008a031805150f4100001405600020100300101ca00c40140c41070b04030940c00 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 600695818 1250 600694568 600694583
    0x303031b160605010f06140f0a1e020c0a0e090307030c1b08030d0c1704121404090b03061833040f061a0a150504050a090e0d0305040b07030c0c 63
    0x3103200b40304269110a04075010b00d035030000003580d601e200707544a4009001c1c0c00001c9200b071201c40d902c4101c10000b0300c90030416143c00310041c0390800307000407545031002040005a10481c0300201c94240f04180384050880064000e04030303e0301c0c000d030903075030b101d4200d000b010444002444c0040082c485400240b400c605d00023141c1c000d80300d848503590394100034007105149092207882402180128039503e400918159029071540e52602c0361100814255182e0b810060400b400112941c02c96000e40040d0000c200081244100c0c00105031071710b4005404031405070f8666103200a51100040c11402e803211807001c1d0503501c101901980924602c800c400c001c00070b1303207070100005c00c9040704001d00094800c1604104903405c041000784840340c0c140c2008d40103030356400c007440000803d04d43c00000011500d0464501516480400c010320103d6002210b100e0300e0b8440c0c001c03d240309014036110b207c0c49d403604002c28907145d141e101e164203001e4801c1c000d250f03a910049503a2480b9444100380180c10810 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 600697068 1250 600695818 600695857
    0x1014150609060c010e06070f0905010f0507050105070305010f1a0a141b06061c03021f0b04060803070201020c030307030c06050c07020402070c0302030d110303040615150c02100503060303031b 84
    0x40e0113028114507190105903010b01000600c0450186426241221840c2e40b0068103030708000c019a6900e0300c144826091100900c05180010024042c0d0351040c003940c6d90106a5501d4880209509200c41d08040000300c6419131018801c0303c80f0068443d100e005250895801d514420070fa42c152241807000c08058425450440d841c4000043c40da0164000343c8295031610443c4d00c8800036444c040b80e00500582140020300d604920850f4400314850940c000000c40c1030782580003904907007066000d03d0031600b000c1080019580c06011100000700158041c500e07020659400410429513424018216540e450114444003914416692119030241c011943d40601d4140142d4490070782c40101d02c03030b00c1211401c0780b10502ca066400b484128100042d07007161242d6488001501e80782c920281ca101c020307180040c16101d004050311485403561100500d01c0c8050042c41881c110034000340050007000c00a000050b00c0c004202ca078410b03201c05960314000e8205408509900c01d40000700300e203a20149 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 600698318 1250 600697068 600697087
    0x90f010309050d090501090f080c040c09360b15340b1014061b1c0206010608240103060b0d0e101401030b100305070f050102101415060906 61
    0x40d41d00c07d0300c64141c0c0315514030854440f150240118081500001081241c41c203150300070448004443c10841007179519255194210801ea400b11610401001045808044500a0300e02c0f50103124609100e891000700c04140424290308035880c2140e000a070316015001c03500c0c1c2041003544001400702c20014a1104401f100615000988025401ea0082061481c00740c010800719500500c2e0700881e03001c4001008a40e81000d64000d4866400c00541c006441c01408448600c01c290065540e0041000e28000c2c60020141c0048091110250901c080d4400b01242c3caa1499078000c031034855401c003040100c0140c030039079104201c204000308556619a90307a40008004c0c141170012a540380007104c84a200f0b6503035080b990f02008514130018408200c4086040781e05c04550038801081c2da56030344d1107602d4654141d00c281d182c4000c0320420f010960b414841c86801e105001d070180b180100c2c450588101c0c1c4005401c1e00a0f418401c0d06151240d01c0340e00075500b202d2002040c0c0340d1160b0001 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 600699568 1250 600698318 600698327
    0x9070f06081e1b09130c050703020f120904020a020115090b030f06010308030c07210503010905010b0307090b031f0305010c0201050f01080604120c020409051b0604030305090f010309050d 82
    0x741c52103160011601003074030b0010061081c50384940510980e2001c1c500c41414a80e0150b40404645500903000101240e15881d4900900100c000180d845a69600c450b040080c00c2c86030312965502250004282c40d9004041501986e5400e4411200180c0d6400240c01c16401409001801e800c2c243c0050f00005e003152150780814460300c410740c20786a001001034a4103031281424040100020300500c0414000c01b1a040940600303441201d0070381d008201e4002c84003090780c5040d410000580c002006001300e512a0241c0703070040c00d9403103006045080454000c2c10340c1c600d03401000d070401008800100d801080440400286030020000503103a034a07401c009010340b0381d2820301d402646c01e05010415452017040b0f0281204c0c0c000b4082c184540303403030766690001070383c0e591000b007008400102540540c3d0782d4860605864440d030000c0c000e070400f8498049000b00400e60040c460b80046c0001c00210b6000707002c0b18a040c0302120b9400000d0b1404005038006d046038080a007545c440d101030142020f401 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 600700818 1250 600699568 600699571
    0x9100c0201020d09060503011a07080412050705150307110118060f1407120f020d050a020901140a0e1c080301031a010504060303170a0902060a03020414040204080604030809070f0608 80
    0x7030b030a0324640030000400b0703561100c0c0b62041400145080004000488902c02176203450310304030819030325010381a29003604a41107074010319029100d00c0045000c1041c20452900284415180c0700d94090032001560140c2c00b00510500038400701c5e0110481d4100203502c4a0f2408040c000d840058031818100750000388291720000c004946844104400a00482d0302c01e413144080c1e9480318a0130352a5002e000141542054801106800740481a051005030240620600d1140001030722440344200042903045d0050b02d00c03001c09001c00c00c092500d580802d0342c14048005403200c0040d0084441c0f0358030812036924016000c42000300002c82000701806020020399404000c0900303903600c0b0420007003110810302c0000e0120744c0343e000700b880707002205503410b6201d2002c44001661800a4010031080d0340960b04000010f9030000e0103001ca02404c4150170b0880d4001e640444c2400c0c104142c6941d146c07005032000d400c2c03204420019404c04000c000a4020b445210042101d09a5460000d07211880 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 600702068 1250 600700818 600700823
    0x123013203150315390f2104020105030c13030204090302060108070b16061107150f0f060e152821050d030b13020712030506061315030209100c 63
    0xc2c00c01681e190180f0702c00c040c0c00781c000030110b40d20200c2280c800308807100c07601c284591404690300100124008803005401d5441d00b0403501c640e1000080d02070b6241d004440041047c1c61006024080544d070301c08262584140500315403992070104070403a20102c00c00f0350000354040c1c02d0003001004c242c1e01140c61812540c1f4075086528190711403800c00382d64004c00200d081008810320309440070480c9500500420086994100d2030b008454071009801c42904214051154a0300c410520542c000d224904441072207801c200710b81404d00e0040a200200a03080c1e12820002504c030fa0f6160392500c1508161b40300143d905200c88181c6140d81c003110a241c41245c800c1c2e42c0f4820007410150403804100b08641d07001c00034203949007458805034000c0a100ea1040d4114405400040f6080510b100600700540a01c051807aa100080c8008090f130780001d24290045105100c3c0e501c070488500c0a120540b01c0042803010310440100d0101c000b03000380a001640300d08070344c1034500ca50b030308014150010b50 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 600703318 1250 600702068 600702073
    0x180301141303180e070207030b0c0406170a1401080a050705060a0c030f050c0304030303050610020a050d032a05310b030405030c06010e01230132031503 67
    0x60901811110010048a50040c140420305690300024443d4540c140d6100c82907540b4820603440e94a082e0721050200c80a1001d64404c80c41401400505070030140d000c001d800e1014605420801c00509003801003081010f0b408078140413410410042e00001002132000e01184503e6a403032101079503a20800c4011b80b210f009265000ca6542401c4c02114101c0c0f0302a2282c5900e103c0c0b03a50211040d420607640e080c200413080c03004180c682e0050004000450081e0380104190401748108140303111880403100941d40f25001020011341c011a43c0828113003e810001140189120049000e02d151242c42c0105501d0001c4040c00301e8010010303140410b05015580d80131429000900742007482143c8000400b0280001000450044c1c401160302502c10001d890506d46040141490100c0a81054000d800000010320031030700c1c401e500d0352000601e8041d030080003c044c000a030101c000a4005103400c58820f00111420920422621481480c104c0417a0740b4500121038a44108840d41443e20a0 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 600704568 1250 600703318 600703331
    0x5040c0e06010203070c121a0a0e010e0715112503120e03060c0c030909100816060f080606120411120307050d05160f030203070b1e0a0c0c0503180301 66
    0x154400410b0324440350340301c1c024440d1b907030400c0f286450403100c8083c21224075041c0321a1b0b184240121100500800301c1350310125180d00804811800e60340085854611030b44540000c00c400b800c20031500100715000e082140b2044070030210503081482400c2981c18075842840250080034181a40358100c4e030040e0b4003d90840b4a00004991350008604080e40c99808840442c03180b204400007050015092001c5030b01c1c0070040000301b008035030100c0700002c58401e4208100b080320b43c18054208140421070a98101d10700b001c3c000340810070038940c21010803940800007040340d1542000ca81100000c02c114401030303d018600142c00b107402c524260b000d5044c81088022180c800405d5540b00c80d880740c0507011600d44007904661540240c110701c440140900c0b40200490480c20b5040007540c013039405155548071605019070750240252a81c40304002184500301d110b03944e1010180c0210380500041802c3c1c0c05184100ca8182c0d65103405442070200185a032000c02c4168403503004000258002d0110 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 600705818 1250 600704568 600704581
    0x90b071506080a0c15020a0c08060901060b03071d0105070b160905030c13110403020d0b01081216110102031e03100e040c09091703071808010e070501140d05040c0e 72
    0x124840f2460042800510142c20701c40c03918410140b80014020348100c4400022946030850366540036402a17510360091028024083c6003030103444040c160b007610f81d6140d03043c0408014803016030184005e01608541d0b4000c4020380c41902103544007904051075440d9402c14661040b001c9044803201e03404110410400285030402003040c1040110040c00703080b800d50000c0e421409082d0301041e2184c4900c08001c0840142d44114481082c9401132820b40749560501207400e1420002004204044900b031020b12407503500008a40580f5504c440c1412a61003881d00503865401404141c00d1030482035909401503803810406544031b04503803103091441554618502030346250541c0c0c0074000b40e0244a040c0703d10006500020010780c407890103590b2040100000c00460b400590f125000620031010700c66a10780c0454441c409004543c0c0200494a51340c0070195a0300c2040c4615414402c0141110451414401c141c9891700031408044c002840d05182c961517841d030601441c004c000740e1034081802c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 600707068 1250 600705818 600705823
    0x13170703171015050c0703020409030507111905042c010b0f15040b030c0f121f0602030406030b01050d0c080115020c01020a2d030e0f0103180f03090b07150608 70
    0x1100c5019141c03410000b90001c00301c031380c1d600c8840200840e1051000c0000141c64501c1003403821800707640c8490311600185800d00020b800c01c4c0070140704104e620015041640500e81d0a011200200c40016405140c2e00b0300000000c126810312442121321048001c040a064100c04109881201d140807050441410840903180820030707501130120900041c030201300f40c0c0000315040090802d040c2e051103041500381c580c45c3e00640c0e519844613540c0f414003c1811038007049105100c02c0c0116280780d0b504201009589c2d0140b03109101c100364451480400c9a4041c008a4840c400e548000b404001b400c988080d214610a2003182c40b0413041c948009081740c808561241c10040c16400740c50b006100e615034041c14008601a040c0c004100b42d2507685519a008418000d070703200752950302661004a0400c034010036000e80490615040480c4240320421491260413501e510050844103500d4500b0204c5056481d6000b54200680004140c1c0a004200d0640c44405104503010f001858603184400d8 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 600708318 1250 600707068 600707101
    0x102030a0f1512080d020703051b0c030d03110702030a060209090906160c0303140a061401020a11060d0e0604060b09010906030f0311211b151317070317 67
    0x5a00c928190420f001581e440d881d000612405031000b02d04003141c454105040342d208070000c902007000007640b843c0e02c0111940b0302c3c000313112078805445032003960700c0030a49881900320307100c08250b0741750190054148802c0c10344000580140888910302000d01c0c000d0029402b083c440340c0b00e45241300010303841140000341644560341034454444044034400007a1901da0480104405160700c4414900408011401c882e10900342c0000115580d0300d00f4008281d00c200c611400c504541282d44c450003c81c09030890144814030548589030b42d6118808400d009020b90300341c4510b640500e034180400c3c45080e802c030401c0b0680880386800c4c9070342c1c2d90a5400498680b4031004061401d0101d01001003070284000482544d65a4103031810205030344404640e880302e2108540004030003140e455600102081c2d00f41402000c05c0c010104640c00801d03012001c1c400800c2c198000881968920402c040102c210f8100e24001003a80d40780c107400e10b8003920f4490b041040f4480c2d00030f2000090300e440d15900900 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 600709568 1250 600708318 600708341
    0xd0b011202520501181a0c0301080312060d17030f01090c0801090b0a17070801060b032a040905100509071706010c050c0303070b071805010509010f030b120102030a0f 73
    0xb1441c500c1840120708111007018000e58107556a113040c0e0564840d541c5801c07152a00c5814803007509440300541c0010044040c1070407c040d802800140038064001088410b2401044104006580c800707001880200c00450000c20803000460b03030a00481d0003d0145006210003080110541c4e01c032110101165940643c0c000060120001000358261590001c41351140143c0b04044a030b4413043c40d4a43c0704030b004202685540210006c00c45c8050030301c04c50028044541d100e03482c50504450304164513680d808a110340040c189001d0b440840340c1d0084400500c590401800a49011100304101c0600361041c14003c06602c4001411544100052848555541d010a10b2501d8410046400c00ca500313204594a115030540d00c0c075544d41c00c00260522610401030340c0c03180d00d003010300180a0f01c1c03e03011072240f811410704140450b80c0c024003078451218007032a0030244441011802c0707000d404104080da4100000c0f181c1c0050100040d00110b100303508600e010302c415924002100115844150705 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 600710818 1250 600709568 600709687
    0x91c0207180e0109030905010e0607020a03030e0102100f02040311030a0b01350102070201030b011b0330060602010b0f060301050f121b0307060c0302030d0b011202 72
    0x81c07024503036103100d00e0403901a9060000301c6024020b0b4803421100c42607400c1d004540091010030156900c41e04c90503191005540082c00c14449501042800c403540c04009c044c0b200050388401a80d100b041103d409c440b001005000d6441304015100c025809400160340019004014020310700300054001c18255000d205081943c1c07030595010b0465801640c007601200008803000004180314601d8400000074800041e0f5070300b8644000f504032800f1028203810b010381c00c1c07112519000020082196581c250600705102c4500381c01380015941004800146500c0c5d0a4089110429660203441955401e4008002481010303080040140404131203561000d01080180014100009020340c0141c5c040d00c5150344040701c89116042803405003402459540100c000c28031445d0400100005000380d0420010000700c40d10025103911840c40c2c0c0b82d03c81074498250f490180d102d00c0c0f40d01100c0074100c100f1500c5a0403100b15101f8142220303105031102c00d034200f80380b01d042c80e81024501124550402e = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 600712068 1250 600710818 600710833
    0xf0303140307022a040c021608070b0a031a090408030a060e0c0406141e1206180a090f080310090501080f0c191a1b011a1203041d091c02 60
    0x403001d01d21030150000081c040001104644141c17600d01507201001c903a03401400340f01c0d5111030650b041c44400c0d4003403c5107500c012001c100c0603040710100e6603d10550b25005c19602209800034507030350401114650010300c08010001071000c04006540604001c540a11400340e42d00c0c4180c05088040c0c0e8120310001040000f044441d0059078214041c0c10224001414010145480810355a20800ba8070001d40000390034a10041811460b550200040b80c0784c0b9002d01d409070006144010040c05448103603624440103091140c0c100c040c228059011030030030381c1c82c03a1914400c1c0c5000b489120b102c0c0c0450030203001203183c0e0004950b10340c03a00c078050014440c00d4a58420402d00984a840c0702c15440036094000ca1440003e40512000d100d0780b5103040c1d5621180555481200c15006c0e001c88903914202d10940702d814542d61119040c042206e1a80107207141c640c5603070544c071a0754412082960f4041a0925200b80c3d0100346200b035045000751286001c5960104c0428002902c1241c0180c11000c0c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 600713318 1250 600712068 600712093
    0xf09060103020a150c1203020403021c0c0504022803150e06060702091e0106020a03090b090108040b06060906070606170a03050a031104120f0203070f1a030601030908040f030314030702 81
    0x120380013014990352900403c3c0c04e50750307100c1c0d5011807800300400c00000e8000400f4800c2d401c1052005140c6100140e020b050348042d03440d1401503225500546218980001c1c4540030800d24100e03000c80940040d1115407010399560001e8018a0a904c6061810b10400000220304519150040c441c0c2005024149441400d81c200510646d00030312040d0840c0483c80e60f11418241c1c01262806041036800600c0c50214506018050b049103501205d0365800c10000551140d0b88140c907140c0042e80420b0114080d22060000b590b90302a410b4150b40020002c503059040c0207954110400703e9003018401c0d000c0d20006103c440c0c031204805005004200f0030009100310521a502a00d0a01500e454590403d900c81007400e114501b0760740c00750b4105010704202c82c154034040c00740700010f0003040b40100409181840901e1581d4110510b40808803000c000209940d000780c0280e485c0e00d6014140075500d40d15407400050108160000740d0000d254203000b0394101c030001c800c40c0d01540f8a90010102c00c038020 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 600714568 1250 600713318 600713339
    0xe0f0105070b09030c06040c06020111162003100506130209091306060512010203040c050118091806050c0d0e0a08090d020d120249260f09060103020a 66
    0x80c09003c3c1d944401c100d0031010007010302480b40500c0c0300b0a60584a280741410090a42d0000b003070030501d0540c03c004041c41051861052100b190744480403080b0514400540380c80d0401558003070742c050103034280140c0302009a13440903101ea02c080354640d034105031052500c001ca01400b0105600207141d20041200455081812990541b2409020910359203a40100384d55020445d40d010960b0b4010041c007080003c2c00c1c8058014010030700c0c20042590700b119480c10f41e00103d200b2441c005a403855820401e24190030303046601034000c0414429801d02c600e92040d15448070941d00b0525141a4041c0c0e40040041a6200c0c055000038035241418449001c0154500d0980400c81c0e001c10311500643c00180c425880d200c44061a030094080484601580c0d80c8540b61500c00701d0702c20300920808840003200d40d400600a40030080c5030130031404541802c0e1807068143d00c00040402c0804508a00c050700c100790300f44164404e0000790301c10f494070020140e48850a01000b9400b088500041c08814041c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 600715818 1250 600714568 600714571
    0x1d0a021201021c050a050601020f100c020304170d090f0311040b01030b03010509010c110a0206190c1401060303120221220605011508090d030b01090306020a0801060e0f0105070b 78
    0x3000180740001c00096081241c05401080c080c3c65150720821150810500c142507010b0001e0018010044512000903100c00501d55480115655402c0700d641a80c42041510b010300151005480c2d8140f01a0800d41e546c007401007140f0005518a07004520360080528540480b544000032951110410003000040c0000040a80c10150340d008200c0e03030342d030b0309026090140031400d0001445004001004002d07200c91041d500d0740e0b174000510b80005858107400c0f1500d600040305100c40200d41303d201100c0300c0f00c903400c02520a901e0040d580d0404101940540110b074402d890344a455010807010b072050703001c0d85180711070151018440b240303003c18100340309900c4165031203001080c2128000081d090f0652941c15a026540d850050105800010394190302848509000070180b4140e15030b19503401090000408042c0c58003180311442c0d002d4900c14020b036610150640d15640740c1040103100368070034420100002c030000f482c0c00290404c203588907000701c01a502c0901c1c2240507151404140c50 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 600717068 1250 600715818 600715849
    0xf04031104110a0806090109140a0213030506040614071e081f03150e01090506131b030b150a0f140a0509010f0303020c010503070f12060306050903040303031d0a02 72
    0x44072110000c41c2000000240400c01954913008580d0400383c00740070350110142c1140d64154074000c5c403000091021115558001d100c2c260150356000d0360401c40058000e19170005040388282c10074081000309030381095156541306141100c0ca0b86d1003040072030700b100812010032175802402e0220300c0660711605202da8040420305550440010406c606000c00c0b98503881680c03841d0403014140440030440c0182c210a0031120028802c141c0103803034064a502002d0b1a030301c81d0400c507604001c10001e0390703621800c45c0d0000c404080d0619559040010910104071040b5603e141070408510141c5461100e0314140d4403a920b10060301070078540320607907551002d0802c1d60301650600380080c8950300c40d1102800391109400340749000d0309e54500646085030300300c0340c2d9040c01428000c000646600594428030612103141003001a00f040008070018030183c0c2010300814282000c011183d80300100500803203100355010000c1d0349130340068100c5100c0603001c43c40035400042c1c050015183c087c0d050801d40c11b = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 600718318 1250 600717068 600717071
    0x30903020705100f230405120c0607110319050d030f090503162006030a0f0e0f0105090c0102030c07091113060c031106100e0910090c1a0f04031104 65
    0x3a1180000b5515150718020040001c0300012094103869010b000c45681700f02e400068881c4007041540c5410301e008034040c4500408044120441c04c4100b002144054400500425540c1056040c00000d00d4050301000b0300a200f1081d40380010305220082040c600d41141c0545041074698104502078860400c400340600d495a0000020840a100804034041040c0e2203040300303525840d05926818030003410034000300d986801c0d030a07142c4035807040300e0740665010710024124008461180040c6031009a4841c20f00c200d50704400440c2d01584041c0c000c50020080b9030080a00f00c00480c0c2d64446d603e240f6840e07401084042040c811a40c00c10310312002c40280140c103040407410440c40c164003580c0080c0001d10f02c264000103044e000f040004800c1d224101070961490003c0c1990381d070410b00e205000300024460002040310206000c07082140281841c01d203c4003000307081895040c020350141c90824a11402c2000f13130407881504459200c1030798008c01341001e140da11078059940c1040410381e00103 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 600719424 1106 600718318 600718333
    0xd06051c061107080c0c1311070609030e091e0a020406080708040c08031305040f0605030a240f0f0b0102010e100504020f030316121e03090302 63
    0x55048007021903004802205605184509075000d010960041500c00c480c5001080e1124110b02c100c1e1141d480343d682c001d00d40700302c4180c90094040c0b03a01c100a9140001c026800c542003490180c01e101c4403003102140071070304100d01103800b40d550002e807007080c468101c048000540c000100040441c1000e00313000020340381c100d0140446090141d0640018200a203482c100c401814a030400d4039111070030b224000c1c210015600850340700d24207198944603da4218850303d0100c0d000203008005668464440200007410101801d04000316002d00039040e000c0e43c0210700b114010903100040104000c140402221542c0398032030304690504021049141c4002548510b4880c0b041002034940c40b03510000c2d003080480000c103501800042150300704020500901020035020310b08121040061000480303400c101c001c8a603d09980a4a1103003595105c3e0b44031b90a080d10a00403941c80 = true := by decide +kernel

theorem cover : BRFrame.Cov 600539568 600719424 := by
  have h0 := BRFrame.cov_init 600539568
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600539568 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600539568 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600539568 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600539568 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600539568 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600539568 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600539568 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600539568 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600539568 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600539568 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600539568 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600539568 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600539568 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600539568 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600539568 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600539568 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600539568 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600539568 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600539568 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600539568 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600539568 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600539568 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600539568 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600539568 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600539568 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600539568 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600539568 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600539568 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600539568 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600539568 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600539568 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600539568 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600539568 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600539568 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600539568 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600539568 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600539568 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600539568 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600539568 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600539568 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600539568 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600539568 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600539568 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600539568 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600539568 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600539568 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600539568 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600539568 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600539568 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600539568 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600539568 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600539568 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600539568 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600539568 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600539568 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600539568 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600539568 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600539568 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600539568 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600539568 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600539568 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600539568 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600539568 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600539568 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600539568 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600539568 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600539568 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600539568 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600539568 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600539568 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600539568 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600539568 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600539568 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600539568 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600539568 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600539568 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600539568 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600539568 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600539568 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600539568 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600539568 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600539568 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600539568 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600539568 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600539568 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600539568 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600539568 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600539568 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600539568 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600539568 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600539568 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600539568 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600539568 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600539568 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600539568 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600539568 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600539568 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600539568 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600539568 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600539568 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600539568 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600539568 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600539568 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600539568 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600539568 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600539568 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600539568 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600539568 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600539568 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600539568 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600539568 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600539568 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600539568 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600539568 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600539568 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600539568 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600539568 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600539568 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600539568 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600539568 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600539568 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600539568 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600539568 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600539568 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600539568 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600539568 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600539568 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600539568 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600539568 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600539568 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600539568 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600539568 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600539568 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600539568 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600539568 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600539568 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600539568 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600539568 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600539568 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600539568 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600539568 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600539568 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600539568 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600539568 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 600539568 ≤ n) (h2 : n < 600719424) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
