-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5100
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:44:54.190868+00:00
-- url     : https://prove2.me/submissions/d6fc1e43-6add-48e5-880a-fb587acc7cb0

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 917086330 ≤ n < 917266187 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 917087580 1250 917086330 917086333
    0x30c03010c170c0417010b13140a0e070f171612080c030d11090907051303111810030308090a0209010b0a020a0c180b0f0307150c061506021509 63
    0x15200340e00400b0301d401d50160b80400a030382800e442d0080f540040c0c4450f80068402c0e07654203c8204545080017038400c03403450801c401d004060016003c1c80d10703103c1c064441803503192030720700c064003032402448030202911511880a010a07625032411001d10781880135110107004111a04e900c524002c03040d001915a82a20780240310070135500e01c49560b00560190b90140030622401103030121600a14181ca400c00c101d064980c800d110800c20001c0c40078210a043c480b08004c0c82d050401314071a00b0701220740000c8500321040c22007001c644100c0c443c622403460501d0080402010000721100003090320301983e11401d503548d84c001d03080e698541102d0013035886015540108080105030000f0a072420395032064410881c090703520303e224203641d030300140c80f00364a02444980d081101d10802641a504030b981c10340403400000801d480d00c0450007010340d65001103d511400501440c161031a56030720460070426104803d242c101a18914024500107008082032030400f280c904d000d0f24001c006a90 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 917088830 1250 917087580 917087597
    0x301020a05070b07020a0512040e1e0106050f0405090c040807090e1b010c141b040b060a0c17071209050607020f0910050414010602011b0206040f03141305030c03010c 73
    0x300e8400e0f00090041c890703400c5200d5000c05500080084c4818000311200081c032944460428a50f00d00e4241c00030a000f046c0f0390041010303082900c5541403941111003c0c200186e640c007503038018007141d2003640c0110390005c2041007070248840c044001042111000340682c0d142503211030150b0142c2e0700f074280e0030507154000b40540d0016882180c24146003501414004401b0750303c2e035039207010310144521100c6150406004841c1c80c0c006208030440e05042184c0030000c1c80003020000b4400d0040c1400c85041180b8860703d9020051042d041c1a40700441c50700c034076140d0420b45001c401510013602801c00143c500580041c013410300e00d06503018690300070428492403a20b40c051003450300c2c00074030860f10866401d100254544a034414100500c0302002912803d40c107200003c1e0940707149401482c440c1600b2101e402a480c0c0c04602c82d90050b9002d6003207a120181401c0803240e4501c58402e0b00c54090b0005844203a04400303051003021030390260140c460007000709082601700d6000042c3d00c0040355084 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 917090080 1250 917088830 917088833
    0x6150d0c030809041409100606031808031005120d020111180904030509040c0201020c01060f0503070612151806170a06051b160b0c0325030e24060301020a0507 70
    0x20140c281c00f24003803c0000c16841840788a40c040c0c070255000d60b1680c201c420526104442070207002e0150001c2d050900c20201c4d080741c0b0000e40503200130090728034070002c40810524840c0010210090000518882080100d00c04164944403040e9100e00550b04e8070100011050b0404c0503940070702d00141c1120100c409400c2804542c420082048040041c1000180e01603038a40c400c88400520399400186c031040781450503801c59441e81c000c40c010344560601006a070750700041802c00c0d21071528000e913491256100c0c0002410051240f075110348030200001c2000c0b4030307002c040503c60050704024000190394901c0814a40c902003d0047c998104150010200d82c030354101e9604880090502201d003008246085080e4000c400031041c01d01c01d00c121401445004000e060f0810380b0340c82100e255040844120450480481d01080b2503401c1d8070301500010300a9201034180c160340c1e000d503800c02c000811440040c204038030040c3c3e10800390801154090505100762041c21006895461070800c20f0b = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 917091330 1250 917090080 917090093
    0x1f030201030e1513050f01020301030b220f0317130302030d1a0a12141b01141605030c01060b040308090f1f02010903080a050f061207030605010806150d0c03 69
    0x94911030760760b2260600e44043c0d401c0302c8500314030035007180140003203080d91841e01c01e00b880b80243c241c12a0b030f0300500c0107001207808030b01c2094006091042c1000010388101c80c111412949100162000078007400b1001450340220040d1034900b4030b02850181540e8855070445c00e0204000c001c0c0041c4e00c24044a082034072640c0c052500e80c0c041c0880c0d8081251400005521074506e90080020100545040b408001050f400100d00c204c0440207002c0c140c1c1d01035180782c3d551075000d142c64100200240c0803110f4200079012507e041c1c141842d90441443e441c28180d54030391004101e454690320300752002882074100421b4800381c990188407103142032603480801c80f00000c0041c21940c014200e503c4554409504040100402600e40001ca8070700c0c014240641420700040caa501e500d801d11040260703041901c00300315806078040f03844617049906540020b00d0126550001000545420300104106000040d014460b10410300e4049490174540d00340400c640c81a80c00130706006908506000046a = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 917092580 1250 917091330 917091341
    0x901060804210201020d18030f0203120a09030e0907200309060f1305031b04061a19052203140d050a0e061c0218042003043003051f03020103 62
    0x103070f100250408610204d0360302200e01c5c3d8000321383c400071001442e1080542101140030b540803680051b45c2040112210344003e510002c0100c16400d0390349a01d44100742c000c0040211400019041050303519000078064100c01c003542c5140f8513001d45600815064038000200c60304040d010300300c241414131610386500b840e0400c2c07a201c0c9651307050f203a000c030310340e1010800e40000395101200707a03624482000500c81105c40710340141000d894512204180c3c021b1240840d0764007403c0c100f03446ea41180d803120841c0d0602601030f516541c2c0190000b15502011040458010380340203407104000e40004403105079481a6905500f00030401c140080e813641401450380c1e02c403607100608024039014800e001c0c0b0b80180f040800d4003520a6000c40d003c91100002010740c90424801d444c100000b15906103103a00103150701c2059640a900080010200501c80070028060300e042904201c4610403400a542c3c0b0f010304c6426000060702e400c1c00a850b50080c2441c40c540804080d08a0f2026419074004402901 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 917093830 1250 917092580 917092643
    0x91b0409120903060b01030510030b090115090204060201060b2809090204090507020c0a060e19030501050f0417040f060804080c0d050408070608010803090f0a080a0b060901060804 79
    0x6030340d03140d850007082440c06646184501541e0752120281146010011509401002410507182504125503185081184411b42c1c2d0810b19590060b41c89021050142030000c80726901341c5080c0300e0004110002e50007a0050711310300c0e0000d000694854003240b4a5026045038084018101c0c0300d200007076a01d4141c0c102c0c0340862840c0041c09a81c03600c0600050b0790040d07214010081d9a2410000f00383c1e070506c200711600800302e92296000b072130490f00802c921a0b01c08020320071100f22152030210501a00c1000086d94000000d1100b46040741c000c003243e8004880030317160641641c031214602e0901904032800d444541103c41c00841c01c004045481620040c4100c525001c01c10000400c1c0c0c03c200f00c820900905075030707110707a0f850a20000314100b6649030b1081d020b00084400602241c00d0100c10749103100da00795580e903c40400d090004a600e4000d40c0300c0a0913019200b1314000740040b1900d4030b8402c10b03013030320303603c002d0399850300701321081071003201e01030f01c078480d400f18201c0c0340480c0d05108800030 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 917095080 1250 917093830 917093839
    0x4080f030c0c03030709060906080601120506060c10060303080f041511280917030d050718080304230d0308062d130c020d0f0201180b061305091b 64
    0x5807040c1600c914550056581c04045081b1000400a89900c540900701810051130140d03442d041400011300184400003420001300c1c4c6410005540d1b865100686209840e401c00311341e800200b5000c040e00400003404143c001903000c42c0003c500b540381514244c000c039071082c1881100744e11265810000e140300600200342103000c01440007007080d130b5110350610040094124201040003000030f4090401944440c10000b29620f00c01104100441035481c14074071100046182d40c0c0c1c3d44012600c80401c41c2e03a60600800c00440407a0b881c80000290043e24050307190a52004810101240c240800300617080e07010710410070f0140007070303c10302c1580d404c018090034070004040034400c91b2880c014282015a00200e060030b202104d45041d8031750034448040e0820800c00c40b80384140080d00d4200b004240d00c10f2182044020310a14400d40c005144480c0803103920700c20800615281360032038000e031a200c0c414410342c030040784c2d04120f40c0300c0c01d80166490f00080c55000d9802d002c4420242c1540d259035440b = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 917096330 1250 917095080 917095087
    0xc0d21020a06050c180f011d0a0503030417070b07020616061e0209040f090c050105030c04081603030f030e10180218040c0e06013609061401020604080f030c 69
    0x98001d000d01c3d07018540001c01c031a203441d01218028144104c24003000d00c0743ea00301e0003070206a40c204a0006048000a1400d000409140c0128444c4202984034941621001800103610117101c04001601190744064851807a03441d144c017045030003a4000039521150800c461001544d5043c00c0c480c62501c104c502044041c0007550411142c804a28000d00158000a910b1030902d064400e158070700800c2c290800001503151502c50106c0c0140c0038440c117004d800008106000d00e854140ca008210900840d601207646910500d0100200c2c44200c001c9540d60202e8404540207005401c9081d86500041051400440081000d4080302030300008080070031110700c006d605c403182d40c1c1200d03036403038151345500b400d0034505845c80890f280c2c071404c032900b01c1109100d40c50b80e000103422010280a514204207400c0510000942202c0c080780c01480507100e100040c1007040c54100d00f00311012540310748412042c60340166194081100d00400b81d10041000b0810454820003642c0c2008109544a05 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 917097580 1250 917096330 917096333
    0x3030712200a0e120c040209030a0c09060f150f030c14031e1b1603030608011e0518101a0a23010c031e140f0403050c0d21020a 56
    0xa0394105403801e10794128001415105043e005421041d0540050340c000b40d0041020f6803150320340c4130039144140b140781c00040c00c013000e82e800c000b40020217400440c1300d4683c0350b80c0c5500100034103103441000441c12950800080f540d940d500300f1559624943c6808452800c2c1403030450044c5801641101441240c3c00b190b007592040f0400b442c070800340e1030708010390301310000101000004007d040d9107d18030b03000c803040c010340154030966140d1854030710801000c65162405802400c056000b415281d0b2074500955400c3d00844000c4206090b0281d040209403200000300c202580b4005a00950b98800424a2680c4840da032103440076810f2400d25843c940d41c508005030b9840225403141c025220b400f20448050b864450444081300d070242040e03030448100c0d503409000818034a000000f0304030140b6000450301c0c004c1c0845801d001e8a403201791fa403000001c1810391160420300043d1150b100e80058440c103420600740c001d0101e60001c000003c0312800c0c01b140403410b1f9030041080110f0250706805070 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 917098830 1250 917097580 917097611
    0x3061203121d12030f060a050303040e0a1b030b01110c0a03081c0e0f1504020d0f020409020a1205100504053a050904052a0c030f030702010c0809030c03030712 70
    0x40f80021a030a200d07a41c1c2c148219044898030f0f000d04071512500800c007003000103517000804c540c00c030380c5503011148155039072418040007401030242025010000060003201e035903040c4d002018181098854140301c11140d03400b079a0349c0b00c1601009810104900f01400401e11b190301511160080c910200d84580d110350301001544d4003c100c0440c10703405a000c14003d840b00707001c0b40b0340d0707040c0c100c0d2015854035007600050301c5c00e603210101034412174107403280c14250340b200c0e08080859a0040c10807038103039658401e41c40307041410003020f40da1070280f00e04c00040f03450180100760181d0f4010008100c0c8401140300e9a007040c0c0944840d00c459030360b80a1542d000300e513044003c501c0400340d80710140c0780c6040d00c05110079134000400300c881010449940b6405101900110000c0044461040e078a40400341e0f284c81c910320440c5245074100101004102e04c2036030540041082001541c0c035094541c80d181c0c59543d40c5d000d9a0b0a0746100e410078030001300964810441c00080303403040c0c1001305000b4103148142 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 917100080 1250 917098830 917098843
    0xc011526120c0a0c060f0e13140411011205060901060e06070b0f190209130c050405130f11040b0f071a091509240a090c09090303061203121d 62
    0x280d46500f0030400c03203041c0940c0c0000c100003002d4500301141b101550b058010510318800e03c5c13140c41845103038006c45001c1c01c242e010100d0032101d131080b1041d40c209410903418a01c0c03080d034050700140018005000c07018483c000c1c2d034000c5401410b10304540e420011b06030f8a03000d232403079a41c0e0015030030f208140124408020142c02400084929206401d02d502aa004000c80302e8050219900400809455440380c54895041c0d0104900004620002d884100d40520940e880303d80c0c071050068580c1d043c90b1443e03100103801114100100001500441000c034603028511900700500c9042c020f155500c10340d03400800f601c500c02c202d4062820a40e8070b4540d6810030566440010340c2c0b10412520307180008281c81e41c0c00a403404d0080074200d01980740443d4414401c071041d100d041c041d102040f8150403e402642070554460714082c0f42c207854648407801000e1100080d00000e0800300c0c000307174400940c944a110b00340c140e13a541c0070301044400700d0741c00f9158052494041300780060300061000c0c0d050060 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 917101330 1250 917100080 917100097
    0x10060c1e080406050729060f0438090408120405120a0e030d0306050f040e070906080f0715170717150909070501020a120e0d06020c01152612 62
    0x13040c0d2a031369603051458424184040c09160742c00d0032081c440c0396a000c1c1c0029644410308031100781080c015040070602034000180c48410b03900c0d40da412020b040300c250f0450b001380010340040303805020440c4104810040142c4001d40340c01010000088030b1022000c5156004d40141e0880d00a045032092103a95070b0f100c80318140002d00c07100c0135050300d46024401c09070107031071a00d418424a07080000080301044914180f510450351085201907505060050b4030040010355020010076030b0301d01209848010030b019045c007074060014041b03000d01e410050785458040a41d40d00410b503040304440b005490018001c00c0030303c0b43c1c2c0280f511921800440480c46203c00214210400c01c00c1c1003481550580a40a1412a007110106116907680000c824940d945c00c035192051041680c002a80d040d102d020041d0340000342c582c25042841282e400424000428100801034045212804044285d4501a11601c0042104021503082d1154010050807155106540c4075420b00b40800d003031680050031 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 917102580 1250 917101330 917101337
    0x50f07050f1b0111060606160309032010140904021804060b09040e0708063912090c3109060c0e01110607030c0e180f10060c1e080406 59
    0x1500a080d6404043d00036a130ba02e02008002508103d0f000803501d003d592888034070408660101c50030705100342c044100a5402044036500c100794811000c18001c11500300901a64804002450481c8101c0350103440d483c0710b520103414411024200400b96001400c00761424803215106001a07603540300b110001c1c081140c003559278201c01004d000c1034a130781d24511051600f0240b410000365202084003940002102c481e4021201c80840d4030402d00601000c0029244881c1f071647c410a807a0303401400e100440100c2b107402c0350344100b40c265a481c10201141e07003003a01202c48020211181d04215070301d00507040070404203900004a4421a49540c505580075030715106188030480d0011182c4103c48800e1030311103002c03086030502c81c0e40c8100251a9401b01655891040d151503c1496591500e52000342a008145804003002e030540d1010741d002081c070380c004004502c004070725100c000c085440b03548400032800c0366501d82d440450240c030225034080940700008400207070144000c0019100984 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 917103830 1250 917102580 917102623
    0x2150c010e240105040f0207050f0303040b0615090d0606090f0219032c1c020307121121040504090302030706050105060f0301090c031415010e10050f07050f 69
    0x344500d0180b030010040c4094034000c0c640810381d12105015819540709640c0884c2203200884008020b1107021009419070290003404102c1180c0030004600542c01890500307400e8407071400b0010303200341604032070124040c01c00a500c05400c090308124003040c052000042e00380d50750360290051310003071020282c0d816030000f881410321841c4c0c80c10060b84502840c08001c5040c4414418160b0800d20096508216090340b842032907400400880a80d0880152582c0391700051400207503582c0c00c1035008582004100c4152242107200310054070103980c030000185045489890380506840300405110030b9002c04100215464456014805140744a5030040d82c4e180c2141c00c1020403a0410780007a03204480411110002c03031809019a41035031b41d200300c0010321810f0010300741d0082038201740680c040c0340b80408000403a10518403404070b054003038131500e01220081041040486c00c0c0768016004c29002d105003241681010003600549100b50f040f40d0b04842d80d40d00132454070100d00a034501c9a211807 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 917105080 1250 917103830 917103851
    0x501050c0702090c090607032d05030405010b010e03100e011104060216061b060b0f04060f090c11100902011106092a010806281d0f04030c0b0402150c01 67
    0x3001e541c0c0d880b0108030101414070103001c00191b290304c82c00301d01030204610070448410181c000da0031000480081d460406104080710300182954104403819180d40d440c7c141d000c00d25500402180c40d000e08001c0142011200c4031a68500a10012001c46207541d6558400035584403a080207102400300b46e002019440d90391240740d001d18240741c028604000074800b00c405140e90f0000c1d80e50741c0f154003080102c1c450940c1d40200b0000c40002650562003410714400084c003000110b01300b000d45100701c10030b200482d2885d4003950200124226001ca5900940c440e0307400c11502ea01c043d1040303105250490354150700165080c0707031900540342510180c00280c0307554169040c2c0107258580c09010030060a00440b8032001074070440c00141041e01032408001d079501c888480f504050b64514515a0b0b540c4016114000c00c0e00c940604034251905503492800300c0d81c0c0e00209a020f0744210b03803613170300c0d641a044d4030750700c3e030002c075902400c1281c020403030389100c001c0c80b884180076000c281c941c00c0c0000303070007040b1 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 917106330 1250 917105080 917105089
    0x9080d0b040c0f0203431514060906150d1401060905010c0b0601030b040617012301090e150a051005060f181207060f09210303090309030501050c0702 66
    0x84000c0a10052112003c4003a030040140d64001d90301d01e01c80c5640d601124110081040301d50303018001c14200001116081e0400d4818986041c02079141c01c4812400c0c40d46c10080382c410844072540910343e040000c034145000c1d52100c0e413107400a0100c0d82c00003000c1c107600b582c982003868910345950f2220114091030441e40b60715030050040386081c0e0313002858803002800a4450031005041800f203c2d000407900d90013034112244080c00500b0400085590701071944034070b0021450258154200b41000c114010241c2c140c0c0c230441608030110441d640780540440c018141451007041038002e514200d0006018400258410b6440060105140c60a004924101c003000c0d00407034400c420500c4070781d0a80181c0c00998242201c11040c1450704082d02c40001d59041ca86100c1981a204820001c541194001c02d81e50585103503440d12281c8940381d042c90460143c50b007130182c5200580400520100f1300c02d4000c8620280203090007643c0b80e0702d90b22060f09481c2c0c1126940514400003c4030b10450a0 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 917107580 1250 917106330 917106341
    0xb04030b042f06030a0603051f0e0303160f0c0b0c0a170c0a03091104060f050901090c0c030c08070c090606110303040506040b180f01060f0b0c0d1209080d0b04 70
    0x81400c00d01c802d20041c0046002c078584180c0841c059100800001d044c07860942c060400b85400404448021914642001206803400704410100b424100c40280390fa01c000145e2340240340b1010b07646528010300e54226210043c5400d030b8401c0000c02490305001c15541c2207803602504041d940700741c0c0d809a444018001d00400d91840003003003500030400040711503000c182c0d48501910f203404142b0603010305107400d10318202880941d00514001001078450015100b02040f80c070b050307890070216030b603682c40790741203c070381d0408080400c40d070444801c00284650618440b0030b11803035201e0f0030315005890302a4940c105400c209481d69442c0c07002d02c40c02d0b030444c2c190305010005200035440c500e45503031516240c1c03501900c01490360f0142c2000c1541060000505c5240503d80411215444180741030365010300900e04c44d001c0b0095580d400440c2d80c11140c2d00b03c803200e07000940240b4541c10100411030301d0601a02642c00401e41c1c42c81c040000401000060800803804000456813000a108200440307c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 917108830 1250 917107580 917107613
    0x80714011d040c09091b020c0109080a110d0f030c030206060a12080a02030c030729070509010f1209050303060a09050f0a11040512030a030606020c060412020a0b04030b04 75
    0xc01611180d140e0540c100460698071041ea80492030701d003480011307030b11485942c00461182d03003000d0a02c0c0c4142c00010460f4941603c0da42103400004000005541c005c08a000c1d01c0001d40111031b103c008904d07061205044607001421840841d1596281c0090140041c081240000d0410740040c00b030560401c0400d8210500b114000d00e664684100108019043c1784010004000441c445840c640244240c6550341010b0040d03a43c0e070385481c542500c9039501001124030070072012441c8406008407026031413181031140c40d558901003492005444d03400c0700c81c40d61130400440c1d9046401014150240c903040504c903800540d105e00b050740c104550300c0140d811801070f03140b603d41040b60520b90f0324046c60300010000710001d031505a0088170001882660090381e040540340416510f00c80000000b44142401030b5000c2141d15140e80b07040f0707101c590301c503a0f29922003418003091160481a143c400074292004003100c04031a50b403541e05160750040e5006a503d100d0020410090000842c4400c003d00c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 917110080 1250 917108830 917108837
    0x1905011d0102032e05060301080a0c270509070803041401020118020f10030f09080a0206090607020c190f2c1e060301090f051f090206040302040c051308071401 70
    0x10f1606032a442e910282100c0102d0707906004500296821301c80c0c4801001a101c0a461266030b980c4603200c180d510b5035604402c0311002c050900c001000d02c890a080e078031081d04980342da014504460300c000c025040152411100c1e00a5420018078190104000d0000b030500110203664405034030700180c02c503419030362400345000c400b01c5041c1c0107a44003030495176000c1d400c485030102003107005011001003071031001800030036140a55800c28081c4940241c048800070760300322407c0e59984503c8076142c1105076590400750740b001003400b034540f404d00c2080c221015001c620041490b62880405005603060340003005510a041e2000f140201c0f8000011b2035101c124418606d5084c50400042079024900b802080801c0c2c40c004100d01c3d41d02034000c11744460700150b0142101300982004c580b02c01038040326140c0d0400394141e03601c40810074010311a103640c00900d07450a207881c1d9001c1c04068142040d1307100030441e04210420a0000f51300c40d0300c0142442500030604a030414564038150100000c042d0b060 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 917111330 1250 917110080 917110087
    0x40e10060f0b071b12050c0a0b0c0606041a0301050a0605120f100f0e0114060a0504060e0619120804030317010b0a11120a110c10020607111905011d0102 67
    0x3a0302d18241100c0702181d22910742c03c0030003c0c1d41c01200084155401081303d0b40308000c940c6042c40070020340c0e812410070440d000003c403640c41411400c148509503000481c2d801510000307119182941c071500402c40e07528075800002d04458002421608101c0b42031415550792281481981400c008542c0340c3c00c0d0410080143d022022050b55440051001050809443e134290100395111743c1c00c4400c580c0c450700002c0c08103030b040d40300074461111300701d401134010141030900160901d041c0c012101182c5403440c0504e050b8440c4421b0084401e80d01146070315011201c000081d500d41803e0000b2107250080881d0341d10f803811860003d1a59210058503510303080004c0040c4031a84081044030703a502c84a0900380440c40703420700c2440c2410301d031040b000320011001c030384d81005541202c804c83c0c004040c0c4c07050f250b20b00c001c00300f0006180075804455006900c241c00187c42103000b08840b95450042008484070700701c05100b05c0c4003051912030110340d87d075110001c03414042d6082e0000348000301c914000751305 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 917112580 1250 917111330 917111339
    0x1e0203060a0312020c060711041512030305060607020316030311030403020906131d0a02120d0e0105030c131d0f370203010b041503020f0f03060609040e10060f 70
    0x440311214040a0685060903a4803c5128000c0000c0d84214801612241c0c4030039160404140300d60140c1030303a500840c20003602d00c001001d0b80d1001d4066405095504e41160000c0d1022401010001d1000c0d030811410003000b409070390204441e84886001500303520351300781076140082c000c101c0154000380542c0305020610050b81c541d03400b40c0c4d05c48011f441c0c000360002e048184001504000080000b5142c2000220000003400704240001a0090351b0f900b24000c101c010700e0303981310341040030a170009aa80300f1482e09580b00e40c00541c1c114114a0440c0c2c24100b80c0c074401e81412100764444010f01d2002410fa40c080044050501c0e40b0003040a4080b1052820b020613290000000042002d01403001b001c081041d01a03070002c0002c1c0910385802c544075070310382c07005c40302035800741c0585212011b03081d41400c2c086110b4022160007030010350401b400c1441010740555641c102501c074a91146051180c0351640e01c07a48034106588600f003000b044402440030100301116041e400084022003030080500 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 917113830 1250 917112580 917112589
    0x10b03162108120a14091b30070e090109140d08010306020f070519031e020a0609060b10030f1a031203040201110f070305010510051c241e020306 64
    0x201030a8851001c0b5540d9070b40c0d1031361030006042010400d01400c02580c1448410000003c0e108240500070300440d1030f9181c1c1400b00042c1440c10050f20802800280340006c800300c0c01c05070300426003805400c69203004d45034640c5040c800402c564403100341e0355130841c1d6400c0c4075842415032014521003020380100c0052610050840c00140030280281c0d800040041e0004120f00231a1441c6401c43d003964020b5200d007a51b4400c004c02134200b5000600e8201d00c10a5600c2410511804035507a81c0080a12440541d198000ba2030824019520603544205002c1d694503803201104241c610f075030f4006140318202600e0022076040d00d0070740c085440d41051814940e107000400c00081e5480d80c0c021503c03a991840100d070404410540c022960081c4c03d020880d041000400c00180c0344110002d004903540c0050201c00b54101c0d100300c5600c10301c603c822130032015117084015040350050305240c07a00a14429604050102101545029541ca6a0b20041011450a1074201c03c10490702945181440400907 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 917115080 1250 917113830 917113837
    0x2304141c080a1e090501020c0105090705100f0309080406030203040615050d02090c0f0705031c2007060b0303160308090a2406051801170703080a0e03010b03162108 72
    0x42c074401d03500c9400da03204400850703058044081d80e40702840040781928289010303401144d04104150b0810012030a4080049402c0003076847c0a0310803030328241d0640c41180c946030100354000a00d9035501810740898000d00c001d04c0640615180580c0c0c03824149414411200c0d000e035802c40b030344096403041c092948c03841e01c4050111340440c1c1d0840591a84000c5000c184074030f41c515001150001885010401d0100103007000800c07242000303522408400c543c0040e541b2030004c0030400e00040aa800ba544a884054549140565070008114034034801003840c5521454901800702d01c078101410806920050490340000004050b242205003991081d80703801d120300c0d19071101001d8418207000f40c50769521120092500805000e0305505030b01418200407000e01600aa5041c04400c0001e1345800290070380460b83c1c030400852800f04001c3d000c95035130740540407560f415500c03000e907418a550100141a0f5911028020050481c0380c811114100008280b040030020300039845040454051002d4 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 917116330 1250 917115080 917115091
    0x2060906010b09180703051e0705070201050d02090a0f171b0f130c0c120c0f1104060b0f0309010c0f020c060d02121e011202132304141c08 61
    0x40c0350301d07103c00d5800146882c15a041c1051065032220070828078035899040240a0b4810356412a421849819100f4010500300c80e140c020440800050b4019441000104a42810a04010304207001a000a0365102c029070284820801c1c000341844280d0f940c0e1a01504020000e0051000407400c103050888040306500c4503110303041403c10780b5020b4a599401000034150b48a080140e0440c00e1009040c418455000f628500c5101140748119409403150034015900315155588000207561001070b05100c018005030800e07182d06000a11811420240c400c010413240050344920306000d07031908403a441c01e040803c0040051a0201d0f4980105130707910a54400c1da102c40d6a20b038034500d00c6029209904802019080d64030800c0780c0056100701000c2c1c00b10342404206800c1e6603508000f02d94036020a0041e500c0201e10791001103441441d03100c0201e400038500d81600c00b1102c2d241451710400d08a40030380341194040208514103d09100c0d4000c603a940042c403080d980184c080041624000504 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 917117580 1250 917116330 917116349
    0x27040b07200a14120c0303090c011b111507050604052515091503021c0c12022a0d0e03124614041d1b0703080103120206090601 56
    0x4900c0e50040c013803201c01d80e90f030390781100e1559419102001d0f6507a40d004994070006c6004403c0c00810940c4500007401000034500c090780360040301c0351a0003c0b10f915080c20154020356844003d035424074184041d2418901a0016120a2800d8100300d400c00e11b4070500000c80300c1020f02d5082405a00a5032201a5041c14290703217461030f02e03140241c503029101e41203500e092016040e515100759164004004044c3d40040812482c0c505040c0d20040d5208c405035940899807104018603001005d0307001c0d014898512001000d18002010840c40d64940a0303104255500414800700240b500001d50440030780082c0d00a00080c0f00c082c41000351809608000382440c1d4605809802105200800c1c02071710311007809010b14041305840d00c000c1e039a2034040007404104041c1c010481015500141c80c00c40d080368840210410001c404040c02610040ca002404101c903402d8040c2140014098074100d88240c4601840e5415414018080403a6504200c2151300100410000100102d041e5044a02865 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 917118830 1250 917117580 917117603
    0x70806040b15030a0b25020712110a060e240702120f100c02160825090213090e0318101403040503030a05061e27040b07200a 55
    0x2c0d00c0880200000141d4180b00300f03100c0c84107000020301d5607030150b003401d0b9203e0400d004e590417040c00440c50210840c0541c2040f0000c0007140c00343c04010703012503c03e030010151500110000f48843d001c030b030040c0340050340d118998800c5040c090349281c0410002c12012210806a02407100544680000280540407190030882100420013042490a030ba00742034a503500c0d45807075600000d0100404000051040d11944007800e5041400d0400341c500302030180c40d01b00000c90b840000306e9031440000070059030703242c4002045d1403c1d10140a01c050f0f45454010514903000081e811385140034910a0325400800010120068003012008012025a540c0040e0701e030402d0f066403144100440d034404110004204400c110002c00210b205c0c80d19420100500d0b04c825061090291982e4825010480e1a0340041103c0c900036a1031031030a106030550713216003a03040d0714803150002e045e0380c2160000c041c4000c0c0030880d5040104039403035030400900703a1007012201c40b95503036502c00e0002c094620030480 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 917120080 1250 917118830 917118841
    0x181b120a15111605060709060f0c020405070e030604030c051203070e0f0109091104030624060503060a03020a0b0319021e070f0c08070311010302190302030603011b03060e0603070806040b 82
    0x5955051031004007660b180b8103e0b0409070344608003100c070309002903071000020034114007405441c20328524507034485041c0d00c6181e0a000003003001402d440d061200040504c00c5655082280c03a1040d0700c00d0b0356284100c0d4003850041c4c40c1c110025070060f01007800344204002190b0110300106200822914050300a514900588074401590030010580f424420802c1501590300020001c40e0300c102c104221075845080c0c803d03e10482c1c031a0821500031640303810801c0c144200081c40c0c112600800600000342c4e01e5000580c000303e150b100d050004004030401103490010fa04615440c19007032420341c5031410b021042e802d0b80d00d8148020340d050780c01041d01014010804880e000c010307480032401d0101c503110111555200702c8e501c021500d100c0c407a80c40e42c206501c01c0c001e031002880d540c0d06d1070300b03a0240031606401a40004000743e80642d41d800c40c10540040301108421012030f1610f0006640c0d00709980407031420780003803443d4041d5000180c06c00c8680d60028126901035004a800d0035941c650 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 917121330 1250 917120080 917120111
    0xc03130204020d15090204031704061e11031902190503090409033501120203150c0c1b0a0506040e070305060a03050a12030f05040c0608181b120a15 65
    0x1013995002011400b280410349940030342c020001e5a00802481e0740c41d41c0007116107074152040703010301070000b207100031120b02401d21403441070035910803401d12040307007041208400d140d90405c481d42041c8540c6030150032007403a01400008a6000310200c4029403001c29200c4e50b83d00d100e48400b05010340c0e0b807204140c052501c1904d11002c40c124011441c1c282038040b51110500c4a0851403d0307584454090001490466100403200070039400b502404901b0001070400301c41e81d000030020400c0e4541017081c441850401e00280c489058801d0303d0020112881080c0601013980c0d0300680d005180401c0244071043c001c141d440d03484030161070003041590f101c1c0c012400019980d44000c100e0301c0b88000101c10080280002069071280d0f580402c8202c3c03010030138030140d034070689010f001c040702880d0078441c0901ca20034156000022500076101e0044d400402d501c2c000492141d214150307102d4030400414a0030b42d04020103030900000500384098980c854030138401301c1340136045101e0743d03840040c06001c07503 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 917122580 1250 917121330 917121341
    0x201090302240301080705030c1e1003020405120a060b010c02031510030807120807050301140d061d0c0a090903210b180402010e06040f180b030f0a0302060c03130204020d 75
    0x40c2c02c2142c1c40307507990502660348009600900e442802104524100c81c1022624500c208686000c2d0700e04c0c8044c0d040c24843c5145c0b0841003e410550200b1020030503071a00000b500500c00042c00a2207080d0490505004a5240411084c1000012040b060140c0d41c0000c60300000c040842d0b240d4035544031040404807000907a880100b48403000b02e044418007284c90005030b024402078031290400c1d0703185201102c07035200900401a076a0308514101485003440c103c0d21740e02510800d000100400341d040451405801e507810b14a6a80c007240001405050900c410401819541001d00c055011a50007130504041403030312825080e864040700d0307204445604a10b1a2460240c01031001c220003001402c0e080c00c080f18240c2c00300d521803040181e203041c40d0044a0803220791802400c522030600c10442040c2c49140f540454081d1204500c441d039a50038403034500310145100040081c15030b0341c58040c1c1821401480045100300900400c615850202035002005904413030040e900c00c4400002c0303000f0003 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 917123830 1250 917122580 917122639
    0x7020105030a0b03120304030314041502070321020a1b1a090a060f0509061308031513020a09030203060a050f2e140f12101e020a0e0405060d0201090302 67
    0x422040c45480b0044020000d41c007ca010355000d22203031410889021480d801918005c0c40c0c0c0e4095284903680007034a0b8041c001140c401c1c038000d4200700070404400504d007410b424030540ba9a0014003601403a800c200c1003541a46080c40740c8817145015200c181d115240c505e4010441c1d1401e6001403001740d0244900b1550a0340214100305450341e41031420020407048038240c41c04c1c4226400710300540c0a4001c0d96a045a10800440c41c540c0c030284507a40860050801c0e0fa0400c4584a03c0c2c0ca5059483c005000b00359195583c0e14061440d5004052403340040d01c1040d5040c906003d0200f60480c003012580e0204586522591944070107021000381b44141c800160184038400c030108030000780c68041d14101000b00c1f803d016503001e100c100305074240d490340c40798515444403001041812180d003240c520325140305c4da03800d283e0b207512407100160f074031402c1d04900068181c4c90010b80c900e410710a00c0e8000e00c090b5040d03034441300350341e0001c2e040e8401804040e1044800c0b421201414005030b80c483d0041 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 917125080 1250 917123830 917123833
    0xb06030115020f150403200a031202040306060b07020117010e013b01060806060a0e040e03040b0a091e080a03110c040e07050a080303090d0c0201050405061204020301050c030c07020105030a0b03 85
    0x1514404c044a0310107825a4105c2c0000e400c0510180c47c80c0300300c04424030b2824110003805044800740e80664081c2c0b2055080380314250240400004510148500c000900d10f003074441d03984d00c1403403000508141d003000b41d00709a9244840140104400261081d041d101c4807030203080810cc52404a0381662010021952500c0100c1e8540105107000310981e81201c1e4242c0b50305000b40c44030800c0028034050611110001001034400a0940c6420b0f0001040e003079100341600d203081c0e100c0280b03091070b501002c501c802082c86007004001000880c60325111100c012007140010798141000b49803665003100f80902003040440c2c1e500840b101c180462400004010410020500e582d204281c448000f0f03c1142c3c80394510540001e80804084100c80c803581e243e0001d4518016091003c3da285240802c099040120500002c11036864600060141400c01c0e6641905403511340304041c00d40324001d019400d2504207006004054060405545d140303a42402e1a945075070b9600020401404440d40b1745526 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 917126330 1250 917125080 917125093
    0x8030a021c0902030c100210051b0a020313060311040b0d1b020f0c0a03020a0b0d020c03041710060311010c11060d02070c060804050a120e0d140708010b06030115020f 73
    0xe00700035a02100d04030384294161814041c101080000d1800407400c68005600020300485030b00304031760b002c650b000784c4960503511a107004072500007641d0405401c080150f4000a80406006a001d80781070050111b4a400e100c080c480c0b00280010b03018521540d4140c500101d01130004850f01d401408918610345400b50040d100840007d40e51074503410101c0b65030082140c00641c07400d0055503031083e240c02826a030b0380d80d40b90264601d200d900001902001c185c2c20f00502e241c1c118188010401800e020b03401268100041c494035080c81d52401c481b80070146010402c01c00262003048143c0800b1003420304407640d500320704280340660248003210f91302032000500c1d201d48102c5d507400703422887e00602801500ba521030a081d24030741e809903006082d580c811040c0c0000128401e04032048002d091800e044c11b80c0012000c200c4102884c13500f111035225000042d184a8010007040e4000d020000017800002e0700794000c210581300601038010074415003040c590846d80200540c0b00b0b10381012003160344 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 917127580 1250 917126330 917126377
    0x1b0409142802090610021501030b1801050411010e0111071e050a0e06090a0e0a050d120b010801092d050609070801060e0108040302070515070b0a06080a08030a02 71
    0x119291001001c1c04a07030752042020040319012910911100d6010308a00025140c620800c1a0f03a0328031524102184120504100f0403400e0218240c000e600c1059140742c5802c0800c004220564003480d13004081e0314010800010540003107000c41c402c6c40a003046d62a1a032070100480301004000070340d4445129074140050f06031100c01003594041120754417940465140c0c000c000010700903124554514072040089411031612559098200d40070301d2000403061120b01a85040ca50b050308159503540000c0940014150031280401404000b40401c00c10100e503400041c008550600903401103980d0b0361000304101c002d01d4207914640f01410b0601c4103e016400028000e050221a803d000301c00880116503110b004103102d0703060320a9501c903115030811031001100c210200034016070440c420240c000646480d610000b118103215040344030781d610218101000252000b0705030b82c48442c6400c0040200381d50100da06001d4990041000e45c0d2030b00c55000302400f9004890088104008000707c019 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 917128830 1250 917127580 917127583
    0x1e0903050415030209010207090c050d0c0806040b0109080a2613140a0b03012c13140604020603010510020c03190203010f051014012d0801080d021b040914 68
    0x802c407100910441c0181da944541182a030040d40c0310140588c2c403c0744144071218103904003005c0f040c030501c0c00c941001901d1503080d00b5a01e5240705c0f44049200041030202c2407e00b400341440102e02801e061a11614003d034a95448040c05000b412100500c2c001d4a021070300c0340c02091194108207580f503103c150b01e84031591000958031443c00e684d00c05c2c02c10200740342031002189088030030200b8a642140c1c0b90003441c1101c42449038503808081480186a1070084080c08003e000e20401c502d400c010440915282d11803a00c01120810a640304030704200041e6913882c11030381034550590751030748031074210740d41030303203003e040c0340d00280d03d4055101c882c06581200501c40d0080b90003200240140402501600b044501c26a00c0d80a054882c4006010300c00303682e042e02d13980c0c0070103240203034449040d444564001c05420082c0040e80b040c00743c0236900036900164080c050160400609500720f40000065641c1c0030081c1ca040088410044000481e544d42c2d01c10908290826905218201d0003107009 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 917130080 1250 917128830 917128837
    0x110f0f09100e070306030b0106050c1005010303051b030c0a030e010207090c350402040209120303010308300f060a03050a03030507031109012019060b0a050114030a1e090305 76
    0xb0761203054610001103d0500ca40600f5085a82000032441c40ea400c1c410111601c0d4012880d504003481100004c1d141c80744148980b600960080c1c0d1943d071551140103412800e40b0400415100c41d6005120300e4024020100d03c81501030707410706127090042d00010050f410503400f41d02c00c800e0b40e8902920000c2064105503120710300780500d281040c2000c15840700b10215501d8440384007841000c070000400605142d801408080001050440500380c1c00807014a140c1c801d82080340c4142e004580e000d007020805a940d441c80c0410761078601c2e4408101800080000010500700d00100c20744086101d03501c480d0b0344a4051600300e0b040d0750321744241d820054040c1c10207592840000e0f1034201e481002903421416600462016035607122019825083d0106140a01d4940380807401070303007140c9044c0707490224604141ca200b40f802258038407414040015014082d4803190502c442c01007400030065440085940c009600200051701302805240c4c00b01c40304525081d24081460512904249a04540035 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 917131330 1250 917130080 917130089
    0xa2a06110301060c14070f08071502030f031b040302100c03090509060612091c021b06040302010804021215070207052404032301020d05010302040b0904110f0f0910 72
    0x2402010618110814148024480d0000090304122130000090100c0381c03240d40001d405044880760b50300d907c011407400c26180c0c41065203034040d4034201315100c281c5070328560707690460028604029000c0c215450501c0010050004d8201c41c01c0c0321400b40f12140d094802070358000d40143c118041c0c1e1f00300500031025103201038003c18600d00002603141b03480c030016845518060001ba05014207040141d009042c040c000d01c0682c0140307054181d0490041c52100003000d0745030700420040036000f0307914070803c446203040f0740202400c11013440944d800022494109605842e0440d00b400c11501c80740c100a805e140c4240001034190030b109000303070700149275070a4900444449000f5815185050115142d100258903407141c1403100b000450354059400481c06420301621001e00c49402c030785400c9900021100b002c1036620001803040d4102840b5002d54003109550007070042c00d040e250000b0740c1c0c03080204c4134481c1344082c0e030140c0e01e9160701255680c2c0003005800069103043c5a813035812014a103005 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 917132580 1250 917131330 917131343
    0x92b03050a09150f020405151309050705030106050a020f0d0801090e0102030103110f120a0f06060605090d240e10051b030f13080c0d0305060102031e0a2a 68
    0x12541e45000d610640380c00550011403605401d518982c1200541040107002e28241c0d424000090152202c3c90020400c268002c1c200340d540c5000811196100c0d9941c00c110391052070001000045900310048a06440403403c02c281c5800d160f2002300d190034000c5401000c180220080b00080681001038076060b119030100501241c2ca9400d80e080c00c13800244806400c25010602e403a4942c242005691407200024110382004c21703154566030724101012904030b440743c1e0150114414070840348910000380140d0318119242881480c0011950701060801600e41d0000014001143e40c0381c0244044d075000c0010300340007402c21045a251520201a690001103040c400040d21a4800d80c40004012140300a01415502c45001c504070f003560080210813404504008000801c5a54010b0050701c0802c0700205100207550f1030003415100c0140010f030641d84103000380d40c025440089529241d000b064122603c41c180050100d80ca10810103407500c000082e440350362100d480c02ea0f040b0480c0c074003850 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 917133830 1250 917132580 917132591
    0x180d291b07050c04020f0c06190f05040f0212031303050f010c05042601020f03041b0f051302030a18142404020405040516080f191703092b03 62
    0x440c40441407203080c400600540284160307900358075040e4007038081d07500c0d0003001e14208244005100c1c5801001e50340e900d100c210320801070b81c0e150f80b240600440f05584003004d01c1241402d5a0f11001111081d1009108903001c040b084800c1d5800c0040d120780c44d00345440120116078a007051601c600d011203d013103040d420440d070070850b203010f207044500f00c50403502c0418201d00e44a40c412020610030030955019502080001030b010010703c003840c040e030702545982c0d0117142055030b1844070700c08980c040300701c0000c8401e0070041999959503400c3c01410340c9101696a03a910b170f500034021700c1e100800900030040c40000c0024803e035110750a00c1245603074115074299a038003100e941c01c059000d44092500102900041c01420316400c810742261007601141c01000701c0007068030b1030301c000303030068452a40825400351001c0400c100341d80f900344103c01c4d424a03103012611403400e10401821124821400000031807d00e40d010894000c16806d0052128070912a200b00e00130a111600c04002c002400c16 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 917135080 1250 917133830 917133871
    0xc050705070e01141203070516051003050601052d0406020a1e0f02040908120411101b0201140d1a01081501021b011202130812180d29 59
    0x5003000e050f03c4040051813190306120703040001403100c484048049000138090100091401c004002442404002c405081070030705090001c0000c20070076213003c01d0300f41802e10000d03036000011101c250341c000705840246040c48001c241003040c08000c0760140100020009001540401c5102c0e0040c851001d00d1800007050310f01e59002da8074640c3c05001d86000c642c03138100620f031641c0f10340c0c04c003032203060042c0c2000b6080700010343c0d07468100c41c15903415016200c02c502c81c0c581a0807040780d0200364181170104088103002854007a120440090500c1180b840d0844980001c0d010350b4030b001062042803004002200c401c0c200c00f035402c403105010984890224222421044090300700d894103074003e1080c06101c400b490388404901070b0450504c15660701c00282c041d0399000820112002400ca200c9445c54000250b181888040c20390b03a45400070301903660502d002070f00094420740300300c41c4918044141e08015607119001e0302c000c0c48254483c110314a1250240d00b0243c0300e0300f030b003500440f02039084 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 917136330 1250 917135080 917135099
    0x1a07020715300902041808030105040f06180e120f0307030f0605040603051609180f020609180411120d180806070c170909010e18010c05070507 63
    0x15001e80c000c4452141405401c00e44207420a520300c004201c480c800d20740c41607420841c4400710180a003000da031206500000d505040c015143c094905600c000540003850b02c2d00c01480c00103000d40d03840345440b81400300403554190007140151088039006000600b599107a03034001d2841a001224a015541941c24504404000d5554800d08400298603507554801c088005007000490410301559400010801e1b407514403410001d940301c1c0004228881d07480e01d05c00c44a400e01d0307112007015800c000c00304004004240820012071340c01201c4c016074500c07610014941c1d02030400242d1700642d2003110040003080084000b8000c50040c8003c061115048060041030038400c22112003560110030240100c52181c002c00390079148001440a603d070301e030181241040402d03202c0710300180f0b41003803503014400e0700d045500d401c0e00201041440e20500b60007069030548148101c0c00c00105980000d9200090040c401c109041480001c02c036183d00410003605a0f0840e50017650300d807003035840100c2e01406 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 917137580 1250 917136330 917136343
    0x1906050c19030c020f1006031e050a03050705030d0504080702010e090c09010c02150304080309160609030312020d050c03180c09010e04020109090e01290a0e13020d1a0702 75
    0x103100c00d00146007000756400364094001440c0240440c410003001c003a541105201d101642d181583c030200341c0500d1424410f0600035850711124030403518054502c0050400122a8103259042c10000d44a000e6410a41e00b1130062100d403248650500081104202d400b00c02001c049100340c039010600145002801f440400840d40300e10b40005c00c212450340c80d8055000000b03010305c010061524401860b5280203150029182154800404414004100700a1001051481194520300756903132514000411001140c8005001d01c00e480060342002c41c90358044880520715110280502e0070302c842c140c00c0e00c0d4000c031440d082c05c2485000c603240b1560003041c6072440110040c81480c940c3d007044400078880a0191080f030500c8100721000032402094003a050f002200c041c00000c10b507100419420715900c0c1000301e4407001071100d0700ea0760340e966296200005c0d07411103400c03c0d510b6a1490b00b841c4108901000c0694803200d4450000b080149007807410300440020000848540c9072500c0590390b480 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 917138830 1250 917137580 917137597
    0x1a070203071403120a050c090d0606031e08040306050c0c030a090f0f050d060e0a05070806060108070f0f0e04110d2307050a112409070e0907090b030f1906050c 70
    0x804c070700822014003054000503000300d024070940b45010b49060010348800824031045a843ea2608010020b05c589100c00030b030000555400e600010841d030345c880030284220b0000410f0595101c0c0440c0411720f00c40181c1d06c0800c2e040003103d03034440c8001009011046548604480604860408a41c0e071000a04000031620080d10700c22940d5069a5403001901d130000045c081886008021404182c003040502c00810420000d01b00f1400c001000604100f4001e00e01c0d014040c46004112400e90301c0924020001c0c030034075046c00200d4004001801905000c800b0309804940403862202c68000c07680f22000104042c810440d02141e08145140c041e40d04071030600110304184100e554881c041d9400b005113458050948045102c80d282590000481d40750309120040b0080801c500d840c4100302c09405041a0100808140f411421b6980d40b4201ca010340000f0940b106040743d05038400f000000201350904059881070141e403420100b91103842003081d02c0d11070604011940d5501038078112074015 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 917140080 1250 917138830 917138857
    0xa050405150f040e0910050601090509060109030506151905151605030f0301150c0210050c03070c080a021512070311070209011412010e07030f1a070203071403 70
    0x14a0103041080c1c116090084820292040082254040c1508001c0c8040e0900c43c911820509200288034503145500001100e41b6281406002140e80c1141c41c0104583d8102e031141d2a40c0c1da1000100c0b6000384c540d0008203107115800900c01001d4201009070714a040c19a9080c4501e00c2c51130041581d1200da1040d25004408c10790702041901c10700c001845070105d0300302d01c400417110590391146194003400d0501c076407007c040300601c14002c0d0714400302001042c515081c94240810b4001500b650855042d41d03080c00000901026200307018802d8440e00b68004100721811990f8800964441d218404224802c1c491114041a0205a0701c15a42c205c00711104481c5030380e0720110107600802520391410350420043c044140165958901d80c2c0c06405808011031014520f0307802d0010881c885070780d032095a41041d00300800444000b482c1c0d401c6039001100c201c0c9502c01d6040c14500005a01a001000c40ca680100001d16400100611216100b2103c00d00a101c14106241d124000d4402c1e61501 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 917141330 1250 917140080 917140087
    0x1e05070504090b0105070f3c020406091407120b180603060601140f21240a05090a240308040e01150c02040f020f040e01050f0904050607030504030e06041e05060a05 72
    0x800c510360a108107001d080c0f21100740f40154076120714484140343c0b04800c0c404040211380009c5007401d00031080201000782c418840c240070110300000b215002064003040104030810303c0030301d2030940c00c07860b4540400380c40049242500c0c0243d116085040b6589400307841540d01081a55100b07100a03610203100b02d804a08048420120b00d195500041c41c40c1e800c4410316204a04102410240e6402081220048414007094a0083e100d10318403000092080c9201042003020344c0b5007203203507035202d081c015001548800209182d06a90901a6241c082c410415008020003071220000c0046c0c2d20200b560701d00603030f40c0704682403981021215500c0041c0c1c00050301001420036800ca280220131888001d420000c402a40c4141d40d00540d01c00055440280b00400c154103001100c01c401010030340c0c2d003040524007170721460f685440203041401007559070000141414452075601e1070900b4000e02480ea11582c03030270510548201e40c0385504402091000010784d0f0301d0941c00300d410740850354898506 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 917142580 1250 917141330 917141333
    0x7020109060c0503090907030f050601050c0705010c060617030406030b040501260a080c0714060a0c030503040501062c0a15090c020f030304060603150501181e05070504090b0105070f 80
    0x106100469812540c5110500040e5020350311054102d10580d00390340d0009c2d25000d10041041a50005030a280c1845001c000721a05600c0100b103040c04e0300d4081c00d04039031103183c80c078006c0028a041d9220500035000b2100796214600d01100410483c1e802d9542444510fa13000104011100c081c4030302469414080445544110b01c0c01c4c24501600500e070039208080715507120312100b603100c108075004581001c64180182c42e0248030000b082c0700107a40340ca081031461000a464514040c8015080c4280880080c0c10460250800f03409010488110f01c1c0f43c401c03040300596001010003981a181e01c040001580000302886128803650165003400440d9103840c00b00740041090300c0110085000320f10441d400901c0030402940124880c0b0400100c65185040500700001060282e0000908003401044100030540c070010340c01c4140c180016991000090f180c07c240d69080010210310700b850200701c0310715000b00c094011560060401c1c03007002e0424004403518460140010b0250015116900 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 917143830 1250 917142580 917142587
    0x160b0910080c12060f0406090501051003050f220818040608010e0d050c0f150901140709090b010306090f09020f042c0111031602010f06120f02061b0307060c050702010906 75
    0x260051390103090710407604902404036080d0f904503007000241d03070b449800401560414858241075603200340790401c61802c240c100c0b100c0c0d92901500d2004851401d41c46a411302012807100c2d1200d69100c1200e990700c1e800f01030034510010046e041984100d2506a001a8201040c019601d00c0d11045016240380381c555503040d18190000c201201c1c2030301c90744002da50101004c00c240b02c010842d40400904c2460061f20362030075910b849041003010001c21061020f0b031600800e104099821000300810703001d1068004038020030b10799014020039400c01702130031061801c2c0c0d0301c1810180d000340c0329840d542420358140070a444040d950214909078074224000c2080d00b01140c1c890031202c4a00108000b1f0301111540640e801c251200300012403080845000340d5024800c8080030803031ba44050100900e061405050040004d0001d172980340c010035890110b47c1c3d19400c03102003020f58000d41b1460114220341a989411000003210740134078048903081594040d506840030740380d05a6940c1007082c01e01008a = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 917145080 1250 917143830 917143867
    0x30e0706030b030c010f1b0c08061302010c0f152408061509041112060a050703060312110f011503110901030b0c0c0703060504080d0510060801140102160b0910080c 72
    0x101f0000b41c1c1d1804030103e022508502c461038010103c3c0019581020030560501174040c2206608852407480d820050760810780d001e0a40340c102c1c400407000341c0ca82c10140c0c500da48607651800d2940c50721000ba20040e1143c10240702604030060051002d6480d184441c2c0c0d40c00701510005003003010342c41210b43c0c0303141c0200110751003445880400440084d840120300c5010450000140c01d802000402100101901c0b5050b0301520b180b0f000d000d540d00d941c0304c0092114004034034000700400c0b06e95078501c00c02d0802045025800d418000c02402da142441e54400441c640421514203005a0460b00da030728080c040d02c1d040e2a0494a441000d45030082c0003001c0d54040c800c0040136000301c0c24000081072141c0b00d40e030300c104c0c043c21249a440078009038400031140010002100d61000c50f1040c17142a0307000d0881e9054440c40807049146014100050740f031718400c07039110070200ca988000402c50840007806060310300400e403108151440545402e4600001c02c8032503c120720030a0060009916255445 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 917146330 1250 917145080 917145107
    0xb0306040b011101111b0a031b03200d0215100512150403080a0b0402071104020306010e0a03420c0c02190f080a0b06041a03030307030e0706030b030c01 67
    0x5000745100040c0342d00d00759a0414052010745d02c1c04601c820003051450704110301402c011001d0f08071604907030b0b00074100041c140143c003070549102c005002010701403800058140c4000580c07101c0b501d5043ca4066a4001000c8400b0050080d03c128084040c0b40089141c0900e49900e00b08004a09200c144128040c1e060030f454201e1041a0441031300940d00050640218040e548400ba9403074201003c0b0f007030ba8500ca034810b01440c410000d400c049006031094071000c080c02c03100542d6a44a01004890181045100550000b1034000000c2080166403510131900010f00b880611101d6494a0700e81e00501c103c4041d03132040500340c40c0511203455600c80180c80a2509000308015800d0300403a5581040c022107038201303156400c05100f01c0b101c06c1d100b03000800e00b0304024402c0302050790700c07400080f02c00741109002c0e0303849442e052034012145141c581d10580240403651030f450112401409412101800c114502a266010130307554402e00550980d540301800521003140c0c0c040045494000146c4e4 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 917147580 1250 917146330 917146337
    0x31106040b0409150522050406020c0f01050a050601080610030507120507030b0108150d0b15030a0302030a0e01090605030f0a110a09181b0503041b150f0305010b0306040b01 76
    0x404103001c80c85002030000761120700400990b4091000020300c00500d40d80169120b403581c5d05414110204e8518443c80709440c100000c80d9075161443d0040c040d00958880141e11300a1041d01d00602c0015800030b44a4000c003030040c480c07512442e00645d480c41f4207030360745500140341c0e03290122000e009420468202c0c901e4900f0b180c14001d030303400204c2100c005464103c002900c0f05d55403581580c1c083c9041d82c00440241a4000c500a00d80c002004082c20200041003034400000007900704240c202c40c508440009016980c0c850f04901e40203449500c40c0c10503401003081103290b403042d54030900c4507105807201c5465807441d6445401210003034081c02090039140d07640b641031151404940314040d0445408030f0f1166100c1d40d0038074141642c042c50484100301818544900e0101c41245c00401d00c402c2c2c841800c00e01d03900d4941e814451100c01d9441e54800000740c0103c40041d1040c2c3d0881842d060301101d541d82c9082061030305040342990401c0c840d1070f1000380c060000c00c0c2c1a2a195201c01d454080504 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 917148830 1250 917147580 917147587
    0xe1e040b060a090501110709150303180b04120507090c03140907054e070e130f050a0602160308180c040e100e0609330408070f120f031401031106 64
    0x1ca581c003621025810340e0450580727000304004154001000201d104040414001c0031402c0c82e065002d54000d900c2075814002e400c4400506000003400400090034401c1c2c01800178800c0c2800c0540580b024500c0603040b00b403000e0000e640e001c0b0114020f0259480100a5440b0b007040c00c02240a100301d0240c0d812804507610300c0c080b0708012040b51058030320011003045085407100c9121600305542039000003400401c41c410030070b500f00501d00d40032410760702c100303400559021400c01c02c1c64180440300c0108424030001d080e246802071511001c00c440e10981e0381c000c5030760304d540008807042119401ca0b1a564400d5081d011545499006448410008400c0b100c100c1022002c00080d500d000b60035402d541c00450500c00015030920442098501c40041d040c01c07018100b00114481040066007000e4103804c1c0040380412091a0403200760b01d4003e50030340d102032170718100f907039024244060b4a4041441c02d80c00c0c03900c56019000300c180350400d601210300c05a2031038440c15645007100c0900c1e5030001303040 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 917150080 1250 917148830 917148839
    0xf030a060b070b060301270803090c0306010f0f0b04140f030309060a200703020d03030509010603170c060105010914011409030a0c3f02010e1e040b060a0905011107 72
    0x2c1c1580310f00600d0b60300c0040c14200305150840b0404084021100701203440d000404410a07002d120807a440540d003076499495504850410f08450f10495260180d84000585290039802d4a000d0701c02c403a1840490710303965254150b01c0e00c100d00c201000003010450b905500d00e011090000802c102400b686d142030003020004800760f01074908100410398038003070390582048100c10104a10501001000c2c12400e513000074a54484040004041546460000b00040020740002001b55444116104003408400d0305003080e82202c48901c2282c400c000c000101584149000400c40b038000c94444913401849004490040b9488135460000c10304024900894030f040042c4048240651314103c041030800e007009070001c00c0301c05140461054850742080103040982d498455822061410300d0a009600c0181d900c400c16104865020385c1071003840012141c8486000c0c482907040710100140d601c044100a440c0c0078000c0d5840010310261310503c140d500844e100940c54980704201c40f61159203 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 917151330 1250 917150080 917150099
    0x901110909130f0b0a0f051b1b15012c15062109010e0d1106151807020715140f07170a0519030e0a021012020d09050d0f050f030a06 58
    0x10342c3c1040c0e006650700e04c1b80e20025002d100c1d250f0030000d41042c42d030604030901d10b141800c0c083c40c1c0c0c4805c949030700150119040c48041005900400b11018030080c150703990b04a6200506601030078049680744040302040700020700903002d02c954220000c1c2c0c841c0912540a011540d04041d00c4000d0000801001910340250030b446103108091110010420060312407035182001c1c02d480342c0d98207000d4080e82c400018040440c000350302c140c0244d40c40011090b80400106500122030b1080c0f4821802001d0000203075012030220f050390009900780d4403220f140f03070301211074041020040c11488000d008520710095160003e0189a00945c0621011442c40030038050943c84007d045000c2400020304245940024003155086100307130400b00800310490142d581c55090445000b8454031a4000c4080880c2c010b103005451045548400c544851102000000a2503c0142510148a05c0361a01c2030b4910850b40e6540d03a0646540301420000120040c1c44184c0026082e6104142c4404011900c11031 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 917152580 1250 917151330 917151353
    0x11a0c03071b061d100e09070306090509031303350403030813050a02010e0112090b04170304030f0509130c02060406061e03031b0501050f0901110909130f 68
    0x20042c0810002191400e030500c54000c1c1d00c4441440328144440f6076004e00ca0840001c00c0300309841d90b50f0020501c40b811162001d04030001030344000700c001845803c0b031b8554020015540404800c0140d5102e411b0040d0b541c2c0140d0b107d2101050301003a0a1000070714200100084c4400c44005040c8010400c44040705800c4080c81004d096001250070420b15500042d51070300182034240c00e08059009071a41d80e10303001c00a03006814441600a513903a90f900c500c0e0180c61000b440803040245c802d10f4500450701d1041580d0549030110b41104002942d0800801c03a4010341c0d26032181e140d141d01b0070350140c510360021002039a0081100310301241c0c05000c1c1c010740300c80d288158007070515840d107854200100c0d07a06030060002c0304040b0b00c0d58425080c110210b030050f240c02d03041403607060680d905001404100c8d0a4014540d50034071080c81400184a01e0b0203000380000030090007244005030721000380380198900a640604001c000c5080c0c001c035203414020640c040d0b410b15243d01c20a031540f030700d1100f = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 917153830 1250 917152580 917152583
    0x16020d02150c1009080a110c0a0f090f050702150c0705060a0f150b041e031407081209031b0d06110a021006230604080a1110030e06011a0c0307 63
    0x10009a42c0e02003001480441c0194186460801c01c0949545651442c5c2c042d844803042440f10000307040561083c100101000001d00801980c441516410400c0d1000c545200b1801820b0911244110306406405003d00c12042c40d03004024a403103545a81c1c0307000001130505a1103a2041186001003082800401c0c0314800881c0c02143c800a8641c20342d0071601c0190801c2190303884c00c1400c0c0b020750000e08c1201e08560307090f5880c1030003072510720210303c0c41361107648005c008201402d80d043c564800400c1a034225404441507441c00c070b49852906282d07104240c03456900d900f0525510301c0b200160042c603001060041e00c0c224444809503901412a0f200600c49101d0302c802240210580743d040007004500d4141c0c0038180441032512003070600100c08800d40583c0c1c80d04038541c0390407544402c1c2c1500d000344084812141908098140303200804c6640c0010340c010484214a030400c580240141061940b14000a00d5140e10f444611100242a0740290007402c0c01080102c4100030204068a50303036 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 917155080 1250 917153830 917153869
    0x120c04080f15070f12022a0a020a060507050307060c0c120e0a051516031b03170f04050303191506021c030b030307140c0405040f06050702030f16020d02 67
    0x400c880740c11080306500040c03141d4100005451311180c3c0b250b1106045156010000c03015803074002024038018884100661070300d00055480041c0c1c1e65000024604d0419070090b5022541d681d22030b003040326075102c0c000c0b0151072a841004484005a0982d11070280c54500b80392410f00742c219559000d880d250401d107c900000c030107d402003001e19000701c088000300000c40d8503480034440f02803501c0f085d00a0541c0c0741340c0003000b00360020505008040c0c44050104002c4400000c0c4040d01d4043d040c502cac1e06010811500310740c40011405100641410b00070758210f001107040d540d1b1035031001502c002d0300350160112600c0e03c035101030040320010b00c8000f60002d038000d00881104110710040074020f080b40c0c0c2040505007407050101d9100401129401a001426074051000051506182100041000f0b80091410b0700300001c1c040030801d408600c42c80b0794014070254480c072000701d0b520300600b5460000310350200590030003522283c6440c4030300c62014102d001e212444d0707000161000c00704001560314 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 917156330 1250 917155080 917155093
    0xe0402131a030606030f07090b06040e04140c04020703080105060d0b13140a050403140a03200403051b0907030b12010f02091c0c050120010c02100605060f120c04080f 73
    0x250325003848032a6009500345c00500d0b07814103800c8103507034035041c13072040d258480e03680d800003100c0345c40301c408683c0078013042285484036080c40d1400e00a4141d415002d21414000c0715070210f403c1c5018003c66681c56003691350030006074240700400c00d066000800d010070321070342c070040c103150b6442d80d03001000901d01090000038a641e011082020103103004050100c880d142c10700b00300010b070f00304400e0460388860500842d19255132900580061203e1168074001c020709003540c0769000c9040c1c00410603a0b104600343c0321656102012900e0b111450300000d0762000d036090005146510980c045900c005c0010212030040440448190071146000d00078042142c000404054030308110304661111401d80601c1c01c0200116140c01c052029036014040c10000d4414540b124007107401c04e003185855201e0300800c000c0e0034841002c0d40c0c40480101d03407081c00f820010005044d14003102542c4110500310109468402020303041c2402c868001c11071161100188008110b0300010050782e22039881da0701c0103286 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 917157580 1250 917156330 917156381
    0x40e010c02010b0a0e0406110f0c011b020f15070203071e020a0b12041e0b130204051006020304050607050f030f070c05060304050a1209150210050f01050a0e040213 72
    0x1c2d01d1403c0c0c01a0b026140d656400c0260a4009030595805a088480002c4031040607014010768401c2c01803000340d00802042082100301c042d40034041c0c1050b088004c0720a0080b80fa0b0591315103d80300c00e0030034240c100d131140c61010611048119880b905905c196880c0c4030b007e9076181000d00140a06c0818410342400304411418190004005070441c03e207a5800e0035241c541203d20f00f0070040c80208082d210700c0c02101c051241841c030851280e4004450891840c081a00210300001105e090340b02c0c03400c1c10040340100c0354244601054032020f81c0654901414a000d00001e079000c071204542620840c0d042c007040d8003091000d0940c038265480380325655400b07802c1c101100c009035000244552020000d0100007400055201e580e240c3c46242e0512100c0c0f860000c0d60601038541c070260314550004808041c0a50200d409491210201e00410180d26012200130011400f4024030707030404640380080c01f8008035040540d50061005103c21019010000f41c0c0d01580d461a0f500d1a278011030300f100c1d81 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 917158830 1250 917157580 917157583
    0x8040513020d0e0a0b070c0f0b0405010203060906060c070b070f0c12060608011a1c0501061d010f081f0f1514101d040207171e0412080c0c040e010c02 66
    0xa6083c6030f41c00040002d2069911580c40c40c45001c0c0a220500189071189020454440e04401e022a001100403a59286c2800c215010f940225030380e91240000400248a900c1d2000580b400203050070020000d0030700300800c5102e580c0c4031580555000d2041801c1800145007028000c015003000202040d0185041c60b0a07010380d140c54001d14603a0b4142203038002c89410910b20311703060701d80c211144283d040d075034100c81a204a1b0000050055401c0502c00320780284070120070642c05a000050708a1607a8801a810b10081940030383c04042e004000380807081d440d003001c415042900010b00058001c049100f64040315191840140280b62040040208075800419411041000c0d54514507030003100380c0042002c1074402048000c0280c07148142c00548480d0305490b40203500c810805001c5080c8028142c10780c11102d2400c072210603000c20305c0c00d0703107401c041a40e08035600d11680c03c0b15055a95070b02d182a40084208603110320803a070100c0d1099449000c3c201d1075601c100700010320780043c100300a = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 917160080 1250 917158830 917158841
    0x1107060207031107121e03050c1032040623100608180715020f070f05040c02030408120a111c030e0d0e09070201020f040308040509060d1e08040513020d 67
    0x107141002030400300c0b404244d00c41c0001e0000d106d8520707041e0030251189410b803405e0160711485442440781d0000300c1d001030040c2d0b02042c5801d07001c0c414a00b03441103514014528010010403202007483c42d002050003e00c407508108418241e8598891200c040300390400198001211041019010706ca000c102d200d82015585030441d108001420b180096030510782d51f102da4912580003000c440499219516200303002c101c4240c2c2c188400c2c1c6070219a100601c00d0f21030000e0007001d01c10b514141141444500020855088424010107007190f4090301c072099416412041680c8103000e0440182490558240000c044c5902441003103800423504480c0201201e00c0040782c40c0305e1b9400b41c07008580c1550030103207a41071002c00302c412084641c1c0d1146c080b030290081c02c00c01c20200c100403c0101c03c100b00c0e50040c02c00e590b41583c0d400000d075a481c1c02c03c0701500c0b5102001d01303e840c0c01d240c840030b03c0040300c1d4a814031a000345000c5292960700c401080c441c42c0902c810703144040d8089105c42c0c55410b68001c1 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 917161330 1250 917160080 917160089
    0x2030a1706031903031d06090c060a09031e0b090f100c0504051302040b0a020708010f090f020d1719090509010f0b2209090b130c06031107060207031107 67
    0xc2050a14014001c25501d414004003400f1107100001d0a008152080d00035020708101104582c1c24204607a000070b58842c02900d104240c0c2c080c41c44107031080c0c1845000c2d2450210283e5a90320100c0c5541c5426084080390f9001402001942c0021004039406200150041a111008003811100700d591130381002e41c2050302080d01824800910b290f41c7d80a0140c805030740007100c0c00e003002c24004030070710000e01c103550040340c5a00000c04c04644c00b540200d20341d030807030b0440340082c8610b495100001d411110f40680007040c9014407030b012070160030041049011103105a0b040d105146a070000403503036802c050300f5100d05003985050448450303405513110009100545034070046504000031508102018013030310102040110b189070040900d00c0180070b441e801000c803031041c03a44926100c800340640f94400c0e103000700a400401c04804031100b89030340302038000070821450307420a2002c07406030140704440c0390224020b114200c04075920348010100d06101c3c2d103801320b50040a250320707803d08165030302 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 917162580 1250 917161330 917161367
    0x409080301140f101b0f0b040203071a0301142701080f0a080306060c070e010b040303030b030d0c0213110c0c10110c22050703050108100b0f060706140702030a 70
    0x9041e100380c1310000f02050403c680d081c04102c200695103215134256801030064061802d14070b8580c01e204440301a140124020340c141c4100545a11445d00c844256144004146c50108010084968041c00e1140c8006004000c103071030760814030050f81004a4003d85011355403d0703a004200e50802000041e0024541c0d1004d007911941548415181c0e0100a01060050708001540004524144264006080c030340c0028070781035850300c00d80c2045401c18042200842c1c5000030108407840c0006a8900d4034100c1c3c1d0310048030000ba54240210208a00780c0f404000c0e031070300110600d040a00d005032107400ca10304000d0482143c0300b410080c08070051018001404940100c00000c0c0001140c100011582652000f02002c55201d203211081c840d0405411071034a4101804240d0760715070490340c100d1f0a80301c1100c080d45c1c203440c08203040303422600411398840b46212541803e41440c4010b8111507000c0c0c800010303d5210211000c0d40701c0300403155400107810018140400b00c1c0c10030500e4010481c3c240 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 917163830 1250 917162580 917162599
    0x216150507150b1c02011b0819020708070305011a040b0109090b0a031e050705030c06070b0a0f1503030f0305100320060c0d080105060a0801050904050309040908030114 74
    0x4801400034030480001411401032119103041c05600c0c0d8020041ca00c3c0c01410504008402d4003010805011188080780003d480403100282030382184d010745a8150094075080c44c0a03c1200d407601031048020701101540680d84000402d076009100100046005900100740f20984c681020f080c0320a8034185403280f4508031556040366400102501950740c8036200080f081041000103001c0c02690740014020302c13900c01040307003400c0d41c00c00040200b80301d50211221591900c08058890450003041600700c0c6003808204041011440b190f0340004c141c50f0001400c00403140d03910f0603100e80c4104402c1c6134820220405c2016070028040000c101c007031a08020b1810b1004040784400e0307481c413010b003040d80c1c5480c01340442c42d076084020040c504020071b0280e680894624550300ca1081c8080c1d0320208114000020f038a0030020708542031400d490703440e21403a81c207140c100510701e80f0150068030503100a00c0145852b88852265464031401248a25202d600d402940300c211050498403500925406 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 917165080 1250 917163830 917163869
    0x20a02011b27060e060a0e09070905100807050306060d110708190203031924030b0108010b0f030613030c0b01060801150e090a051902120a0b1008011412030a0216 71
    0x5500902e040c204172500d035614050680c003102d0011080350000d5104101000340b10041d900107080100b164401e0f2064081c50340c684000340c414400855805000c60b0342003000400d28075100780140007000c41c400001070b42d160792900400898001c414216101600010003c45210750411550b20380e402c588000c41c90342c5494012181302900409800403201c3d00e5420b44800350b01d107882c0f525030125054559651856481c01c02619649083c411120f25503e0319803d060103041c11607000b0b103103600280080840b9100c000d545920011105401c1d0204612564811300040d154402140241110307910001c042d4106501c03200082d80015005086c840001050303e65511951006036100103280c000148940d01d10580d050b19051144a0400540c0300080030000c2580c0d002096006141150040040e460000700b80000010760f29202d202007001303a40100700d40c02d2034001c1411241e6005e000940f04011070b4002e5032840c1c200d60000c6002d80c0100c0301c0340f01382030f40c4500d0344801845010505584180c1c007 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 917166330 1250 917165080 917165087
    0xe01030c1511010c0c03030b03010b0603060609010c1202010609050606040e18030d06030c2d0306050903070c0305060609060a0f091104080303010605070b160909020a02011b2706 78
    0x507100340c400c032440035580707082014007030880049602040c030000d010199002e070b40180880c4482d201100800d28200c007500140c281481500e240c1032005e0003152464031f4440c200309250b00035444460410491644c000005400c0d100d012600c400c9a400201e032041c102900c403410382d5002001036010b040203100c100801c43c2140c600a410074080d214035424064800c03d058150303c600c03210140d29504040000081210006e1144104c1c5c0348440007000303c6000304110b0600507415001e04050040004080c0701180465221540091811044910b00706c400e80e01c02403c0d0700154800e07140d0750001c6040244500340a4106c50707108208590403044103040461200d43d035482809001d001c240e031880b81c414000305a0b0105e40280c0741c1503049039243d41e076030300c001005d90f840031004490303185403200030840007400c2086070845124103455950100381495401300094108400c420115074031005244400e0504013003220b04248031f651040d000d908a201c0044181004002d540c01c0c1441c010020400e95a2 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 917167580 1250 917166330 917166353
    0x60602030319090f0b1e0907030c0e13020d0b060103050708160c0201020a060f0b031209100503060f0d03030b040c0507020d02153a02130e33010305010e0103 69
    0xb103000998071010b402d00704030f032603107820380103140000c91014000c1e02d804007040141020342100d400d110665441113100d071203110500c8010080a0185801d128440d01d400e0030982c0200072481c1075031403644c0c940000c0e00490f4100030682d8900700800038003000c1d581c075026440d4404400d080414443c18491202c800175186031155400304118207008100310780c404d0094164680c0c20410901044100135110001003101181d428800d204011903421a0011401900c0c21540014103020001d00380602c1070b0703901da10042445a0111040300c40704d00c07a40c0c0325081d600f1114041d680001d088101d003024807044a00b4044408140002880076800681d1450801da42c0d60f03906444814051101c00b80c1e4840d6030290307003402d006c902d01c50883c0c1007541c1462280e8074a0444000c03207401300c0704144000c1204901c01c1d40c280c954925942031052010450000c002500950411300c242d41a4090308503112000481c0c20340b40d4400a00a00111000d40e81170080502502d9a882035a03019455a0340c0c1029004 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 917168830 1250 917167580 917167621
    0x3090b0a02070305120c01050601110a33060806071821050d08060f0105040308031b0d0212060a1403031b0102090d0510060e06010e0f0406030c0b030a0606020303 71
    0x96000400c92140c601c24403a020080d07078840200c4410000c01070603100d564110320310481066190400103440d6612685e031810002c1d450700c0240102c01c0c4562200b00c00c80f074a01910088440740c0b0460005411800030445180412115000480a003804201c030304004014190104000f00a18200c0148122240e8501150000c45c40c004001e441e000c482043d095145102800c82d0240c910491035140d001900b040c86040100e8407a4050800e0100540c0c0c5030207903000160600e00d0138800914132030448a80d8001d031041025940c5d05180130071050405907480300410b0380e0382c642200c081c0520380c1443c00c8514090103200142911080200001c6992401030030102001000b06030010f20040400390b040f59248600034045000540060408558980c45100720b003065528040d030014650400c3c125690080e48140d6900c1d18940300c2c0d0b03003080f036035459804d0015231150362038400000040d0502c4960004180c450b0220340c4034540403179104100c48840e0311030001c2d5002001002445160000c0e41d00305407 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 917170080 1250 917168830 917168849
    0x160b180a0b090f0310062c10030b0601210e07050a14060d02070203030711030d110c1215090a1403090105030408180a09240803090405250918090309 65
    0x803c1c10300300207442d20000b03989000d580f52070300a0100d0014041c100e10b074600e0ba08400304c940307803001a40a803004030760100c0c0c1070103000c41c0302d403414400900c415640ca40c014905142001a1131660704080310052030343e000815085959652000b85007000b03000b80c50007001c0403100c044000d0b1402d00700760703420380300c03004003d00c035800020302038403203903a00d41c181c171481500501142c2c0c03200010302e420840c036082d44220910920901c0d154448461180e59448103100d07111001d0050700d180641404140070140c00082524000d203004540030343d4200071441c0c810582e9100800500000c1d003494050008040480c07101904200500c3c032160741c201046940255100e44001e80d5071040c09000c00b0000348400d2690b0b409184103c001a0300030003074000301d00407111824545290202071400b803a1300c41c5070b48207415407034001744240491031400345d2200d0381c07001d5440c45c007020000640c10343c11184400e08050f040801c4003441c052000404407a00f1000c0e040103004c041202c23440304c0d2005440103420f0721941031034 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 917171330 1250 917170080 917170099
    0xf030601020a0501060b070b130f020103020d0b03160e0106020d0504050d140a15150e061e0a0617010e0c070f140706120c050715090302160b180a0b09 66
    0x1281d01c2046407603203558000d0020401c281d1180d003402010b81c40004241c0301c1046180110781c522821142082d011584032000c800040c10b40c1e401540030b03411102c1d01d252400c2c0c0d00c0d000d021f9680c5050040d02c912880601e40c0141031802c040c40e10300d010030181c000c401158480c4e001c40700d8441d04075088405a8070110b4510402c11080e10b411060020380b1a1001e071a80150b0580c07070104407600600c40a00c5003000001c2c04002e01c410003107400307010b0900c9290a01105500400e01d80e060a20036525051044c1c604000300210403000b056401c081c55202c0e100042c0b54605012800c2454411103000d048400e4070814503082c401800103c1c0d0141510203044a4800030040040004040104291591103410f403444591b0325030016040c1080601d8030411503041c038103e5004144264200c4000a0303001c8500c1106c002022460740080c800d4041c21800d51148030100e000d4101c50300d140310000d20001800300c6ea03c000f0071158030f0380c0303660703031030901c0c2c010700600700240002815201510b80548050303031107500 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 917172580 1250 917171330 917171341
    0x60c05150c040308210610120f0608070b030a11040302010f0807020f010509010204050a0e060901030f050c0d08030601030b030a030806060708040906061e170a0203040f061d010b0a0b0f03 82
    0x301da00c643c0c0e2004090b402c00066103264061a1404400c4401c40c2113038044150759a50140540510803804200000e01c101d0801d4001d00480e91020303501c080f03032600000d4219203030000da074a4003140e40c00c0100301d0403010042040c120501c0c090303001c2114420175154103080c51580044c1c541c0b80078585803400c0c48080800154070603c2040302490b4240d0400c001d11150519001442c002d506c94090140241540303803010804d41050380b00d0300c0c050040078044210580c40c540342c800718951201001c503aa40201107891115030b071641e008200c41401000159078a0030f259000ad0120b840420005020303800003410703503021940001c1010791111080c1c44160782c036082d5180c03040d03141c03150b6000140510300d400c5c0003051555010030309a91403014500c1000028951520540e51000c1c40030b20101e1015010000410004440d0091500140304441b50921110282c0c1c075003069900d83c50ba00301c41c124239010070b91906002402901da05200030f40e11500217505042d19180280319030a0135105ca20b000101150 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 917173830 1250 917172580 917172601
    0xb0c0d090c0f0503070f180c09090204030506061c0c06050306030c09090303070225180908070605091c020c040b01111504030e09090d082d0f01060c0515 67
    0xc11a5882070462111a03180e41030745545100324082c150081c4641407020a40f80750b0040c0c603006498403a0302c0050000c0c402005400035207051040b04d42004404600050100354074005030000d9889a0040d041c10b180c40300030700442c2d55104208096100d001003200003c076901c140d54205480b0030345005552999504042031520b020422400e802c500f41c0403c121820801001031805002698280c0e00c0e000180f104c1c0f41c0e0080f942580341a4101d1803041d0070440040c040c1103c28100e00c04000106841d540c0f0b88600403150080d04055035425118020003200034400e1162802241000390121060124a20001e50350f10f02d03082070502403035a0b030b1342c0c00040fa80500c50000d1041071034012242c0f40c84c4145d000d8100c101050b0b13400c8012528041c80c4030514a000718245105010340c03402424043c2d000b4004541e9030001510345856a180000341c0c4590b2a40c2203200f072130b0500c11101d104100d003058500c41d8500303d0141d0090081186c3c3e5410400001c6002c100c160640107550340900c0c16440750070541 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 917175080 1250 917173830 917173841
    0xd050a0213060518010903051207020312160201030f020a0e12210a091202060909151215010b0f1603030b0405070c0201020c0a08030a0302160c0303020c0a0902070b0c0d 74
    0x40114056004000340042c3d105000301188030788034142e80804140d200c01510380b4562800014080e4011504480e40400c3c1c402c040c1c00002d00040c1200c060340c0921500600300c0c0c1c003c80e0024075000c2600100300540d40c00d40107841e00c070030034140218a406d0b03d2903402803c101000404a22403100c03140303400001001000101e124a240c07003031505065038001c00d02c1c6510f600691124000c2508010006046041100404080381d0040e0401d03241000400800500b43c20081180c6650403544040d8241c0c2d855400c13046102202440c0140855400220042c200400580c0041c5040408004500481c0c00080070f680142c0c005c070b8a080e600c10303158a000c0e0060b01d0030380c00381d90b002854807041100d2281c0c05030386031840038000e8007500c1007503990000303000c0c00d001350340600c44156000f04140c105084c800c0e40140202c483da03034480081407403240d8445d03000001c40d50080e001a07120080300103840c80c04803a200014441224118a00042175450010518000b4261004c0142c0880d9483c580314568119 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 917176330 1250 917175080 917175097
    0x10e0601111002030114130207021e0102030d0908030709080708030f0a0504090f1a040207110906041409030421030207030201080a3c11031512150a0f0209060d050a02 73
    0x5546940e1161b80030441844081c020500c40c0c42c0e1480e80400791041403007280e0f20590040c0000380f640c00c981c2164401d2000c00501d407070440c0b204200100e1100d41c248100210944600005640d03810000b4008084005a8100307400381d800c400c600300114400001203603003501015480ca6200c2c20071500549403401194400043c290800005079100e80841e8000c2c1c1840d81c030080d8a078100c1a40a052008038000e00070300400341d803051350943c94585403102c2d02c1c2d40e10500c001c2c4003041c00ca0345501c2c41d458441040d07030f014149500c0842c05001150803d10350602c68801c040401100351616100259a500d01e840040d05100b40c0300080f40101c00c183d0482100012801da000004e5050500a00654011060741c0c0038007240c801c031080112a8140214961010301d50701e002c2c2980c440c3c1c3c0034464449620105243c1c0078050800d950183e44003849240b003a04018410304003c1d02c0c3c0032402070141c550002988041c0c601c104040f1074107030303940010f032440e14a4a200008031655040b012200a1040702d28 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 917177580 1250 917176330 917176363
    0x22121a0c27010903050d2a42090507052b0503090607120f020c15090f03010e0a061410090b0301062601061d0112030c0210031a09010e060111 62
    0x4013400583c0d001a94902c9007082060307c035181c80380e41003c140d804020144018402d6115440111080c0103403604211a002400b0b0742150140400c0102c448440081030740c00c0b00191114208414070030207100310303c01804280c070300c145510350030700c201882004452425500c00b9a081400c04c1030207070400950b4080000540400d80d1000e141c2810780b80021114810400202500d4103520168400b0656400d081400f0b448002582c0e5140c0101ca407036007000c0100b582207040c000f1444201e55090080a00c184280006000d480b409400d02000713403007101004070b940604400c24001c60b40321030300d0110100c41d024000010502c100b4000a0301503d00e80d402090305440c1910b900000d1014110304440141c0044020403c0642c1c4000c20903140702c9040c040742d05c801d80f40f401000407090444085a03414400c0c03402d000e000d0925400107a048104554580020741d594014680e0382141c03440f11503200d881119111410b615083c652000b00100521035410070802140c44c8140f100c0800504589962204 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 917178830 1250 917177580 917177593
    0x60108030306090c04150509040c020718090503090a030c1a0a0203070b130c030503180a081905030d0212010e060409020f12120d0209010f0c0822121a0c2701090305 72
    0x400030151f2300184031030f9110b180750000080c11140005031040440d03090786040301035010a07a40c01c8c0e0040c0320041064559010421010f8115614011280091803180710a08a50381c18001408219241d000c0c3c0d005005c042040130805098000040d10b60f0540e010f0b0f1107100326500d284074401e180c01010001424000310700c0c0084100003001c405000c00103d412090240900c500c4200b162016061040544540050400322a83c03540080c1415203107010720200ca2506848000c1201268450800000806010f41c01030141e18034402081d90005400c840611010295030001010b00341500640f40c458000d402002c0c040398000d010b2903005091444249850351303083c4841801941c0602d0f4150300203402a1686107580340601401c424103070b0400d407032504003061010700a501042c40c0300300d10102031040320005016405c0000c0009001e204010200620f00300c2c0920071315001000e0031418151030309000416955010303030500794032800054070300c018001e410700040e00d8900c1a60005040750203003a = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 917180080 1250 917178830 917178869
    0x7150b0d02091801051b1c140406060603060b07020609040c1b051615080109150b0c010209090a201c09121704170307020f030c011d060108030306090c04 67
    0x224a20300070300b2054070081c00b55030b0b82c070702c2c04e407851b81c01c2114001c0c0b081e4001c1c0100b03094011301940b400d0000f2401c0d100040c0344044003160740041c1d44215000c442d580c0c2c582d9000e008155040c0548002000c15010b00303810612242e000550b6400750f80c070410700075546c0b0010142c1c010b01c122004803424844105d0a4845081414001d448480b561030035900070200c2c10000030042d00007100d190000016a03120440e076400c254090000d04003981c00b80c82c41454840003c02c000f02254003d007444003400c00010381c0d840b100c2c801d215603804010400084540780032500c0100c180030851250038450501d25003030341c4451000f0455805080c2d40b5512110303525100220703042101c7c9007264206d400c07564541d03403c1c0100d4a0001040c004007201e00130024120000315210303544801001d160002594016583c1200ca0306400b545550407040064000da9107070301503420788840c6c4221110120401601a01040d81003034803d6030317244005001f05026907014000144420942c0d0260350250090307042c80c3c60311f0b04c440c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 917181330 1250 917180080 917180101
    0x18060e0f22051b0304081b07090507020c0907050d020d09210914010c030f1707020319020703050a0b060d080a09090b06030f0f0601030f110403031407150b0d0209 71
    0x41c16030703030351003500d00030200e1034000940086100c2010b00c6262546559140d9a800483d90482d0000e010503a00c000200c940c0340c181031000f0800b400c4028000600c524103800d0003882d2000032405d06015104100901000540c0181105e1b03039070003150303005a0b031003180201c42d000038280400090b1041540003075088200c4922004510140d4081d40d84109444d01d034035049845030360818501d408505030721400e400081c0154680c61481101e030401c01c103182d19807813140380c204130304440f10b00050300000703184c420300e0020500030503144c211480102001411603407402d030f03541d0070000c020f02890b01140000c1c44990700e441007565100c1d0302c08000b9403600c007030100103069509203014103803206050440b000190308000d025280303ea81500701c0e8104a440c0d45062120720500900900c0c1096120743c6900d407514082c1c0110708403282038a42541c0d5491550900038460840070070b18241080d010424540440d00d101c500d01c5001c4580320001402d4a00d500000350903030440100250400d03054030402400d10f24 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 917182580 1250 917181330 917181379
    0x3061501090510090510031812270902181206010f050f0d020f1504121110051b0a1a041a060102031b0f01050f011518060e0f 55
    0x1c0c0c840801d01625401000180d95001d29a03070005a882c11041040340f401a0810b8a10103180c10b0006210885801c08001000c0d00e060a4450489241d0242034441d8441414a00c24125014214005e17070000d0204d403285106101e0400120b40101d20b161080d499000907011680d0700500868007007031030810441c0c541100340701d14103041801c1c680015403405c044500300c11800e001170039581c118407964200f100c080c017502d081503040ba0040040d000901c0b03640004001070010030403a05408a440e141c5104940d40d012840384c0103080000c020484540c003c1c003070703c0e880080c02494400003500038045500e0031207007842c0500162110020545400410749440c1c0c0110700070800c10440c902281051608808107442c032a0059004005081520b0034080c0003042c81e4407104251124129504070160039954140c40566000103503000402c55290390218036000d900b4141000186400fa000001c2e8152040c2d10030001031200f034080c0c4149039621000b40b82c4034407000078140d00c80c0b150009050f034481075 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 917183830 1250 917182580 917182621
    0x50702121c0c0b01091a010302031906090207150c09170a02150301080c1504061b120302120709030201080408030402030f1204080714060d021b0d02032106030604120e0306 75
    0x690301400440d280c201802000441b0010340e400d01080f00c0100c00440c003d600040500d400140d03503460030703d59044113029910040c0340c0304d1805600c4840700d00b00810042e410b20f146200d0249000c500c000001d0300598248206e50340c1d403154003511015044001d05006c07800c00002e41c8040c482c2c821112480d00280514140c8410360115005007085006011020202103031000510006000c00c000300ca101d8100001007582c8414a0408240950345800341c11403d16540c1001c2a0085401c401203038012070103951080319450480040d86c038540010381403500181000e0710703159001001030306548041044940b0390f1503201c111449042d0101410b40700f41c001e03005c3c00e03506010301c2c1130010309800b4200c0302210b204801442c103031130f2244104240c00290b009140c004068452031000c6403090f501404882029000340c4c01031a0740b525034100a00342080c20114241640d1401414450903880005016601a0703001c0c610701107410b4480d1050300c0e4040d001e003d041e407600c900010010030310b00220580e604075 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 917185080 1250 917183830 917183843
    0x207050607030608031204110102120f04030b0601171b2502091305151b04030b06010e10170702010e07030804030516050d060902010512071106060a06050702121c0c 72
    0x1544c83c0c81c11030741c036446045115510155410046000300e100304404202c2e504050046410119090020550540000c032181d0620a00030030304206026510081d01d51056091818140040d80c55182024640b000f07000f15031455180b01261003400491804c40d2404030445920800044c00c40d100d0945840040c417007203000e10106000f050340329074200d00d81d802d41039106d4080c1c100c6082c288442d89418000401032183d105800890780c07003406207440113101441c041d2440c0c0c00c0c54a407220005d862115650721640c041e1481040e0b2200a40e032003404040c80c51240c0e401c0c80e501c1e40319500308a0141005100031200d901501000008101c0c00100401c00c580c03150040c0c440e2180c0d001f480f000d4404617807080325049601c0700541c4000a0141e40807150035403050401600342824410580c041540490f0b004011907075050312980d500d14208031072640140100d90050080e030030000d00411074064800b0080c090b415401140d190303040c050220300300c40142e8904440c10001d8410b801803801500203002d41c0d00 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 917186330 1250 917185080 917185091
    0x90f100b09030a030e0d06050711010c1407060903031508030d0b03010504050606060304031101052706092805100b01080702190206071a0a020c190b06120a06020705060703 75
    0x303142180a580450200402510484006860945540146080d0f40f135014400d143e01b803000900501c2114012130250b0384203400d100d103c1088500f1103020300e60b410203218030004070342c80d06400c150450f41d4966000d84c0214540f0b42c9460f090b07000e00f581192a8880c00d8800c400030503111000030141a00d909103a50034000f2550b80c1d410b14ac200c40f82500c000d49284c200900003200b03410128019030308640700b460b0150b40580400a4a82102d01c155441524680b25840d440c80e031800084003000c110182d9000f624040c280b942400740e4900075000101603d0810700c011300300c0403000c0c00d44801510340144c151504079007401000001001d5034503e19000c510240b010800061001035038444052172200b40300101c0c0110340130010a500000004c560708400c0030340724034518500303c4920b030040984110142c2c65010300702000382044042d130011591282511107682c041400041d85642044003519241006440c0701c03150b034200706942101500050000a640c010400e0004145119148a40c0e08009 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 917187580 1250 917186330 917186339
    0x302090315061c170d0b01260a0b0f0301060801020307110a080919120506180d09052112090f0a050607060506030c10080411090108030409020711090f10 67
    0x441c91020781e02c1640201504001c001d24000c2500b5040c80c180c041c01d10220010080e4030068801d40c0180b003000003058075211880040d58100c2c0030030017a818921000c803940b40210289038447d91700104030300308058950542c00641d44403d2031840160001500030b001680e113800780b05020758426210300d00060000301199580c49004900304c80302d6a4040311551a110b561800c0051301ca034403141c02d41503030250081c0021420380c28081d0112003403080c4090481c07450300c0500345a12070011a61850103410041445070301035070241c4a01d059642c11600305c0e0145800e1221a40030030b04054200340144036194100d1070f40076071b04c000b41c17a07e040111020315400e00024244405010786200b2181c009a0030f021401c000384250304400d911150140481e0030f0742078080d0019030507002c02c0210101140c24081072005100e60148650035a150030342d07190480d03524224202d996441517100d40035106501142ca042084981d4521113414039000700b80849a023492544031103006ca00395406e0040e8414180b0028 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 917188830 1250 917187580 917187613
    0x1d030d0503090c040c09060c1a07020615040209030703150f0c02031c20090d021011010b0d020a1e180c1b1502070c0503060907031703060a150e03070603020903 70
    0x410381d840d030300c940403549480820343d803071188104101d510b10462740c95480160003210030300d8400c2e1003d034000e0170b985c10070407090b016081c101a01c25000ea0b004000701e9040e074500143c2503003129072002c2055851031807009074000400818860340319142c00c0c00340210844d64008060540c2c682c0180003c15860442c6070309004480403815600c42d40c504a001d4604100e05410281200c071074042e03c21407900440b0390019400170408510075000c1181c210303803410601400d100f20f40c03000005071002c0701150416000194508194410318140b0302503000104040f40c11070580100805c402200c80402c02602ea205034098400342e180303600004c1c02610852210804214110031043d0842e580344012401a0042006035021007402d8030100c0300d9820014090710200b100b0391051241c00081c3c40380714110700d415103081840c2000e1008855060092002c00c0d9540380300b0318101e89500b2284075541a01c8103003540e8858035010040c0c0e06019040001480d02e8041c4c000b007a091008030191421304001e41c001c2d8 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 917190080 1250 917188830 917188841
    0x3070c120819022a06010f0f0e0408070c080106240503070e040c05041206050402030c01360b0705100c0903030c06050603010b0a0f060e01030c050a1d030d0503090c04 73
    0x200d81003110780404078001407403580107145842c03080041c0c011010014000340307a036513070b080001d1340e195200d1030040100d07150b040c0e0a040a407940d00e2040ba44240b8012444078100300281002d00300200004042040080c1819110018070880c4020300c586640c0d4100c6284075406d105806e940c105030701d0580409607100304112031251500d074880042c09030100044c80005d04404040400344007041001050b180f000ca0003a1007454030402000c9a9440c091040c5800d0010300041c881c14003130702103110f21860762048212600b0030124100318510561054a40c1e21640300d95000c4c911104001565409010b4042803480c1c4c50003280304144200c407000c820803609036000b48006400101090010000901140c0050b030f08600000e001040e40d81130100000d6540002e5445510300b0048020204920f03038200c0d407240801c09003420100003001c41080007801078842c8000f400c0c20000b2490002011007100c4100e41180c920207811034509003001000600264070994070321506104054508500340380a0040 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 917191330 1250 917190080 917190091
    0x3041b06030e0c150c1005160f0f0c05010f0e0a050709060303080c0d0f0c0c02030705120c060730020d020a0818040f05190608031e0f071514060409080a05091503070c1208 75
    0x22b00d41036040711802202c501c540d403141100c0300d54030340300d20140c0036480f8010407660504074800381c01c0450031031403d00c0c42c000a540c41070800505001013000441e4010340c0301c66228031403000c820340d42c4140c4500540242a940f40221443d4941080310100c10350181c60b4031031217031090703044641e03c0752600c00300300030340c20842600d05d01503008400c0340d00d40381030410151006910418180c00c20303550301c20b52032001d07203c154000240705000d001c541c803c05504000e0002d201e00140060a100101921200500d1003500c0111903101c1000c0c0014050f5116588040c400340c40742d01d01000b031400c1080c04d80c04204100c00100000301c0c1400c002103280318001c000c840c0b0400300b40b0606648414016100340340798215131081002000144540c80203d4804044094407000340840003500144c85100d40800440142c0901e000350301c2c10041d0000101404c0440700300c54480c2c100f80da06d403a02a40007503122081c00458105140020044c044419008095020a18400e0000000c03032980641d0441e0a000c1c100c89 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 917192580 1250 917191330 917191337
    0x70b040b10140f060c0d051306050408190206120a0b0a0501030506060a0305060d0c06020106243e0606090105120322080303041b06030e0c150c1005160f 67
    0x840d01400d28100840580c8140c3c0904a90300346100b000155040881d07035420940407407030002e00000b004580315140006000c5a00b0b160b4202420010713850b544200c0e01e42d05c0c1515541c5c0e030f0151400e5503111800d86030b014410020502c00c503d802000c540c0907101180000b400350298940204080d80130340289441201c000d04514108500c40e5401c03005010081c08854014841c00c00b0700003c5035007134445001400058001040d070520303140a000e202c5200b500c200381d011003645c8001c44483e074408100f050403480115184000c80300c0c08048100c00001c0b1840810385148102418489800030414504c04d8000b2a115051030303076158180080c4c1040590220400c0e0004c100b21802c06409444544c80d00c92030081c6080d019840b840614a59401900c00f582d410a900c650b02c00e61404101d2210090525854280310707280ad40ca80e40c81e690021640003503c07078100c2109080e681c544800980740010039407030031294014000000c1400801042d10b074035441040000044030b40b28042c0c0903c036010840755030f = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 917193830 1250 917192580 917192609
    0x1c0f0b120d0e0d020f130506100318030809030d151d040b01030f0c0506070302151807181104030308150103050c040501110a0206180108161e02030708070b040b10 71
    0x2010011900ca100000b2030784100c0034170008038180c81d11048112040c0c1d4991000072682400c4081010700911005040c0403d400d05500303020ba801c0710b8a0b03a044543d854209588580c8407109818103501488011454880c604121400c10300c0004642504403034664414412001d02c0e2503220780000c20480300648006107080040002039104020b10107401c0c0180403064900c0d80f110005801a2300ca481c081d00144e018541203804405079894150700300310400191800014000c0c0c140d82c44034128858440a0b81c0e03003501c100d8090030260008003000013200c602030360391900ca1a0140030f49000360b41c02d0310041d194405214041d4068400c0c507000f41c50000e24141000d1510004640ba0760401c000ca9029002e10342c03502c03005031281c40280101c0d180212400440030005c1000615143c4010640781c10300c0910641c0050b80d54103c140110903420141010b03e42d104404000c0c0c0c034500c5407240c018200070000136641d09012074a02014010383c425412030341e20b502c50040540240c1558061001102e4004 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 917195080 1250 917193830 917193857
    0x43924050c0c04060306050f060f01080a021e0a0906080c2106010e0d080901030f05040f0204050c07050f030a08070c12230c0a2904081c0f0b120d 64
    0x1200903111914590048074100c0b00c1100c046000d6942c41d138000c5509039200d01c1402100d80724180c84c030783e000750b05171058000c98401c0f60000340007940c080c041d01060703540054400c0000b100c00100644420442c3c3c00180d981700d910304000d10031b40980c810080021400c802280d5034951100c111501c040110484031401c8a20a5a162440708060100e23410300001261000890712220120803201d802028296143d44c200350000d0705880e6440f41c03414180d4501420040080c100d405548400398060360009181d540d8103000b40520b02c41e02c070028065204150060b07007000400001403030b42c000d05984045164480b10000d40f111089204020078240840102200c4680700740e0303008013506500e40c4403002c450171000090600f98000304802e4015045405a6024403001e2514420100c0c260900a00c900040b01c00305c3c5a0000003030802040002e0006003484240c0c0803100e0100074128510040103c0b01c0d0301070108000b040301d101e40c140a00c01401540e420728501080903c4656245e80341c240720004075 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 917196330 1250 917195080 917195087
    0x50c042c130b0c031e040c0306060902070305071b1703130e13061e020a0c050c01110d1d12340902030405010216120809030f12043924 59
    0x60880c0e900c0481c0c210860300b40a00344801724019401805000c2d0414214100941500c1d07060b005869003034010400800041d504c041140c0c001600001c0744010340302a4540e00d520300c80c140d0320400300031200721048401344101100600d41c2001789103001e214030780e403045800742a01044a90806000008804501144494000c0022949904c4444080c640d4055000d0101d802001002d0009a090101041000000c1104010f46170090038541d80c20550080c54641e602e4000e04581c04021202200400503040002c142409881c0100755404c001c2840300410b90303400d258822441c00d00880e07a401c0d42c030300090b00c441025442c40d00c0d109440113405c244600c40079500c041d10464082d98208121100b10b01f0040503494103d20490301e211a0144100000300401d178060245100c64108100b0610614000070444444410300404a209070303889052204103852001c207a2160550400080f901004642e080a1468a0207d40407000d00ba22541c0d0080141c0040c41140c54000c0c800d409001c10901 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 917197580 1250 917196330 917196337
    0x2030c0c06060a15050c0f031611031b010c08130e040515041e080403060203010b03010f0b130501080403030e01050901050a0c0e0915060c190312090b0a050c042c130b0c 74
    0x300b480c200d4a070031f000b4240700d80c65944491201814191400b0405081045142041195542c00c600401d0310841282445102802100d10a4140080040f074401080401c4080c2d40001048a2081e040c0582c3c0e0154004840b1081720111400d005080c0040111402f10200350700840e0040024809a4a02e501100301c442c00030000b941e6100050000100244450004501030031110048a441b0351400c210640c0c03901c0d05400000780c0100520108021100516182e800c640003464610419125401c05500918a408200c1159402c1c0010045510710541080740a81c1080d03008001c90700700031504070b61452080465581c00030911001c42e00300c40c4094130600f5a000d0040030246400d2000112900e44612003003a048030f8500c901030304060542101c0e11000703042080704240007800d99a614180401001400c2640090b030741c0e0049481e05182c9015a00501003100c8500c0d0310801034558010200703105081c0300d01700346807880026403a581419240000e03650088201b9a2908c0c1e64a52202031740 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 917198830 1250 917197580 917197597
    0x70e0405060d0602070f050d020613030e01030f0e0c010e0105090a09050a140a0e150412120b040f050f0109090503182d12070f03030c021302030c0c06060a1505 70
    0x4080d0042c0030702246080c0f00600300c1d03c0c443d05504d52921140c2c5007480c00c290307607820708005641044040001c03420002d100409007980c545001aa00035003280164002c0a92180815402c0e00c0c101109180b00340002d2084242c22090b00c51141a201c0e00f0011500c40c490903100c181c0000348180304200340d4081d40c2207650408000721010405440c101241c00104d14101d40785c0016644074140b218080c0024060340c0e0f5030700c00d0350407070503614038007070f2a412004254014003008021581c0a0444520940d9001d1004005c0041c41840740703240030341c80da0015210644401d807220800340000500d0509a2040c120220b0740034025609185103000c0400020a1078140704c2d411034050503080700c2800c1400184a021141900155400307516003062000741c4111030540480c9a00902052004c40d613008030517411268103241006030600e09201240d250286d00962046490001c82404011400300c0003404c0e040001a04071611540e0381d400300041542507108103001035005290b02007000b40f107030004204a2 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 917200080 1250 917198830 917198839
    0xd050405070b070f0c080604020603280e03250309050d0303060b030f0403020f1614012d11010902092e03050f10061805071b1a0f070e040506 62
    0x1d40d940b6142c4603a540104000c4420360a03d41d020010000354540c02c5024203041e000030005803400713a02040d428070024061000311400d203c41e074400c0d5007041c003c2c1c05c5400c404c5001401102001020107650350010700200d24900301d4031034080c0182841e83c1080994039090740e40e240500740350905228a0b040260003d40406440d0b5a000c50886861310055005000c82d19a0019629043c14000d04000d034200424403a600888120364184503082940b0058800c05840e08001404640c01039139480b001204e001e1160354100d400308403005107441c00d80154241904e80c40341c0034004500407030880d080b08100950290b0040d01280c6110f0302264040b41110b440c10101c1ca01d03050a00c1120313012117880d13000300e410b41e012010b4440089400e000310030030103000c840d05000c00c50030032000e282c951322003c0180d030100c3c0e0348400107031245200e1102d400b041700c0426048884000740c0d040c00c050f820a0032000b0300c55905500301142c440d03030548241e40c0c824600c03a940d2804240c20541040054200030305602e500 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 917201330 1250 917200080 917200093
    0x50607180909050d090b130b2a0106050a06080702190f06051302190503070506030c1209030306150313020f0a270e01020a1d220f11040b0d050405 64
    0x1c0612501c82d022905010308010080380344003080043c14404942c0110100d43c000f44034600e4010311a10002081d0340f41500020307203404003815001c41000b83d036400b00017500d0050711805004003043d8481c40aa5000342c980103401911041c0a81d00c00c0301c1540d8400c0103900454034138139100c03010703808480154402d00c231440383c2c02e001b9240c07035003960307400e583e034902c140c00440c0f80204615282c00785c8803140b01c040c10b198100b5407810707000a4880800b0b1040350b00582c00040003413007400502c400c40d45890b5031100c0e07600181c14050b60072541c9400c101c07032913400b41802e41c1400c8510390103282030b20300c210340d100b0600c420400a942446421044c0030074890b0000c40241e004140755100c841d00540800101071104072030508184820f0031703035100708a5050941d00c104080c1021640c4210354000740503180d641c420791800d106021844068040061415248444500802e04010341e00021010f000c009400c0c0711050050556401a200310301c1082e009200400000e0543e6403503412482e4414000d8050303552 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 917202580 1250 917201330 917201339
    0x60301150c020904060b040507032f190c110405130813150c030905120607110a02130e0c040606050a0c0521040e07031a04021b0a0b060111060405060718 67
    0x1c0f000400d4508035a00c684516802d03866040c18840c143c5c0c0f21000d45020b001c11140b000741c24003660028000c0400d02c5401245590f0251602e4040b148a0420512013513aa03a40825001703190801010044404011b807150902152500380101b1740070707401c2031044c158062059680c0e10300d90760000300300d80150200d507080012046444ca0f6010140401910340e0307241c1100354600108403a40c1908030f50f2050f585150303c590f004000040d22907000c8404c1c03c005182610000d621840c0034602c0100951000301c1c03002808040809402c00351070010301c042210032800c1c420080109032a800e00a00000810506c2984800c51040e01c032201c8860059050f505440e2425513659107038031040910550120002500300091030000001981c4415145400c001403e450b05842210f2440b8540080c1b20701d4000c903121010908000c0c0e4200320000102c01c4500d1a03000303141010084400301e0310381c0e010031080312000300c09140214040744202c0e804030180100c0e640304101910a0f075260601d07007240c50f1b01003a0106 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 917203830 1250 917202580 917202589
    0x702120a05010c0906180e0c160c0f15020a0303020a0c0c0f260601060c03030b100c0b06030a021c060603021018301e080909070e060301150c02 63
    0x50103070300610010400a501080c003a1a407010340d0b2183c01000840b1304508045103640e940d52060f01c2500701c4004840c0c40c0c0c004800d0a6000780d1403501103582c02c81011204100c4042601012a1000b140c001c0070103550f100180313442520001000c0c0941c015900d0f10700041d101349e00509140d040c03801d041c00d4184d03443e200c9100118664200e040000b80c0c0071010302140e404e1104440c03000b100ca2003860440980d503442d80f42c6649040c400c18040c449601c1c2d40343c0805000c0c1d0081028000047c019101da610341c510001e200f981242c200f0b50381207800c0b00214444c1c0c10041120490315802502c1d2440510602403101003118040c2c4017603651541da040044010303925600304803000c015035600c16681141c183c0442d1115900356021b400e01da002031070b0a035101042d51a00150354010700d6180c2d1510302043c00c0c0b041010180682d54800910380881d41d00405c8a040003500701c454050300d0303805669541a030280c40c1c1c2454165003990100050004004145141c0d208559114161a04481c0d11400f640800e = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 917205080 1250 917203830 917203843
    0x112030f1808010905070305010b0306060a1415030705090406094d13080705010c08030912040801020d050a020414100e090c030105090907150e210a0302190215070212 73
    0x8417101d0b00820030400600109000e1060490003c5001c3e1a1500380100003910300891803084446006500c0e1201165688100c0c0250710740c400641441d90702c2c0303080d1100601540c0b107942a01d101e1480e0540100d6144803070300c05c54003000b2010512410760360711040d4449402080c030580e405240003d000b401e81081c944000955042100caa03456152a0803212418402c1f00b280c1000d8101e41c0903240401981e80d000c5002c810590700121150b5070383c1c13103800d41c6038100312200c140c10031140000a4001a4202d0550040000c400728000c1040b05880c1c94511344140d201d00c2c840c1c0d4461400e840c41c3e269041c604407038500c05011150070240c4030102c07041c021864441c012100302948400105c01003255042401c08560f00c90f070600098100301d401c0010071140a02c0007085032040110f2100b00d4001c1e45c403401d182c0f060f0030f02c030a62510704000c2885421980c0d480031050440c0107015002103200c00e009280e010541030f690052822440d084800003284544d0811041a81c1c05402014250b002034030600c201e = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 917206330 1250 917205080 917205083
    0x3030712180326090a0308090c18010828110102100906060e0a0c0f0e01021e010603060606020f0a0b0a0f0f2f0405040902030c030f150112030f18080109 67
    0x1441c0f00405040030070440c842003041c06045080e50001048003a10021540c8414190706080010207911115000b0380b0b065442000e01d0707004071032070201490920386e4200c081c1c101e989040480e400c8452420101d007400e83c900d0294201840e80e14021000190702109003072000c0410301c11161464105160722041c1c50070520141d4515a5801c0288102d0040c0c481c034aa101440301340600c58020220070040c01407c41403058802c228001d680c1d07005582c403e00581604001d00f50241210040401010b4020030382448126887d91802d031000034414008903c01054001e01005011900a01d0b00c0d01202040020a210015991403403503201142d050b01c2680d8402010305000602c008040d0100c1c241040d080342c0e6244851000707080035003130021103001c85064440c02d480201d2141c60380c0c40402d1400b00440740da250b050041028268400c000029400c40e0202c07007079a06191643c5c3c81c41d13075011036804800e0141c002032600a10343c2081d401140c641703915200c403094840c01075640b40070303c0d802c40327400040 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 917207580 1250 917206330 917206337
    0xf081b1504120507080904050a0605040608031c06060207150504090606021005010b09131107060e0d0813200d12020307051203091e0a06231305030307121803 69
    0x1800140291407011100d142a1403c0c03182c80d10155485003000c600900804510545d2070300000340d103484580c0c000384000c280c064400e00019031503c3c881034681d0030481030040004401c44203000700d01e085000700d2044880e1a00640780b07035400c01450150910444080b003003800303002c02000400c01c60502c180d9000f0910760303014251060310300314140141c1e00103074084413042c08103100a150a40d240075100501d50390800000800028444400c40a409071500150003145018074101d500b100100f0035062100803540e990f10181e80d0080082c00021840320090500b246241c12000e088210a0700c003c00d1400041c034032803201031181d40b9080c50b10461059000140c1003c10b02c082000b1080040c074000342c40d00c0d0030003419450031810450b65940c09040c8a0100b0210202c415070f0820305201503940346030011810701108800307041048241c40c000e0b00c045a038020400c0091590403105a5100410b94400003961468803802d00c101d5900303456034201d0f203010307603a0b41c074080400c040c01c40c1d0151958460784 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 917208830 1250 917207580 917207623
    0x150b0d0f1b06050f1b07060917060c030637080c12100b15030103060b01080f161d03031c051b04030215040504021201150201090f081b 59
    0x1e8049014070801d6850700d800340d900301041c4803032600581560591507007404c0d525111300c01203881c44103511303480c2c9a401c0d0382d000d02580030550707590003200c81d13081d600c0780d5480030001040c0340e40c0e6941d503101c02c840300c4417150b1091002c5282480c0c00401c0101c80300d1090420b9155141540c0e06038811030003114480d8203051000d0003041102c0d410300122030014001c840c00d4140a90100221362500706521001205942e40c0742d40e1100fa0741da5514590400510800b126100e6850349010300041554204ec64041680d07080060b620f1043c5852a80c4240382d0b165215040d04a000c000352020703800d2010402d400b80355158030080e640c07410005040010600c0740050200c2c502003010004440d00030b0880d00303c0b0b2000c00d42c3c0c010700c54902c4003110212070307060f15003590780040c51603c00c1d0280521341003194058000500c3c603121800a1170114180c580100c00000a10134054040e0b0803207110b01c0d001840078100200c0300c404207043d000540300461416943c10b5242025102c8107042c4405000084488408030 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 917210080 1250 917208830 917208833
    0xc0f02100c051e0a060e0102120c040602011b200f0d03090204060b13150504052706010302160b09010f140115020601140d15020409020a11010605060403150b0d0f 71
    0x400140c03c414016000c003401d000c1c01e039000c698032000700c81d1000c0d02c0b0b01d40f514240b0030045070950448900700c162903498070150070310401100e1158410701c030b42001982440d80c1a01050402902070b4122619900c07944034561178110010150416240c4d00c007010300072a5154280c0000611150002901c41c0d0780003d01c0701014030420040302c20300e402040c602e12040c403502458409a809003420396514100062030f50032450b2048542d8425600700035003000f00b4002234600a00300b80d091b445250441d4100701102e07070b54000110704134080c1c107010f600b2071109100c26101007000354403041d0b0004459000800e035880020300b4081a00c01c101100c800c0c6080f038900400040b2001154001c0c0810184042c02c1c017545003650880d0707465a200c41c0a8881d8440400120030031420301c15a08443c88050b60564030780380d850b0b4821000303401c80e40c4a4008104801c6282c85a0001881002c081e100f00620752400d142c1150ad0391483e03c100c1c0c1c01e0b0001c4441e40c802c1d000c070160341d86100c021540d0f8403d60102504104030b = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 917211330 1250 917210080 917210083
    0xb160609080f04051c02060306060d060305070e04050d0c020a0b07060204170304080d020d0207210b09030405040b040207080d09080d0203090c1c020906060d021b0304080c0111030a0c0f02100c05 85
    0x180c000c45c1810030421503444005964540840e50000000c9a5550320b07411140302500c02400f440d40010800d10030410001207008a0741602c52096000714241e55144d0789078003040d594401c0742d071402940201440401d0203540341d00c1010340074517030060500504040e280e212140780c80d240041000c0c02d681c40440c0800c1442400c0101451202003407016002248441002942c7c640f058014901070780d204038032610341c040340e00800b80e00564000c220a04a820208615070f181e07405402064041ea0601c2a20382031801d1034000c503034000d644460303181c1c40c00e41c1f12000b14006241c2018111002d501c00c02651403950043d0001c3c5000300580c4c0080c109a10088040222010400d17140d49186420801041c015a0342c2015080e031182c010703a4182e03920008110004000c0c030460503440c0f2034900b01e4440740d51115000016000340c031a12001c50721082c2549005451810000016081c503070b004020b041c002c40d100382c40e002100351250701c6401500c883c550001e10465000511600042c0c90b400d151001d1100 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 917212580 1250 917211330 917211349
    0x30c100501051905100509060d1b020a03080a050c0903070b031e0118051b13030b013213060801050609010915050f06220911040b160609080f0405 64
    0x49a04480010b0f0383c9404104902582c42910f105409454131a82003501850856403210720007001c160f9241e030412075460003040c03030901441c0301042c1c071800c4460b040e00003d0034480031a00340d2942c0840b650b840b00202d0240070000c0c40704000b48014845084551410441040600700c840c8031244c9034500006442a00c01825888060280347c2030010454103010110081c03441c25408804078040e520000c0716100d0240589040003000000100304d00d50601d4003945030300f60303481080035121907661040c018892a4668a881143c440104607030080c01c0b040407044214040042c112001c408400d0712440304640c01940070340d00d1070f511a8200b140700d140c68105607000d005141020802d544103c0014503000269000b4140a0550b0481c44441c50f03a44006544e110300e0040000e1240c0d01c0031402e0482c01052902c502803043d410404900c810500d800191410f9a118101003818200c1640303500e0009203071101d054420a075600507000214440030020b188400a408489070760381c4c508020701c009182c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 917213830 1250 917212580 917212589
    0x1231521060108011211030106031b030215030405070501110f03030709290a050a1b0303091703060913030c050706030b0f0306060a0608100909050a060605010e010c03080c0c030c100501 81
    0x210f0f8018040c10381030704000e0002e0f40d000740c0b2449040100b4000301e8010710003500064180700100c0b4071004144e000300b0844042e64400d03640001c07501d01d8149299041d0006550080040d00082c0701070240754494801d400110300329008480120081c80c200c40c0c1076a0042e100200007440c140c90603c00502c519640304140070040741e154018070344150401c0d060340508031000c0c040040c0006c00c5181c180c4070b80c1000d26090148403140c0c00c442903501e0007400034150080101e410b52128504a00080c80320025a8803900380034142000319910710200c43c5080e1922201101131045d10b903245004a03c0400030400a4115618005003800e00e440822400382001583c440c805d40c030450410615444103100c901c00c84006080060040e03c50002c00034056050b0b8000d103402c90314001d4214284180051240d610720f00805041004588a00045070046500c094950105c3c0c0b40c5800c4400187c8500c01036a8804172614007541010182c2ca0300509650040c1001c104503800a240c10707a0504041c4101801030 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 917215080 1250 917213830 917213837
    0x336060a0801090209120f210c0309010e0d06020c160801090528080a0804110909060613180506040b010905160507020301060f12110108012315210601 66
    0x1010120007421020140120b07900e0b140c01080c0e111040c0c50311086c603d200c2110b601601c84041242c0540d50f13840c0d009050300c12003919072141d00b50751104501e00b150200d1007618061072074101004c00541f110340b0240c142c07540122106110074040350251000d046110710700390107400c1c0c070a0402d80030800d400c401d400c504003070792400300c0d180c000450014030011817020098269910b00c205043c8054940c0364840301615040c4005901c20381581e00802e440e01c0340c1d00c542245d49183d40740d107052040b01c1c0011194803540d035110b040440c0c1285030488446c0c400c0c1d19422004110b180d40c0620341c2c00c640701c2c1020200c1e400d82c80701007400100101201c1050142101403000c02507032034051160101c200119055000b0701000040020954500390841c401401040c0300344107010741d1740c18003119501d5580300d0540c1c2100380d86c03152001f150310445059048407074002a5201546021000c0c90502e02e042203211390001c2e070090f0805000300740c40d0283c00c65005100258a088100c3c915000d01d440c0001c040718100b = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 917216330 1250 917215080 917215087
    0x6080c1813031407061d1902010507030c020f03011a011209030804080a050c0d080105042004060509060403020406030501050f25050a0201142503140f0702033606 71
    0x1007008030000201400d070945850003000c502da403030a841c2c1d4820a64003601c0706041c0800790740c800707548000001c62810443e044602450340001c208a074030384001c00090004404100450100b88507211603144036000900060528104030300003421111083d100c00704001c1c120700441003560304100342c0c031010380d9a024180403144069400030b2001d000140003d000706000306454000ca440b4000ba509010102c00032100c450383c54003409051030b00244507031441a07052105044000b211803000b132880844040301d450405c0e0801505507110b0308002203050b00040207000000143e07807a4055400114040d900010381ca003801c164840003007000910618084036400c0603d6140b4201640c3c1e4528160a4079080340c03100303103a4400700d001d880c0600f47d51840034501421301042d1200c5018000805015422456441c07849280560598408410070f00c101200840003413400700010480e0b80e804581441568504a5840081d1801b004a820089417043c4a400c0000c8100c140d401c00850f0142c0490300f003401d = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 917217580 1250 917216330 917216341
    0xb09100e100c0311040501030c052215020d1205181006060e0316050409140a1104063002010207030b0f090d050f0702100318031707082e050406080c18 66
    0x13918400d0303100c0c01e41019a103460070320b242407140c0140c0700d00d4103982640c215020b49c2c10300d9440010707002c0e01508000898212101141a0000032080005039094071240c0306030b640120074100030038000302856022181c0500069041c042806040c5100001a0380020b1039402c0201c01000328042c035139801e00943c050705466403e0052410385c0c030101c94003100c012910187c54504083c40f514165103201e01c6105003a601c40c200107512250010f0440300341e8041007080d40d2030443c0004481001c0340002405031040036145412103000c81220018010700484d1600f554959858140c100c086032030800102d08507043c45084001884444040350300c5207000d500701044881000014407401c24000c3c4114602c09001c2c11090290f0480d6142c035028216811406803a81406003c101c49002007d540148960025000c140034810f01d9000d1030814030164540f42181035412513200c003444844600e0f00800000003920f6603240524805004410060102e00790f40006101d48101042c0e40301d00a004440308014 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 917218830 1250 917217580 917217611
    0x60506041a07080a020307210914030109080301080706090803190804051516020c0a081c12060b0711010201140a020f0706150501110f0a0b09100e100c03 67
    0x3400d8aa4001144000103044440101144204840203054280c0415481c140940102c080e088241c02060080c0014242c500620142442ca01051010441d09001441100103104002000b0007000e4000a03520085417900c66403500f0980c803a1a6581c000f41051040e561311404000040022800550801c0c400540103100c520b2070804400c1000302c5c481c00501841400c0010100380e044554442595040c42010441d41070302e01c1607080090720600c0381d500401d00f810f400c400d08440702030006d4420034608100094240703080e80d017958200400700c81c8030090802d507403040000030550741606541c4c844841c0780006501c800c07260041c7c103591604402c0c00c890148803214503031000b0040c0300185d5403500380b0145c200307034000c80740003822281c649513580881800c04000d10050390801d80707500c2c00345150b04081c56070b140c0d818180200303260440b590b0640092201440550040242c6003580d0340c000a0741c1e0300c01c0459181d421030741c440e81d114101c0b48800386100c0c0f00e03168156170f8510703003400345107004903208 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 917220080 1250 917218830 917218837
    0xf0605010f020a0c1403031201090c0306120b010306020702031c02030307031a0d02010513080703060203040c080706020d03020a0e1801031104020a59040c0e040b060d02210604060506 80
    0x2112043e252032003905e2155820300440d2030310700e480007074030b00d0a5840c0c000c100010f0404005c20404a0714000001c03560111410503002c0065003d0070450480e03007541d603200041c0d00007020490701403149000100c0141d45001d8003068500b0103600541d00c81c5020030009003a1169941485010000e0075a11a45a11011181c030501c1740c0a081c103580e2040c0c25114602d04400070307030000b0340ea4000c8030000310400031590000c50265000e082403005481c0c841803925110b21a03841a1009030307001c0c5041e100920b0013038018103208056801c1610b20340b4004800308005240d180300040c06140c0c8000140700300b00d942d070000e1100d10001c0d030b801c5052000d00d0344c021b0284010342d9080e07182c01026441d6041099a4141c6000048441403d071540344c6504020042140c4140009600c400003202d1030040d19040900c0360b880b4041403951110b03401c0c1b40e903038240001080c41001c4e4941000c0b04004031912140d003800200702c83c1d036079800c0c504071042e006900c0898040000d40200c1c4a01d0421f0b00c00c004950301c1070180d = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 917221330 1250 917220080 917220089
    0x1317060a1b0c0302070b0f18030601080a0f0203070510020d09080f0309040e0c04090813060c0c05040903121509050609010b12180a140d08060a06120f0f0605010f020a0c 74
    0x980d680000e904081c1d1800140340d01103080c0301b80004190017a402c00c000940040f17071000c00c4048221051004060301c0740024040d12021303034414920b00e030200e108070414030203042c0090151034045e40c6843c00300c3c070304024122200300564000d41c4d5142c1e981d613020460364020681000070303102c000100e4000070f480b4800c400c0d10700d12030342c1c480c040c0e006488428000610b080c00010000c00c009882440e203825990401c86002d01842c0c4417150000e1840e0042d10340d426520390000901001d181880c5c1000b00a0005010640400c07035912010000404c05101d08040842e03828803101045140503800700c01e884004103000e0007400c0803001008076041038002d44912032042383d4070080c10740c0e540f001a180540c80b925000400c1c400c0c10200d40a01c07103c548505100103106069a124a1103c00b00f030b520030000750f40340c075080300ca115010010580300344801000740c4031242000c40c011002d99008400d940040d0007003011143d540c20304005a61300087c500040b10305034005000d00104984a000c541410382c400c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 917222580 1250 917221330 917221337
    0x12200a12150501121b021515060d020706180b0121020d03030b0d05060708250c080d0b180a0c080f13030509030a0c090b030c030c151317060a1b 63
    0x52044c40b0200c25080b0070660f940852201c1a00502400029900e01c1e1810f0905500c1c250300300820441024968540011700e07002e02544d15124204c1c03107420095000540a807903080d0307103031045c0d4403446d20080100c603d42e0041e81802c000c0c0d4100000c00048034204206103074041201c0003804016200c10100107400e5400d400c00248540340c0e8004981030b2440100000e0a80c0a400d0130019001d801001c141e00455044004469814030b01c01c01000000a685000020171840030903040000c2c0c1001c010101e42142c0d95011500142220200c1c40e901000c002e11100345c80c1c1082081a102e00c81c0c4a881055011842d1180f01410000140c2c0031014016020550250041841e50149070140b021a40e003144054121a1521100d05000c035082c10305000f078a18180c10603695101030701e8001a0880301201c018051304651030034400300010007284804001007890188000700f0000c0700214a2001080c540a0787c0c81c2a81840012508040c401401401c5651800007034031311202c2c1c0403403100001e10071402c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 917223830 1250 917222580 917222597
    0x2e12090b0a0e0c030601120c050103111611060403050703170310090f2c060c041d1005030106030b041a190c020a1e0201020c0904050d12200a12150501 66
    0x44400c0e0030481c3c40d1007166054402d5100000300072549458010a0038020288012102d0312500110280e48985200300946003052043c0310f081111589025a100d2084000107c894000004202d01d0303000340d44165101d03080b40c0300070818410211000d01400780192050b528600e0300c04015002e28225005e002103503955074181942d580059030091103171511030124007141415824001044a08100d40c1030118061440414079050252060301c09079440c001291151010866400b6007215009048541008820b0340000b2144c400b031240e84061402012030040501e41402c20344004200d03516003801c1c6075101000c0104682a0800b1150803c0c0ca8400c007107009008544200d160005200c0050300c00041000041400c0f200c108400c84410320030b80035500840ca298042101d10303042250702502a030403000c0303841a01449600070303000d1000d0b035040010f4140030303126000f90804c4124601685006000900c40311860300082404892100711000f800101049445111200500e203d8a410b004144 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 917225080 1250 917223830 917223851
    0x603070b0c10050c04150f020d03020a0912050105010f06050f0a03020c01090c0b030114011b0b0711010f060e0a02070c05090c04051302091215040305092e12090b0a 72
    0x30700c0100c0c10740c550b852091000f410301c0d0405081301d40c0144164098441ca604107010400c0c0102c075032458030ba031039030064414000c8405080d0007a500044101d4100300700d02c01b01146083d0342241c00340005000d0703400050a903040c036180411016040d0420801d008040c41810ac070041102c0480307169070843c1c1380c050707100c200200401b4054881d0440007003d4a50065010039140a20000741d4100c540400d000b450100002e001551556920b032059107280311000f980201040882c01c83d140c1000f4a854407420384500400f0741400c42d42d040c46a8034880d62140b00c20403001d446200225007048540c0b030118500347c03060345e402801c42942c7c41124002c0441c0304c0011401e00510050390f00610b40a030a0450600040380300c40000c0d0b01100680e4803402038880307090f902180002d0052044440300d0503c50050b1150740702030743c1a82121b2102603100c0070140c2c0e49464900e0003200c603000028175241d0003048044045001d014615054100b034000c0d49409512004519244035483d00000400400503240710003 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 917226330 1250 917225080 917225083
    0xd06140a0e0c0607020d06020309150a06231e010504050a03082a03070312090212150c1e0313020d051e120904020d0e061303020f060603070b0c 63
    0x1924192010109110400004104907002008040022010356080306000001c00a480c000c0d42c00281d0000e2034503808600068440e402190050760f140300320359241d00b42d901043d4144000716800b05009441e07400401c0b900035a00c3da0198110400c00d15003442d92030700008a00b0b0203003c505103051002810882d09100d07402031086030f0181034003a0031300c01e034103449040c42c0032079a005a0700791422800341043c0c501c0380708424080c0f00c4d031040c41e10b0207980b504d0000e450868901d0540300b1a041c0712650381003140700607a00c98220b140c101d20210041d15a0028035050000003c000421000022808104800910728000c2c1c00d1008400c034100321030303283c0c1c0320783e01e451501039030b0410001e42000186000e0340a01600007241074070300203c040b03040d03003078500c00d00b03065140c07801e0200d4007101c507100b4404001907140c07a0300030340702203020700200003030440da540400b61500005071020501906003510100626074188800ba60a1200b0720080072a82000303000700e41d8401d03140c41030402c03909020500c0500c2c1d520 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 917227580 1250 917226330 917226341
    0x911070f0c0f09150b03060f1012051603050a1b0f020c0901030506060a060f0806010e04180c060216030b130807051002040f0509040c17030c010f090201030c110c0d06 73
    0x20301c1000c0e00340c01501ca0744060f0081001200d0740039101e00c0c542000862401d2001240e00c10603010f0b001d104a003d60b501403107026507143c0306c020180040180400c00c500c40d0b611881307208441c40da247c01410004694041c084400c040d041400e064140400101d0900c3e5080f441108080703149440c880d05078140c10304030305104c0c0340f107030742a4800d4008000005204001403854010700d030441e001c1e901d040d501d0005442d02c43c000b6409402041440c80000c00039030284d0b94845100c080500045950541c405020800c003000c0c0300704a03030443d02040c0038000303158108418034281603180c24103a080741c00c5440e103100c00740d0010100b117071010156110108000f0128250750025030312200303c07000c803290300c0700140c0a074025018a18240800c1e040010309450b000040d03900464100c3c4808112506149507c0903c00c12110441001e21040003840d040442c05d1182600608045000059015082c4001402e807584e544c00001004241c0420b205844070200d03102404035003c4410100c84521407801d6800b401c0d = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 917228830 1250 917227580 917227589
    0x140d020603090109030f210216060c0807080105012c0f130519020301150c050f160e01090605130b01090e070203090a170d050c0304150c0c0911070f0c 66
    0x34004000d1211072a4150400460035109441d40c00c0d1440c803000e011942d90380104405a802c250801c0314003045c0c01283d00801010f143d440002000c03401580320038040d5518400b0400002d1008020821200d1b03001220502500c0c09291010140c0c45041508d00c0c4400300c62900e0059458011000e2034603541c113407008a620700068807000200c9100c24400c00107200850b840f1180030f0000741461045211842280d069480c02d004070f408000c500001190b0340d040303030401143d5510030700800303001c0b43d0402c200e6959441e25441007800b065040062407008448181c0c4140002c0741415001d000c50794030100e203400811200c40c0006129501040101c400c842d0325031104080c1045c1c00244402d0035404030060860180642d42070840d01e5841506a04280b206000600340e80c11008101c1c1410744250020002400407100f00c07400d0079180d0040042e010a6000c0c504049400d000000c4104214800200d0042c1060181003162000544240a181c480c280d401410b00c0b000d02c4100040090b0012805d0103131 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 917230080 1250 917228830 917228839
    0x40b060d3818091006180e0106030b0105150d0c05070b07020706020d0e030f0d09150c020303030109050c0d0c03020c280803040c0902031501030b0306060a140d02 71
    0x1201c056a146101c40c600919102001016080c0038410540a140c58030740050030040c010204914050502440a0316001c4140203900d04103402942900564002c1c020002040d41e01e09040c03004801151410710000105134141001080070a04070740950b811104140c8241d03000c4189084800301d82d100319041107800030318014000344559400006007100c140f1442010b5015100d88409907070b00d003c144203410041e484180c101d18054030401c01062106801b0b0100d5070103401c655201414040c0c2d40e004000000c00b41141000380a131507410722070103ca5a8148072407074455980100f0b441c1c2c84140a01e000b62610f40380030610502c0b003a070441e0030034040c0c00003c000c842032011005020b584400c040c00664410701c980c204842c2525588556111016044804074030401e0355609159000100300303580100f41c55000081c00145800114400c00c01444c003072110780114800501282c505110140c00fa80c014410050301e0340b1050b40d180103680c800e201070081070b5060800180c4a40255000a420 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 917231330 1250 917230080 917230091
    0x1020f070f091d071a070c0314150f2202090406050f06040b0a050411090319020306010b09010c140c0303070803180105070c12030b10020d0e0102160302040b060d 71
    0x1c8445a004425260040400c0c858034440043d0000d1101d800702e81c803540d60308000401c00c80848065017800c01d01102c013640380c1c102281d644581a1240d440c1c1d1050f50009042429003440c90018040c4030f4580441c907000c03100c18200070503090105400100b030b10822091001c40d60030702038017620006404650040202140d850300f072070f000d0058503064401d4182081d003100410700616090140d44210800500b0641c0c406141c60104030140c92400f902c10600081080700418948060101c0000c084001819206440c041c0c8181803900c18141c1c40b9000a503070a0103540c3c010781e48000b100240e1031304150308800241c4d0300781c0c215080218807229254184000509101008000c5018500c00c0614100c10100035070380e001c04c1400c1c2c80c0304442d0700002444807400240082c03088a0311941c000200e00d40040d002001d03002050b0814603440c00d45000d0780c0490318001d04154081e00e400300b044402c0c400b41c1362240d00201407200300c10721800001d21032501c42c20700c003920343c5072001078840d10070481c3c405100 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 917232580 1250 917231330 917231339
    0x8160201020723040516120f18080a0e0904020f1201151214010504170c030f0f031801200d020904020d06150309110d0f0204090305030a0e0a2001020f07 67
    0x140e0f0464401003500550501001602c411850219005414090b803a032806041c0215034900013490089148030000e80d5a90509040301e054000307004080f03228040340c69942c2c055010250010b00f802c01a0351180c1c1002081000680310b903100c84d410310400f80c50380c0b085038040030500b601500d00b24400c1d1610024518001070605e45180d1002ca0450182050400001c808080c85080c0d8000f00c85c044c005003000b8100340303414141d0310010b1103600c0e403c000352814994600490174150b845000b410443c00c3c4003100780020b481d201410350144502440c001c01c00f511039800803007007103040b10008540d20b8602185a00b24658181c0440e64451402401103607258107402c04680244103900030401c004140c031202d050854005d1042071042d5030015924031020404170108064158040707401c40c1c00d10480503240005131280c0c006e80c03100c2840384e100c19481c0d00c0c1590082c0c0403642e801d001031b28a54030138481f11000c11810071241ca0071800060002010030800c0005070f01c0c01c41c51003002016031065060004 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 917233830 1250 917232580 917232629
    0x5060f130b2805040218010804030210050907030614150105161b030303200315060f070b04050610120f020f030703030c0c0b18191805060a0e04081602010207 69
    0xd41098114044010603900d0b0f2081c0801ca00070142c140101004100030405598000d00d4070b1540148a44103c8103c02d0a40503414103072202035544814590242da400e104000340c600541c0940440102042ea8a14041c230b210000f42d944250340c00c2c144280059101d01c0000300300d09a50310a600314012144d42c0c0300b25180d48031101c28030310055000900e0404841d03582c45003031144032242c2c484c1c00740d807504684600c2e0784104401014409640c0c400020030812026600010107411a28068a410131030361a09041c0982011340003425682e05410044090002008142c010356207260452240c1440ca2503920104c0e100710080c03a011949485001400002c140c0d0040e00da4119900c142081a03600d6551940d1f80c842e4010780d802c004001c1d41042031902103080420a00355541d10042c14031100b40e540301c2822044482e1500c510402503110020171105040c075454207402804900300100b082d04e40745d16151040c0c0209004009000150100003065a00c01c208102c00741c260719100b1400b9800065480 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 917235080 1250 917233830 917233879
    0x91514040209090c18090a120509010e120d08040f02030604050f010b010807090302130f0234030c080a03060b1206121606050a02120f091305060f130b 66
    0x882c0701d02480c10014040102c08203242104060140030b980441c0040000c0b0180c82100828141c41c0d80300340e40c1e17882c010a0140c5820300c0600c041da11903075903402c42d01000504030620482c2a0b07010300030303565003243c2e40e490015030795110340079914018005880300d25241100a84002d0b021b5072500ca0482030106211011550360b83d00f03841d00000b040010105030040d291440c04903441c002140b1011410805410f203203016440c0d12074180400910f08001b0030403074040360441d945440d150f0401d0104040040081030072805460130200c540d06003960350350b500801080c042e40703005140440114100301c0c1035000f0340001025150030340b0310340d8880c0d207249500340074440304642c618402d14000804003880e80000c50302c021100041c1c2c040c000024100401038455510a020410031481600c02004030050f0600180404034585a51705546901c180c0400c4910944107403a0760f140c0303241c8001d00c5901e80d10300410301c044120964020026807442c0078040002c0020844440e004029503881d1800b195401c0c185 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 917236330 1250 917235080 917235083
    0x120a09080106030209060d05160b0309070b090d0809060d090620031b1806045a0b03090601051c050618070803041d0106030212070309151404 62
    0x2011121039540e103400d400d8030620300c400b0390000b0704280480e00305e05214803000150b60140084480080084c40420405c90362540241c1c4209000300510940140900c5817400401420140178200b0010400055081050a0000f0414000010300710000e03124202518403036480340380e04000c620060700740000a4030803001d400304820400d4030034840e20030b040c205030b074080c441100b8400f020222400e0543c034258440b01400d0585040400600b402d40d503850014809481c100014600c200040701051041115016243e40c4052130390141141284419910b01400c50468003e03600c1c0c05024100021178071082e8008100c0c00000008005402130001003e0341200c4041e00c804c0d490001020700099400e0034508020700e190080e1011424603140320842e200010b0042003640d0340103544110035441c40d40194440e016503851a0188002e4440203004070f80140072a04003945000712903180c7c0800c84000074645001d25940700c031003100b40301019040580408140c1810050751064941c02402c00c1e070100c50 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 917237580 1250 917236330 917236337
    0x1b120709091a070c140f010e0c090609190903090e01080312060109050f06090402040e040f0507140901031410020a0302131211010507030c0c0303260408180111120a 72
    0x100b110801c0032000d8951140c000c0742d48070545200e20743d0300d200d4111400060b0000c80d1103100c03a8948542001c1c818640801c41c0c2c80000d00c0040d91000510503070080c01000c0354440c0001804100303105243c035a01c480b0460704c0d400001109965032900703075042d0807140c00c15000c000f0754070008035a424000000b0b02c02c245801482c2c0c03030540e032540c00446032650f0328001c10350004400d14004020b0b08105001d0008548018800343c101a1100d03045804400112400d9031000c050f0301c81c51060000034030230200035007117000c003844442080d080842c2c05980188001025001a440701c210314400c24030100b0007a1014120965031607441000c0240650440c207814105240100300000da141c1040b03502c03901c09a400700d500c0e4a145203845c015102900070440c00c0d0700780600711148400242203010341c44061480303a11b51518044418209164018a500308006817000003814040490700480541e081501d103086a484a14170300c00040700c4540780ea00807007803e88a40000941d18485a5001d0800502d81d81d4 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 917238830 1250 917237580 917237603
    0x1115040506090c010518040e0303041b0803030105030c011115010605040612050108070339061710030b060a0b040b0a0e100f030902150706050406050c0a021b12070909 73
    0x10310203526500d181200c0f40c04580704014007240d48071a40300c10042c1a13402000091015416054030b4119401200c00b143c03050544051510090803100166010741140b1000750300b50f40c14000800d642e9402c00c222181800345101d0b458040c1003040100c1d41c100f212040c00c10002d543d440c8000b03041e0f60014090038012650400210400202900c034280c100c41c100002000000e2954541c51002c03148003010858143d041c1c4a4050011f520f20500c03401d215a00321000f40261805000500c0804c485500d203480201d203200340054003000901e00002d8075003100300d00d00d044d22808002001044a035000c1e00c1848004a00014540000c0001d0060650580c03240c0d44410000010086400d00d07408005020600c0010181d18042c480d61015001c02d00c090034110090740e410000b15002d0300240022503541c0d032500f0400c0308010090040c290008071a0003400d040c00512000a0b40392000744485000c0c251030005c41810030b0fa0b8a1140b188034450364410b844400f51501c0800002c0c1a01140175503900640305d = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 917240080 1250 917238830 917238841
    0x10302280806030d030903050412050c093111191a0c21031f090204091b4d0a0c06050708090405070c060e0c090f22031115040506 57
    0xc2c0580303100147d1607030b141890703e4288051369810200b071030707400e0303c641c8151a481d22080d210180303810f00450303c512b0150004000c0044490f802100c1016a0401014000442c8001015032413092181042218400100130519164031400b103202d0b03000c5203a90b40e2100a81c20349035001401858400c49940558ac2c04541c103141410079080741e0710690b44003000c00c0000400c40341d80900b0649940340794041c1890400d50b9640d03250f0590f0040d030070100c02130703a40c1e5180c01440701041c8107a83c8014402c3c00c2100c0300c4d0f0710802d4110b1400c114900d100c122459040301d04481c907001000701e40d11420f00d041c0b0700d03601c01ca803640d14035503142006402103e00c01d2080d900030030702c18054010b60f41c2d16980603405034075100881080c131010b448003621000502042081c0940001d41d00e019042041220a00825000000d142004580c1c900038018a200c6c115101c2030104401202140d6200490314600f4a50811454a01141d0042d48001c801c5010300a100f0104405108502c445000d14000d808a40300398461 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 917241330 1250 917240080 917240087
    0x609050f120a0f14101a0f1318081b0f120301170a021e03210306011b1707020906040c020715050403150c2c010302280806030d 56
    0x2066a0100d030350b1100b40b1200020f02200e2a05034040e21689022042c0b100301c0b9040c3e80760060390805441400d4807040820740c1001956142c01c1581070860701c084000d01c504001c80d8403a980c81c0030196259446505060300710740b102c4078503000b0961001c0c1e60703a55802100d240f40024410400c80102d1030145406180c0e000000180d607007480c441c14104640b6503468240c0d095841c46001071001164000d992180f40541e1319100192003000c02d0781e03891a510114602054100300100c40324440844c81855020401c00207101503a40c007041c00e080c040c525441480c00c0ea000310b805140024001010f0180d00a5880307600c03806449118801e84268280341c403610300700010360308035858a40c016031207480c04110144020010140c100000d04085180a4603515000c000da1b0b51801d441c24101d0311003c100000c1c0c0e0b401010003482c0d450044814841e030440706070100b641601009907504054001c03c84407400c011490304d00c0b038125407240c01801c000200580203440d07603408940d00c5100f03000340150051098003 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 917242580 1250 917241330 917241349
    0x1103161208060117011206090b160806310b030307050a031803080d1a0a092c030313020114040602011e0203073c05031f0501050706020915040609050f 66
    0x1504220000282c0c00c0c01c04010f10703c07100f48400d030b48007620342302c180000c903001400313081c080d10300240500c030380c08294240a00000000b400c00c5001d503407044040c068081c003119080070035446040e002c0c842c511021840401408141201c00e0b80b60000046403c00c204000500103100343c401d4485030303012056221003141c0402c003848040c0506104210302240c1c80300a51100c00240244500008054221008540200101d030001400c4a079128030001803102050640032207400c84d0745801a40354017030700009489000c0503022005019251a0080c11680103144070383c0f4804800c46010f03140c2e503a516000780030f00745510340400c0740b0041075030401c081c007002c1c001c891281d0314540b070785040700c1900654218260700042c5120300d912020408107145803111050f180d00020250384540e100d08100d01074020040520308182030540502c4420072269801400f5958110303081080161900c0300c3c40d011075080700702091310020440e40041c0105007079802400d03100595106841030210400c0702002e202c034260 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 917243830 1250 917242580 917242607
    0x18060302010504050d03031e0b09160504031b150509010f02070302030c191a071209060905100507050105011e06081027020c06041103190311031612080601 68
    0xc60410082c051303400c00d44842580d1078841e00e00001c0c9030740014580c8505e13091555881d07602c0c0b51101a24009898004d248681004c0c40e4011200088611040900207120318440100103460103821030441c45500940c0c1002408184100c000342c0304405002400ca901000416010500d402c100100c0c01d440024010705a0b0b0340034008200c1c008124080040b11510207083d0800d94031031046c046248940401c0305003100c10101701c1591190301a151503601e5002555641c000c1010965003040110750000b03200044032026104221715103010741c3d088903107104540c4068040d6017442e00000e0320340e9580000446c07800d00050681907043c0c036158122180c010035114414101d40881c81848a10889c3c4020095111180c0e40c00920400729100c200c1a40c0000c00344640701d0b0030520420041c4a801035644019100490140c010403e40d803590403c581003000000e030810000c000242c1000404000b102d1801030040c080c0d682c00d01d51858038090b00c20007814510001103400010454550241c0d407080c4d40301 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 917245080 1250 917243830 917243837
    0x4060e0a0201120b03210316110a020405060112021201241403060a0f0b12060406031a06010207050d0b01091b021002070606030f0f0b0709230a08161806030201 70
    0x140f400351074000540b43c0f4840840c3d01d402204a62030070324074000c9015045c12100c1c00d0300d5450b07243c11480c818140b45040604401d0040040304a60303100008101c5107802030341146c00049586910300101c820040441c4840c030340503c001410022002158a8281240e10748440b2501c443ca4401000d0581c03110300b07410303001142d600c0815545680140c1d02555110300041c00051103155218281403034140c00754401039414100043c1800e10b1442d0841e5103510050565060082c0c40c81c640c1d604071641d40c0340485107442d11494020442d541e100340034420007014010020320000d6000e0038800707020303d000e01c5440c11031032a140c0300c0f900d0400008024107904801d900038000004280e407403100a9480742c8401c442c82030781e440e000b00019500b0002814542d014640f0071690400504e07002140d280003a00400074040c1d4a401080b140304007100d180e044403420f1040c45038840700000072400a0007960041c0b505e40c01040b414207810304a00c80d03a5000c88038603070b41420342e00c960807052508440d20b5000c085e002 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 917246330 1250 917245080 917245097
    0xf03060a170a0f050c0603240109240c080318010b030c03060402270a0b01020d02150c0d060308030a2412121704030e1e090a0506011e050304060e0a0201 67
    0x106180c20b040010184c06070f0241c5903403002e0107000805c150b20846c1c0e03c2030071440301c28820100c0d42180583c446011000e0909600d20b90501c82c4980c506424013160044040444100000035440750241c2424250b11510154507400c080361401c03c01c020180d0100860340c40c10341c940d5035903d40010b010084240182c0900540d4840d81c00b8000210000300c210301c18400180d0100b46074040380d62030782e403140441800029154114030002410701e0540c1042d41c0840d80302c40e25405902d001c4000158002031a131541c2c60391a5800788282c0c0186c0010f5101074202940402017159402042c0c100c0b030300460440325940d000e1118a0007551603c1054010300c260b076464040850005a50b01c180c10761103001c207080482c000082440140312601c0c003142c0c124001070300c0100039242420030b94010b829028883c1c0307036410070141d8103011030074070000100310310089500c0700c01080d5581d005219400f044600c960b00344a900c82c801c10058a1075106440444d48240b5209002c654040c02040b94600315905030b452400 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 917247580 1250 917246330 917246333
    0x30a0212090a1a0c0a0b040b0f07020c0f0d081809100e0a0216120e010305010603020a0c080901230909010b040803070624080f0705040509030a0c050307080f03060a170a 74
    0x40c3c1002d0380d0103a40110304100000251450b041050b468450303c141400361140c906480c1c02100854080c1408600da0750070030622011f6900820400014807040e50805020015800000c0315103d003403038050800000012680c0140c001c18000c143c040506903800e5219031182000044504807034802c01d403400f06400040703041003400360010a040ea0440e043d440844140e0746030414041c2d20303801c51001081500c1072800d050f513018020340c1d0060000342400c40c14101035010107003850001000040240500255102103680508810510180c0c092a103007a102080000d0700700d0303036100c0242d01744a01600710002441107050021101030703444200145040618941d56000030300b460b030b900d001808a405422304d50324103401c0441c1000b04103c800400b540e81e16010f4586c01c1c10328641006d0700403030500c03080003400c1c50004200c0d8005051840e200501c0030340d9060250440c000c1c000b006107031140010310311144141c05e4010714010304048800d1041946d4800c41c00d490310b10b2420002441e5000400080d0 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 917248830 1250 917247580 917247599
    0xc18030c180604110a02150406061d0a0b1905090a1407091406031b030a090503180a0f06232203030305060109061d0a03050a0b04050f0c0d060b0f12030a0212090a 71
    0x5810505c03503276020407410303216100a02c1a804401e0346401c01c04d002010841e009086000d0842000707010394140d0011710030701450b11816251406501e003c1c600d00b50215904a030345501c4004802c681039602c18090800c040000c040500e82d104211520140401c002038070304d0204d044900800140c40e4510002034520b00980381d0b80c20051400d40d000390f4070b0360710b8070100e402480244035a00d44030ba02403084185510401c1f28244503a040007090701940d0360f041c0a40c540015000004201420710340c004140c40d2034101c1c034944100282c20042c0e4051b01b98810240e0013111481c0c06492103a10180072641c0c6041c0119044c0740a440b03000b000440303510201150603501c82040c55194000790808a0243d1a92102407804451050480d82820544200414000d090101114084070302004d050f60340c02c0d00001488a40301900e01500c10399449001100e15903071342d1080841208050403c144140045955030340700d41040350054058040d42415200840b0030500711040040300030801e00790281007040c4003 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 917250080 1250 917248830 917248873
    0x190f0f060b0a0906300507080601050109091b050304080706060b040302210703030e12030f0d0b0604080c040f0b0306040b01210f0f031404030c03030201140c18030c180604110a02 78
    0x101c80c604091390350f450204005002c241d000d09500b8001382711355454200014201d5003554002c101c1a490440708001c6407034003101012004000c1d02c0c017a501c076110350802d100c05218482d401007080f031924000007419004803006c0c004890089688016801950414501c8034100140c0c040068000900600020340200c208546511020f0325074240903141180ca5441e591115058012082000c1106a1040303014010548180410341d41d10381041e10f811007041c0d482e610929240d1299403100c80401a519003640310f020203440050850b10036082c2800c14145400c07080c0120501140d81d0301d00805070090034290702d082540d000e0414000f409480c0c88030381d03000b80500070440810100126103550440b01030082d2000d180682903560503130b8510301c0c02908450844501c072403082054010001d45540311000e9454000401e003000c00301d40c080d0b00c00241007421a007000d950240e035450094014901540c132042c403a40c41900d0400480d00f03002c54820b005d008a0b15250700682c0844030508a0000b020f02c070 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 917251330 1250 917250080 917250149
    0x207020906131d0304050310061a030c0d05010e191e110c06041407050a1208310603051b2a0d05120f010305190f0f060b0a0906 56
    0x182c0c0000e0f2501a000494a0a40b0614203510200d800e1041d4901808034500502903c241004402d10301088060170301d03104007400e00320b03007008400100150070f88000c03540e4250004074104138940c3c4031803202540c40e002380c0e8608000980c1045955110446200e840718100e80c4112080c145107003902d21502401303659210303034400c81050026029880f410030100f400307684941c000311001c4035440307081031034551a80c0c000751046054410421041c00e1030019507559503000070a0380d0f514000004080401100c0040d03c040e40416031524406884e081c4400ca41036a0b0103a400340700a480d29503861070340d0018010000c81a0008009588010700c3c400d4404104401760001c2c0b103030044d00004e24508061110000501080000403001c40a4081070b010b954040c001560b4500c0950445d107601d5652240074005000441070004800144220340c03c001c3ca8440d80107003c14100541d501c1c085020740300020000b4090203a401300402c03c04500d00410095580b5030070703c10a41d0048891048140007440c15 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 917252580 1250 917251330 917251369
    0x9010302070f111e09180109170405120601051e0a081005010f121a06010513140418120c031b120906020a080412030e0d0308070201050a0207020906 65
    0x510000031110060b8680b600d00038507692602c0c035081c500307104480e50300c500718081d03d4220b058105031681e40c110503a60032481c040d240d0703d4074907050302a050043c2000340e400391402d8484040c29400d0b550b080c000300152281568900994181c4000d2580d81c1c820078040c56034802d18a905805c10700f454903021541c040c03401410300c140190303a00310b1103040c20382011a4200580c1c4900040c011072a001130510028904140d040c4d9a40e80d441e1101d401e40002501c078601c40f40300b0500450001c1e8401d8095a0b05501c480940c0e40601f69031303182558046025074005405181401100190401408a1210704a41050300341b0340c051000303a0308449080503580114148080c031400340c01e802010001660312103209086a0030b6122800e00e018003201000d902060442d03004004c001c000881241c20348046801d61b40030084002c2d494501a101ca03496181d0341500030401c801500c040c19400380b0854021703001034008104035110030849105a00c40c000000c1d40150451010410609090840c607682021619 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 917253830 1250 917252580 917252587
    0x120d060f060216061713060f021b07060306260a080c0105060411030c18120f07030c051503010e2707032906060a170a0606032f09010302 60
    0x141034005030065400000050384003250b55520740c14000c1c100c0014040c50b06203501000840303a032442103001c008003070f134010002c0811410204041c40d00041c4e20b00d60708450940d215104110303880c40f41c15030340507108031512a44c04c6c0000d00601912512083c0c0b403403c502c2814040820200b000e108000d81544d40e070f148070f11620000886e492201825a400000001044c2401c00380c040105407015000d480d00818030070424070420088580c100c40106401e40b403002c40c0310400d00c0000342640080c1b02550344500400c00b0030b007551003020900e031042c1c0c0d11039044450b5a0781c48400f48140302c40f00c16a01d0310140001c00c01845605892600a6803211640c0c11101c1200d20b06500e420313508a0301c0500040d20b40c130034038040c410040c4054103004480007002c5040074819082800390380401e00500b500e40240000588540314511904295070041561194124136080c07200e45003004112512400c00003030325240c02900f03c4031024960440c41c2120484449140d1349010040c10340c0e40c0501c00c401d040c90707400c1 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 917255080 1250 917253830 917253839
    0xb0c0705030601090f05070e060a18031203020a1103070c0303030b0d0606080f0d0309020a120212030304051c03020702100f0504050a091b05030906070c0f15051512120d06 75
    0xb003107000d0103441c2c107607004220411070180e408166840078110005100556401c0961a01c481090306c61400041c5403010f10028401000005103d1680006e0807051502034446412a0140c00401a2550907901c1c212a04080d651031038803400380c402c0040041d92a039000f00082440782d000301c807070810001c20603030a81e103541c2c3d1190112440384e44540410313048900a02c6e002a4140a04101005e80c0d007424070060700d080c0d000582d400658010307211f0324040515004255191b510300a4580e02c1c00c80216594ce0610382007140d0f440940902034924004040c4280d9880d5200c0c0c02030360580303580500304c61080c030454282529485051401842008010b100009840e941c214522000703000000d0001201ca5680c0202840159042c0014085c80307020000d00ca85000d00040080c0c0c02a80307440e00105440c3c41d450300340001c05100001034101130348500700d040d040440d640914001c0211004803a40c503002401488540745440c0c1d22680340303402103c000e003500750078840100503001d642507001440d20f44a = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 917256330 1250 917255080 917255083
    0x5040c0b180108010503010b09010b070c081009020915100f020f0706171503030f0706020f12071106090c0402030402040906090c090624050c1011220f0b0c070503 71
    0x400e41c06000358030502481031165070040f48042c00342500350000d210701a60440801d00c070060600c551003a2100c000703a0318013071200e0750340110060044101580c2c07460141c5a14000902903100303040c1c0c4243c0144010030f48100d0421905604600013800c001041402a00180c03044111540d1510642c001c116000c00000000e0240b480504841e499401481d580c12450f8505000c1c01803400b902c488900a0640302d650f070000c143c40c110492040b680c0c0d690300c1c09292080c040d0190742c0c80082e1081003c100e15000700840c40d201c51041403e0303514048900c5190045541d58070058840b40702d241c1200506446a0902d60000e580c058000707400845e800c0c15698840d0100c40c035a034002d83d084d100d207100038400a00140102d20041c080b064040380b80d04551654500c49007815203180003804000a4640c540001c144070400761b48403101010403000468401d11072342c0340d000e05000c0e0703200b0409840c1424020070241c0168103483d0192030f07030081e0720300304410481c2c1070f8052140540e45109503180010981d0f0b0 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 917257580 1250 917256330 917256337
    0x816141e101205060303090a0506031005130f140601270f03081b0304030201120203070c0c090b12030c07060c0f05100903030f0203071d0402040308180108011205070905040c0b 77
    0x1015078441c0c1d824006050042e00310380f4068102d0388690010403c0b48a04d60314002e1400070340300d04aa49a64a80b00c200140810000550142da00141d070701e4111052480d05900901350903908007130900c0061280d010090f030a0104a60305408121b403410704980e1509031852402c0d0f020080c03132041881e140c0340c0806105000841e4002c6803013400020f5030080e12968554070b00041010240194285410360340007a0a03a1000d5089408483d80840001e240502c40e801100310303140c108243c0d44c41d80d034031542203801a20b00030070b8640c0100000d0102a8607404000100c1d0004103400c0b000d04905800c20408a44a0f031284d44243c81d100041440400410403d203c03142001c4440240011400175500e000303410340c3c0701c42c00c404501d43e10510810007400e40002034030070451810001140c8a0f08510700240080c01a40c00251504001180c0d4103209026003510070f07008034090f210154036070b03a82d50380c5a24000030800010180e4200081c00c000d0445c8a070840c81d0018480d152b6043e00c10344030441c80304240c1 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 917258830 1250 917257580 917257609
    0xa12020d06050c0d110c12030403090e270c090c040e060405041109070903030f031103160522030b0a0603120807030b09090303040606290c01060e0c03010816141e 71
    0x200000d0714000c80301c041080d07c07d28605020018118507050314041d0118900b4411840003e2441c1c0001c1d01c80003c0100c1c0c0d00c1e614203040c0d4442124011180d0042d50360829078401406038840c400890720b41d40200c4284c030211141e085403141645c0d02c100c140070141c00054070844200710b0081485605d6900d500182d8070942441da5941a0b042c03843c02e0040000d40c0b120340713850a040c540701414039441d0340c84085a502c4190010009244190300108940c10b11035110b140c0e8000340001400c4209440e8001e00a048900901c0d00f05110f840d42c01229003180d03400e110003014180300070751810710a8000c2c00243d51041d821300780003500c0c0034080d021a50409048441d00c8450f000003003000100320151150301c4c081c081159800c54a8107010000700c040c02e143c40e41000340328101003000c0c442c00c1c0094201c0f0340a40b0518030b8008072400c00e03c41d0004107401c2070081c407030700d4060994458078120032450000122800c404c0c044007100381d0031051142c3d0f1042030b041070b43e8481040c2c800140c20740b60003000ca140349 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 917260080 1250 917258830 917258861
    0x120907080f0c120726010b0906090703090c090213061e0207061409100e090f0907050f04060801020a0306050a06050f0702060c0c0a1503060609080d0302031f06030b0a12020d06050c0d 80
    0x4100d01d0b010b590840e42c0802c1d9941c410103070107049c0500c940f01c00300c40342c1d8400e1031401d0008100c2c445050942000c0c506601400540c0e00000b08081c404401500b1107040740c4040e2115000702d5000712582004c82241301c143e07001640007003402c0007103901c140500001c0b4012901d500d441c0140310f0001c01c40d400b0f0207000e00c00129044000302c1e8818149000510761041d01e04c0c040c2011401c0c43e40441d5107404452050790712a2991140b40c4540359502e0f400300e0020400b950085640c2c030340d00400075001d40614803a281c8124000c1400294240c0100212400007003005552494808140e080202d2a000009000258410300215100f07130b40796528440b01074001000c5a60130310b41c07a52001825500e040d00210b0030445c0c0c40004010341140011190110561414056125501c000b04544847c0041c0100d66940d50a01d41c0018990b400d9803242404400c19211481c2d040d0f200c4815803803201079290020b4004608803a6007020800a5000c2c40d008911030720843d1511085c0320392882903400048001685 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 917261330 1250 917260080 917260139
    0xb220f0312080703021306051c0203040b040516030302150711010e010b0f0315191410060f03020f0702010f11031c060e06150702010311120907080f0c1207 68
    0x100e0b820a1000394441d50920b000c1d0300d00402881113004410b842c0c4101000e215000c2032800314007981d0740c0ea120312124002c0e8111740380c0c40d260030035100c0f0b00400d0358165000c5c066180c140c4501c002103111101500e80540092040d42e80000c900a10040d00510000401c031030ba520350048184203004481e50350780e0318000850030072000d42c1004500051401424401d038886e4485161201d03410b0021944804280740505c00e910040c11100302624264101074130504142003001606004502da000c2650504c1d6103100c00503803001c905504a1003890280000c43c08140003150066200303440352a2561600d291400e04c48528184451464101d00902840c030f0380050f03640c0800c2030191044a00820341c0500640550800e007003c140e200380101c82c1401c0c0e00d48006880815640281c008020802d8404d030203d43c0e41c0801d100e812a1030303000b0342c2c0f03600a0740916440000d20b4140020344070503040401000c1c15031680d1850800c01e1300902d030344902e6860b0060364000210741c1d088c84c417810451001c2c032100c0040c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 917262580 1250 917261330 917261363
    0x1312030209120d1b021c12030c0203071a1305060c040302040b090103080307080408130e0702010b010c022112030106020a150507081302030109140f0d08010b220f03 72
    0x12140180070b08010103074401d500b008419070784041588188501e5080340705200080d030010801345404610880f24100303c00c0a21070070000c40e0b00c48074440002c15a42007020380c442c114100d850307104112014200c1c640140d4039a0511503040303e01a0441c6020700031100c005200d51310345052283c21250106001e0003c1010815401c0500564040d1202180d91003510344c110780d2240901e0001a104c2810820742c3d0b00001d0410902364120707503405545928644006030b4441c2c00d41c20411080f90214015401c0a8400032154000d2410111403640200703440146141c5a01d040098a22a145840030b0b00c40c0c403102c00c00c000c60190055000e81a954058902499507081040f00002d10001603140607280c681009019580184d040390881c0503920740b5a60b06086000003800b404002801400d01c03000c1c200e1301b140314000041c1105603481702d070085e80e4044085080c203440028003442460a1036004200c1d0440b142505004e000d90840480400c0c2800c0782c48007000003450801c0d40086840c0ea04d800255130 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 917263830 1250 917262580 917262589
    0x10f0509070b0408030a0e0a0909060b1e091906050409120f05040609030f1406190509010e060c0d060e070807020601140f12031605010203010311190e1312030209 71
    0x8098121440c60b0b07850240ba001d940e03680d82c45030030f50900070042d20887c418500e030748018061004007c0580c09003c000c1e071a091420042c10610740c190f00c110203d800300014401c1c1c50401281c0900c00410540c840d5980340c2c0081507003440146492140341c0c1d901c06c00301d02c50380c0310300c1211511405001c0e9800d000300c0e10203001e0044049d501810081c010140410016154480d0141c0162684682c548007440c0840c50103290071444000114450300032101000301264034001604480d1040d5039041c403094a03080240740c222050000200150f42102c8002910080100001c100c00d40c102c0d13100007070080d59144154070310641995101c0005003e8000d1007011a0b0422049002d1304403031040f2205045034074005684103800760011402200700403444003560005000340c800303506d10400b4904d8490803518105000f90300900048400300003500d01055207061481ea281c003443c0c0403d08a030059402c0c540410701c4610001d00802010b4a034580c1a03000951050f0010310b5801c06480c0540c80d03100d10020070 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 917265080 1250 917263830 917263843
    0x605120c0903120904091a0915010f141f050a080a0c0909050403030e0d0f02011a0109170f030703080906130b150406120f0c09050c0406050c030c010f0509 68
    0x400c80d446007482112480d590100d20000e4560b0002c2402d980c510f10300c2c011130f010740318045002d04002511042010036144100784240311350401c0701074030722140030101031510006080c01070450030302550b01c1c107200031842d1424400448100404089014183c2c1345040d507080202d80c070440c0085c00201d00d020200c0c0d04a8900343c0c205c2030301c074000d024008141000504808107442888a40b03034a9002141c00d05002c2e40c0311000000700d05e425102c1c0c20002120140c0b074044c1c4400013100541c03a0107185c440310703a403180d20314030b4000d416501c004010b842c080c618078481780300940085044c010129a190f00900400060030114400c5e19580414582a5090741c1030640c02000314500b890000d01402c000350960458503445502450944000194603022400034001c80c0c010380040180382c1184000d0201d040000c07035038944203090828010f6280d40080c8181d034070545a0403c034500602003404014010005440c11003401d40441c2c0c1009008840c0c036003907030000100031030b4450303076203040c000c0009080c0b044 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 917266187 1107 917265080 917265091
    0x16050f160506010501121503300e100c050d08130b0c0d0b060c0c0d08090415030203060a0b130e03071202011a040903080402090718060512 61
    0x401581c980b020f000e00c40c0841c9882e080e1303e800650728042d91400c86920b600744201c1900d16983c912101c69854a440d0030940d048d484c000c2c042e01c1c460401c04c103800c450b948540c2c407104c030b4000384252004145003030b800b08040da014100c0032440c0094480a0f4401b5071400000594680c01815501c140c012401050112854288584014101c010b07140d4036010307940812015684c030041258070f105000e0641c44507084940320f4002032404000c51244980200050b41c41c180c01a03001030102c640f008c600341c48040042d8410310640c28104042c0d5441081000200000d407001c6001400c400c9158210f1801261030700d01d804140300e01807080c0c903401c0d0f0b40030521225240504d40060f002e40000e135103043c465000d2064183c81c910f41400348410351031305a01c0720030700c41d1140c0e024840741c01b070000c110b00d0603c002000500b44d081403003120f801c0144280d540320b984804004180b4411510301400 = true := by decide +kernel

theorem cover : BRFrame.Cov 917086330 917266187 := by
  have h0 := BRFrame.cov_init 917086330
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917086330 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917086330 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917086330 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917086330 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917086330 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917086330 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917086330 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917086330 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917086330 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917086330 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917086330 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917086330 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917086330 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917086330 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917086330 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917086330 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917086330 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917086330 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917086330 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917086330 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917086330 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917086330 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917086330 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917086330 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917086330 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917086330 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917086330 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917086330 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917086330 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917086330 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917086330 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917086330 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917086330 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917086330 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917086330 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917086330 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917086330 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917086330 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917086330 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917086330 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917086330 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917086330 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917086330 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917086330 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917086330 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917086330 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917086330 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917086330 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917086330 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917086330 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917086330 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917086330 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917086330 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917086330 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917086330 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917086330 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917086330 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917086330 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917086330 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917086330 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917086330 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917086330 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917086330 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917086330 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917086330 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917086330 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917086330 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917086330 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917086330 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917086330 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917086330 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917086330 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917086330 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917086330 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917086330 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917086330 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917086330 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917086330 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917086330 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917086330 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917086330 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917086330 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917086330 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917086330 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917086330 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917086330 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917086330 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917086330 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917086330 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917086330 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917086330 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917086330 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917086330 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917086330 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917086330 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917086330 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917086330 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917086330 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917086330 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917086330 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917086330 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917086330 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917086330 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917086330 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917086330 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917086330 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917086330 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917086330 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917086330 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917086330 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917086330 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917086330 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917086330 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917086330 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917086330 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917086330 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917086330 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917086330 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917086330 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917086330 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917086330 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917086330 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917086330 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917086330 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917086330 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917086330 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917086330 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917086330 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917086330 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917086330 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917086330 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917086330 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917086330 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917086330 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917086330 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917086330 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917086330 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917086330 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917086330 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917086330 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917086330 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917086330 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917086330 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917086330 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 917086330 ≤ n) (h2 : n < 917266187) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
