-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4120
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:37:30.502981+00:00
-- url     : https://prove2.me/submissions/61827d86-72ec-408d-a186-6fe9380832fb

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 740827338 ≤ n < 741007194 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 740828588 1250 740827338 740827369
    0x80a0c022b1203020c030d0f140117010e060603060619030b0106121d100209010306030f061a10022e0c02100b0103020702010e090a060f1409070801030302060a0e0309 73
    0x1500d03160a02004480c5160524908083c10298240000c18002e00d0316800f40140c10740c400d944413440014001090307807203a4601750380d174081c2c100c040d6180c0010301c48100301c2e140c43c401c95610b0300050103003a840004085116950050040c42603a90310310610071013140c0780a205000400b560b41c0800080d4800442601809107581c4104c00401d81d01940c40c15a07500c1d03042094041c10310001c02041c0c8401160080d80d0b00c0810b2805070f61640b40c080121b0080007150300180045c407a440c60b0004205564000c141c4007601015100b02c0e94038140d04101108050318065805039108001a82c43c01d10300042d400203071403040b031183c1c861614030322400050760210801c0c800181c001c0c0d0900c41c0a0800ca20440c010181c080ca021410100d0f03603030010300100304201c0003604c900380240004100b1040d94001402500d0b0621820b10055903440d40c0312441c40b141d1f102c0030710815a140c0010b64107803040c500a07048075003550083c152038944a85002c0100545918403e00b030100300049542a00e83d54402440542c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 740829838 1250 740828588 740828659
    0x40c050405060a0315060c03321b010f050f0f0a09060921090f0b030408090a1203110c06030103021e09010807180b03070b0c10050c04140a03080a0c02 66
    0x6059140c80308245249805c81c0c01848040c0c2d2511005c240c1c400358280440c42e0444048800d103205a8408645d466a1f000309c3c00444d1002a20800b600703462001041c0c142498802400540d1620f0141340545200702c804090380003030000001e9404840d03400c026041520310707200040d0000b1581314907086d00c1c4102d000f500c04440b0041016803a0200400b0910442080c2c039095101e20f084c10110488801ca521a0000e000d0002c0080b03400e00400d10111032400340000d01c200c13011aa1f071484c00894401c0b110003030f0301244c0c1116030700080e500d02160114441c0b04c0146040e107160f01315070801001c503d031004145201c00710010007100e1902c0c0c1d62201da0180c08840300a200c16407274882c4602c4865000c0782119606403c10b031030b146807601c00140a81c1601d0011548903210030040803010305d02400300e100b40103228189018800a070076480000c005542e8901c01e0f83c1d041c0d415880600100620920000300400c100b04420f28a403481b40c0801150380307200602d41000c00111504600c80c008000101c1070001 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 740831088 1250 740829838 740829851
    0xa03060902070c23030c0d0c08160e070903050715120510180204120803070c080d02040f0803030601090b0d06030b150907021f0c090510201605040c050405060a03 71
    0x41d40d241c0100c11006095800c104109a035013000319454142c1c044031140240442d0400b4070800c202552044040c148103c202e8030300c54400c0107074a440c1001d600c250030900c803059022590091040700740c0c2e03068a40140080480c503203000d28440d02c0503244403955082100d46017100111034900e02880e80100001d190255082d801c03c41c00785203030b0703207802401c001042c41000304110001ca001c0c061b4080541190055440c2d0384c3c1c81c02c0584084400d1103009000c10400283d0b0071403460503901a00c1507800080b00c00356026180e40d4402c1ea6484190b40e41404a85030036420808201c1000082c01320001440c0040f542990782d07610000c203400107480d0400350094403070040e502400c0008100c0d0340240700e4401807103a40c0b0b05454601c044201c00c00494001c80c1c45484218800d0b0050300d640004003000340000c038408605c2c01004220564030f00c80c1e40f2001b1055400d96031049400960a00d4800035034180f4402285084104401425095a07000c2440000d11001a03243c1e00d10016100c180c3d920744021404 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 740832338 1250 740831088 740831099
    0x1f0204180b0f04090b01030f0302160e0114010306030305121506042c010b0403030e040b0a030803090607030606050d02090d06020334120504030207030209071713020607080a03060902070c 82
    0x20004003442c00d80c00b0700d140c2096000410191481d16044030b4100c05584512880c40c10124184420701e50f442c000340480f00400603880a001d00c03514100d402c007000030000580a100114252040c501c405070004005215903c0084601e0400d141c024400014803900d41d040c0303002241154010b50300c04066001c0e0032481d14007801031708114508203019060800c5c015810006010b0701c43c0500e00018040103051448031045032680d074000301e44501c2c000c10130282c0c0740d6685064080d603402100c600c02180551000f050a0382e0090080b81c099881d0703501c1e001d0034410b1083d8204000e40002100c103921800340e41c1c429002c1881480214000d910361884142214038200d40351b1303801030501e0400501202031030342d0101c1c01544405c0841c001039007890b000c9a42c0c0c4480c10b04a20709201504086e501000001c01d009142d90000b40401305550310407580406552002032018800c4a42e035806500100c00300002800104140000c103103460103420001116900c032045041281c00003401182c1c0640f03030003000e205 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 740833588 1250 740832338 740832349
    0x10305011e060c15020d060303020d0e09221505040309080304151409040f0b031e0c0d0c0f0b270d06052a03070f111f0204180b 56
    0x54480d407600360510303040c0c1c9035803204520300c10701c03420b8100400c5201d00010055001501c051007503050303800359180d1161100e080001c10316440201e000d40300d0119070584e414003c4480c0300d884000204617084a41d98641d21603107044408400b450381808181000e800603a02052101d00b81505403070010b014601443c0180607400d25400c141300356031003808204400380100d00e28030040d0130b0300e18020000086030010500ca50085402403a402030030a1104507581c900ca0340301c070310032a408908070359640c48038080380700d49030409507410032464106e5018404039040c10851907004511450981d40e090b540e0740211850051150400c1ca0140400103002446450b0400801c0076a404080800401400c3c2d200107002048100c1d4020b00c10750b00c42c000544820469500c5804008620703091540012400766a100c16074401c40da0200814140021082094405c044001004044200800400d50b041d0461449a1511280d8652a540802000c0f0b40c0c90014070b4525082c1a84031800314503944020100b06 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 740834838 1250 740833588 740833591
    0x1804051303090506190f090b0304151a09011205031b03040e070318170d0914010f020313030c170f0a020106090203060109060e030114040506010311060a0c2307060e010305 75
    0x144901d42c18050090070b003590100b022817200341ca00b000001900355031001e40d0307050b166621018241c02c01008000034400e00840d00400b221032503070200640a4a40c00343c084d018a20301001340c003e03440707800603c50356002e4510080703400c0c0104216401c001540b000402e4505d0b07032505000300c5030000700b020007120901e0300e50140c0201c0310b4103003444010407404005050010394540907141c12110700c0704114802d04c0c14200c400c650490b000a0141a6050404820703103150143d0f111465841c5c000c11188403000c510a4a000d02d4002801c54004001500c04a13510000c0e50070580e030700000d1040c01503107114040010305145044080035519005041406401c40d20550701078040f150040042100c1c682c1c1c000c0c680015281d5600308a04d48240001c0032a0050074015209001d000c07400c8140028420002021412039101752034407411040c2403c24012940501c0c1e0464022a00700c10024001031902801d1011020000865245448a159400d450040703141d020074003141c3d0015468902c0d50f0300d80540d5 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 740836088 1250 740834838 740834849
    0x1b121b050403051006030b1f092903070806060918100f0b09160f03060e0109061809021806123705030f09120d0806012c06180405130309 60
    0x8006181c81c40c0c40d04401d0720340082084011082c00e0014202d1071500910703900c05404d089504200032082c511002b46002a070541081c100c103014000340c2030610f40000c1c880d09503210140989144e03219103081c8103000c04050806e10060040c8000040d0f0044204030030795080e200c40401050900c00755101c8001c80d00d8454841340070300700c483c041003450382040d1540c0c88880541e25060703041020780401100248841e400048003007440c0c2c2c00014440016400c25400d4800f0a1556150400c2e00e210781c42c01c640700014025001240c20b061050980e044440443e03022034003900ca1641c1c2d038210031007141072441490081841013804030501074203030503c03201c01c0c03028100100d418000311203e460725a640d006403010741460310300004034030455444d10b1121000d800b4800080314a0044010005403440e40200c41c6280040c1a40926422820341c40100c07900820f8094580200c3c0c0c4008014840c441d8445107500c1c0440064030071284503511184256846440c10380411b10b040c00c96460010510046540b10 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 740837338 1250 740836088 740836091
    0xf0c060f090d0e0f13050c03040201024e2205010f0e090a1113030302160b0d24030c0905013c1203020f010507031b121b0504030510 58
    0x81d100c08641100c0c803d500a081240d107800e40040100015240b032801c084545080b034202814403035203000d40700245004e46e10036000c1d51070800b003440c1040c807035021820385143c0468981c0c1505044003a1244014800c2c00c01c40b160b000320902520b01d12056510403194004800400600c207000c10400502d444054207003403a01da0311412880d60000c2490030030345c06041c411941d450110711411055030155201c08c4800c007000d07464400704008510305500380e2200394054000e07200116030308035030800c0800507102d1401e4540d04004071900e1082c001e003008841c0604990003c05007411269016040d007008600c104041000c1d82d080240710000c0c2c80c010307446280300005044081e0801e03d40104180802c01c80780c01c40c10704c242c91444001881802a81c41040f40b0254002e03c0780905a011079215580c0704680001e00c000d8455110440c101c4500c510554241100700300380c244550f11a09203080e2050b60700c0b8002c10b00202c1020b01809208a003e8100c000c6200040c04100b002002c0c4080070380f000c1180b00 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 740838588 1250 740837338 740837353
    0xa020411030114060f1b0f0139022104030c05040504030504170c040216112215150206010305120304020603010308030c131707170712080f0c060f09 65
    0x141603c1c1c002103a441548100004a102d2102c0303081c3c1c0056981c0110784c040e5841850107400122901c60440801614642d400c048582c114030440010601d444c0d5005968204800701200410082c000004258011401070b8820714482c200007085100600407800241a07695185280c149503403401640070b980118209800c01011130380010666007282c410003d03217904250281003090418031071050300c07944a0300c00708590002046c075441108410b0b11070120b130000400d50504200995407103a10001e1300e00c41140d400c001d140901e81252140b05501c090f8000c1d1181c403003400040e90385c240c01d001300040e48600b00400510000b0084044122650340d0002d1441c1400c1d00840c50714841404050035a04000000c141201c040c07404844051031145402c4040c540c642c52440d20303038100c0d200c01d80080d200310b00000c1203c02c00351284c0d4024000071001088a10325041054215104c82c0700103035540c0307100b400700c0b0b000c15030710b01c00034280b0405030800b4105600d07001c01210100100074143d81e156502119 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 740839838 1250 740838588 740838599
    0xe0c0d0c17011b18030b010e0a0501050103181e0c080d02160308040306150504051305061b03040f050c0a0801051603060b09130b030307110f0607170915030106020a0204110301 77
    0x10549441c9505a10b048402036040000c02c003844e45181d8802040401a0800003810004900040c0d029a000007010721a0341d030707100011030960722070701b0705081409203052201c800030f4a83d0400c44080c0112100915200c1800e45900c00c01e10740e281d0007504550400c4070103a411540c140700c180754400e0104001003d440c155240e4001d240607034000101159580d641c0d028a6064084142006040c02001845185400c0b008100707030348840942241c1920803200800c1c0c01c03628014211003d110043e03001400c607a51a15125841441854182d0391400341201c00312841e21501e000c08040e1031440004100d905000d080c5403000c4403602ea04008161801106000080c5140308480407207000329041108d03054201c1501005000e02d6800982c180b000180c1d031820818515501c01a00c0303401c40700346443c44c50183c188407051040e07400041400007121501c1480d084541e0241c40e00c0c010241c040c104102010401880a910a030029400f59000e5080c01e021850107004d0b90f04400703820b0001600350351414 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 740841088 1250 740839838 740839871
    0x100f0807030203040c050a080f0706030c0509210d0c14031c0f110a0201200306030d05030c0c0303040f0b062b050f010c03020714060c0a030e0c0d0c1701 67
    0x2800034420140c0000c0803c083c8925901130310080e0030001c000c00138072a0764009080c0e0b2480c0d25214181c2500424a0002c3d055010748900f010426550300d030a45459400000c1110009005c070031207840c0c03084040140c1c013080c020000280452495221300d01d503040e1a044c02c03c642100040580d519a01c108450405194000c40840111a02001c049205241d0802c60000340c4088401c00003150030114810040e01d5054102c044613101000f6a180c04050b540900f009078481103d0180c0c041d40705540818916100c0c3c8001c650000b40310400c1800d0880c03105295080d5482038400392005952071215500f40a54039070101c0e000380c4210b400c0702103d0b0b00860038241001107039059510300d40c821000903041c00340a11001828020305e1000700580c824205e8054000d4000310800e503100c8112401c609841c130400101030f40a400e00021b19801c0c5440150210040c02c0c1141341d00b40075028041c04445103488010103400c14074030640e0f000c0403007400c00c00028401c540452103103030140e051840501024088 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 740842338 1250 740841088 740841091
    0x40914090c030a120e090a201306050f0f040b040603050109050601080a23011d06060c0319090b0310090f1518091703040302010b0f090f04051c030b100f08 68
    0x10803260700040703865801c250b80e2043d07203012031344d04480700ca0200803221f0030702d81c05440c4e507014401d00000e05c550421561041d40c00b0341c82e24403040c000701d064144541401040541030300500796002c5440d004d504003403020590420f6000081200000c03400b4401c20741c02d80201405000004020001da14104000030403c10018107104041c960381c7d07495100f196107001c146a010501e0f0035440145580d540080d40d481d024699400b1001300c1c2d41404103102e46012411902d1500091000b0350a214041c5c040d01c900c5041c400c030b80300511080c05000242500e00c1d10156125881a112500285103440c140d54165460300f001d96000a1400122075001000000800180c400f24a20002220214607149000301150040900f1048624440400c0b1100c2540110701c0349120764001d2100c180c0f00800d010341121080f004a50085600300024035150401079542e03402405a001ca030101a014400f01901d040a003620000117a201c6003c0c65460070200d80844040c00185081c031101604007000400c880030 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 740843588 1250 740842338 740842343
    0x110a170601050c010c021c02070503280f0602070c0f0810050604020705030c0d0f09061e02011b120b0a0302030601061b0606060f0f0e0f060705010908040914090c030a 73
    0x100101154003644244150f890300d1401c01c0080100602c40c2502035540d007421030440c0c44c91403d1200b051189840821b004c800c0b03810140c02801600850f01180074480140c0e1814008000e044d804080402c0c000366000007028052100103a131040c0c80d040c200243d074201c1c3c1040600600100d4108421040080c00702c82c3d242d943d8000254540310080054060302c900c1c08068040d11003c1415000b28101054030b490b40c11050b183e00c60660a220416500d10555105000108290401e02c0d5a41c1310810360710901d01c64107100015480414200802c3d04014054103d4000344091550740c0c2922894400c01c21020800c95454031240c1c0707141e0019030340300e03c140108010040d00b400d91401c80b055281d0100c01c03055000505211294581c3c00c028101107150032032030000740d6900b5020303409900a12300ea080003440038001039056003042c8144402035000110032180c0b50b58030348511000c40c0c00b0901502c050108181d0101c0d885000c110380c03003106040a0304003403a035084000481c0840c0e900240800300c407076 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 740844838 1250 740843588 740843627
    0x34170f060307230604030503090a141804050f0f0c0a05030313030210090810020702181003080915030a0e0106080714040504060f050711072309100b1606110a 69
    0x201c41d8010094450710803030f15070400c01c0420080101b200120151101017819100f90309129502c407071140c00507280220b40c0d50010982c102c01031030071040f80a8554424020400c83c0c821840100c200ca2400e54201240b1145030801550300c581d034a0301040c40d800800e0210011800c0c188200300c5c40144204a1000070700c107520074040340140c80e000d40c11044c000c1c000d05090b00c080030b003506110000396201010403031140c00c0b03c20540d40c41c01d2919400900612000c003040740124110340d15415141e20041e845030b4018107403034031140c0000542000f548541146a0081078800b40082c0700750940e09150402800354118050500102034a007014410b0300100700c60104540d161810047d00900911600d00c2899082400b04005250005c0318642c1034000d07001102c454a5070f641c0d10400511030920f1002c01601d010030b0b40c2050307242034210950400c1000140816a9a40d0031030851164010810b110048104000300814020180703d0301004640c004041881c5c1142c80b840101840c18801c18000c224 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 740846088 1250 740844838 740844869
    0x501140a0b0a0903020607030203120a02030c192c130c0206070804060605060403050c120d12090606090e0a0b090c13020705100f02120a0c0834170f060307 68
    0x1072094007043e000b190090710580e034845050034000c0d16540128581e4510507000000314400300064422244a06000c040e8a420403101b40d522101480a2081070400c00441e05040342483e5020303611948c0007500918400004034101c4180300d40d40840900080030b1034a06003810356001d4000c20b003564042044c2c07400700b07416621460000c00401580e001140c2080000ca400700401030005082400700c00700710348114040145072000344e980d46180b40d15800041000008500c2641d1035085003206074428000420520f07201d0415004849401c0300381ca901d0342c0401c1c4541c1c20b225401b51150b82140c95980904000c000c520040f50090b0b0344100e4200d1103a500282507014441e092050084898425005110b42c580d09000000650841ca00036407441401c0d5010405410710b901c00c4070070141158945074007a0ba00c1c51006c030100ba0072030b001c0c815035005542505880051301403035200031400d1034560b1881d036260b041484805a4004081001b0b810a00c0180300040d50005046d20440d0036821000010 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 740847338 1250 740846088 740846107
    0x10c09031b0b121f03080d180210080103210801120218091c0e15160503040e0f09060f01170111040f090b01080112060506060c060709090501140a0b 65
    0x1020744940c4a021440070200700c2c0b18084040303420b040d0203003d0003000c42c00030f450030302c8418112034140c1c80020a80c4408200d5145280d405402580c56401c51400c00742c056070040e000f181c544441c050452001848802c014001c00c114400407a4441c40c1c541880b808c2420395143c0a080304106000702003054001c00c500e00115a0bc130030b008012600d40400d900304038100a23000c6607948034031502980b4844206506040b1040c420500000c620304020f004546d0030b0b1088440c00302c580d10684081086900f400f00060210f40c08100400051040c0d00343e10b074007460030084800800c4c40240070300240b508100c2c10f02405881c0380d00ba890540e17148403820f400808000d4822801800a5400c4a40ca407101090000f6845400e600c46070490308170600600518030f0b02c038011100880300340610780540300078014000224141d50300c000c0c0e100c1e602428992602c540c0d14109494150f08450f660300180891038144030bd40541d000e014010321701c01c15070700c030090b032014001142d03403c0300d000300d40c05190081100580d = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 740848588 1250 740847338 740847383
    0x7030318020607060b090604090b010b0a05040f0f030303051005060a0806030f0d09080601090c082a030a0e0115080a080c0c090f0411010206060a05010f180807050301050603010c0903 80
    0x8406070300820840e911001d0745000740c00380c001c03520700600c070b2130f02c0800103003840c14180100154a0317413003011401e10740e00b00510414a074124202c88001c0010500020880821420024001c0d14650020028803855450018259a40140000840d6440490800507603c0f040700760b90348a207135810310b841e507036032030b180828502540504401d01c9072280010190a45400622b81400d0b2619842541c1c110380c3c0b61080c4006442805180a001600000000b102d03c1001c4440081919002031450300243d0007091805194006803810741085070340352942c10713803542c003441101d51984000c1c8004040d03910700b020b40b0752a0221031102405207600052402d1403904280928180c0300001072a100300707400d0008010100034012502161400700b25034100c01c1942c000105c09203e0300300180032916080c10800111400343ca07141c2c44d1403c1c0f20044508107030404041c0310b40343c050243c40d401003a009140008042c00e54002929043c02a454618280c107225071105da02c0003a02d4019500d0400c80d8110550800d = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 740849838 1250 740848588 740848631
    0x10f0e06041a091e0906040b010308070303140c271509060f0705010b030f070302151c06060e030114150d021c08031005030f07170a020307080106080d050708070303 72
    0x3c1e80a4007010030450807180c401a0002e101e40480350309011650742840b04d699540040c0c50260040315040010000108944010720a080c405c0c81c0115001011181c4070fa00740109907121f600c504804103045001d036040da8500083c0c0c042c0076980101d4080ba48001c11704213100402004200500020034146a4452108444007a0030017103509035a02c099083c414002c01000002d40d1180c081c4101c90701e000c010014562003a04c3d001480300b200c68820031607902c0b0035486100d00500300c2207012415501c1c441c1a00c1004010b200ca51038218110000e00109400c543c805041c14811403c01800d001c0d6640d0600c03a0110661411f407150000f45410380001440c604245c031000300c0840c41c00c14060100a403100c06503000d411496407800c2c00b640c0315420181c0355001c1c510034038040d42c001081007018801d98074901c2d400e00b0805058902080a54000c2030800d0302e00e400004040e912580304005a900c02c00030300e0240815450843d00b455010b6855241e98071598102904054850041086803501c494901 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 740851088 1250 740849838 740849891
    0x60a0201091401060326090d0f051501260a08160c0b070b0a050f0a0929011a0405010c0311030f07060b03060105010f0f08191d0105010f0e0604 63
    0x504102c54803018240a418540012500e840d84024105540da540c2110240c050001c01b8150b820104044140400a5031444003500c036016501e00b1440840c01c03c0c4050042c41c08908141041503040c220040c100c80e0078080040712401500715684c98500d0b0106580e03d41c1c507480100d0542e5401e01d10740d005200350b034140021f802440c000c1c03000242002c610000b0108140305031009001560340080440844600700d0b001a00200c411000900000560b8400300030a41701d0501039504510f8009600c2a603203c1d00ca19449600e5640c005020381e4104c846c0c04101344810030042c0380780c41d081000080101c07016134002000d21421207041d109481c1c05106448480b0052314039241c071580103092010103040042d1805019000c3c94002080c154420030001031051503507203605414070302100e0200e5075400010403020000d031898920981c00c81c414007440c0c81103c1607940003290440300c03041160840c0e02c1079001150608110070200a490f201c8040c0c02d91180c021100010190f2218030100004203561684 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 740852338 1250 740851088 740851103
    0x1e0c0f08071a040c0e04020d02010305130b0a0b040b04051303140906030a0f0c08010f1a0909070816020303132018010602191106091206011511030711060a020109 71
    0x200303100b110103681e40c80c80346002d03e8107003003020307039401e03500c0004607043d1806500550003050400241d4001d80100390007400c010b1000e00341c20541d440300c589454040d110607102c3c64440d6052003191a0900540e02c1c0703144112000c004508200c1c40302d4a120480c0b500060a01030f0034a21550002005015503011081c05022141c0e02e10b05105500020881c500542920707034a8081c190080703a105840d481d0580d1202c403080c411280c14542c0d000b0384040b804a040300040401c102c3d144454a070b0f0711410b8050841c135160b20459080281e040703145202200030010441d8014800c002c842200141c55080207900300b161111254075110006959041d00c54209030000c90154007020402e2400001030304841a0b0707420382341030007440c0384c0c030500030810700e4070287c81000590301c80161481d105000380800000100011540b5000c05c0759039090080036449050a00780c10500d03030707001541240d9003c5036801400061440c3c91a2940c68411303555650300080d008020200d0f40010345e174002d50000007042d401004 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 740853588 1250 740852338 740852363
    0x180c030c010c080415120516080a02160512090a0b071707020d33090c150e150a09050d0305030a0e0f0a080d0c110d1b020a03080a1e0c0f0807 62
    0x140501a41041146e4040c0245032000041c001c0484010101e00314460b81c1c0c075103200c1d03240e85c070f0658080c1d00b20030144a01d808515070408006441086608485070300d008105403542c90100810081c003125034080200310074100700407000121628207a407404180c20010644445180c004503486200d000002001014005095101591460707000082c5c039043c02c050303010100300c80361000251807c0c03800007004841444010f01c09002c0c0c65078034040f880a5403401101c0b001e15240064034014090300001d910090000754246499480781c0c007400030b040d081c0c540941c10742d600c1c4d078010300b14800140125001a40da40f41d0192120080c4400400c00c0380c1402212070b08505401c00100c25440400c01c4c81005103028903940354070340500d030203d03140c24015000d813000c0c040c61041070380c6001034141d940300d0501c0ea5540e90001642d460b941207020714003c1102d251208a8100c01801c11401e03000d0110809189180294545a0007841240405c2e405191030319490042c0c68841c003c0e0007020700042c101541b401 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 740854838 1250 740853588 740853629
    0x5090403080402030d09050a0603090512070317090a0305030105060a0c05030a0504080f07030f030f02070305010603030503060315010506031302031603110120071a0d09060203180c030c010c0804 85
    0x10181c0d4001ea00842c250b64040f10000e505aa032070f0300300d110342d40c3c00800c02c140c20005c030340c00395014204a038018820f0b910146a03080c461001680000b008070045102030b0180100d900c2980c401b0b65000c0d400a00078128051640c0f0040c009000c1441441d1041070001500e120840c0300e0488003d0081d80241100c0c1c440d01304510282c0705401078029031400784500341c400d0300410750004507070080300e800c114040740030f0189440c00c0382c50a0160130300d00c0540c40f840b40000b0004072309116000003540244c0d6100d4407400e1103020181000007c40f8070000d0035060707800500c501e0f40c0e40d01c1100c0d04902c072141d48441c5010107201280c01d09a000100c00c141225090000040c00703007001780c900c0d8024090b80c0d1142202082102e002d200c00381d50301e42c8411580131403c207015005408401402c00401240824140b010501c0d0700c0c2c0a5800945080341e0703168012040c00b4040e801d502c00d181018034454040c10241103080c004c01da45a101c9500141000784110034001402100c01c00c4402038481c20889021401c9070f013 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 740856088 1250 740854838 740854847
    0x20f09041515090b0306061318050f010b03240d0f0605090d020307120e010c080c0d030c030e19030c0804120b0606031509280b0406050301020c100e0705090403 70
    0x5224401400b0480b040c2401d081e4440e0010409641d101c00e038035400c540742d00041c840c880e08080c3c0b60318042a00400003040140c0401641ca8131210905800b00b40c42c030702614100d01042060384030564000b002d109111007010328468191000c01c2c0d100510442101520004034440180100503011081d00070710700c81170003007d802491240313034060f04484a8440603003040b41d5a204400f8080d107403034569442c11842a00c65051188100c00515081c6098000d6807180c04090b80907180f050b0481c0e0006009401c0300e038250042004602003401d04201107200b03031800030b07202d0006071089a00c0700100c0706a20101801441d40b050a01c2e0085030854031142c462030307100b048668041e000c0d10b4050303820000448920300041124071840e01c1b0010140c0a01d00c040c14040c80700e01c0648403050507005080000d1401051081e1103e01000400c1d0115101c44039500344800c840c0560000c5004e84d00400c00260201d800044180f107607215030b840007400c0c000d00b00c40181003600980249600000500c00c1c8030500d41d01 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 740857338 1250 740856088 740856131
    0x80702210c0d0e0a0b030a1b0503061905060414040905010c051e0412020108090c030609010b0a081209090a02070813170d080621120703081e0a020f0904 67
    0x3150211490052000e100f500c6801812071801d030311842e6101c05009034001c501c0595008400fa4034045080040070b009090340d054841500d800160b00070082014a00e0f10720741c0c1400c0c420884000c0d64140d400e1901003101c511848c0900e91404042d140300000989480e444002840e4002c2c00070000001d03684030003001c0b50702142c4000200e42250a10342181c0702c0f650119800c0300c0c80c152100090b00c1c840d90054900d004002d019025600641503151482c0d20107002036803241000c0e000020766003000c40d0800c21048000e4001040640c460708241c2d0200d00c92380110781d545402102c03112910b1b910540c403040a403050220060840201060900c03880351414001c0b025180355880095504034881c10385661842007080c030400150301d003404504d880c2004500002004003c01c81c100c1012501424185400c2c0b03030720345160040c100040c01406140d84580c03050703040307800c0c80204c4100c002d207480704d40c0030981c01800d84041c1543c000343c94100d80039880100e4480c02005002840b00c0c041d2008c1c180c180a69 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 740858588 1250 740857338 740857357
    0xa1e08150d020f040209010c0803040804240903141905030d06060c260d0903030b0f030d0f05030c0702030102120405010506091303140d1a10031116020f06040902070c1403060708070221 81
    0x70001480414400c500480d040c0c03030300341c0cfe60915458a1602c2c0c08071345550420300103440f4041d03c91302c28241480c00161440c5180910015070b034170002e403e40c0d04116100340d13200104221601011a0005000601e440100c4e02e0082c289038061802c81c004407010311460039402d40d800d00d00f450444c20140c040d001003003001170407620840a2008141850f490f42e14111110000034611741010348451b000b1070182d80c2000e407030072010f4141100da50209089a10800704207005650100c200020002c09000e0141d00250640b07850001c1c1c10312084a52820b80303442c2c070043c240600c0d4070582500030900d40540e8a203510105082c0440d050b0440710101604440701c4442c0030b0043c102c4131444140c000d01646084c403103510b1181d860300d07185032050440da8030040f900700da0000b908130000380c0079582c0001174005030055810041c3d640c1103070b103002d40294960780d1159a40c1081040c81240340e44e0041180e50780942503041a04155035040b00413801c0903003454158070002d40c0d0440d540305568440d4040e10b071004 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 740859838 1250 740858588 740858609
    0x2071a07120b060a270f03060506040605010318031b0206031303110601061b02211005010e0f070507060609050112061a0607080a1e08150d020f040209010c0803040804 73
    0x1c40e48052203c81d104040c00d1a010400c40d10940c80c0030b500805040d407012103c01d02e40043d007500c0700794410f40103201740d01c1920181e480780103000091800d441564010002400d00700070030f40c00410801c2c0c05441101000d4180310303a403082d10144000d040f00d0344440543c006c000c05da0b24545031043c1e15110b808214250300241040403010048000000e01c0c2e4180e4006803208114104071540412600d00c100c40202d03000542c60f1000100b01103410b528264000c022405488000140440d440c100d07070050f030040740c9003058182400302c4c41962002198000d442454155034504543c108407001d482c01360f01000b405441d140000640d10a14041425518401c05052108000c8501205400c4c001c403a4410f5000c94100500c0d00050050750082c2240c10b52800c20316000099482500c40c861480d1030030358081243d0300304000b03a000b06040c00b548000001c503100d040101c0280c020904005600c202e4a00656000602401e03984c01001041c3d0813a50050310300da624038007440d14480503000b5201d078039910f2 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 740861088 1250 740859838 740859851
    0x2071e0302190209160210050108070608090a02060702060d1b1d0d02031b12060f18010507020607051303150f05010e010b0f030c1207020a020a08010b1302071a0712 72
    0x80c00002e4041901c0d903001090b440158070313140c1a01d0a41156012040d00354402c040103845c513003440e401450b000f80030380c8001d00525883c10802804494004200346c81503000301440f000140c0da100103448800e501911030380c0c4c40c2c2201d40843c02c02410b110700c036910b103030248044e113106260340a40f45455a07650a189442040425802d002440c0c086044c000e606030411504011a180010b01d0b0307003011a0003c10041100d510740007046c0c100502035071f007481000c0045007040081c8003049011080565080000c119600e0032041c02500e0b40c0b006440c1070100900081c940070803c611040da9800b0f581c1000c4031008000c0c80009040007045691120180c09080900000e480f0400d103155078102d844090100b032500c07035020700845c4103500042c19140c00c04018840b24001c1c0030408071403842003d158004020091090041042d6148143d000301980c0e030401c40d406102e6192407042c1101004106409619104285040811911044100808104110100324845502c51003928400c20b250004108a = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 740862338 1250 740861088 740861113
    0x1a010b030c16021f200709020306010e0d1406062d130e0105010905060a120f0302012a09080c0a05060702040603080a0503181b0f121903030e01091e050102071e0302 72
    0x40710307074415044217581002c0c40030401c1d04e40310780085900c800c052402410480280d030000c0e039480c040a500f81e035601e00c101c2c8854110101080b1443e048802203e906003444400420164000e40065240310031200c40f60784d040050329040c50386c5100910000040c800c0a03000b04090b4001c00c82403054214040c20040840c0300d0b030520300420001c1d10016890344410038029100c03c8074800030484128115984d900131086901e86242c1d070a401c08041003044403045660381c0c1d0041804240f600800700940107401c000d0417554615507441c0440713070152012910391016000140003020f080d4000b4000c80000542641504e0b840002113100e8042d05145182c14111602215500c16004009101c1d1400700030821201d460050342054070a040200020b980002000000381001c544003648107201809a10759410550180030780b240131024031008000010098031034100222a0480003442d502c1407403d504103001c4290100c40800d03400480c4690086142103401d04d480000300710540041c010610314004 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 740863588 1250 740862338 740862377
    0x90102091e03030406050f12151207082508010612030f02060705090409110a060f030b09130b0717100924090c090305010e0a1a010b030c16021f 63
    0x360301e030010700290f041505048060359507038005080103908003000c2c41a90030704070b044002603102c1d20306000200d40c1e03414100c041c0003000003080081e0340310707820010003030000000004507101c10b2000c440095090540741c0c044405010516004a41c05509211012484a0f503035144030307a1280c03283d5620b03141c02000c4c000c206e0b00ca80003540e4080000e002045114198a070603040114240e00484110048a005000048903400b440e07200304040303980c400924100c95054405d4812000d800d642c6080203281651410051700244100180032030340001c00b0505d403600c2902e80065083c585290031484d414030403010410341070706200380b24906051614020140a11515000c415001941d02640007420b041e0030700b020f000d443e408002080700401d00000030031000d0285280030040300d4098601d2104c075003800400e4006010406a070305d400301004012009462040781e61141000c0071a54561000890450301d4109c0b10102a40c02000300000e118000e40071a26000408642c2e01c1d600d450001050710102e = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 740864838 1250 740863588 740863639
    0xa1e110c101a0d380709050405011d01090f090b01030f0b070306060221130b0306100302030f040b040303060b0301080f070e07020c010c02040f0914070902131e080609010209 76
    0x800c0c80d00900c130414607521548101c003840508450b002e10300008151900843c40004541c5030000410b003500801c5503050a104e000d0140041e058140c1c1c010500840400f00000184101090103035101e0650b655201140c3c400303085175502c04d410903102d507900e0900021507150880281e82c2c404d40c0300b02261703806000f44034440848410760040c0c280d225030803010407071841d10085c81140ca40800c0003070000441c3c2c0e4800a07406090032000311b6480c2c0c140302d01800000000040e20304c007410710410600c401085450413030381d07009a100c0600c0380d2a580d5454210060b004540c03084801007000720020803004000325503990b40741140c80480e0101d81d694040c0655055080c0d40a20140c0c10031800e4a40c4c44d481140800c0c00a03001400c049503e410001e00b510403034108010541d00c0003440101d20f940c0389410702c490310040180c00d2056040c4207800090800c0c00c010f52013441c05501005000c0c08140140c000700200402c01802a0790080c90159142400b079400b0100b4688030706079052a5042d094024903495 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 740866088 1250 740864838 740864843
    0x1050a06060c1b0e011223120f0c060112021002120913060506040902090909031809060d020d060203070e0a260a060c050901080a1e110c101a0d 63
    0x41641d0402c9440e005520400514100c18200e8100c0011840781007000b4102d000f8540a158031040c00c005080001003002c0310a0440f581c00d030882c0d0030203031410001504030500c0c883c03460710642e40c41c10400c0050301403141154070400e50295500000700045880394640300b890090b60158010f02a20b0f00c201d888400e40c0050f04007005c81030001541e10300745140343c00d40380307016020005890342e00c03400054220307041644600300c06a000100c0d0391050034425680b64011171a4401542403044162125180403040350103035020f10b80d81d00010f4255505c241e01c8100340c0343c010317081b0101611581440000707580200c5103030001c60300c0821105183e0500412003011210342d062a200d0342c01d1640b664016140e0581c0d1520042d10403805284080b40c124410752030142e800d629801d644028401c005404000e00502c078118035860506814100b180304880c104200756070100025507174248101000c1c090040c042d8490b00d40c402c00d10000e2865016901810059118a2420703900008550400080594a0100 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 740867338 1250 740866088 740866097
    0xc120b1206040b0705070204141617061e04050f09010c05090619030b0909210403021309020303040b13030c0e0702031e0f070305191d060304080d06030c0801050a0606 73
    0x200480d03140340401d6000350131480c10318504403050300001c054960900e500342d03a0a40c900148910f04e02c001c8051410b030415820715038103685090300d41d414200d4009241c0390140a0340c403c02c1904802d144000d0442d804010401c001508002006600200c011211103d540d80707812141051107024409494a81c28000e15181c9000076a800c3d00c44880403000c2c0c14400d01d611901078161a5071408840c0d0b01c5201c040c0d004159846060030301103003114885007000a0618200003e1016803905403008014004040c40031070300300c2c081d10200e807551240394010341c000007000c21111445117811120a046038001c07408c003010a52103910403078a400040d5400d1000d60b10408c8071130f82c214900040c2d90b1118408006060030451942c108026590004404500094000441c036280b5129a201a05140214a4240c3c003030050380803200e82e905a08120903215600101c002000c00543d50101c4007450007018040c007600303540c0d1601101040030b42c01501a2175007000001800c1d225a4418013003141c40d185d44 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 740868588 1250 740867338 740867341
    0x20310052a0702030f0d030c0c030c03050327030406091a0405101106070302040617010608150d060603080301080706052502060712210608121c0c120b1206 68
    0x4028074503140704520303110182002e00c001d4015a40c140500b03800e0302c2c55036000c2c00340288000d400030100c500740b1819800f809610031148001c29800620704044980c1805e04964079110302180e100c41400524640c0d41440110144c01c95009001c030162088807110380f500c0c03c24503101c00d240c5009000c41407080707161120a110401c1189041810400c41f0186030903d101d020580202d05810700d032045a40c04e020980002d000c111895000554007604004e0303c14540c9254100300c8001d01216002c0c0000c05032003016a8003004945d40c16088904242e03000c0b504003d955542d04d850f5825800034441c0c1e8007240103030180064034500500807501000542c400d1480b00300300b00c03460200720000030350003a41c10103400d010300d0300010840b503015105101507464000541d501e132502010380410303200507900ca007030500404100c00d120009043c0000c2030500021610780d89148400c0c2c160104d59201c85691134289030a10154a0700311900c084540c501010901403030078251301380818400300d456180300c07a030300120 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 740869838 1250 740868588 740868631
    0x20309011206050f100908010204090605093312030d05010603110c0307080a050702041e0f09020102070e07170403030203060406051c0f0312020703030501140a030320030d02040b0702031005 83
    0x50708204517020350600302031098540c8891422600140c0228400c1c540d680028400c074540102c4d40d41d40f11040c0ca6803040110260088a0b01080f19202c910f00d04020750012124907a8600d003030707100c1000c4844101c0c0c1d11842c10501400c040d00080c419503010a180c070303007200c498031484421200034201c104020b619000040c0d40c1c80340d080d4804c4000d6000c0100902c140c10040e5280c0c0074200c03140035182c2c80c034240e503840302e1403d41c100c640007585040e0051400113201c00503600402c24000300c0d1900050680c03c0e549490082d544483c03440b00088005403810104002c040c0c055020f103000b280c1c140c0c0d0401c040c1d0745507003e0054413544010024141441c0d011200006500c1016081c1418800c1c60002c15444c01403800740706903085068100c000c80d4848005010f03c80140700ca0340440c80045400060341442c540b009082a2580414041c1075403540100e0010540100304441c9110043c0c1003c40d0f4507991134020b40825002524128800e004209554207a240140a554003501e04a1400144000d141 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 740871088 1250 740869838 740869849
    0x30f090613080d0f061806050109120209130b071107060c0b0c031323010b040b0d150902031b0f030d021009020102070b030a060315050c04090b010e030a03020309011206050f 76
    0x19041000120b846607900303130400680307015500080111050102c18803000408402c1501d203150400d078100914803d007004401c46a040d4820100d03010381c3e844141d80c03a025406600d520742900041c00d540c215400b0b10090035408508800e000c01000180e4841544444040f1811034900c08058418128280405c6403010104005c54100c6240c00e00380050000c86d0741c400c5282d402414866810a100702e0110201d00d0003030043c406550022541004164071100c000b510b9843c011b000a04801c803407405024140f81140e100c00403240c1c000f0101c03611501c0143c621500e4030140d0201d10f010708592000d40105007800900a0000d00c0c0c160058485807403c007940320000c00d8034040a80c118460402b0014034444407500841c0a42e0601d000401d0181c1141407104030804008500322049281208001d184640d00e0155009d480386100003141080b10800100c8008400d1160203525016458803070040680001c003d046000c000e8035051038010b54804254110b840a1060a030046405440c0c0700061a00 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 740872338 1250 740871088 740871097
    0x50a0b0304030c080c010e0a060c0e041806050405031209030301170607020c01140d020f09100f090501080604110a0305010e06010f0c11120f01060513050702030d050903040812030f09061308 83
    0x20718000040701f80c5100342003454041c909030152403140c7e5500d07280101c02e5010b4500c46130300006980501c00003100180012032004a060064680ca507540b020508201c404d00840b07030500c01203c402c001508021900ca07403070751300c00e20811121000c04c1c01400c68202004c110b0300d21801c00d81d00075144451040005680e125000d81010b50a102c00308401e0805000502c0a482e0042d1171010b0b0741e072038070b00e010180a00c8149100400040c440ca80c0900746189078401c202d003003641d5003803901080d9511084080350240601682c1d04002c040040392003024a941036000504031400340000e04915110345005507140420041c440380001c03028101c9401141c424071180f0142400903222018000329051598105a001c00b41e02a040c2d4541c041013086141c51411940034003604c0f602044981410b0f440656240300d861424110183c0b180005a00a8014001e0f200285102416a816805404811001036004a45a450007013600b4041502120300003001482403907500204d414411851701e0b1203506400 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 740873588 1250 740872338 740872357
    0x71220011e09080601080c090106050a0201020d091113060819111c1101030c0504170106050303030a200a090e15040c05121609060c02030a051204050a0b0304030c08 72
    0x2115400c000320203800310902052841c1903589000d05070604030755a04181d0103030300400150b4030507109401585d40e0317136a29034111546424440e070703a60f134510b801364064010052032001a17032070407450106000d98184580080542200d090000c0708022a0203800c60780c490007a800030703a1180e44003264041d60400e2600f012400b031141c0c8122900040d002401903100003584080745c03c06510403008101408000704050542424244074814801000070124065849034000165807034103c4020441c084d401207010384006000c0c3c070350f00d25125940c400601000301c4610031001103d1002c0c0c50340380358007003903440c41d4001c2e6840c00c1085140060b51080014060144c03000305012802c0044260303901e104550701c469032a155203885004c5542001ca19080c01441d08103881c0c2c0c80c26081d070380c040e40b060364030055034018240607800204a002091810011000050180c49844100203011002034003910850f00d045460511068550000058500007594002c01141c5031071100c10025040380c001d010038a5 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 740874838 1250 740873588 740873597
    0x1030c0c140d080c0309150414070308090111070302310608010b100f080f0a0f020f09040608070b160f020d12030f0605030703080a1403100807122001 66
    0x10501d07215180780380484442000c050380b0404140c81100d07040304103d640b004449407105d0551404501d015140c0340401080744164000100050402c0101104103140e46420400c980042e0b4503843c0c074100740d9124407025404220340309401c0c600c4c40c030002414400d41e07a0140423010707510950150082c008403980081210f10800d40590070702c6124920500005003403010010520040d04414080500590000d00c0200030103074600004254100b4501600301c1960008a0310ba9982d0285400041c4504000d0034151400050901840c0c2502400b0f0044060200c5003003000301c0d55001c40d9039603401c2520443d080c3c01e609010a01d003030f0b02a204060070040c0646001248130388507500083c1201d4010f402115007800c0b805882d4445a0b040c0308504030300c038005100300007840c20880040d1307032080e443c80001c01c1070400042a03217510b4882c10b000d2900d42c40d81c028254490034045110040b0f01c125001d149400c0c803e40b500014080403d690031340426400c2030020f00c038640c441c10b402504400c01c0c01d10a0511 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 740876088 1250 740874838 740874857
    0xa0e07020a02181e010b190e1806090c12010b0f120702011416020309040b06071a0a0c050405151308070f080f060601020312070201060f0b030a0b0405011401030c 71
    0x16142d00041c0f01c10400c208103012110f103000d0445101d101115020398508502c0540188441240c2104032441c0144030061281841a02c0008075460030a40741219003044200c00c0030140031070000c40c2c03030340161000c4452501c1c665074505041e401c0d014140303543c0282042d10b001041907a09080c02840c0d124002804180b0b4500100441d40c84c0103000d60300000141c3d503d010451411a0003040140c00810701c541602203e0301d4110000d41d00d00604903260b05c03441c0e81d12148156a951803046596141d40803813880c030803030004458003130b6040c000c0300c80a02980c200002039852600c182c048800741c0300020b0502106030b10145600c0c80c00d402448080c480550b0200c0c000c14510402c0126034014190344024481c0c0c0d6027003400c2c1e5400c2056080705a00e542d0704c0782c418080701e030f0380200a4407148400c81c40c90709074030703036559004a01400d100e60210508801500700400d10012420095206214804051142005e400306200c00c444007442030705148507a80711940c41c0380d03100e60810a1061100e1070445000c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 740877338 1250 740876088 740876093
    0x2031605071e1410091806080a050c01080a02030f0114030f0105090304050a14030604110312030a1d0604020306010302040f0e120a03050702030406050706051e090109110f0a0e07020a 80
    0x10b0404000702541e98642e5007404110315003011602d030300f9040040c0d908008540d5146000780c5041801e0250340003c140c0c1203201240080242d100100402e0350200300c070b825900c17a04005459040d041c004900080f10207001503d00980c40c000c4a00402e034580c440c0d202c60703181c062440d2050000305003495140c0681c03941c101685400b400303494000c0c49054043e658980c80c1000b000690308a83c1c0c0300c1141e481084220782516035010800070361007504082d00214041c0c6d60400039082060580240c030b281c807004814007101021a6005031003000c00004141020051403480341e54890003210300a6040c0d202c0d400520050803d90001002c0c2d0303900180200d4520401a810b60520f51008240142e404000c2821141c0f41d6041c050b42e9000701160015500e8241000700041c660710070f004003c1c192940f988003090361804080c0394201002060008010b0a00300448080d0191003000c0003650302844411815615150440701120760100041170403e40038540760840528980085c915001d42c041c40388154003 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 740878588 1250 740877338 740877359
    0x190b190c080a081012050312090106030f050601050a0b03091b041b051e0301060504090902010c0b0f2401050d0e0f0a0c030618080d05060f06210a0506010203160507 72
    0x40e6642c142d11811442c0c50041143c901004443c0c0c82000b000c10f9111400340400d2003c4200c0b0741c04061014000a203688454500c1d0140000d0b50000300320041998440d41841004900a4180d030000c03580d01590075038a01021f02640003e9416940303070380102e1400e0f03085d4a001201c0010b0b0842c0a800460406900010204038904144c91440460000902c5d0208901008500c0b01c00300311200c0050f003103506001703008155000f01e01070710001a90303810200c01075a0050601e9280c455010070541c1491405070080c542c120f00035910020041104c51f4100025100401602c400c01011f079145410041d41030003050180442007002d80041c02520540da080c0076040c8a1442124001e08182148515501d000c1c070803141c011009044100130340e1b1006c00012010780803250242c12070b0401151326251072001808800203030107100c0d40002d00041015902c0c461021a1f01807040030700300c0004642d50040d0b06419075074100d94403070068008000b5030b0601c0d0140c1405032580360240084805054903035840c0030703 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 740879838 1250 740878588 740878597
    0xd0e220509030c160e011a0d060f031e2006250b0a090b04030309110a090c0f0e0f0409081c0902040b0609030a1103010f140402190b190c08 61
    0x2181c503003000030041018201040041d402038008001800c0d9145844400184a9010b000300d0a405184100e2405a407035107200740c076020b0300182e500700005c941d0341d41380b80e2800e8864401203034640c0c10b5191300700c20041c40c0b1700d03039851164202000200c80603400c600d019030011203040e0507a000c002030015082d283c900600c0b084040c800890302c02412403441c14810072200009000d1030b012400c240401000496140640b41c03c07560600380424498075902d0102c0111101000f407035048000048001001d44d495048840b5554031900c640018142150045800c5a041c0c980c9640000011480b41203070f0820364814a0403e00647d10325060590305a8004180781841110384107690f100c117070190a52520f4402d1800701d64048a1280c0f0301319056001c2030703c0d002c0c0e49030050705050296000d000f40e601c0030341100106041080040041000210b04044400c4054409038055030b50808030401c481010300070074058509850034030f81495103412038101c050180340c0051040007551a60b01e0b0008441c1406807 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 740881088 1250 740879838 740879851
    0x307030f0501021b0316021c020301054f11060a0e2d0f19030602040e09010203012106090b0420150a030b120717010c020d0e2205 57
    0xd80c0d02c030104c2c90003407085494002d01d041079070802c0140b14042601080b40130003541e1f0543d00070807100e0100c034141070101425030010703405500784410404480e41608031040308000e4981013116a030311354211100107421200401c90303509000114103403188400003042075090701c41c488a000c0700ca25680400e280350403281c0d008021900009040520b460085c01c0001c0c00e0122540040700e8264625040840d0400ea0075907030301840c01426420b5194907a00c4031040d6101d25030b03860f030030090350701d290031002548144501701501808002003a1001018000c40c0c1c100e503007010036074400c0326124612941b81502030b84102d03180784d41c0b070b400340340003886051109100390301404908181400c00d82e5010207501041032403610840045125201c51840035050784c01e000c0441ca00002c44c0d080c40004140001c45207184501944a5204000794000d1494150071141b41e07040c0090040381c02c03c400c1603076241550307960400440c8264811040d0307030600a110080c1128807210700019601ca01c1c04450440710b09031140b = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 740882338 1250 740881088 740881091
    0x18010c05190c02010e1210050705070219030b270a11011e1b0c12121b08030f13020d0b012c07080702160f141f0503060307030f0501 58
    0x2007041c6002514025001d00107541812501002d07142c1c002002e40f99401240c0e40b01d0001407030b92190417042005101280141300304100114100441c0c0500a500100400c0340300e40e4440300c02c401c450450120b410112580001d40340340580b110900e82d010003640344145a01c850040b40e40c1000e142c02008116003542c010841c00045040040005005103120142c02540b6241c0b8a03060010310752110405048801d0820360b031440c5030b9180362040481d512580040881303c090340707036a0280400014910410350b0b5640f110400d00b00f41c0c000004e14551049000b4106043c184000348190001000f201d034400358101090207201e410b0f60019562084d91001641c40303428910040c460100c4040c0044020f8500940e1a0b24040d00c02d50200100302d0002c00180030007a00c48007140b00c1c4c40c0204074030007030074078050784654117103840d010014020780c4a4454200115900d1210f400365040048011340c401e0641105041b82900052040e2156440135003d5178140c480c014000010403600d60101c81c90a00c04e100 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 740883588 1250 740882338 740882347
    0x4150c090f060201022805090402070b0a0c0c0f0206160803131e0213020d060f0b13091118010e27063a140c0405220b18010c05 56
    0x81c0282070340c400e60051003d6a2041014a0303c040550307212400303404071464006400c90502c031041740c40340514490079070031600216600080080041030030380300d58100c040402c2150712220701210b00c1c80c040e0324007914800140700140e0140c1011802001c803283c00403886c181c04991540c81d5210703540110342d402145c0d02d0310204035041010b8111514101d4513141c01e640001d0501d81c000a85010f868482034058035800501e006404000740c0100d0010522a8610400c40369103180d64121548400811031210300d09000104404c0c850b0302c5024042c40c0000030701d5091540f648607a19500801c0d223500c030705000c0b15650302501035031068030701850440d000d005410083d2044c50402412403000e06142d10484401c003843c006e0012010020b60400c8051007680c0c01103008170115410b88040010103002c0007d200d20008404e13000241e2800c1011090f42c0400c0b05903184424021041c81a00702500505100811200481c1c401c0800c40d82028580c83c034104100301007080c450845120048402c04202c000c213 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 740884838 1250 740883588 740883599
    0x50a0209060f0a1d15130902031f0b0f03060d050a150213050925140a0305270c010c050c04060602010606180e3715120b0f04150c09 58
    0x30b80e401101c1900344409940543c031000245d04488030803503803491043e01060307204503a04100107550080c00c0750303002150b80c0d0030210103070900703180c0c10104001c1c030b80070030800001e00c10002800c507014502a002644d00b544c80310020011328142002c8213039800e2003501d262102051010f44990301c040d580f0080140c1d5082900c484c0c180344146030388014805e461803400c016070800c400300c00781010081c85090381c1043c08100019503414580c8801c0c0f03001d4542c0403810294030380d01540070701d005982d520403d0741d4800d41001c5a8034074404480704440540c12984109850794054820310318007520450640384c0c0390500c040403a007141c005074800b40060391254810041284c00484904594240500015401c0c4c241141440b00113005040d482c220b001d03003042c3d00c4003c102081264441412001c10128180c114625800900510014501000795400b000224000e0f901e04c14141741d98420501201036407100c045240c030310700040c41520803480150a02c14051b105105131a80385205440e070b140d0060521 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 740886088 1250 740884838 740884847
    0x50a02180102071203230d020a1b02010f111212010920041e03080a020d09170c130605031504110406050f0d021f11160506030a050a0209060f0a 63
    0x3004480e0642d0050001030000f034401903004420580c240c24103521091000003420210310104a202240c050041940f50f14074840b17800a06516001e0740e02d141c490821a0701c2e840d0000c00c1c005009000c241005840349180b809805004440c44400f41a40c40070107078088011035a038001210420b5100d1284c0c018003403103000344505140c60484809096800b03040310a804d0442c40355000700b010780d0f000d03c03000d11000c05000c070060300559806a0b0240d16066004030187d070361403052107210041000c121001c512110201d08000c01415445c004001c4025000140610b12000d0320124081a894507004034064070100301606030749038944001103443c0b400303080075607420804060443c411030030103038108003c1d621120113803800003044840300c2030307102148000761110350144041004080781c440020748040d0001c100c010b0b10603d000941e403081514484003208402c4501900341c1c444004d02c0443c40c5c000e03040d4070641d405050a2001442c0c44240000241141c210004e42c00601c000041c10300d1215501 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 740887338 1250 740886088 740886127
    0xf020c060403030c0b13030c060f0216030309140f1b0406051c0606051c030f020c040c0e0306130b1f03051b010e030a0c050d0f021806270403031a04050a02 68
    0x141b0180024425641c000701050829000074142d01c2e110702140c03502010340d81c120b0784010805651134142104d00d19011380a041d10403001e03591301c2804841c400380300c100401c208201c080c0300c00140603665907410446440d129034020300d94206550788408a072684680c0440c00120000c911200303210843c510340a03090742d0882c0c020b40e0141e480c040c1d4145243c045a0903000c03c0ca941428100346000c03900744100d00c0c01d68000c000562041c14040d4485245802011301c1c111070783c0c01d809803021950b90b5007451078a60b00540d0001c0c2192480e60000f800e42da504111603e4580a810b4851035403540d82c0c503558500112a40c204500503444001c2c100c440da00300002d45c40d5407000760b01900c2c0c0b80d10f458403405002d01041c411140507034a00f400b42410403c0c43c2501409840e03005003421900d004a08070b88a021380210b03600c07401032a4414440e203032002d20004c00c51180581c400e04941966455404031b01500c51120142e0000e61101c00600540d40c40d4045d0138442c00d0109001600d410340040d115940340790 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 740888588 1250 740887338 740887351
    0x5040f09110913090606150e0102010207050309041d15160201140412090315020a0f090e040312060e0f040201020c0103020705030906070813031506170d0f020c060403030c0b 76
    0x140000c0740307642850510a44814160460320602450008541ca101400b201440140b50310724010b8040b6248a100c081701580e1000c5565984002e09004016400c038850703010040d01a13030061000c07849900d81f90700004144040340111114021440500e20302d070451100322003407403a1001e000c001d4400500d201c001000820b500c001d0145808489241d845132001800c050b03d04100c0311030300c800075406402d0f108001c59000d802c22540290320503682000350030070040c510001d29043c4003540da40d446680c50409540411804030060b80b1103640c1500c0703090240d11200c175851f46418000404014003441541319402100850240d0b06e4980f000a040408682056060520501c60540071030000011754504c1d18041e00d02a507140c102d814490b0b054020b5a0021038207002c03110b00801044250988500c04640030350080c8841c68440503004004469886520150b5014916507551144102208003560040c1c0c0141c9030503980c280040307441d41c2d0094000364080750f1894080410050842c500d15403000c0d = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 740889838 1250 740888588 740888591
    0x5030a03030504020f0603010303050a0e0a0f06030204030b06010e060a03180605090f061f051e06030c0d18020f0405130b0718140604031202010e010c03091a0f1f05090705040f09 78
    0x107040d0b5a01400c01d008501807933040141e01d030510b09030b548407400a68041c108411501d50041d5540700010003a5000340811a950700b007101c042031580d4095454001c000308024000380c01c00411003000c41c02050801071007400391400c0d082d01400f186941c4121405910ba030700c05007465000800e40f49103454805826201c001d84107064001403046400c500300140c8071704942c00707840e0f102c10441042c00d6040b100d1072294010400004e101c4129860001403191801005c0e003030068600d01806d405c650202400060341101c5c01c1c20710681d0342e1a19a02043d8050101aa0012070168548950106107000c944100200710030404100c8000440141e0074000c3c0043c1203520106c0c07000c2d001280d110b010b21b11004003031742000c18034421054001e40080603801006c40c02000035407600c00d0002c0c040c0010600030303515071607607210060010040a8180e0320489007144c03050000d480c0c14000030b0f14644001403c00269803801c0010a2a90718000c030386000e1840c1d5030b1615103030350421803002d16a00140d4004241903 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 740891088 1250 740889838 740889841
    0x501120b18030a0e030304030b0a0c1409090f061201050c03070215100e0c0408120d061e0e06030109020a0311011b0c03020103020708040506191101110d05060a05030a03030504020f0603 81
    0x445a2103800f41ca0301c07180f44070006010924600654000414061202080196803403150380650780341305c41640c6400c015562a22441d04900c0f9807903a264120401d540050400d181d00340c40940c1040e0050450134402180380d07244c908551041d6140311101c2400014003065a50400c071070080050050f0f601c0825090180710308078018142c2c401c1003c02c40414001620b1400643c2c02c0d200248030000540b820200785401d541900da1001800c0b84059241c414086515601400e15420406c12803580030445410207010569007000103025641c10340d00d880310040161121401540214420f401105550002c0000134040105e06107130348410840e481c0707054000c02d485061030021641c081c24016943d182c581030103019841281c202c0b81d00300500140314500b001440035a021043d05540d0341901440c8444a5107080c2c60007106d0781110484244001c980800960b0f0243d600014010003e0401c02e50b104042400c04c004501d0070340109988004020070340c01e111400309a449000ca4031140b86 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 740892338 1250 740891088 740891131
    0x1080109060e0a1a09090c010f0908031209100e030405130e0604030806010c0204050f06091b07150b04060e09060604060315180803180f1207140109060501120b 70
    0x103203034014048400c03282c40d02080720b4241c2d85152240750000010f00b19030b505d40780030144e0756076441c100500e4500141c01024902c0c03110384100c1050081d65640700186260101100d400e00381039030094990501400b4007a500d0801c00d05511521a0b03e150f29405141c0712842e09041200201c3e82a500100c0f107400c051154201c2d890205040364080d5050030500141d8554000480b0903482d482c0000390428645014800c4058244840070b00c64441241c00b06c00c60307a2500480c001002c0e02540c004860078090046030002168510745028001c902030b40040c01850b12000030303007500c0709544030304140c50f424418000030440c01e000e02507200606540c24400d0301e2840d52007640141000890905442c0c0d101c0c014035a19081c42c0030445d104d0b8100c401240c6a040c65075502c04101d0088034044543c3c0320380c4851440c803120200700c20b910708032510603080c145459030301d40d00720280105004040301d56954920b403001905920805010b402c03000d02d51900705204e483d1850311500d0241142002c2ca080b10103d286c0d = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 740893588 1250 740892338 740892359
    0x3021e0d081803040b130906060804060e0705090105060903030d14060312040e190f110903071e030611130909120302161b0314030c070e07020d0f11010e010b0108010906 74
    0x2150990100a6900d820740342124241b0751094001d00c110b01d00b071120000781c05501031065801030740115010081d480100c1c003881e03590032032845060303040b010300001008146043c40203080a03c501500f6640f5000a101094003101e03003d5a008607540440c8050010a00f41082004001306401c40c50034034090038264161602d403801400700040c8521000c101603501c0c410b0b040062609444013041c010300d04a1420a005c54002e110440e000b0303c03900d20005820b07840100c00c0a2a01820850600802d08548884003e00140c100c0e510f00604200001c50351314480441c000010001702d800010610420f1421600410b01360040000701401440b01c8004e10200700b81c2c024185510941da40c100100041d081900807106034409060726140c52607000e02c0c00004801000f480c001d010903100300c240c42e88208039008006a440600607409109804010b43c060b05011490a0803400d1210048003408691802e4880c994210b00141e51a10501703101340d60032a46007030144c507201e2001e0000d075040c02001c16 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 740894838 1250 740893588 740893597
    0xf0c0a080c19150e01080604060b18040207050d091a09090a0f0f060b04050907020a030f0507051914070f05010212210c04061b0b011203021e0d081803 66
    0x10311524105a652100900502c4140010314840ca950b2407524881c003800b8041343d152450300ea010031204030026040e882e0506c98107059604840d02e10341032220026200d170041780d1010480ea040ba908000700741c0450800c1042c1a501c11050f81d80012107810641d940b02c07078640401c910354480300306026041ca02c0c1c9c0e940c165150300104a00c1e00280d00007001a09502502c45800300d595620716154020800e900c030301000700182d440644406000b0b46800c04100d945070308001000e00041c0c101c2e0160151540300348014100c19000c0c0c0215940c00103000380b262110403900404540c030318695000302584000600110000300000804200b03088e00d0100040d482d9201c80000e503410040010380d159a1224110029007030f4803009000c60541d2400d6443c5601c10341c4203000d00c0300842d0425103070039100f80d24503803821901d90384001000e8040c1d113020151081c0403260301044056005004904140082644201c0e85080c1c10303400038564807039480b0002e4080350000c0c0c00c01030719406520145620202c0002143c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 740896088 1250 740894838 740894863
    0x4140f01090b0c030a090c0602030d06050f010e1504050402030c0901390302010e030304080c0f030f0f090d06090b0a1112150619050a17060f010e01110a050f0c0a08 72
    0xf19926039400000720014500380c41c00074a666844240030403166030000c0a06040917091004105081d1100c04101070b402400105c1030000f5004101145607051407401d0001c0c1c00540213146061a4030341700060140d81044031521600c01012503081003960780f05007403112090403001c001c680009804560110b43d080701c010114452045850802090300c03d502c030044c0100306509494480c1428038181510364401051201548204003528031141e41c04411100b10598210035685407034501c06804407640c104800190b406030060f4104004904035015540403240f050390700300340343e191102444007101c00704200071840c9902800900c00c078802048032150080341e0b1208089002ca240b40020302c9c54031802c04c5920034560f005049032005d60f00100074011603821034803051410652030030b06141d10354003110f4180c1c0c0500c0c3c0c840d01011950144401005005061400f184001070180300d50345040c0540d02d007214076900c07503011950454014050031981100031140d51011030b10702641c850752030182d903655 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 740897338 1250 740896088 740896111
    0x10912080c0a0c03030510080a05060423031813090b0a0515060702120715111009030c0204240321111b0613030303200a02071a0c030304140f01090b 65
    0x451f20034102c019804004124040071202c0e12a0286040385c2c55282c10f9500f02e5418112401a0452400001c401c6039400e0640d001103081001000343d4041c0c05c0d4030000240c1d040a94240c800c17803506c602d40113110006002e0380d002d41c1c1d54100101c540088807001003061402c2c42c0f03a101d41000c1c5569140444182d55012921204608070051406003000b42c41c5d40a140d02c90011602d0180c2070360040d2103041507400441c1a42e45031110401d601c805d071001150020001910241500e0041c9025886071120392406078403903040b18034040302c011140095130000e5440a2202d01d50b41c0a501d030070b41000101e12118a00f841c0d668805048859640207141d65035884900480c0380d000960319200c4c01e6402c8440038401290354a6602e0802500402002025400a44c00c5488902d08280d02e0001c4400b8500658014910070b8a4000da81c01031416a6410301300c0036000704200c1c0d000d404200081c0d80501d0040d00210f20480c4c0600c2c51520b0048081007000030f69040062540101e0303803c0005961003000c9102c1d = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 740898588 1250 740897338 740897341
    0x1306030506060d05190207030804110d15051b0a02010e070f06090314011b0e0f090402010909240303111027020f042c2b11010912080c0a0c030305 64
    0x100c805c0d81807214003c034810707102003106000d00d58040764040c09903004100c00031007001c0717800c24440343c0b9462120141202c00c81e5540344840011644c02960b100e01ca9142c851705200200160380c0040d8002680c85005070744910100d9030004d000c0c0034000050a0900d507140d025842c01b00c001d804103040780700240c903441d9200c11100070901e0030b40000c94454000807030b101400d40035200252085542c07001480c00ba081d140c0301c0849a003404006d031401207405840d0401140e2030190000c004e032810808000c2c2402403034483d134800280ca0140382000e903203c0d482d40006040d4212049140842841036110715500b0580c0c0464280c4416002d4001d20001c200031032500340700c42c00031858031130710310408075041440c00b00410030b0341190114000c04a00708105000a450030a0f030700135030b00c01c000b01036a0051109010b0040d64000c00c032003001940800c81c10014116085025558211480316101303688603480c00c883c0300b0503103512042c404e0b4131143d42c00c0e0302c03070070009100300041c02e10130103900c02024540e03210b0 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 740899838 1250 740898588 740898601
    0x9091015231303061104090c1b080318060a090b0601091d0a110d1a1005030604050405210a03050106260402060f070503192a0c0e0c1306030506060d05 66
    0x1c02c0c25000c0c581020b0300b44a55058940c1c07814180d84948100c94402e032911340d040c003081e81706540e01c68280302000d4051040324001c1c0c40d800360a82c4043d00707035200e8402004194001e0842404114401c4169607400620402103083c0840c2000c0000c1c8a1410840d840d46c0503c12000601541c540303843c10300d8152070150b6100c101000003006c0b90300c3e00312011100800d500c2140c03001d07a04070b00c6010303483c4d102c1101840303100d02c1072000004000b0003010200e0028000600b05043c183d000c0c40c3d005000d10700b11804019021201d1101301034121803400500c0d800190412429014010280103001900d000b154126145450214244098802c40c40402680020600b5940c0700010740d076045060300c000030340c0d0310150f00c1c04a503a07a0080c1900040c5e500380568099549000341e80c0307000380e01a4001503120046849038211a60040311004451858948501007014482c0c0e10069109014030f0540c0c1d030380d4540c6d405031440b1030801c1da40140205414101080040e488100586042c0300c070404010030b058540c103 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 740901088 1250 740899838 740899867
    0x120f0909020c1009240203070e04020d020f070803150a0303080a1508160602010b0405101a0f0301030605041e0c090e030403080d060e09060f0601050304080909101523 73
    0xa250500f01d140c2000982c1c000c0c8603130345552200c2d000d6144c41c40c00fa5010b20261400581c003045074030001040c2940e602800710700303268004200303000482030700500d4a9141c1d02840c50304c0e0005802907820b000044208600b00d00c0d0b0300040804000102c41c2401e2103440e554005001c204000d207243c0403907440e00601036110000c4c0b00d4500142c400034040e0b03001c50410a050b071100c1d042d58031442005609101e84502181428840c1902440c0b402039070509180c20071940b1a0005032104003030010210401816210100100c0514080c5101f50070104843c02c10342000c425075110180c12244141007075854100050b440c0900204903040400082031030340c3c0d10f1401c2c41c29401182c0c009880900009919005021070303038402001da81004c0c0d0f03020582e4a40c000603c2d907030a000c40d000c110195001000c51155030041c009154014850314101e0300c1e00c40c5850120f40461030541c3c0d0581c02d240d03441c2083c410600060304020b811800341c80d00b995034502c1031003001c400b142c46521010342d03010001361000c4e80c040003 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 740902338 1250 740901088 740901103
    0x809040e0a0210080703060e1306090222020301060f11061f0f080304080f0312010b130510030506281802131e060905010e010e03011d030304120f0909020c 68
    0x9000c1100b00801440203000c8040848030b4030006450060003090a23004101958080c0500702100401e820455480000078950040240d80c080c610404950042075035030440d8010701c6030403c000da200d501d08400502901e10145039001402840f0311426111440020615803100348840f004480a500504d40c5c41c0f202c299801214400004001c08134407050000010000c40303980300700b1a200041420b048076281c3c042e01c008050700100340c030010000242080b01800401e441107121100243c1d40b6000903405034036030606100440e8a841c200105860200300448420021412044020840c0b52074041000f805000721804c0e2044903620001381ca071180c1c10307100720710182d0b003846402903110001c03000c5c0100d0700d1a941003a000b07050800720710781d0303c103a10300c07011140c043c0c40b060003018090300191941011088100c2c1c1545d40e80c100002da01a44000c1240d480c0b03101c1c800340da664181820714000380b540c858900014040170200c1c00c0d490907841820401121000355005880300d02032417403503041c0000c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 740903588 1250 740902338 740902343
    0x8030609190905070509010e090a0305130f06030c021006080d200604051605030d08011215110a0e040212062b03051908060105030601030c11060c0717070809040e0a 72
    0x81e002680e800c029001032244142d45c0202c44140440c1e0703880401d0300240100b194001c02c00d40000302c3c00b100185c0190042c0070326803401d080004c61940c580011010034101035201c100040d44405091403242d0b0180485220390000d08003d01c5039900f040421035079044055003120402c0208000d8504450440f03208003a1440c500003651518101802c0003580c40000c80d43d03000c07100d11203900001c2c4070302c0d0014640700040182d4440002d261300c0e190784070145820303005041e00c078051500c0d11000d07103c096201c2d151405400030303685038035a50403c20040c8600340e40215940a00e10401a802075580d10102c141d40c0010110f42d0341c0100c168040402075250301c84e01b01a800e0000e070300602401c041e0840050329084c04c8001030382428040c591821582080281c921601190040001c034000d54401d40081c0481084d90030700b03d541d100b00e403110740d1411404590209600c5008100e20b410021050b0600c6090340d03007600700030304000140d140c0786003601c90401a9449039599904041c418081842001c126a4 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 740904838 1250 740903588 740903591
    0x11010204050a03060902030715020c0d150c050417030f03040f0f21080703090f12170a0204030611030405030f1804050a050603060a1a060d11040807030209060d0803060919 75
    0x1643c0349003160250800a808078424051100003050300c03803c080680d68040070f10b500030300e85126403400780310a40070740c00010382e901c0266080316800c420043c010820f807044a40d545030794a0786404054000c0410400080c1d0307058100b0000e000c175076501c92003a01d400c03507044620a61100100d10b402c2e8284514810010310100c00301c906011075000180a460312203070070391101d90040c0e5911000b02d0803907040c00001002802407100e8000440c00340c147e0384040d0000350606041014050b510030700141422680304010540004040c81048003034014901000c01203400e290850030a070303607883d0300c03401014110b0103041d0004c038540c40d80e040094550030204001800c20030180c100f00d90074030b000d00302c00c5a00e10300901c94500031034070320a224072501400000501c0d8000c0112035207401c01c002580070184180c500364541c2407810035400ca40c40108001c00c0084014683d5510750301c140600c000c401808144224500c8440e080483c40c43c1d0308403035104804a61a103210f07550064541030400750816010034a5 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 740906088 1250 740904838 740904859
    0x302130c020c0a0b04030b0c0f0703030c020f010e0a05070b0c07062d080403230d0203100515070b010e0106050f130819060501090c050a080403030b2d041b1101020405 73
    0x7000d1210043c030940c0c1c0a581c10000f0b5588000c048100d610440b01d0a009c00e40f8104040f5010070320a80c0240200c02c42032041c0c595081b0580030040c01c0d50103c000e1038855801008201d01000000c211080040c5010b042c0e103410030f4000c0078580c0c0c43d2600ca208100c1407048815901d1101c0120341041080541614611100062168001403000030201d4084010802055200c550a1481c4101404000a031800585005003111488010f50070280c0301020318440c0500115035aa905401650f045151149083d100e80c05800c008500d504180e0242800414010050000503030020455030b44560754004559620101a03450140210741e078081030143c040e001b00c0003000c0f412007180c0424280a410b0a200356600c03070f01d45204840380c0e040179201080d41040462036280c01101c09030f6106000c1e050004183e4503900102d180d040250002d030044020010501c080548103e400c0659214269400c200704d141c04000344407003801c01c200f10000d10040f2001c0e50107403442501241c020300805800300480 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 740907338 1250 740906088 740906099
    0x902030a120c08181e0303030a0b0109030212010e1203010614030c1c050106020d020c1e030f03070f030f0c0203100f200c07120b160509031506190302130c020c0a 71
    0x8009020203040e10403000c45d4000042020002402200c0c28002005140703591030f2080c0100060601d509110306101c034030040040543c0e240030b81c0250002d180400850b00108010b0080d0405542000321090640e080c00140009940302d0201c002e600741000c8802c2d5030740c0302c4000251440c068080c200c8500c0010f000920b80301d8172280c000710304032030040d000c44004041d092011307a1128181c4003a590401d110444025014403244603402d082c04010b426154007044c8903911034115804039109442242e20282890105039200e100001d06902c98640306c00841c000340c2c0080e40f1000c50078510500903854113a1270741214140d0303000c80c9c60098000040c6011010380700449d0000e40020f040075000c0c0c014900300054084405a4101000c0da00c00f002421070303a14800044506030102c00e54804204050100500a40702000315003001e5010300621091441c000003080350b080302031100540c50340781d482c01c1040117880f50104401030b500504004a005c011b2000120b103828031040d00709600c01580b4000064 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 740908588 1250 740907338 740907367
    0x2705060f0607140c0301022106180106020d090e0108100f270c09050f0a0e010209060a081602120a030203040f020a030b0118110708160615180902030a120c08 69
    0x40103e903041a12000c004902c01c05080340a61784441c100d851000781640c110030725841103968040c10081084912000b90320032010311500903000325026900c103820018089803c010000001c0915014034107056040080322382d25a40070026040c070490b2584500300501d00180c20040e807a24504100d28034007002c808a8581c0b01040b2039054840c00c80d0200041211400740c09598410310344160030b01c503141c0350035107100010400710110a0441d5400d010b124966502d980080c00c3c02801650b50080e181804ca001040c0b0000b0344582005650100c0d480d81490150401034030204026403c00580320795541c10020401101030300300130760118100710044100410181428145c170004031000300c402c00031404003c119a4004102c1d0030014003408400c0000d89098028400c0c00440303410360411405a82d1000c065994440c1c01c180d80000c82c680912910b40c080c04411441458410180181c1d1200d40109469013130604025100e840070b11900d200700d6018400d00f008080d4045441d69a4054400d6000c4 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 740909838 1250 740908588 740908613
    0x10f05070f06052d01030506180f01021801110a02010e01050706060f06030c0221070b04060f050c1b03070206030c0f07170a0e0f0a18062408012705060f0607 69
    0x14903801d8502d1942401c484c0048107060301d0740302000302000d44a600d483c6c09941c68110500b03680f03103d1798010504460003030000c0c00e000c11000090b90800a08500094010101c80e44105d41a80c044e120010140c0e1b400301c0d885050781402e003041c0c0d43e24951420001c01400035908230791443e80f1000b03000100c0590503404080d18007400e40c04d460803042c00c00316840903e208107404201030b510030f0007848085640040410780152041000042140c1907244580c1625411581500c03501c01c0465219240c114803281a49181c02c8a40a54036160450340040c07064000500000a5400c020903007142c001007401c112080d0540103a283d8564880800d00c01a0580c40084e1044c0000d180b403412410300e060816005080d01801000d0025103400c00b600820a0b0031074410b81130050780c840da00001d1000240c008040e182c1d45074642c000404e440c0300d001800b00b51040c0d2110400901e0b0340c04d441405a002201210186810344003c00c841d142c40b800035135620540702206601c44000078603072082150344015030 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 740911088 1250 740909838 740909881
    0x603010b040e1003150f180309050324010b21181b0d11041112090d08070903080702030c120607030b01051326030a0815040209010f05070f0605 63
    0x880c05036480180c040d920328464440100840385c0503a100d800d07128075410900c1c07000c1e042d9500207804203d40c40e04402c1030200b0038040c0c0c01706640d040c0c18007141c1424051018070007007410101c1001048154041c5040205114070240e414000c651600f001d2182d840140ea400200b4550341c91900745820540214150041543c0380382c0f0900405000e003100300101c24115100083c8100c1010a0070307200e00301021060318009078065910100408015882030140c04221021000b00b142481c0101c0c1e0b0304d00c0c2044800e140024007482030308200d1065480340111065a9104d0301c0340703490703030a20701c042407520011440065010441e43c6114074108000940740e07100c1c1140b0f503414071011541100564051040d00c0704120340c06804d41c000c0c03100c030f203040c0c1080e441c4041c20f8110801c090034007410541560040e104100c00524081d00b030000d5241c6004030700081b00d404490451804188100180030894941000003d02c440401d251050000700001240032941280042c89285060138403807810a1b40701805 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 740912338 1250 740911088 740911109
    0x506160906030506010909020309070812090f0927010b040f020a020615011202181513080706091a1303030503100e01031a06190801060311090f01050f0607020603010b04 74
    0x14820b48640107090188a041e1500030380301e810906144043d500040503030701241300310758001440000410842058000282080e900d560702482080943c0b405031003c940315122280c20710107075142812040429146580103407422609000c0d41a02503c00b159680f9445846e03c0040405180541c000301880c080960a0350760981d1444001039844d006880003500142c030410f5400110842070340109040c1401400c000c409031440c1000030710280001c00c9121141002240121080943d6400b0358090012030020b00105418844020001c48280c4940c00c2c0254200d08400f618203c058202c0b0b040002000ca428042500e034100038195038019210b01c01c00c0010504005010480c103001c150680394003100c07101c1d84041041100310203c4d400380071146d11503c0c082141c0155405003101200500d020000800c0f060701d981050030702c3d8094411005c1c0101c078050704101410a0b05481d040c10f442080310050700b41d104001c08204a40680240250400d1000001003684440340000e001100e206616 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 740913588 1250 740912338 740912357
    0xa1b0302030d0f200a030204030503070f02090c070f0305070311030c06040b100302060405062a010e0601050d260d0f06081603051902061201030305071a01061d030a050616 75
    0x52021941d03a413640320892000e070612070304d18013004801001040d80c5860301604007a1aa00d441c0c0c01d55110030130468070300d0740d290007540c03c5042103602c0d15408070f24107010504000a03911a042d41d2059000c00908020000810100705406040300f111500e1140007100d8444c90307404199990b5141c12f450554841a1980004903800ca02d4142401943e49c09812107080918000c01e000507604a100c000f0100c3c02610044000035007840700248181c0440000401c0ca19400c141541c02d1510681045000d20129000c0300007241c60401d4106415004464400d030030051035041011900030060304da096607082000c0c14403103140540195040d02c5003c0300380c4040780d0741141c10900c845650300c0003c100f608200ac0090f052145003010a00050001d0010303403501c058905011942d9209030004c4022600119015051003903504103000b4543d208500c81a4a505101c0040e150141c4a4a10561809100c0340350055440a016000c0d10340e6000e8121003241c100322041e001880032800c10640002d15001 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 740914838 1250 740913588 740913611
    0x109050f07060c0602070c1e090c18030b0612010e070503060f070207031704050d03120f061802070f06060f1703070839010c1202070c05060a1b0302030d 67
    0x68a508586140d103d4501c001444d41d210000f94102040a646c841c0c045a00002d084004080f20790b2403010446030840d0103803e225004040740c44a81c042000c00401c40020035a01001d0307002401501d820007280001590f5000c000360550480f0058050709500b4044903031078080000400c0e10036150120140c45660b5622240362001c55000c03144100180c0c44502c0800104d07555015020954102d040a10310702901c0744049456034814484c203c0014101500c41403251005200361460300e149800c2c140003540c41c0100c2003421131209040740d43c020741d0025188080068405054441c1c076808803007849079079510b050285140706280300d0501d03900ca82a011101200012040712040c0c0d40c011502c41c1007065002d9185040c02d01c1241c181d04c0400206250301407440c1c06001c0665407200c0e08008250030601220042c140c1c0d6080000380d50359801840384a00045a0402d044240c54007603500540764500340c84202d94500c0791007900d440440444070140285540400145a03403180c0d0981400740700f41a0 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 740916088 1250 740914838 740914843
    0xa0c08070e0906130f0b0f0403031802031c091206020403060b030f031602151209011109030709110f030a060303021207030e101809050a0e0609120f0412050109050f 72
    0xb00c80d40034464000d040003030b00940c19801140a0b007401a003c0a80201140d69000302e07492041d0b4070aa5540300000c10081095414002d90084d00000005c5080303101c1c10b9400b107a0382d100580d50701040715020701da0302d1007494810748032040100130003034400c2111105420110004d45c00f03404191016802d107501c42c40541000201a000c0302d140000942c900f40c0e44208881d6002650513089a01c80004903900c0034511841000c0c000e030001000c5a1081170512400d8242120303202c00802007d404180008402980c011503544100c1d40c0400c0e021030700300680d0031940c90b1441121180c4c0d40c0da85011090000ca0039050b40480c0560384a89c00303c0d110707240c03d030301c000542c2e0091040080000f03e510400c009076040921582c010901c45080c00c440c0741002c0f186044050516420000940340c0c1d420821401150720700400c89a0403034a00504801d0902d01400c0340c0703a03002d41505918001c07001651443c0089a80d0482d03005180000030303000c10768518a0042d019016000741075072148201c40e511441600003 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 740917338 1250 740916088 740916091
    0x170d030204030b01030807020d060219091502031c0b12160b040b0d230a0903080a020703080c0c070305030406030609050609070e12031207021606050408100911030a0c08070e 76
    0xf00c444010368619a00c00f2030950000004a801030a220ba007080003408500190100c4c03a404030a503421410310210080150b5440e074020003030058804c1c00341c0582500841141d045141c3c0140b00d4840c034001c04105409002da011415030040c14402194500c000082020f800e8a66505200c0050a6881080c3c1009004500508118040401040240d000390382c0c44800010180f03d8000724030410109041d105540c202c80907000141c07911004001c01d94410803071036110686032411801d102580d01c00901d000c0340245003900014000801c5180b0794000c0042c0b00045500c00101d90360b46454403001400b8045a2007118040c60610002c55103518000150b144290f1144e6904000801c0a20801c00c481b080c03401c07441841e020810000400040b44c80c1d060b44501c000341c0043c0148540860390301c842d035000b40c6c440b0341007200c1880144400040403407504580a50040d010800304074505122056407186080540d052060a800c4010040c03541c500f04200d1b0010010384840564401d04412442070 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 740918588 1250 740917338 740917343
    0x21c05040603020304020315040c06110a0c12022e030507020c0f061b0a060b010f090806070509150315030c0a05010c0f11060c0f190b130318170d03020403 68
    0x1080c0000d000e00c52003a4080c540c010300040499002d14668482e03944071100c159026100f04000310740c10b200168201d51018401e6030701d44028541028030b51100384500c519405890703070540040300d05005640e070780042c002115000c9604004103281400c05180110740904078070300401c0c00c2c000090386003800415408230040b07014000122150240c41000f1540d84645800881c2c0711031030740c6002520b4000c1240101443c4203100015001c40b50b40005402d45080781c5002c000c01010b00c3c8240410213022803140e0300302070b40d403d0242e1a07120003030000324404030f9690a802d8010000c0300300a1001d8580c14407011088056096480404119040c428499024014980411800b5030300000141d80e5941d1b1404560080140710119a06030300050318980c400e91136030b21990310640e5000502072042c4011007004c070f001003040c0340d051025680d0780000e25006101040c0164050500e809042c0030707001048074419801010030196840301d080700b08a0310300e40b500072424401d00600010490180c0300311002e603078 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 740919838 1250 740918588 740918597
    0x90406120b19061203180506270102190506150613050111010b09010e151903020906130e030d060f060219080c0304030827010813050a020619021c 64
    0x152000b0351a0642904105203540c8103603940350001d900d103203038441041064031955600c0d1001d03214003441518040c0a80085105142c100020b0100003030461a002c00203030522207500018501c3c000603400d0002d94060b16410b00700e103040b44010440c010454511940c802903070300d02890213000500c580c50103280c018178002e003c1c0c2c0206214660055840c1042511200000315040b40c0e10340c04a1070f10700d000e038010b040f1803071001c3c20710070340d224070111951514101756001c41c2c0003028110501d03003444031440040c1c0203510950104031540c039a0301e800d00788400042000c1c080c482c16107101c44d0b5207901007515140b025260081c0450601140c0300306070704490003640108048050a8141900000b00f02d4080307942e5001003140c0d290f0a04248080d000850007a10641d4450429110720344910307002a541c15a80004e68810070074685e00200241c0e0450ba059a05240507070092904925000300050017a42c044004114070f030b4503940c03d10174808429402c0d802c1d907e6030350b4119807824440d285c5003644000324 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 740921088 1250 740919838 740919841
    0x110111031302031f1e15090f0e010c020c01020c03060114060f04080d1e0201050910051b070803250225050613060e0607110405040311030c03090406120b 67
    0x100341c0000611080d000409032507541c0c49070f00da036072114400c0121000f469900c0e580d04411a039288545811228031401060109a036003103608a5001c07940c1c0150012a6513070802c09490f0101a80402c00d0110440000c00c1066880e41d0081c1da640b6080600340d005104140c100e030817500303010500c28100c51410060241a850074001c0090036002002c1201e031f140b805002c0051520002c2100c09550012601d8184d040000e603a08a402948561140009e5a041c601440034410000404000e180103a250005054940d41e00055800f4400c1d8010b1809110101e00d400901c291030005501551682d04080c4c41180b01008500304040004e488002507000340303205101303404051100c03180034807002d401002c00940741c00002e115600040040d5146209004062068079000b000381c5e00f013400220358060601c80c50b42e90f22011184031201c02402662510040340801d4042c3d031441c44031340190390603a038031484610100c035901d4101d102414881c074141200010000e001544a404c4030740c0059107951039 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 740922338 1250 740921088 740921101
    0x1150e0103140102130303030b09072c0619050d0b04050108070e1302040504030e012706200105010b030f0109110712140319050f011415070b0109050711011103 70
    0x141004070414100c82c0d5001c0103031500d02d145d0703030010b40059446a10000b800342215024040900402003c0809200c105c613224103031121415a42c002801c541d0307203d10340e222540b00c040b07481c1b40240703540078490a10198000c814a074008011b403031100d0141c02c00700482070b1224100029030340700380b02c0c2c00d2084d00550018058850b44402d52980810801c41c0c580940d000750b40402d0855404407000ea0011f00a071150401c69a4803002d01510b0b150046011150900700310511440500d5510584050085050200f043e191140103d96410fa104d41c000f004950b0f901c2c440d900155004071824805410000004903609a4501c00d50303104090031800d90f41001055907540200035042e64030074060008207000d00c040c001105004600c0341206003041c1c0349101050301940c040c0c600c0500390094100e640c90052140f4400b0005250030024100c60140c194640c424070101d00e403107001c402408081214001280c2135002c1d80216000c0e01190b074800348403c04014445080702c10448030b0055140040010410303 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 740923588 1250 740922338 740922353
    0x110f0405011805091018050103330c020a02100305071d0d020d06290d03080c0d020304030c0c05040b010c0809040b12010f1103071e051603090801150e0103 68
    0x1c00702c1120302200d9403035443e14000380c41242c0450354000c24442c800004c0c4190000300340703041c000d40c1652409000c15410740c2e41d609401416482c0140c0305010403661f81c0e079446105c100355526040078500800030b215400c40000d4a941013821309034015142412900e485c14800d10410703101d07141d1a55540841141c58100024022002050b90f5010244140c2c0714013503598006a8402c0c0d43c40342d03030002600a001c44c46003a43c80d06461615580042440700c000140e112001e40a40340c0b0761510b403550050740e504c640002e00340181010000070a2001c0100010150809007201e81a4018801810390380d98900400064411412210303002903030110182d0005201c0782c0103094440c0c0014404598280c2031000300700a80703c0300c19150240d81d11000d50152464441c440e0000d080803044501d480c42ca0a048040d03c0c450ba45100c8014551041410f440102e111b0004c0d69145000607401140c02d00321810000c10280280c01000d07155480c0404078144040308800b9002100c00360741c50300c199a841c43d1075105 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 740924838 1250 740923588 740923607
    0x11a030708041109100501110a03051b01060e090a02040f0b030c041d1f0b03070608072d0809010509030412021c081204030801150c120e0a0b0c01110f040501 69
    0x120700b246140403c141030f07520300c08890310030801c5041c0c0b45502460b100c0010304000c0114455045904080701c140c020a40c0801100c1d04e40101c00c42e000620300600340681d00401c1c4503130012441b0341d11030080c0040400003260401c900d90007101c0a00202c040e4100203000c0314094034850b581503000004043c0e081c01c15030000135009100b100c0c41c80d0b114140b691030364100f1a1100090000a108030380d010300d840329074031441110800640c02401c02c0e900b00a00504419001381c09801801038070140d408a5420744809c21000300d000159015088804c0c0001824001d01580c001c8041d50800000603610b00000065030700310ba0000c3e8120110540d16001d01c122401600800780da0f01d001c4009080109620748000c005048250915125500d047e003401080c0c00c43c1a0010410000141d500a400c10740c0000c4242a6a41062999010041a01d400e6407511618410b40703820400007140007a49015401c06483c8080180c1c00902461840244110030f07407113010b1800c03030060700602080c00103500c5450081c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 740926088 1250 740924838 740924843
    0x915032d07080403020f030d1508060609041b050d081206100f03020a110607020a020102100b0109051509120d0f1707031e1505100e212d06011a03070804 67
    0x5800701b142c0c205509085521003501d50071066216a25104259901d1103100c00a20301c2c3c2c0041c2c01903003400b41c0021400040504042c0c0403140b01c0b4280d54420118403140c00040100400f002000f842c18039120f000303070300100880030201c4403290000b411400d28000803491a201030307075401140c9103c0b000c00c0d4007c1d04007000820401503080452401281c0800c980f078041c04140d001000350503491b100082c41c3c9800b03414040c0c2e640e401d080e4100c074070303980060811f803c1d5481103440c00710304c506040c07090006001e414021640010b28160f500c3e100c0c50003141000c1044a66610a034510b440d00c0001c1e2185e10007541c043c074210744844001007940d403003030380610503800b062140f20400d0112440d600069804543c0007410a010b80c0c1002c01c080c1c9400c40001c00c0d0714103242400300040c8414000a2196000034200c5840001011202081140705110420f880e044c900000c100c050640c1081d12a1250407000428651040000106030003505041d1181c0c1d20f0200300540d171a554820f00202ea402e00c024004 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 740927338 1250 740926088 740926093
    0x7030e1002161212110303060f010c12110105060f030309192610060819030311180310090b0a200f0310060f020a080f0915032d0708040302 61
    0x3560310311030302180380020f00700000d0841404030a82401644468603041075414005803066440110f8804000d49034000001c44403070f41003440b1900180c6420024850081c141c58085080d1903900e0f07005502040c0712100d85c0020061a81c540d010b110300182000d850641c180e102b403040f868a850206040c1d0354a07004804540355440e0b44042010320023406019007000c88040403204550031104002e245114420340da010301500d0b02c0c10030020b440707001c0342c0020300c144030100c180603062502039000303916000e8507041b625559007442c070008031005000c00100c82c42401007280c0001d80c0c2c0042d0203880da03203d401c24400d4626448800d80702000b0485003480065150070f1219141000f81e9242c054140710120055041c0c1d00e00d00761000307400b001c5860308801c080c81542da400401d42540010f001c080c20754058403d559410201400700c0240c0180c0c100e00e90700040c010214032080c1c50110245008080035a0b2451107929030000d2040f4202c000803030f00c81c410240000245051388652041c03500640207006 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 740928588 1250 740927338 740927353
    0x150501030c14090a092a092403151503150b120714030f04050c0d0503191806050c07091a04050a02070c08161706070f02100e01060e0c07030e1002 64
    0x481420307128950100041c5000100b46c5003203100c00d085120340181010724021403c03a09006054024000c400180c1410846000c400a60913000303511004d464240c520f039296409a80c1c40c2c50309242090400340d28000f90800e003154500e07656022101042d1610006e0241c00c0c0100c8281001100c040104408100903501c0c04105c058150b4030001d60203843e401000d45000e10b858185240b41400100d00b0302d02410300204810040345e0044140c0e0f12540c500b900b101c00c04060100c084500e1825039694078200401c500c00002c1032a0002c0007459605c902109544c40c0075940c101e03420458842c0c041071003101a000e4100070051400303502507940000e690700b005041901c26194442a100f5640104855030b014403840340c0d038000341440700d0700145101030b80c050080342800f1403191505806410b0750240710324912085403036802800340c10781d8000c1d210410411801c1e50080079001e0030183c0705000e074111100011070003c034640030485e000c0a4264131075001d10340c040c10a00401c4203003c0030601c06c5008000 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 740929838 1250 740928588 740928599
    0x110703080705070e0709140d1203020c120423060f12060d06181509031704031116140105182b080706050a060302010c081e0d150501030c14090a 63
    0x1640a0040c5171303942d00d4001450600c0382c00e07031a07804154503251090789611041c1001070706109035103451980c44e03d80962034464425030740b458196600d18401c04900c02080c0890300070406044002034000200844140a640c0d0b4140300365072007100070303400c0c0a950410002c41c1040070f880c1081d8101c14050210a200280e03521594215100030030350300c104200c11414981800030b4a040c9107103c00c07802d0003c22141d00c081c1e034050314449807002a18008410900080d050600079000e03403009030101420b460002e800054a603220300440c2c0144a018100d1031050f0041d54030440949100e88100980f001c440318001c0d00b01f048000c15082140c0c1402040e811414491003d2003000008a200308101a156039039803070302900703551000301042c00319850400c040001d43e80c01060102520b800010265440150019091b031030ba01544003501217000000d5200e00041c0342d6405004a590303a0494200310303a0b15070004405031904296031400203034480300a600002058001841d030b01c50f000340360209099580 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 740931088 1250 740929838 740929859
    0xa020304050a15030b0306270c0603090607140406050403060f06080316030201060e090a020909011116030816080a02090a0f080606011115070302070609051209010201060611070308070507 82
    0x150800103100f11070401408080d60140581000150f044020700120315140403015000701c0440e83c85114403006c4030700702c84010030034090b0302d000c4540689001d039070f03182c002c895603a10a81641c0039000102c168403080000707070170002920240c0301c29544680c41d09285403504c1000d8151128200441c170740c0e1740e5000555880c204014015002000100502044a81400790844400c0d40c440c40c03001400c001041220100403c0c00c50329954100c840c000d89460310049103004111100020211110000c2c3e819081500007049980c511720a03641c140450356050b1640d4241020720284402150001d03000c80c040ca01385070090600c40c040500642c01140da100300d0203100c0307552035112206075002541440f030325590040001640784844402000508052108640c07250790041001d410194041011400c20031260481603010b900031049805202c1800902c08444e0b0001740076034050740c81c00b64009401c6000b00c2e140ca0071000c008004d0030420b8a03503210400c050340502c40448150041c0c110201d09000762 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 740932338 1250 740931088 740931109
    0x15090409080f071b05060a270303031b020703020f15130b0409050606090d1211030414010807170708040c090c022d060f0406150f03061404080d1509021c18080304080a02030405 77
    0x19950101d1900713369980c2500120382c0c51180f0085411104051000d40c0f5503401107188114183c0341a085403111840020f80b50080004400c200302602100090288080020384180c0d04402e404000d162207110030840740d80308881a181e00200c20707010081c04641d0b10741402103002d04600f001c01070792446114003411503009801070041d821029000e003919583c024683c0b58011812b00b0a00b0110702e087d090310010000003400340080141c00070005d001c001d644400e003802002c9800d028044540100d1000e0b48840c42d104100d07440c0011756803c4120401c280202da883c2c405150040c081d0780c0c4801501d60480f5038001c0045c0d5040d921a510702c0e80741c812084004008186030f400900460341140b81034025105c0c1604407100c458140d4040c00040f07040341c001c5032041814542d0000700304d00300c0c007955071090803168421108141b010491240d00700b609090060042c0070910704104008008106428102000d500509840000d04c00900007070111070080c030103101d0500449003800d58403400100c6070f000 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 740933588 1250 740932338 740932343
    0xf010302090d14010b01050703050f030c0d14040b0f011a0f130e0912130b18030709090201110a080901050703021009030f08090c15090409080f071b05060a2703 70
    0xf46422500040100b0f2066140317a00017440e04529118607078400900c40d002d18410fa000310713400003001c03032a0300114808a0b003180c003030700b8020300c00d00950112541449001720340548014070094001a141d1081d0b01905059500780d0f1541070305885d60810104a5400400b840542228100a0b0364420260b00d1209801018801400c0c0c0007443c2100341107051110051580185e103400740700318000841c0c03900f103080139140c1e003040d03068071801c030a0440031034403545030f04032500750054050215805140b508046101c034000e80310b494001010b69034903642c81030311a00240c5070a10511085505602c144010890603020f44121408204008107400880c0d403008021000f15001c5080c888442c0d4201c51815440314900c0041c140500c00503000c07800d4a001500d480000b42c5000904101c5903456a21440c40c15400400054550a002d09641d00c5903101480c1a500030701444030707913581249151582c009980c0041c001a08281140000741c403c0c404440c284202400180c81c814072046400486200860 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 740934838 1250 740933588 740933603
    0x40e0105030708121207020c1e010e0105040b180d080c100507020109050a110d172104050709020d060302030604030c03030b0301150b071103071d0c090f0f010302090d 73
    0x1454001050701e45880c80e800480c40303800424189910000444c00d448400d180c84104004580d01c251080303003001e21100c502a4403c001080c1d0009000d038000501c1c40a603402c0e203e220741e4060150040d5414007552150341c12141f400c00c240c0400344030001140a899001414009030f00705650303503903c0c241c5c0018042050691140065402c905035034040d40742c008046000030401401503490300c545400c594000a01403901e0340c900030382c0a0302c03049001c59025800501280c0c85506c000380c1c1124940c0041c05201300c003000f0518064500b074910ba000c40c0940c2c0e000340245880362030545480040d40145c1c051041450361544000090380b01401218820f5210340d84451202c0c0180c64040c0881d441c0c0c0e8862030085c4e07d041255a8522080e070b01c2c01081c0c440315015240c484440381307001d04482011845040c0c06014921000491404045885200c3d031b20b448810320b100d560304040701c50b06000312b85241c1d43c0000d203e903912456082070124049014010700d00580f070601d0220101715010007550782202c42c007 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 740936088 1250 740934838 740934841
    0xc020f030f0d1803020d1b0221030d0212010503060f07050a12090204051f090e1e010b0d140d020102031b0a1713051020030a060e040b0411030f1f02070602040e 70
    0xb54810103030001d007800d6000d042c11487c040d801148510210b0100f07403c0390a00d40b58541c3c0105010020340d044050800ca0a42d83c0d20100d41140654a1082c8905402441b40713001240750698030f041d415125480594585082c440b401108079030008000500c4542035a44a0420003d601c440c02041e110301542144020f1102c4504085013454401358480060680b8180801404080102d0121000c0440c580030800d8605505540c50051202c0e800a5a2022014401d42c04001032120f41244007100c12041e660309180c541c00507070903888126103e13102c001c925880d441d10014144040c01989003507150420b48010f1003007143c00c00c200283c03401120480000860000c00808000208034401848418042c01c500080c14003004901840141d0075084003000051510307038643e12803801804040700441141c2801d04100007a40c0017602c00780c13050f004e1038540203a2403c000403415214103994005048207040c0c0000c032904c5a00c01c440c008241c82d003c12085010462034000390010b8444a18006403a = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 740937338 1250 740936088 740936113
    0x8131a01180b060d0f140a0501031b0f0e0705192016091d0105040f0b010915030336050f03070e0a2a030f0c020f030f0d180302 56
    0x5801c140ca44166410341811410801601c41c4000c1d24840da09411010800c0f900c40c0340342d0f0b400f501c1101e10b01d010410ba500c042003000302081e000325040b2400756a0b03003040c003031000b07540301c0004441c0d004480304501e0400c0304105282c012110300380e2261240c5411800e000361a4100269810180c0044001942d42850048402c2040500c1ca240c14820300040020700c040704280c00c901101d910031600a00d50360f0401841d40c000e5001710030002580340e8000c0000f8a02807400170561121444140c402090308000403c20103218800c99240c03554000421035424510383e0111030b441c040203038905003002c010280c402807011072080c509135001c00c00380c2445000d04200070f005e20f4030540340300b0a2203903210060130020300c60641c4400341c105810500128891661450404120340c8498880c00c10720301d00d4280c6444958117501c00120041e00c02c600780285548241e04070307a02e0304a10398544a40d08200b00320000786400c82c00030003009219100100340d1031522000e00144440c10401038002d0303040390680d07144 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 740938588 1250 740937338 740937359
    0x81b15010302130204030b0c0309191b090506131104081501051008060d03030b030a12180905070f031802090c0a180308040b07050c0a08012c0a0308131a01 68
    0x4030f0542600214109841d5440d50382c0c4000c000340481c210341800101141d031124040c041d410082c1c03102e04d1107210000192070441b901740d02d4003181c034420400001c00071400324814010746002d003a0040008517135034440445040100904a401540407800300030000e01c40e0010701203107101d00094100411258503107020301c010f5200c05041c450400000804100704e0341e41c0c503010034044035010f143c00540100c000000c24601000d13482d02a14404a40c2000e40c002a805800702d020000a00c04030f50b100766603042c030340c07043d02c00035111000880c55608040c0c40091007680320080d01c0790708445a40040c0066004580c0c0c0c40c00c1540c0c600c10307000001501d901ba00741c000000001c02c940710034525228510b1519501c01500507406041000c90000826400740101040281081c1000801c05030038595375034080ba000301030495240d51054420030300802581d113070660441000400b4009040340c0c3c03003966002c0391110030040007503402c40b0741e050780f9101007a5500c00691410740110152342455050080045 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 740939838 1250 740938588 740938609
    0x1802150a0e030a03080718030c24030c0e010e0a034d10111b04150524070b0903040914060d0305090102010906110702040b011803081b15010302 63
    0x2c0c000e5110601e000d001a9111401c1c0380d01884074030b011800140f01c8600024200120fa102800303186900c03c0102c0c40700000d043e402500c0c2c012441240e10035003020001c2d416100342c00c1da900081101514081155405811684c051990007407210380c4481d100c1e520702007040c1c00c0b44016001121410700641421b0b1120701050101038030701c01074001c091100000103005c2105141c40c14026807a1140740d4190034007a191900e01c1071401c01c1607030030440215041d10782c40284594060710603030401040c00008801c0780000800c3e00c00182640910015000300d6010040b105c80401a4502007003100d00040343c21100510300801014018650b40d62400540400790345515441c84030055a800a02200c2d0341c3c4d880303c03492400d503d03003083da07250044800183e00500f5100d6010307210504140c0c0d90b0707882c1907250006040b02d5100325010440181c0381001119001080140542c0500d204001480400c0403034020b480315000b80f40408090703140c000c0c505414000b20041c841c00e03038042a4014021840c0c80c22091 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 740941088 1250 740939838 740939867
    0x10050603030c120f0c0618011b08010b0a09030f0609170a0f0810050d26191110060e150f06091509120d030c021504061802150a 56
    0x1581824070b5024826140e41048690102e51000003e902d58020710071410b9640102c2c0040541c1e030180750480e10f10550480d00461382d501c5503c0d0142e0a60100320030080c552200a031560f9290031070782001c880c00e03959807180c0d2440c424004099000070004007540d1403e446c083c4200c0022803e21050b00d02107501c1c0190450348043c10380c0910800f14400c0d80304803d500030000707501d0800d689440318108444201c410303030040d03500042c00084000600600e02088401c240414080c20b081050f01049803505000e29040d603400400300c402c1180303489100e50041c007040c08921381039034080e03200720152000310b1b4039550080000c00b08800c10890140c1c144589204005019644181c00d20040000280103100300d010345842079410403408800301d0815400da40602e403014080c000e0075019804000c0d51a844003180e1130010f424444110200b40c0702003010104890540b00c00d903c035891341e40d1060b010b4a0b0415602000781c3c000c1c4940c00150340e0300000188881da1000c00f055035002807100c020a0012046480d = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 740942338 1250 740941088 740941093
    0x80f0a020714010509060306150a021b100905010c0809091810060e130503071406010e0112050a060218030d050406030b01050306060d0b012619050405072c040510050603 74
    0x1482c0d180d8112045846045003206d10943d00d5540d000007407a09500e0103894a2450408910901b480703400180a40c02010307481c0760551441c03502d008028146910000c40d400141d1040c20400c819400340903082c0500c0d1007907030403c1c10300040101045801104444855007006000807140c074000040c403600324501201801802071a08044401111403000b4040c00c1010f040a604801800001d00c150b60403281c1c4422000e03540c01e03200c201c6660b992001e004800b002203400000040c585a4059445a426400400362020b84a1915a5002500640380c5202d100c0c6199200c00410f65007402943c20007459070311242c0d01c550800c2001411280c000311090b05119080040c06155500c13072064440301d600542001c00c80e0006900101c40602009004580181084e034881c000d10b101c03010035502c40c0545290419041c00c158107d501521026138000c0d02e5608113220078803070b041e0303206c0810702450140a0002c031094501200040700c00001c407425196034010940d280ca4683c0d1601466030001c008500 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 740943588 1250 740942338 740942369
    0x1608030a06080f060403180909260a0f030209041812020c010203040803091c15020304050c1503060f01020f0f060a0609060e010e060a17011b05040f050d0f080f0a0207 73
    0x10f11903644d11026201070184071403d01d80c64032075440841c560015106000040c840e0700c0c801d240101194004da550300c000344000e911024446079044050b100b52109954407458000c55011069000b075200001d4180c2090312810703072880e0940c000c094003072203900c2142d81d4001c01c4800c1000034245020300c1480c0381150000c11040001e10000402c1d0340ca0381030304480c00040c4c0c00503018a10ba0b209160a40100010459404940c1001c40c81d0f0183d0701c518082c0c4159044105400200f00c211205000418115001400845c485080032018024103100600440b00174030b80f000e015500d0803240000200311a4040c03000c00c003200c91540116801003101d5801840302034200200403c1410050048080b800080c10000d01581e860944e000028643c81d08000408410410200d0281810503220903034040561811902d0500c9801160100d03000b141003e14140c0c10321080200d041070104003234802180c0c401c2c5038000300c0c0d502d000a141810020540381d40d201c89190f0060700b0132a01d03503c03140304910703030701d1 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 740944838 1250 740943588 740943613
    0x2406020c0a05130e0d0207060908070617040c0509090d0e09040206030f13120c060518030910020102131514030115140c010c08240f0d05031608030a0608 67
    0x507000080d18412503500e480c020b81030300030701c005203115408440305202e10900610310a0b004030f1302c2c4054a000d652410390440d00c035426150380e100588034000000d12040d2040a80349483d00005030850302c110b000c00002e990340c10005201072000d890400d82d03078000045a07220650004070816080000740e44a4565150940014506010040203100f903504980c00241d004492280900041680020701029002c00120018200e400c0484207d6a451421000c22114585980400c1c188800b8500452401c04c2100910410344e030700c806c20206541d0203004a02e088003c6c0c43d6024041c00250407400000003801074000d1030001c0a54030509800c6042005209080c041c40d0442003514060270f01d01c000c100d540c45030922078441c0100c0e0354560b52800500402c074913484a00d5030301441078100c0b10445072405c15501d450301c043c0603240e00da1203505107280e881e140c102541207200c001d000b00c0540e41418080d10025901800c894822984034a002081050720801c621601000c0d0482e900104802c0d00702d00c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 740946088 1250 740944838 740944849
    0x904060807081c14120a180c030611160f0201021c0f03110d0c08010603050601110a0209061903080a14090904030c06060f0f080d03090201171302042406020c 69
    0x35508421012001d49880b11200c0c081d803141c0b81442d07180b100d0b83d645c9005c00e401d284040401a00c000c0d2800b0b00306294104481c550110001c1519003050950182c61f14642c5c940005142c00c0f0220441c1010901020303401c2640310b1084065035026020b803e00c251118030009082044042c0d040e010707400c034212040b0045034000c0300c00d1030040f440d00700000c0c60100740302e081480e4061007120717402e07180c01c0106101146600c21a21030484200d40c909124545a80c0010340d0044d14046c04624594080985030f0054905200c4040e0001c13400340c102c107400e41c404440c0301f001e907025800039a00c40000180c410b8506a11540301b0040116a14800c3d00f0030041800055040c00302810103000c00c40742801d01818801035502000081c50381c02d5400c902a5910148022150000c0c41804158010004240d244c640a8003482d5030745981690b5801c00c541045900d20480040600504440311400c1c1255005803601c1c403810011b801e5401410b42051400d40c01113048001582250046400019082d80c80e5140c1 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 740947338 1250 740946088 740946103
    0x3010308070618060e0d0809030415050f0412050601080c0a030c0b030a0f0e0d18080c01080907090c080118060602030306100201140c0909010608060307051302190302090406080708 79
    0x400004640901142e0b000c0c101004000c101030011071810102c1000e603100000c0010841c00d43d47c0300c002c0c003661030414040e1a4041c5101d81c0119014800790060103e01c14001010000042d03c3d03403909141c2c4460809400c80c120080485050707000d04014011130100f0009803103048012510302202034119030358982d5101d00d610030b4900313a54012002c6001000250881509441e90742420803011007081d001135a143c08204410021030440016841c00044c0c105e5160180c588400007004c40d0802c00004441108000341081003070702a00e10081402d00c1540a40a51014242c1c2c40700210b504004520241c04d200895101c0f007185040001c2103016004801c3d298402d0f011509101c1468013030704240d01419403561840300310b070750010030030000c80c241e9005003880440550340e00c00310f40c0e252441560308000075180c40c0ea142e8030002c010415483c3c0440040c0c5e0008050b5005414008400c03000005000c0000d20400400d40102e003542e03083c10176224010052480c4401080b91500e460641a00c8101 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 740948588 1250 740947338 740947343
    0x607020405090309040f0b0a050f0a05240403051506010f1202031b160b2d070302071e0201020c03071202040203220602220311220905010f050c0301030807 68
    0x700c0300002400c00006000381c070368604010b03009210200100200c00000c14044600c580714032940403001c40d85082001c420118660b014107501030044c2071008102c010301042a0b026040002c1c5900781d0341c2c030f41c20b1402030f1004501c2903000f407004c41d03503040801070190001030040341003000d10b01100c10041c0e803289401080613080b440050792500e800211500320802d452036005410400158207004c40d800c04405002a030282011000c0f40d103401c440e10104032044983c0002494800210517a40810040c070300c0d42154103418010300d4107466965081c40c2d03d10004410144c030748a4410b030025560140540c4124072021405060301a0800d900d840203400c2e03510300680600d49c04000209800380620850340030b403818001e0802d1246042c5800e5000c0e5010f20644008190380605000c41e03064208600e0082d00e078400400d02c50105a20140700400841c0c11a00d207455110703140c1d55000c40810300c900030086000b9000481d04102c9a0b694000348c80001c0e000044a0b0070030030042010405400660b05070030f0303 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 740949838 1250 740948588 740948591
    0x8070c0e070f02060411130204060909050f0f0115022404030207060305071b06150b03041403030712090f0b090c1e060a0c0602250605103c0801060e09010b06070204 72
    0x44050300800c0d0b45110034207c1c015031510002d0301080085d0441343c84421502d003204144220303622050054650001510b4180d00780061100600031028021811140f40c0c0036441100c1198241c0c1403803c0d0980c500c0ba210b9915034480030140814154180302040107804142814025030030a0880144800916102c401c0f44d00b92645e079000c100840d94101c000b9503540d040c2500c403050f03107500103510300c1e510903207080300c19551003400101040e2011042e203110300050b465070302e44a26840101c4002d0600d980080f500024840b00304000107801e5084d07240a042048021b16445400300700b0b01c1134810b15510905a6891034000741200c65032203508407911130703030703180740001d070f5074138540f0706900039001321035601085602c54040028016070200d04250f1050003441c041c01a0388992302c140a5082850084d000842500081c1301000707405200060b441203420180c46000a4a502c00039208844542010b13010740d444030000c22540504d080601c0d040f140780b9000300204881000003814274446c2890090055 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 740951088 1250 740949838 740949863
    0x30712050a060501061107080a0f08091c0c06030e010513030e0a030b09010209010e060a140309030708040e0402010915050328090c180b0a0b1608070c0e070f020604 72
    0x800207202161041ea40004140510350b1602c6001e070040084a0311440c183c402c0e0b00300003420035000246040c411f40c1088880400c40c03680d840390686035002c0d940464100342c4440d6040c1c0251903200d1380994060240c0c280030069810080c0040075150455001c0500d40c3c106000d22101104219007483c0362a81070a1120061108101080c1c110f159684080c0144680c9802c00c0000c66040d0000e2040503400d80e1254407104000c0100000c500444c26010002002d2645821030030f01803000440d0029510811a0b05200581d0303900d10007644540c1240000d103000d5001d01c000c650f04440d5100c003404d503094181c0d04110940400500601000b03107480c008604280c440860601001e0340e002c0079100d91f080c01c0c40703500028201054890a14801c504204120211480781e03114584600110500000e018401d41840c1121481007074104080381c010300d2060804e03110010345e0310002884a21300c03403a01d005105240c0200c41d000740800030f0142051119075208003043c258041011075100c0d0740200d40c4003e1 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 740952338 1250 740951088 740951093
    0xf0e011203170a050708130b06090a0b0607061d010603021806010315170f0d1d180f04060b010503040803061207031e060b0604060c080309011116030f0e030712 70
    0x30103400242c460001844601031241c42e0780e064010318424601a212107603203440d40e1141c5c228410003d08007402541c0d032440407a01c1ca01c1c095080580007810b0740000b141808203130740003071302a0344141401c035074050769002d0740d40140314054800886144440d008000e81031440e004540c194001003551032022400d24002110341c0e000390b02548615401034208250b294440407800f040340640e0741142c00c10301c510081e08808400014442501d00d13101d60307030702001c00c0d0480505140d032104060f1b52503100902008400281102c0482c4512402c10521075014038201410710008071200090502c0c10450100304000c00f2504060480e5006002603a440321074210403e0a2403c1c003069400044c00410612171741802c2c0141c80b5101c1c44040c0c02000c04206441e130f40b0040141c58891442620080340e0801000c0c808140b180c00955400190f00b000852000340743d41910f0340650140b200342e40301c00c698102010070303d80d00c2081c99002c0b40b91030030001584160840002d648044a11401d0040054440c00104 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 740953588 1250 740952338 740952347
    0x80705061c0609060815060a060e152a030405031e0a0609050607110106030506012c0a09031d0a15140310031101020a030c20060c0a03090f0e011203 65
    0x341c040d101c681007110a885a4400700500000d102d1070445115070030f01c41c048243e14520141c0113400c001c1036079046500d84003055585802c100070311030b4480360801d1003080020159000705001004042103a0b001c0c482440d406600100429007000642c0c8184810300080d1000604c5881e14840400c0010100d011100658075004c00c03134000030800e85c1048a60820001c000681c41d01032119901d4504640c2a50403006003200d82c103100c00740c400d501040c0104140c002c82d090490001c00d02c6d400078108803440d00d040501081c2e0903901449681d0303440e80920189544110840420703070b4016614001042050001345040c51180108000403080007581a1203034003030754400740c103140d0100313072a0303100e2410100c2001200004d100c140d6071103406003000c082540c4040360100000360f0645545400c1402c030780b070741841c0c0304203842988800850802040090350b501005002500e240e84000e10314400c40303203070081c0400c0096000c5416900e50103024040001e010310001d040da10709074001040c03000030782070854 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 740954838 1250 740953588 740953627
    0x2060d020a020709060b091e010c050d0203070b0115080711011503080405030f0304031509021903080c160f0302010806030c1f1b02061b1e0c091008070506 68
    0x245503480003442454540d00070035080d08a4961200810005036581c00c040311500c2241e001d16809a480b0811188000c1c055211385002001072503c58106000742e590580740500300ea42241c0960310208580e400c01110003403440c05000f54841114900e043ca04020f4080a4081d0020080c040440d0f400c400c980000d5000403881154500001000c030360300d08001c5503682c442d0080303038000d010343c017010880034100104a404580e4007004850074440a801c0c84401801741d61004c0741c1c0035240900c4800740c2ea11540a080256005001c015520324044400904e0004500c4184003614248481040680a034070038240c2220340a080961305075858100180c1084010401e0951008000e003840c00d00c0080c0c0501800810103a45900d6010110b1015000420841c024025800340c02003268a12640340d002c0c5c18240d4003804412145506084201da10001140c013810707003003d17400001100c02c90310f003040409030000c40801c01440a43c1c00c05014644a214502919000b00c10010b030307212070741c404100c41c407 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 740956088 1250 740954838 740954857
    0x9050709030f02012012090f0a052409090a05070f021c1110020703090e070c0b04171b0318220507020f1902090601080f060906030102090306010e100b0408070e040206 73
    0xd811151811b01c28641a402801145014481400c81004079082c007840b4a801e40d02c1c0180b060768070480d0100c441450140101c3c0c2c0c030b090300105000792a0b0544801001602844816601140d28645840018401104aa510011584660040c881101011103071400c80010b034a85141e11056030081c4614104480300078645003480041e02030203141d8880c4165096507400b502c0f41103d0307156441d0450b0b00c50040280a00b1151080c408140001c0b603105014640c01d00074031002c2c0c14001d54900c2094140b070070003c542103940000562001070080301c06c8034942c40c0402c6410076031031131502d00d01d80c0f90800403000c02c14085030b40f60003040d0418004c00c413540e40035107598101c8540404c12903174054200c85d407440890251003843c0100303005600841c600c0f48210701d04040d8007007a039182ea0030420402d50261825816540c00c001e14041520f080c801030b4042e01a07107901d00304506210321182140e2002d035000064200013404140070001001c10b855045440c5416101025150340c00003c20b01c0c815135080 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 740957338 1250 740956088 740956093
    0xe0f0613080706020607020708100f0e1006030507050d030203190903020a08100f021908060f21060a0203040b0a09150203150f01030b0f0103090f081309050709030f020120 75
    0x30700700e400181c90b50079185950300303075070954891103400c0c0d9584009010307605594004841c64444c00c4243da1190f400c84100c80e0000c60602c40001510b401d01a400d8242d0303405070388030481401480300402c01c0d0302c01050266080f0054600d5510025102d0090701c8100c00c0446861440d083c0d0140314942c62009140c000f003004000e40e55402e41e0555075600d00c500c40a03920700305000292860006e109403a500300031f419080714500764054080700d44400003000e29a104500b6001c084040c3c460f00408113074102d0300c12400c004040d1000041e0b240c44801001940583d004008200010b0450010300f83c00913180302000c15500101d140140c0c4c03080380381e2210f59a00e44080200031b89140c0000550003000003d5075210036603c42c200045090315114243d107500625008100301c000d510990040150720301a0715008818141d030f9441c61500e600c8060080b207150400c0005001d0703281035200f030540196007414103080d4a0300c0c55448481406001c0b0000e0b050104c1009211034100040c1918410a00303900103 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 740958588 1250 740957338 740957377
    0xd0906021204030306052b0c0b040b070204050907062309130c180312050f090402040b070302070b030f0f07020a120f12020f030a0e031207030b040e0d0e0f06 69
    0x655819400072101030f00041c0c1802c500007003d0800543c0c2490b030000d0f242610514850074000aa4039440a09040fa041182640000b5000f9a100b0181010701103c147c210382e038419a00402013a510040e0071981e09400c5500c1c1000340c7c0750800080c480d510700b001815210740183c151644200c0c01503e2070303541c2019242101841c0d0943c40e07031107500780c40b000b40c84031070142c030030741c1c07880f2402c2d849074040101002214005841400d02038000780842d41034485100d4600303034111000c0307400c0e60800c4c4d2210342d1001001c68078404058051047c0006019201c0d041801c5280051802e508020f018012a0340e24001401262383ca61090011070005034100e200000d100080d82c2d002400c10203d4048500007641042c052114600140200c1c0c071000803540e16a070464030707a144448014601c0e850752444a00c0100500034400081244080c07003071030b00f0303140042e0040490041c0416219102e190203180d40082d240307600703915042503100c03490a03816544610b040e889640854914421884c101206504070039 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 740959838 1250 740958588 740958607
    0x307150513061715010e0613030f1a01080d140a03060e090604050105090111040915080f0714270403090519080c060901020a0f0302011e09060605120706050d090602 72
    0x202441c15001c0102c00307681c113903603800056000114540b400d14002440c9481c4420030740b5006c0b000e428244d001d240d0444c0403580e03c0e41d5410ba6007203162002c5403042d039090442e181307006200c0c40d404c0c018003400000c1e200e50504d03a0303801082c515007101c82c01542c02d07000c1a0b0072940c52081c0d0040700a89405014900c1c503041100555a50b01d1044504844079802c0200007010300d038042c041d403542e0108208080b810b1905080310304000e0400344503040d10100c24120700061004d810008080e0650000c2d0182403114144404081580c0b40c15030050300509428280e414407540303610306000144021051315520b51168681200c580840e03031310890380080c6030418000a04504034100701141c21311811945040649401d0003180d001d02c90040740982c0000c803214020812510440022502c00e20001505082d0b000f03800c01d4a50200200c055840c0d034402101c000c1141621643c4080d140480d042040070004007445542d60003640208020890041101d181c00c4109400a40c0c0a0742c0c0305400755201c14054 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 740961088 1250 740959838 740959847
    0x90315021e030108031e0a0e0f030f120c160302010c030f02010b03030d02090306010509040221010e011506081305061603140c09130507050304080315120d0906020309030715051306 79
    0x183c8076940d140f50038180003506e05000c46522503d0b94490818114140302000b1060f0040d02c013940d05405032100410b02e03c5002c1c455400d602d202040b440b41c440314468500c902e0115040c80684055050700c1c0107101607038101c031646402c00d80c0362411010040323030340d0401c9025000a070185c0d501480086040b480c0840c41380c001d040142c605800311007040ea070b03c1c0100541d0407001e40e40a90006c4900100c0c910202c01c906c1a00d20003036070500045400703c0c40100807401c58001d008407035030444041106029040d480810240c0000c2203c0c6080280d08041d142d190b140d1030081c1000d8644000003400080081c002e0b0001c0c0751b00d0802e0303490703114039141c2034803240c1059100070401482400c10212807a501090341c411035001e5011540d4141c1165204d0313880d00541e81c400313043c0010002810200e07202c0e5030358030780b84802c03407100a0001e4140141c40300c601800d107003910341041c015900140b0141d0300c2a100000c54408480310305d0700858542568074403c2e82d06200d008032000c100800f140000c9840e030f411 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 740962338 1250 740961088 740961097
    0xa05190c0215241c0605090a0c23040e070e1509040c150c12050f160f05011a01081b041502030901020712050607082805040210090315021e03010803 65
    0xb0749584a00f201000200700741618400c0c0814120080483d02c400403603150b5014aa108002108035803041ca050380310b14035181080c0e070140030750005040c60140c040450100c4840300050584040c041e040c205013840b62a81500c1c010f0180c1021600000740b041200c0c03100754481408080c00070311303160809081207818072450303020b10284511114080c101c02886250224060354203d003007801d90725501c202c1103d81c3d60120800d04030344002440590300a0051214684a562044030104107400c51445c0090039078031140001101c0500d40c031141c21503641c002c111540c0c421005048503c0c0880054030080c0750b802030390848100d200c409003680369580c4c4c0000091081080903021901516511401480b090052000081840d08100003042849000355005504000048203500c8a80d9441d08000e2140a0f484402d04486445009001c01d41c2048500d07000503540510705528002d04580307480b910f540005852110301030740014072102001c00c075642c1d503000c00c040c03040302942ca5035101c9840d50341e41c20 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 740963588 1250 740962338 740962381
    0xf070308011401091a030a0b0a0b0705120306030d03020f07050f0d0e0411040909020a0e0705071103030c030a0c060906180302010e010e060c09010e090a0608060a05190c0215 76
    0x40d42c45200b40c0b0b5800703640e4500807515641454a4103075003c201001c1641c2004d403005040c02d4070750b01044c4103a030750340c904e42018151080354a81c8070b0495040041c9401c0b02901181c4254204200b8880591400f180384501400c81c3c0c2009a034030109052660300a110f044000b0708540030701007044440d01400308100d00126110390350844040c850004001c1141c440134061417800d0010002000340102c0c82d040060454002449540066924000f46041c4d080845051001070400614842003103507845030500c0c1403109a0040d802c260016aa45540344212000e4805110785854003074100404c3e500840e020340e0b803202d003e1008880000f84a61407141c0000210b0155081880601c50882c0522820307800c000c000000b4907480c0c03900d112a500f141c1c000f04c6454100408004c048600e500d4880206024654203080062400d1500348000d0820a024290079491400d00f410f2113540308601c900d024807907183c0c3c0000201e402c21110107900d0070003000603182d00009000c1c1040350951411162002d40507 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 740964838 1250 740963588 740963609
    0xc0504020a0e270f0c1806070f0b06030708010605060a0311040b0d1a0f1e0102010e0102030903090f060703080406051e0702151e240603190b010305040b0402040504080f07030801 78
    0x480300116039110040172210b290310b40c070003031060038401051011403601d180000b030065490100a030700d03014600f83c01c800d01610f40c85502020301203a404d041129100030300150000704070304d40c20140091070500c1950041c0c410503455108604458001008550003040100507442e40c8141031402d45014060103c0c40303060400081030301f80410b051083e08810752500003003110051150b044221107900c1e410100c8241150340c0c0d0010307003015100c24401075000341c406200840d1114050b01c200320b10b00403038107841c0d40250380034800c01d4006500f202000d600305500080100d0a640c50b001c103414208030040d11801c0c0517154400784a038094000c83e010b06030b010344080c1100c950340c3c0c8002007020031620001000c02c4091001c0080c81d058140203040100c94001500703e01d01031607160000d0f00343d410a49400107141e007522580361a41413140f0940960001c20700b000e2150f403510b501c0e0401405401030019010350307200c0000604014a0307904841c01811401941e47d103600b4203041c0103299039400d00502420700c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 740966088 1250 740964838 740964841
    0x40b1008030a1701090b2d2e0309051e150a09031431080a0308010e151c0609020301020a0e03190b070507060e0a0b070315030c0504020a0e27 62
    0x18424090250150806090400090500078021140c0401401481f210101c01c10032107803199290a4610070041c0c0742d5413241690409082044c11140c10600442d0a0600e030500ca100021004200902c081042a071110105910a4452414807074030300000e8141c41c581a08005071840c075035000441c503e000c5d50b62003007980401d000341042440781407401d0b07821214600f8028003002c40000e002c01d26010600305080180e41da0b0b0b80c800e00c4d1817a4008100c02107004c85005000041011003090307130007038002c003541e0074188250010801192850180c400101585034003003083c040c29030420801e0a0303025008550b505403040c0300600110078005030318800c3c040c3c140012a813076003031207000c6000c3d900a03a03045450f84403080c003501c5540c4a000c04036690364440142c806c03510070a101e400c1a4a01803166101c0525000c5d8006040301d0311a40105500c088195050000c60718000c00d0b40e003503c0c81510016680e02c50703104255035658040c19400e500c00f610034100000b1482c61001d0841c0c944a01810642a = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 740967338 1250 740966088 740966099
    0x904050708120c0d020109030914011b060506120a0201091703130e010602121c05060a08070b130e1611010b030102130305060708010e040605190c020f060903070b040b1008030a1701 79
    0x21f0765074004000e80050307a2524103001c141e1900341c0c0100d009005040c034107101e900c012541151000190819540b5513507900811032641466070419603101541c0028000233449640060620ada080c028048482c512828009044074100b0484690320f4444540015641d03440380003425041c42400356000600507818074059014040b000e44000d84100402007010200403d110780041400038841548850b030032500091001e814031241c4003518410110640c0c8040c4801841c800c0d000517440740c901360603c41d0400400903e020380580c0d07450030b1481c00100303c5000a100f00d002d800700004059240d40f001662655900d2803c005104413845141a140640d803628000d42d904142403158512480105000600155455003c1c507885403200455201c0c039407080442d64102c0b803c5030203030b03070260384500e00e503034410700341004480d91050f0164003c615109442d034904640d40c2c000351000340070b07103056404540e4403000e0b03c1401c00035000c11021280c440c0c0540500a00311854482003070f040b844150000301c0c4 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 740968588 1250 740967338 740967341
    0x1a0411040c091403071203090e0c1207030911040e0a060c030e0a03050c01090b01120c0503011803120e030f0715061d070e190f090504050601050904050708120c0d0201 73
    0x2030350600c80d10b40d182001c0c42d040d101864160203051566150041e50000714070a00c0c1c44a41800d5140617079a05625242021840152688041c1c036004560f0024481117200800c102d25440e80001680780c00f08181d122443d003200144003400966500504080f1158000d16000a910603201e00841c8140511070003950203500b101c209030841c0089400001c020340100340038100600c840084103000042018494940c840e01200a0300940381461841124405000b50000f540c006804110002c002d401c0c0c1d03001c1440c4d0314141d84c07240201400420380c855081e0351265442040d000c200b440c1a49d60b603070050305264030284e012281c1240c51115043d074600441c0903c0c4220010707107400c1080d80030460070407080c43e954040c0080294040000c001820001529080e04480c1100309008501d80e800741400302410600d40560411506680340c1810070022810005500b41100e4003a82d04590644890800d80c0c00c1152030741003440640f103001c3c01c4884039013000005043c1424110150f80c04084402400c90 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 740969838 1250 740968588 740968601
    0x414041d031c0b040216081324170f0117030f0c0a02030d020115030201080a1b0302091c0c0902071a090a0204050c1c02090f030a050a05060f01031203181a041104 71
    0x141134206c02c0c40c203000240144001e01c810100d00880d640f000c5d690310300400c0c040107444880040544003039441c1c42c00b150820084a05c124000d42d000099140c01d078011194040144168258141d06108d42c2d20710b02070078070486205400106805da650800c4d000300d1541c400224008900074811200a16002e51040c4290000e400c0d41100c0e50782d001d4a140c0044035000d070b01800b0504a01c0e60b03000516241d0500282c0303404051141d440240c0c070f641da104204100c1225521519200c00d4400807854002400b40c1c24150598040b200e0050f140c203082c1c100205414140012400103a000000340701c0c00307000004504000038400c0301c00340003a41e25140040c0c014050a000c0326450010b0407000854885c864014243c04a4085c0050b00c101000800203031074030300a40f00503102038010000d041d06221061089a512941d51031120b1a20751469903480400902046200100f50740d68034030084007000034804840c2c0c40d410002c4a02d04030401d50802203101c038151800c40d81c1e41c94115240c2d44c141890300070007 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 740971088 1250 740969838 740969857
    0x5072606040308060406081e061b0403151e0902030c150d09031b0b040b010e060607031413080d0e01020d020c1207030218070e0301020414041d031c0b0402 68
    0x10500c9444a40d010348420101518413644962280300100e000380041007080320f48005c49200400300e58000400c2800c25802428001041c0b02042680081c840107404550480f5409403060344454100c034142e50003807241f000b001d5119030007807810040d008101d40021701c000340200c09440d45101420204a08011410300d00c02e0380301e806005408466a40703034011110315010303013400700d482c2e64811141100a46c100504541c0142d1210500c018004026802c6016180c0c0d030b0340040580c1008000241140500c0720010100998400c48200481d072000c251014661140b040c0c961454035000c5d060f0f01c40d400c40e0b14402c00a4040c10030b010f00b07507200046035002e406c01a0080c08001c004030092000c06629440c0000c2c4a100c0c039003000006854411413140100305560b0002c0890404800040c0380c1c50340c0290483c0f09a0050209012401022907090500d0008513800520b040b00f03c40c4041601c1080c0d401604640004600188291014655880c810541810401c8841076140800c0124000d1a054 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 740972338 1250 740971088 740971093
    0xc05180105120c03120a1707020703080f09030604080a02191511040e070203030108070f03080f0904090f03020123130b04020d0503031014011d0103020307050d0504050726 75
    0x40150782018045818904030341810344000c0ea410b1004031346043ca60224132000c088000409a40c80c1f680038059070012608204100321900f4155802903954080b4040900b201d4400911251250700300b404450001c00302074140c1d482450715017080602c50300401540c0016000b04c8001c03c034004e4240300300f045040d03800500e01e000b04030101100d070020903251a620b841541e08010224800071800f0025115041550055940e58181000603042c80b4150b48541320009905000344001101c030300c15101500105021030b6201c507103060000f0003401d02c110015218130703510320b13691090660640000d0004400901c10404907091048040003090341182c5001d60040d4101016001880d0448480e800c540010400c540804031500d50031b0442d40306441440e121024040c0800244480b02c80313845400c1c80900300001ca110f5035011a1801c00c10840c2e9807810151300200241090b4007641c1600e07a420900c00d410099131030180743c074607a5081c45000e16115450010039002825210425101c2803e4502c4003 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 740973588 1250 740972338 740972341
    0x1401031101030209060304060516080415091e120f051314030c06030a0603020108070302070317040302070f0e0a11070309060c17030a050609060a0621270c0518 70
    0x1100300032103190010450415408010390001952510090b5001e80d000e81d60010b6641828440080071b1504095403d0034000c1003070402c80403c81c00c03881c055a540540c0c00c00f044500c280e1510108400445c0343c10110481c00800400c24006e03040001005032081e501c03070404946d140c000030b81c0d00e07000b10750308000c0f0b00c500b00000f4400180402100c200c40200038040fa02e00c840c901c4001400c40d002110300b07110380c41d942d02d000c00c03e540e400030b00640c01020034101189401620f46008000f0340180600742d45410700c42000c141010710800c10359004100c105002d0202c00d071601400102d00c08161140302d02681040383c00f03c00044084101d41c590703075054850905041c9070010541d003070b0f0519030066070641d07001c0d4400342d10440724100452080648410000e141c0c0303405420840040e9015022500030001180207110f21908988160740741c5601003002402468488044405030451004481011295098072200b807140343d4020400d8910034441c3d01030081e1034800348130701c0f500112011180c80e41c3c20750 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 740974838 1250 740973588 740973593
    0x906150604051905060316170f0103080a0903021003090203010605060307082a0a090918020306011a0f0406021f0e0c2b110103140615090102160e0a0e01140103 70
    0x100105400b455005500f030095030318000200030360400c079a180c0c1a0610030415810843d07000c80b001c4110b82d148000d0001500300300e02c2d4142984014000184500f10000d01c407100b882c080c003e144002c540c01003100940c1e000300c0341c004000e000c140c00124000d41c2002c1e00071880d45840b50960740b2482c120758520a00b5980c4074002c0341000825014000c3c020082208007907a96020001001151210380f00e031440c0501c2c01c40c0060803103040f60002500340c1c01d02101c10703005179000f003142c0f030441c0d0700517171308501940c00c0c4050420107210301140104010b400003000101c07541c021802d03025644407680c404415032000612842503400038043e01c4211307048001c0d4215a0302d408400a0b120420800030420b1103402c030082100410403002c2e0035150a01c00c48480842903905025060404c41c00d44452039039410b02d00c0200b85599845030010b0001000859000da90703074401c00000f051519030329182441240d860040045101c0241c41c1e9003229403c2044000c0d84ca1814010703c8451034442c1d030041050382c80c54 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 740976088 1250 740974838 740974849
    0x31f0e03031608071404090501030b090a0c0b09041d06040b07080f06150405040f0527030711060f0403030302030916080a0b09011d011e090822050a0806090615060405 73
    0x240313600107000c400d1080051101109000d0001342244010002c0c082d41075045c061034000d40201030f00240e03400706050300d001a07961100742c804c80b01c59400607500c6102110008001e000641082c829405104600074510280000c80e00c0c0a24021000419507894802007101e05110840d880c0700010101404030b26181020b0000c00500c0c003001d0f140754100f40e05e41c0006400d9030140811080c0303480e215030510000c25034040c0794040c0550203040b0092031a008021540c7c49008506020f0b00000381c818460ba855140c0608881c220051580c003e550369451f4a005402500159181151440303600320390a0402c441d004085d00b961a160000c100c40000b039550500015401001001a552142090900592100c0b01100c510100138008115912964004607580455030406425541031800784004100b200d405c4420312040701501102c4c0030f4a001c8100c03006400c91340920b41241d881280000e00b60400701c0c8030303405040796a0598119031a480554080a04640d040c1c41d0310903410803080000d407514 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 740977338 1250 740976088 740976091
    0x4050108030f03150402251202060105100e060405041e0501050103090b0112030c0c060c1118010b0304060209030a2003060411011d040603030c0c0b0c030703031a031f0e03031608 78
    0x5002500d0b03d16000380d0f181103900301f10000303090a004a2000001c2090f014036a003044111880100036139031404c40020f103140c0342000b4910a024003004980800d071980340484000e450041c0060080521005406035417010400d041d061043c5800004261507100f40184c42016401c20301c1503074280d00304084d1310030f030807000d10303044082c412400c85a03000603102038003100003450544c032040402081414807803040d0105a2100303101c1c4e210b5407480030404603085143c40c10340e880e41759065100c3c0d5951604000921410415a606200d00000a010001480411804401ca0b1a1010700f1541c031401459690401510010161050213020268a501c180840c41189404400304011022120089001c6a5103504181d00150204c4c102d00e0901c044020104010018200c0d03561802c45681b104580381d0103046130040030940c50348402001e2210b0103c07a1604403000406403100a000794030860740c070748070b0000d9410f103881c03c0000d00c100445020069170303c984201008101605041441100ca4160 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 740978588 1250 740977338 740977381
    0xc081506011e030b040e0c03120f030f0705040807082109010801270207060c020c011106190621021504030b0a2408060603010633052704050108030f03 66
    0x9a41c0d108400d05c0e6664050112104a00c00162215150100c280760604421f04000580e0341f404110f82d200740c0d0100e0007125404000c50a02d084281c54044040320760780b280f9841012a48511b15000c102541d011a0503d03081c44080d03001e4000c15120104407400d07010301101d29011400480c01000111b03c2800c038031881e4000c80201c04a40c41c040d0103c84220b8005001c180d9905550b001c40100c21501004400044034090810b03203549440350440c15070741d10004140c0704550003468007040812410750800c1014006000780d814401e1a0003100206a4111400607881400b80d07600320f00c0c80741c0f003c44c101c0e025a07420548000480c0c3d983c00906d8003902164a0500400458020040c10005144286406468410090059800e1002c201801d4402c603801000e5090000c190402e120240440509600005010624a40c0c1c1703034000e00361141e008480300b84002c02a0f9030892080142d070301c490b4481a000443d4204903590300e031031083e0740c3c0740a144100c1e1300c059810400700e036400440c89a40180c410 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 740979838 1250 740978588 740978591
    0x10813020d170d060f0e0f0f04030f03111803060c130b07020f04060b2110090c02070f0f0617152b0804090b01020a2003070b070c081506011e03 63
    0x5601c031120501321220340d4010030042c0c01d412130901030b15221200560b00040d1a1084440d1420300e92802c044202d4041c0008040c044502d800c1c40405000381c000505502a400c401e54070782282c0d4042e8407500021502451090203120001068805241c040d1032040c0040345071030311a5410302c0c1d41c1002540c403a140681e44900e00c2d550701e001c660781d240521009004082501519180342050040b1200c03911070350103829842840401500700d02401d000704c11281c0270980410072030070081e016801c0c01c2068101c0782d40750720f4501c1d011600c01380d03041c0500102c80d440c0d5102100001d400c038100c01c503110140e54006a8507004102c2d4450f502c0c0840700b82c8030f1003c6d5003548034003000550121b41c9130040040303000c1b1448500441d08010300c0071507202e100308003032080c0041c0001c89196074900282c0d980c402c3c901440700003140d658903d20380b02041900b000d0b0090b4401584c0ea01054201070308007844910500303905e071050a162182f403442c0e002119000711410b8544030880144d40901e035082c801c3c0c44615401b00f6 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 740981088 1250 740979838 740979847
    0x140a0e030c060a1d0a0305030c0d0905100e0c09040c0510200a030909140601110c0409050309040c090b041503180309090b040c0503160207050d030905010813020d17 72
    0x100081c0010340c014100003074000344d01d10790100c0315500712582c980625201c0c2c02803803001e000319400c02c0031070f42d21001d01e01040d60364805c3c48041e0401000c1d05880075015100381d102616204d155a40416091704000e8100d0306030788010000c1001600c1c04850062020311040c0d0204040d007444520212107024174101a0050500804601e00204a4900e80142c0b60b00411540c4141a04000100f0250902203c1403188141c140c0e0503051110b005450541086401d07025000202000d01c0700c01e50a0308018010b1200780710718280155290080f84c20742d40302e00d10300944280310900a00d00310048800040c880fa003090f20b040c80021648801401c81c1d0141501c6070b0283c443d0150700300300800c3c41d5100381c035480c400034180f44560b000c0750760f1742e00750340d000d070340f410381c2290125800605699011041440104444800c0f43c022400c1541c0355001e00e0300181c02d58a400c1c1015084603116003520401e07611084260b4500009001c4110034010280d0440118048440800e030300d0040c1b0100e40440c400c046107007 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 740982338 1250 740981088 740981107
    0x311060a020a0506040f030f112a03010f021e070c1806090603080d060b0c340611011a011b0c05060c0307150b0319030c020919050a140a0e03 62
    0x8003002250202e4043d900d601100b1b00f05500311301c001000202c2c1e490095030413150300170919030b9104000d81d1004002e44c201509000d04c0329064180002840260080c007e03000c10341032141c040d4100c01919200b44031455a9200c2c3e00c0749a605032004590442c500002d01490140d1a00b06041e00c2d608000c00a0b4540001183c2c000e01ca001ea40c000318426001d00760b4400c171740340041d411100f0301c0d048003085d003008005010018400207840140b040001c0d16003005240c400c00300545002c103400101d42e11b001c810000203809500001700079150400c400080c82500c1408200342d0121401500d05404902c07800413100846441040f4a8521881140029405a00e480020345282c2001c01c46490b65440001d4840c10082d1440d000504000e04080522030902c044001903114100008003103080b200c4c1d0340d00c3c001414880c0d14502c114640140080d002828020304100c40c1143d003000401490303050030007180c115416403140c0d040c0300e442420b2001d11074445000c000058000c0001c040e0441c071042c33000303000 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 740983588 1250 740982338 740982343
    0xd090608090a081c09080a08011409070f0f12050903070c0819060b03012d0b04060b09060c030d090c1719080a050403021201020417030406090303030f06090e06060108060a0311060a020a05 82
    0x107621510349030888c0a40c503241403892042d2100e401140075207080d41c18044480d4101d041c1c24940c0b0760b81c1c1012401c48010b44000c660107244005c1c4001c0e00750401061000125020004007100c2e400380c180e04040d80d44542546580b4220651140c40c054035405101020072416171010010507802400403400c9480848409960300281564a0402648107030340400340c0361500c621144070b141650244562807410350310340190700400c1e1030f050040c40009500c1260000c180216170051040910400c1070800d181407000140c581401210904080c001c0c0000c084000080e070780e241342011810300c100c00480b13980d40c205a07030000031180c0c050180c241700100c0182c1d075000c42c02045401c18400161610718000c0c08060215960110b05800d400401090140d142c0c00003c50702030781d4042c200403e0340966140018010220381c2d00180c0302c075151800008a9860105001d80954403d1360303680559201c00c0e041098052070343c4002000d80c1c815103c40c2e0810300780301c000307409403101c0350060b81d02406c40c0e61100e50 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 740984838 1250 740983588 740983597
    0xc0d151a04051f080c1305090a0512071b0e06042f0d0b010c0302030a03092105070605010b0408030406030906091e0302010e0c0d0b06120d090608090a081c0908 70
    0x2c0f080c807242c0e005803602d00140042e80000b0030300c0c5402031246080020124201240c0c0d00c1d1510410354489000400c0741004008884426600400b02c3e01980c1c6000070740051500400030889450a10381162026811803402404c2039442444040d003681d19075504010040007000607100351414000880000300c9420104046862000c03020241d42c1c003001e00011044403942c600741410b11a1061500b0003003540002554032503101420b00040303948150515595107901210743e410714600d035410440586910001601d04107100e940d050016980301c54803080c1c1c501841c0103074502035205010401c0400d00c43d030046824103004003000608803540b519029415095500e0703402032600108000000c0641c24400c8400b400b80410152030400d903040006144080745803c0038242040600c0800c40c40e03500d80301d8401d0070f600000c00301d42441e040c0840241c00204940f003580003080382c0303500081441c40c0120710b13800d0041d03012441c14504800d80c02e400050105503804440865900d1982c400040d02c3d480083c03 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 740986088 1250 740984838 740984851
    0xc17190c03150512120c0a0f0f0311010606081f0801060602031c050106140c0c0405090609070b031308250305030415090b04020f0402070c030b0105030c0d151a0405 72
    0x11660804a6040b900b00940940c01103000b50407406540688032004207400c41c01030b0768441c4c00d80c0d407114040815842d0802964005d0590040c541170300040040c0b9005c03203d5094440c1c0c80d100c00c80c0c403884041c94200c81640c80381c1000300d440d80d40000d405081405018000340441514910459100c001d80b5084484035080700f005a40001181c1c0300703000003221102c03d00d0200740c5090096605000e402400d0396040c5200e5010302034041140e42102d00c09014503002404081d004101e2840d020052a51340c2505480c0f201c00e5024101011498400140840e071103280c0e50707050740071903501d680d0f103080c8942d210310060081c0442c1406281c032001c080d08a0380c94903030b010b40e5880341c43e802d0a041440401010f941d0319000340e4540000507000440c503441255010741c0403611080040c4070300b4013040191081640c000c20320200075501008200314601a20f051b82d005408072441d8a82d45800d1000c80400b10b40c2c081d00c110103c9203c030002c01000c5c0c12004200d048002100d40071300700c2c0400b1405071603059910 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 740987338 1250 740986088 740986091
    0x213030c0314030f072d150e010b1c0201020f0303070302030106021c0c060c031509020301180510030b071e0e24070605041407080303011502010c17190c03 68
    0x10400c0c0300003080c980350300c488010041c502e080400c2000741080e200e8010000c120101d0320402d21b05550400354004460601c130100c80c2c41d81070003403502007503151154803002c51344c0c0c0c5041a2031070002c4052180c4031115070080c00602040d5000d100c0200680010402281144030748400220b9231481880698020f082c02c0c1c0380541c80303504100019040903120425100180c0c40c6141820056600c42e031a45d02c515041900082c1e0082412022405802c40340c45c0202202440c03a000500b00405900450484464640c2c94032200d854000c043e0a68000340c454170001c907003080b000d1001c1a0316503c3c05070004000d0500c261b01011500e02011403000303150303603400800d030500303c04481800c19501200019030041e00b0710100e04c5400001c1a030038024001c010301a1907841c40081e040154090182401080c0a011160316550b10030000313540e54401d0080610705041440400070b030b5401401620710f5004a0380761801d1184999910f102a068024084c1000500c400091004000f140c402c940d100c0320f5a0b0f40 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 740988588 1250 740987338 740987363
    0x1a160c080a1b09110a110c0907020309030106080d0c14030c191b0302030303011a0c10051009060e0402010e03012c19080d0e07090216020108090609060712021303 71
    0x150107100b108998403030440181000c40c8003218010081c2102c04074102c03400c000036502c040600003440c0c21140d24840c1d80010031030040c096481c5e0000701612501b00102c00901c80c0c2174848100703a4a4810086054001c10701300b0302603900007000e05449a0340000040c0c01c0b24109200380d89020300c1d1403207424809040c0c14024941409010001011042507840340c8075140045e4903650129170b0741c0c8030501ca540c1d4541008091030104000a204807000001198203c03907030900400000300080c1400c1e10440d45011007540001041e8085001d20400c4030b01c0005815460754848e0019034030210040c1076658103540c0d411140f4049914510760a00e129038000351490b900008010302c625242c0803102051a8a1090200c5030000704010100d440c550005880410002d0344041d0740c41c41c100c1c0c4c6400045a49001168240c04130140d8455070880074001d0703071241944c4e194611031a403150070507540346125400450010788924041d05414001c0d92240c071005182500350504a0b0300160f294000319100200c1c0e04 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 740989838 1250 740988588 740988623
    0x140a030e0f03010b0907032c0607021c0203090103020d180c0f091e0b0f121006090e0604020d0201200309131419061512061a160c080a 59
    0x100d07049a07600507002005581400000101c0908005200104060300e034840c44240800c9200b112144d50038100c40b1403441d03040703d0800da0319141c08650b0b2000611803540c203840020520400c0f56088030b0550003961610a03800700460280d0300600c0c112280e00d80711114400482e545241009425000380c204082075414546c1e03890502005501c030b68040c0741012146008890308569003440340c00c029800158407070505020898810414500035403200051619805c882d80c0804d405d010f0352149082041455251500e260840e90300034607210380c40d44240001801401c220000710340c81c1d030050610b06450755007051814510410012808900d4101060a04803810859200342048410000c00c1c03000758180d41d812503105800800c2d45044076800e81c02c03c1440b540d5903003d140541312100510802d0380348280040c007000c912000e0480c02500e01400021400d60006407007658070000c0c0003d510b055041e503d200100000305e0010360311101c4060700055088803c201000c07610344100e42054401d441d19 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 740991088 1250 740989838 740989849
    0xa06030905060a150909170a08090c100c0602090d150b04060b16030c1a07030b01081305060105060a03020c01021303170906070807140a230114060409140a030e 70
    0x680310003e56414001c480e090000d00311101400d40b055070000103a550300c1c0d401c04c0070500640c1c400f40f44101d2400039101d880503601c02d0f2039078400c1502608954ac80b031300c4442401505a064043c0302e00084050306100000b84142d0004c00c2d09071801400400c01800719103600002403203001c01d40204580d10b0908610300e00303041c0100c900900c070500041b4180b4010210300311001d6986400102045900f000281c00c1200100e400c00c0341442c03242c1065803526005a001d00180071044030035010600540000c3c50441c0300740d01350300c6070b10707800302c090002a440e15090211a0700610b036240113054013407080748a100c40034805441034821011088135050f2a6040001403403950f074030501c46190003041a00603c0d200d207c210740c140c0c0d90200150f9500c1505040244050304103410b402c65074012800002c041c46400c800843c55134022452055001c4012200d441c201c0d0510f8500907200c481c8100003c2c150b01d081e41c03050302c406005610b00c4400e44001c55006c1d05050100b0300c1100824080f951705041030604 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 740992338 1250 740991088 740991091
    0x303090603091e28020a1401261506030403020c1516080d0c1103030708101e142b02040207141c090308180a050621091c03050705090a0603090506 64
    0xd130b008021030341a294000c66016103890281400c1000844044d401c82d900c01e02d0441140d5038087c42d012180900175405261502050b101465000e4240c840005c507480c00e441101d000759490f400419400c1e41c0d2109209210f2451011604003240034000c1c1e5000030210040c40003518400e1292959410203140d203e400c854807850301d44100480d468106008000020841381c1110640c06e1050040d40d0301804446140c01c65004581c2c03016410002650005031050b007030302681c0d07400e01070070740e1102c00c1800e02c62019143d104c1c6150b03201d584004003000b408040d440d89006800a480549440303010344501151092013952080341e5032001480c01c43e200c1c444440d55007080302628255822a00e16150820a4041d4243e04403100d10070350703010001603503103800c85001084080c1001e91120355030a0003030780300f00c00c5155442c8011140c00c005a2108008030b01c09000144c0c0c0c800e4003510305030040c002c400411004041905112080180410a0f50781008074001021130b80d40102c0d481065103020741c14001d0 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 740993588 1250 740992338 740992393
    0x1a030a05100b0a1404050d03050306040f1b030b0f04020406110d0c08090402130924080c06030c160506134107050d0b01230303090603091e 61
    0x12400000c2c4484100542240ca150301c861030b003a42c2c040c1d01c4082c902c0c0580b0403a40219072080600036080c08068100000d9880fa5004950820084242d2210074050f42c0e02c16400d84e40d0003180d00100c2e003d040c041c1e80700506410020348120f240340150404142282e21640003c804101c4400001581280400001c1c1600120b4a000605c10001c0d0b0b03600c122074041d44034914452600410300205103802c68210400030030140d202800600104040c60f1318040c80c0f41400c5500c9a41c0e080013184d00c4d140094014402d003006017205207580d036038404051894004401a40031500030b40c13090400f0610030000c3c44c3c02200151141d40e4501030030701e02034501d0300e15403910540303200c1c26260294400145030300a650400044e800c661030241e41440c81400d202d0740d50030095024003426484c20501218803c4c66040c2c40c0c903200100d88200c40803014195501807a118103625901c100711703115a0307080176000b6503004010701c411201c0c00311024007210010004d1003103030201c41e8842400003c0b20002940082d22861 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 740994838 1250 740993588 740993611
    0x3040f0b0708070b04020f090c0901020d11060f1015030c0e010e03060417071e05070b1305040f180b0906011e0504050916140315130b04020a1a030a05 66
    0x5850381e6000c0b0302d02400c60042c00514800c4002000d43d2150005803a017014010000c81040c074008002840036003020b50064011722440c00c1048415001e000004a0b402190000300400c1e03680340408541030000408000b402c0d5148003001942240c0b0061415098480707440c0410149582c542c001e14030501d1950540c1000316448624103035071000308029402030b8000600e98111802c401c0c280c102845210742c0140082c40004000c41c0b02e10394080702d019034610910559610650f2017500c2011402002da41390800210002c08101b103142c154007001c400e541902c4081541880b40342501103144a0080656a6031201400c0111201040c00080d01400c3c0003005180305d8140144620503070b1f078143c011140140d03136507000f2600b402401c102026000c000f004e030f0307544100e0319251060058a500f0310300500a21840c0c0f50901c1c41c04426504d244294038132314140748044402d0b1507282007001c014100741e800c48080034010601840c2c2c0c460f210004440200306a0756814a0341d07030310003151402050000e420 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 740996088 1250 740994838 740994847
    0x250905100903021008040320010b09100e0a0b01030b060a030506040e0f03120a1808130e0c0901120b030613150209010f050c0c19060e03011509151703040f0b 69
    0x180c0c4e601e841001c0d4410140761403511681c56180c107556490204400c141c80c01c5c12055800701c480815000009007940641e0b4241d00d60300c0c0d80c110032440300c6060203410400108074000030700300da1340d0b40e002180342c2c0d50500d00821130f07142500204030641d11011240c000643c0f25400c1040c01c1c01e10380264031001410000811071090840d103011f4507402450300c00c1100505800106130070207519080030030b0704e0b500921410000183c500d00168298406842d0440f40d0744402d5001071a02c44100d82c0c02c1c440c8586040ca5490324030b40c5401103544e0391052403410030503980d070801d880b11920200721f0140308100e01c01400c2c03480c1c5a81e0400f51950501080c8089405004120307600712641c2c003107502044418241000b40d05c030000115041c1c02c11105003070080e08100c500d03245060310382d8012501c808580e403d03110f141e8464185c0e8189404d8910001c2c018114142c0301c00200950456a440620301c0d20300722816030040c5440f001084205e50b40400d9180050b8030100d02131101c040711003c0710004003010340209191 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 740997338 1250 740996088 740996093
    0xc0608090c0a14190b030126070e040201120608030a02010b060f09010c0f150b090a09030938092701050418020310270f0605250905100903 61
    0x2d2200d80a01c52900403001d042107519150f5040c020503c2e01002e184268140d260490700314150030074404d288004d0184000180b81c1a01c40c9024503210050501a200c03550524484066081014204134108400d0a044001a200c244160009841c200c0d000c2c43d81d80070380d003070002e0940b4092480984141c0d8204070365440c85407240d08940c0d20b00702c00c1c01c1c40b00d0a0f800c1c1e410075412550840700d004e00300407242c03640080807000d0f59111a000d503030200c51910b000d880f10f0f2220411512a032800402081c101e09040c04981030300880e6940d80030901c030a243c06032850805607510310100c0c8600d041080d0010882c5950382c80c20880c0380c40e00280021a011540469900c807802c0f1f20018495103004503510018030000d6940b240301c010071950003404588000c80305c4014000280030343c0c545500c0c0c1e0402004401c042680038183e00d101203130042d41a0765811107a4440b4002402e0285c0192040c1c4032071101004601480080c1d80c0d401c070300a417101c03c10700d447d00701441540785011341c0950812031480c0d0301303000 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 740998588 1250 740997338 740997349
    0x827040c0e0907020f030f0301031703011401080901020c0f0c12010b03120903070b0403111005160204180c030f0c050609060406050a02100204091d06060d031116030c0608090c 77
    0x764460308030b0701040643c68000043c1d0801c0394208100b485400005282c1d9404001076000f141264070801c1b41c0d0104030407141e05440c160101f80a48130003452800703080080707584a40142c0e41c009031440c00052502d003000344500e1600b2400404210184c0040800080d00d207840f0580d580d070300051600070301a4103201e03c0040c3d103580310403000044c403040104640f1f501e0b8604000d802e028003103285505584640f2400d00d0018480c510780c0d110f100b903185020000d4140c0c81801074440d040071314170500031043c201e0ba0820000d00b08400300510500201c10055022074001c502081c004d40c09812003031450f680342c1c00c1041c1418401d810950141d0001c01180006440b18030454044465601d0029101c0b018182e0407401e0003810080ca5451a00104d00410021881c3c1c1c03100c100c07100e0720340140790604084413010b03844400841c0c40c5540403003031034201000709000d84c4030240311800d4641a81c40d4200c3d01108014400e00b1504142c03096041c0010a000d4590801107203500058014021f28020301110b00191 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 740999838 1250 740998588 740998607
    0x100804110a17102714010606050d1505010f0509040902060a051308010c0905090c0c0f031c06290412030e011103031303031a13240f03031b0827040c 65
    0x22a00c440d40110318244955055010401700d0824000e11150b40d40e2030f0018040d401c101c8a1000141c501004400b02c410104d824204840c010385480850b0400c01030250b505800054201d500f00b038841c4c240d5001070b90780400510f03054480352106511510b1241c1403070f6404099070015a420ba2528041a181d0364024100d4402c42e0001c5408000650310410708801c180a56032502105218020510081803004405003107485112429000d200c40d04012140554209120718008415100c40315103050348240034070b00e4201400888580781c80d81d135216005d504281150150005114a03003250b8840d03a0025484040140c0c100003141181400500c0018030704404400405040d030703848034611500358130b00004884000041202020091544103800503040100c40d8071440c0021030040241d103080304101c40266030035178080f4041c00d42035540c241e907480f1206200d840c60b0198429203400041c40b81e401071035003180b424901c40462054080040240329008038080c40740381041002491198451081d1 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 741001088 1250 740999838 740999891
    0x3090e040b04080a0314180111040e060d0501020403051b150a120b12070b03011502210306060d02030a0b030c0301020f0706050c221e05100804110a1710 67
    0x8581e03034034008000790000c101400100b50740006010402151f03200580c100d1949916a20080c010703801f684106c00f501d44158003844803045120000b0441e1070500d442d641e81340a12071800103107415142d442e003a203000005106040407a41041e11031180f1700f044d407107482500c3d40c13032b0707541504202d8901030140c02c107500320030b880c04c1c200c0d6a07000d092400d64500300b14181284610040d119980d07100c103401c1580303610900916145c80020540c12801e00c1c0700196030134422b64440c0101c4203440e03442c2c034544101da101808903a440b580a11061900380a0b51008501071880341500140f0b0f0b2804409060030450940b80c02c1c0e104e81d105020200e0301840410846100c2070b0b01010005180d95100111110b501070000d43c103000c40410900c001503580f1070046175081d40c1c1c130701c0c41a44402030b00c0721084507115442e0041a070001561442040e00038011a07880d0b0700700f8480c030f40700214401c0040c00b15507107408aa100784c61100d04a8a03410400c842800501e500044590060100500440e8044681801c10072038 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 741002338 1250 741001088 741001103
    0xc0504020a050f0c01060e07050705010b030d0504030b04080d0c0e01020c04270c0909060204060207080606030d050a050c0d09050109051504030f080c0a0b0105010801090218090a021204050a03090e040b04 89
    0x4042081300b94050340240250301c215048505007103000a05641280104a80c10340c0317000e40c03030745983c075001542c000304e001541d8a292178142107079500610354001400481d5070210a02410300c000c40035000c0d0303982418142e42d407451a0a004c0740020302c3c0120360001c590146140c902004a002c0c81e240d9035500240080034a01106e0202d403034405412800c0f5840b00610b81d01d070021000800142c1d40040048a07010780c03c440c25a9103400c0f519440b41001e0342c0166265100c090303a1801d15009a014114606050078818208401385030202c1c14202c4494000740050320145040c4101d45c1c00403003480c0503010541c0c1c0012812156161107819100390700000e000d148111584404020170b0104564a001004083d503449001501d46004010020302a00340072520210002c5407603484c91003900c0b6000e400354229040044920180801c000380500140300b0700b41c0810104201014000406002e40e100b60018041c4440f2400c00034168402c941003060104940d00034080422805401d094100d50130155 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 741003588 1250 741002338 741002347
    0x3030209031504140c10020303070c0c03020310061701060303021e0106050a03052a0d02040507050d020a09083013270e01180f02031e0a0c0504020a050f 67
    0x103450319400084003902c46419a040008101c40710100007500481e0908942e80302c102c050070403800390840081940103910500001d88040e01c10f40c03801d80094003e402c2410351a880340c010034100074040f46c1c0580660b43303c0c01c08000c002c0900441151202844008000150459034003c0d01c6030000866021040d1f42c204d200041e07601e007076120200500b002071803101c1041d502c2c9030450b00c80000d000e2018440000310020364801c400d0700807598000720700408810341d5074410b5081000401d00a03100e0400c00c181400301d0240700d0400c0c07000b41641100b984480e0416464040040d15220348481e4959813110351448200c1307074480d40d1003c1000825103102c09915800d41422098000c1c44562211041890702806034064100d8040031443c6600c1030700c001d101d5454508905c3d402c0e01d1a050511003101800d140140100b614801c0a104c801d200170150f4018424492682c800034500012401d000c1e000b044103034080021154004001317040580302503081c81a14200501180a01d02112010010004 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 741004838 1250 741003588 741003607
    0x50111070806010305100b010903030e0d050a0204020c0a17120714090406142706040b0303090901092309030306132301060e0d110f0102030409060e0402010f1704030302 74
    0x40386401400741d5104654a035a9030b42000f45d9038030703144041c0104c01882d040000380f0f15407240c0080c20690303415486d01050002c03410103002e410f042d0300d00199079601440c0004001a55180001c022140c040c60042c0100d82460400c000c110004807031241c5140f138100240000e030001d950f07000d035001d500c0c0c4c100001f101c00205030f180040e100d0304a100d0b41c4a403900d103010800303000c1c03c43c00300d4211005480c00c1200e07034109224000d080081c0b0b403444100d514400c000420a280540058085140140607070381859440000304144100a07002440596280d00e074413003144401140c903c42d00792501c3c44560782810540904d40e1a8030000c0d0a882c0101001200c4151010258225401c514070240c030800c135110944100e080708a80a007c3c090005901044840c05442d21408117200b036a000105070300c002030280100580d1614403800b05055000501000840a40e540f090300c000f844203405d000704a1809100045c0a4a4a00c02a2090054100701903034450803080303034039a0003581810016035880004 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 741006088 1250 741004838 741004843
    0x6030c10110a06060e090109020d02040b01020a0b0a02030103110117130206090d0c0509010803090f040902120f1c171501050c0d030e0d020c010807030906060302060d0510140307050111 81
    0x10303006010600c07882c6070300e004010482d0701660842d104050101969211100c034103090301e0001101a40c0a03607a4a40c07000503203040d9000c0603079000140100c0d1106510f6641d40448080201c802000071039000c401002842903112254000345802d1804400c41100c0c11001c0e81b129002901200d4000150000001191202d408541500c00010040c0e010402d0516080608100074012503006455080c00003a42e904000191045002d00501c80408146010b043c4802800c044005a9018901700b92034801000300b0722500110044c0500905403d01e8032851008848112042c030808000c0001c0491a610038444603150f003100d8404194240e41034040b00480740c2e40600f450200c070354003034080300b4035000760107520002911030314030107a03807040b594010700b44d03240d0b41310b41d0b0b000f40410341c2c0800007402244281e0085c010360b03104000009406450f600070602030307042020f500c4a01c0741d40d101170048001030314003002d00606000200c42178115402c804641c03516114440d150605c280c503c41440c0d801010b = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 741007194 1106 741006088 741006107
    0x806060310051b0c0703060b0f090117101d07120503190c1221050702030d0c09080a0b100e010503030f1606051f0b0306030c10 56
    0x44070180d802502c0e000740282524400b00c1103444100c04100c001e480180f2800c2c0050141c0360451800c40c1c2100c0b40305c4645849540c0d03600007040c15036982c04589054900072880781851669080e00c041c5000580c9a007040000c2c14500310a0f0452140700070300280302c900c801100e400715a1109038400c0ca9114a00c040c0c0660010850b500c400303c41b14040221200140c9030030285c6007450707100da007440384040b600400000d02c00e1000d1200085044c48210748180300341402c100c1400d0004005e550b920400d2065014591110780486415004041c11001099407a0503290000c0c914074164102040440311001400e0700084017180402070612a18113aa40c0070f40154a0710754a4051040d65030854030910142440b2126140001740d0180a050701603000303030fa4041d81c0d0001e03111114515280300c0d00560b4568206208000481d94001440b40840b401540c0b40405141c85840031240c0030344 = true := by decide +kernel

theorem cover : BRFrame.Cov 740827338 741007194 := by
  have h0 := BRFrame.cov_init 740827338
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740827338 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740827338 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740827338 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740827338 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740827338 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740827338 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740827338 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740827338 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740827338 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740827338 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740827338 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740827338 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740827338 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740827338 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740827338 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740827338 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740827338 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740827338 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740827338 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740827338 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740827338 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740827338 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740827338 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740827338 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740827338 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740827338 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740827338 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740827338 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740827338 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740827338 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740827338 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740827338 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740827338 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740827338 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740827338 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740827338 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740827338 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740827338 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740827338 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740827338 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740827338 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740827338 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740827338 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740827338 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740827338 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740827338 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740827338 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740827338 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740827338 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740827338 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740827338 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740827338 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740827338 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740827338 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740827338 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740827338 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740827338 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740827338 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740827338 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740827338 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740827338 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740827338 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740827338 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740827338 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740827338 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740827338 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740827338 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740827338 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740827338 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740827338 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740827338 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740827338 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740827338 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740827338 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740827338 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740827338 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740827338 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740827338 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740827338 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740827338 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740827338 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740827338 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740827338 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740827338 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740827338 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740827338 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740827338 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740827338 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740827338 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740827338 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740827338 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740827338 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740827338 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740827338 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740827338 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740827338 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740827338 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740827338 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740827338 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740827338 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740827338 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740827338 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740827338 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740827338 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740827338 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740827338 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740827338 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740827338 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740827338 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740827338 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740827338 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740827338 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740827338 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740827338 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740827338 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740827338 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740827338 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740827338 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740827338 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740827338 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740827338 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740827338 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740827338 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740827338 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740827338 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740827338 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740827338 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740827338 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740827338 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740827338 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740827338 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740827338 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740827338 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740827338 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740827338 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740827338 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740827338 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740827338 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740827338 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740827338 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740827338 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740827338 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740827338 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740827338 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 740827338 ≤ n) (h2 : n < 741007194) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
