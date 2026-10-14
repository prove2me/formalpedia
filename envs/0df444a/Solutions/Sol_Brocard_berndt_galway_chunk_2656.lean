-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2656
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:21:28.783251+00:00
-- url     : https://prove2.me/submissions/fa7d8d51-aef6-4b32-9bff-1ad1fe530957

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 477517985 ≤ n < 477697841 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 477519235 1250 477517985 477518003
    0x405010906060b130b0301030309120c050a141306061710051903050c0409021c03110102031512031c0f021308070807050d0f11130507080708010506030906070e010c0b0103 75
    0x707000703055400c160990b105c000460010070040000c40e034424000c900360781001e00c0304200e03a5220f00700304c07050001c2d9400031648040e60040008900700200005460040240d80100720b01e02d40b0702c3d029048400c60b20411010030900580c1c0c2015800340040e0640c8180c1e00658251400e48610101c2c0003041c1424840e421621040c07418002d1110400112030041030449040c0140307922a4049503810308442680e13104046442954000c00d4026100000841d503c0c20086491b0301d4800483d802400c0d0394030600340128040440070805400c040704a40180e41c8101142881da83d0000361440249107030340c100100c0705c0c0d00340848038018918800c448010300d000d000400502d400d154859003003480f0356024600c1000c21500c1140003a5290402d4086142c00005815214000402055903241c032002c034210f9440c43e09080101894020120b14003c050650356a0116070303c690501000b407005682801a55000100240b002071103004d0700c8951003018034004003a42010390f0b032813a00100a0308100d4001e00 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 477520485 1250 477519235 477519247
    0x30a0606030f0c212009190c1407300201060f060c150c090f030501050106021e0c120f01061403010f09030c0b1b04030b07030e010b01170405010906060b 67
    0x3000751640c4001d4010400e84909112108191100c8001300b584010b1600075554540d582c000ca81c02082c81e0440710240001c6c0b01803400000e010000000104422101e520f082d9440d00311600c00c1c0d080103515811180c0082c6041000d40340c0c21522180d035015207144000802107008408142c0121408040e01d1390008200e0b103041900156141e807a54000400700400341c0801720126206000d5172407401c0d2102c9000074401041c24089560042c02e80025042c140400800010440c055000e54100d030519420746640c3c81d4a840c01042442000700c1c85641c03a80101920003052030003003800e0004590f000c04580341c5024801e81503080d112150700131050007800c0500340585050a02844101401071030b1b00f0010414140e038082c02180c00c402e80036180202080003c1c0a0181c0c1c2c94074a445490049581500c80f5624030780b6040400d0100c0707031200003e061038410700c1c3e00d91050003000c882d40d80503129070071088050807002001000c01041660b940d0b40f40c4800c40c000c40e000e40300d114041e0800d082075558403a = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 477521735 1250 477520485 477520493
    0x1060c0c1a1306360b030709090507020607090905091e01090203300a09030507030f02040b1e01210207111008090d0e0301090203010f0606030f02090d060b030a0606030f 74
    0xc590b40c4000d050060100d02603941003012000b051250300c070807400018071501103200241d8100c44c0e4000051000d0700100b40000c05da0001c5604084481070b040500c11175035802c00c1240c65035070030b80b200c0f804130314007034424450f80c1c055070041135001c0002002c543c40b0760143c0c1c1d49a2011014081504c503565500d06008040d0f0800f400b00f046648201107080242e10301c031800c4003c444040d8613181d11103c40c04903402d00b80034420550034000716044000c41e002503031281400074002c0c4882008031f2089107082e04807415810202c1c0d01c11140403c044564010704074503001528901030044480e003000a401b00020301452440c40900b400500558006180303001c0f10080c00751100200061009000c00b2000700448031800190291000036985001c40340d2541940c0400c0c054400d89800035130650800303c40600612140c5c1c0084100c1c1e582e070b6804c1c8039001940c0e02002c200c1c4070340005681c003e112036500202242d1b458004041400c009011070f80e004000f030b110b0390211003440d0811114004a404424148 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 477522985 1250 477521735 477521767
    0x3030d0903050d06230616120503220c030b07140318010b01172a0c0d030b1206060907051210050f0a061b02132d050c0301060c0c1a 58
    0x150199298440c006004150104800100e0070a00f9104180008800d000101c03140c547c1110310760303c20010003500242401c041c3c807680007140d80702454074600c0d24090032010894520f00d00580c110380041c607980d05680b500c4400b240001c045000740302d004440c1822014405004500c5915405141429680b5541e152825910501100f604000082542c4a01203140e00f051343d812041c112811030741071101d020710301142c10350310000c2e08420402280031159802e02040c48140c001450f607003006000740600c01c0024509030000d4405250b4010800243c1c1c0b42070003904141c002510b800d04a0602042d0607035000c203030004440a40e4500c0720b49800300074034100440c144230701a000b00e0300300f803000b4140034004284913141d06048142d06003150461041d5100e0000400007004105428446500c0444c081e0910010284202c0d2170702d0b10780441c0040c0f484480c810380340541d10380310341c1314516440c2081c11036500c04d110301c041c0d4003a41d0301200000e000400160181c4c001201112464550040401c010f42e1 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 477524235 1250 477522985 477522989
    0x1b0302010f0e06010b040b0304030201110a020102090306060102071203050c190503210f0f150405071710080d1206122405010305120d06030210091e050a0b070203030d0903050d06 78
    0x40b661100005120303001c064402d41d020356259540c1c060316640e40e418200d02420302d854040344e6034400054944103442d410740003000039141c00d40448005490f100012a500d00c1d1620507211001e141542240011b80300c0c400804000502808071504c4000044140581c000c0082044550750300c002407600c8000724841c215504203529441c0144140340010b6181c500fa54001c00741034000c0c00c102c0020f581051041c040e00c861110141c4100250b00e00310202810071000c2c4c10412842049c010009402d18540f91001000e4401080107815240000d0805603455005110400005a154440840e408180e1809ca0242901510885018442c003250383c010045802d40c03903540640c01c080060010810000e060f00480c2c1c0d000034025a41c4106a860400420460b00002d6004040d18021000c09606c8100342090b80c0341404400c00c901c7c000840280b03408910310a032500480049000c000b511500c402610006001505882c54040c5048000c1c00300c50300d62800b180412004100791900402c0e41c818840 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 477525485 1250 477524235 477524261
    0xf0901060503281401020423030c0409020a080a050c04111216030b0a09050405060903120c032503090303061a0d09050c1005030a140402100f1b0302010f 67
    0x103481c104070200e500d800301c5106000c1528031444960610360503641c80541c0243c3c00514880450481c1400a4043d502074030444400c541c2036500e603a00880700024982480400a0045c20012200b00038040540142003090ba4020181c110000b81d8100078040030899510a0700540380403404402080304440c1c0c9150240d80300c042c140302452086404680c800d802c01400240c2c00d4040c03001030012400740c68581e150325000031003800d000483c41c0c0642c004a020b00d2140b0191242c5607031b14401d296a0b401155144a44540f401d4003281603070392550010341e000031011803401c010003124282c2d14007030744035906010f0009580d5104202810351511481d00a8508041141006144001e90350342600514054009895944032410200002004880000c0101500c02c44180004140240040d04101e481c40181800c1ca030101c1603981c08050b1540c401c650003441c11300c040160400445000390b120389442c0038001149406a414104ac050404400d48a9030010400d02103000380d01060ba044650320320 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 477526735 1250 477525485 477525491
    0x4090b040f12210e031303052802091302010309020a06020c010801090515040b0a0f0605041403070302100c152409050105060307050d0f0f0204092910031d060f0901 72
    0x460150f040e4805503d0740160304038003180d00c5404a91040c1188207003410700300107002e44c100020400c003021813a400307518042d4400350040c151084034984c209a030890000d5015080c2c3c00000e03180080c001e100c000d610f006140000b26080940d005ca8031080d0076401201c00f503440685000c01030361b031154005024200400d01070000e800c0500301070160880d80c485941c8a90b0320340300e100d10a526001050002400007006181002c0d039110300141c61a803080c080e10407091060841180d031801c1c0050190102c82e400342c14000d00c04c2d8007180441c0c026211740004ca5200c0103151510f001040ea5009180d1415240c066000c80c07070010b601038000d602450340c041c112060925004220940d2490296a8080d40d030b401d0480e81c034005404904002c003006030554083d18507002910061241a134094401e41d0600301d01000803c040c0b1138102ca45804500950688002e110b420411606000c08105400c641909000c200243e0032020140381406048885c04594411020841302c901c180003440c2e089601e0a00070 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 477527985 1250 477526735 477526757
    0x40f0510021f0b03031612090f031703060418030206011707080c0121050702060402010f030e0703020f0a0e04060c03150f0e0c0c0d09241d04090b040f12 67
    0x1640e0b604809400c040040355031203602400e1504d060048400809071107120341b00700206450602d42e03c0120100150004044010100781c40401040e00019241c00c079101240c01c90384403005003142d9100034415034005807a0300200c1442c4440040c1c0364102c51094024040541c18201c284104032052a28101c45a000e0203081098030004501ca075120740081c0f901030301d142e40150510482100441080700d001c0d24181c1044002075020842c01d014034400da03178000c20f20150711802c07001d40381d04200c6039007280c0000d001000180b4100e5051030b2180c1010302210103259030b82d140e840c4000402c2300d0560f40c4945403803201151710b9161041000b000f071140105205541068922108983e550113024190814840455050304041040d01c280d442410125205005910801005803100b4031403607140b941e909001c9101c0d800c06128a4031401801c1d5105280c6c010100c0c0c900b108003d48101168100781d0700c500741c030041340e000102d02c0d20580c0154028440c00c403092500340850f40040e05075800300146c0c0c0c105 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 477529235 1250 477527985 477528013
    0xb010806010e0a090f09050706030c1b03050a0e122a150409092d0b07020106060c0f08071b0311060a0503040206311805010302030a0305130506040f051002 68
    0x7903101501c20007880090101c5d104114400180f8500e10007510750300c1071400004295600da0091010201155103c02d00703060b0018401c03440c031008000040c049141403004102207445510a5060110020158070780c080c503144041d4240140986495a0055000c10b82c0c08100c22040042c4401c4100340c0d0209041d51100440e0003543c01140201185540c4a00440d018000c10001707001c08900d845030210007034002000040200c80c0f451204840d140410000281c14500610a210440d0030540321445603040a035a088605c01c03103180c044a4000c0301703000707610100d1550f082910314140305181d0030503664114101410b00e0444005180e1240d0410801214001c1c3d01c0b809503034025505503000380c1c5480582c4622104030780300e61680d0320783c0c135620300034903003041003400d0301204540c9014000d01c581e0071454640340944070240030180d0154029203d4200007440f400040c42d50300b0507a00c6d0100165103030070010f074442d03002d81c0c01031008a080035000c0c46149803108a2402d020340900061104981e0301034 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 477530485 1250 477529235 477529249
    0x60d05030f0d0b03120c1507091703070c0e071d030a080c0a02040903032f19120501180c02030a0e090a0b06030405030a09122d0212010b010806010e 65
    0x103400c41880c00410250b00b80ca1480d0800d403d1900000c0944d011400300400030030f819000460000da05105086000d500c1006403c2c9080c041c0d00d03240d40e00c880c018103105000c070445015a0521856100412000c0c1c040f80c0c905115070054030200140b5a11810170f220300810244681c2078417241c00300d203100d03801c1c00c0c0d07900080e0038811345070711840e07041d00c0340c06032402c25007080c2e23603544080c1d0000d0414041e0f070105030f41a400152212748031085080604406011130600d04496400c0e03020441040006800340c4d480d00c192503a401d1036910b03150b442601304a501d0b40c251142070344a40216000d8a07107000e03042030385004492403481c03688011410040030500062840c102040114003c058100100340250415000400c02000141010ba0349050078548255240e1003821040c000841100005c5242030300307d00340c40710302e03034124500c1c07144800c00c4250b0610ba5450100c5070601030b00c5001d90800162905e60710509000542400010420f90810014011120003880a41048038a59244192340e80c0c43c4 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 477531735 1250 477530485 477530497
    0x100806010e0402130303142701031b0903170705100216050712060531060e0316050c0102060c1206190603050405010b10020d0309020312031306060b0f0403060b030a0b0709050306060d0503 82
    0x52074210b4a840588c0140c0040210030b020a452200e819034480c0015006000301c81124891101645004044007d5200d18007034034000400b00e0704003644250242d506500540f03158462a071075208449040d98130140341070000d5020744081c0d0840f10804040c02142c4c49400e03400143c2440c1c100759104425844051000200340500d0031110a40c12023060001e15407207481d0741021001241d50b241c010f5503080c000c00081a0045601d4452140e40c0c0f542544007044080c0188400c1c1000782c145251440751807900c0c1c40040c48650003a0b04406195403003007200d4503880041c04180c80014840c1000e0414078292107030100c40300d0289544680c112031095000514440311103072860005400c88840c40040c2c20061440d00f01541440088188007604a400340010700591040c41c08001083c0d07940204030042c010500724500004c0c05000c100041078581e0459102c882008068428100c15507450030301900c1c068540341d00264400c03601748001c0c1030400c1400c1e089441180c400c1448003880d900c1c076a603841381d8 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 477532985 1250 477531735 477531787
    0x30403020a050f0703110a08030f1602040c030e0d031407140c010e031c1a13090510150f05060d020a1412060a060c02100806010e040213030314 63
    0x102458030900010103941e601c00c05032030a00d41008120742c1d0f2030760140410340c0c1c804501d0b44580d410340f80030030305e4a0494003003801550400c2c5404007050700c190032000710503480c1c3c039090b030094006039220321400c41c51840c25280041e01b0441d0600b420f01d42030703401c1d5160041c9468001c8204640e10780d8100103074081850320344000c500502c401054094010340b2803100807036080c00b00c00740000f08048058900100300d141100031204600341c80b40240e501d6054400850007000c21245e01c0c0c0d00b80b40c2c44144000391142004079480700d07107a441501c3c043d11040000100d80c0d4844605a55601d00051308008010207458514941d09013000181e40b0b1081c5481c034981a03500044550034203008540c0f0701c5210b1074400f1103d4490300e280000224110040341d02c0d031300c20031807800c0108070507000d218001181500686200da041c0d4214400b138800f40c0002e8000c4c3c1c1403000000880b10340d555036000403c480d41e2009030f48808149180f4000d040788040c5e444410040000f0301c41e000c104108880707808901045 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 477534235 1250 477532985 477532987
    0x603010b010903120c06110309160605250203030a090306060518150406080703080333010c02012c030d0206040203061501051204050606030f0c0a12060621030e0402030112020105 78
    0x84c1c107016541c0d680c83c840010055802e1080806400c28441d000d140714005817000d0b05d084c450b500070340c00c030440242e00814000ca0014030111106090080041c010701c03001c225851408409a000286181c0040e00c4400c00500100c0052041000c41d010710801040d09807000b0340b850b400b807070010a200c0743c0140751a804240c51030004000755129081500103104140076190f070992203061180c111f40c0226106030b1a80d51828101c019060244c0001a0406000420966440c02d03080112540c078803500c003d0381000001c105a04050f9001e02c821001822404950310700404090103240c00c10000314501403d5400c21020007003d62404140c060b80200c00104140c1070805601c010307121401003100c40304051050350204420031600142c8a80a064228100c03400100d440b8003040d0386420101d40713150007503004101044001144501a84100d206500100d04141c0b208141d808044001d4250103107012010091420f26400c1600006021810303101940b442d030400000a20503005203e0017810844 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 477535485 1250 477534235 477534263
    0x302011101060e041202060906040305040302100207080303010b07050708070f03170705030a030920150a0c08070305091503091e031207021f270507120503120603010b010903 76
    0x2800794000b00207040400d91610007818107061010710034030240a440050320450021501306080069021b110307030b5141c0d03202480c03e415607090042c5107102c0360031041135100c0c0078004255640c040c00554041c11000021f552244d06504019240c0013980d40500c01302d4000e401e050180f140e1282440d0180c03134214000c03c111040e003500191803442030140242403808003146004540340d01d6085118058060b600b42c002d00421440301c5001046840c41040c2e1050003004100c103440807180c05000000c1550401c906c0900803515441c1541d40016004c50000b000010740e81964904100000f8540080802d1941145014002e82d07a4800f03140050381c003031fa044400703c0200002c08104890a0000107002d04100d400d02000c041d60b10903000b019a0307018880c84101045440983c41f454817444131510119990720411100046600200b19003a1118000c403c030114440c0c00e0901150443e85c03044004595405000f8142400703000301401180c400d0341400340c96440d50b0383c00038541d000e40343c010b410140c803aa = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 477536735 1250 477535485 477535517
    0x30207050708010510030b0108011803081e09060103030306150f120209120105070f020f06060d0f0506092d0c010e0427050c01082202040603240f0b0a030201 69
    0x21180da4003850b019801e01c420058000c91030382851045900c904114641030340c0310f124090981c0d2000300f400c3c0c020203c996200003c01e100b001c103140c1080c0440305140d40c0000d5043c0700e40e20120100c0b0305019950140c0010410590f03d4401d07070004001c0400d0115070821044402080c0755003810b810b20400c80b0101034480c034080180e0440f080080010480c0301d480202840c264041c000403503104001c40ca6070070f14885002c0c008601c42d151703c505400a0000340d43c0340c3e010000c40b5164820150b4034001c01e8030500000540400c000e43c054008100248101442650300fa14001c081c4002442804120b418400d10f1300d4001591501e440c100342005062340d404200450003d101001c182044120340034103041102c2c2d011030108220728020750031b95402120a40066505a0b01994820300040700402441d0100101e60340b00d0055a10084c004a03031542d89407500782d103d00700c40721103800e605030805071903100454038800c07a0b2842400023414000d08503404000f4a5401caa07110280c107000c03503411604548 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 477537985 1250 477536735 477536743
    0x50109091a040204120507080106050604291209060105030d08010308030723040e0f010302100521280c020303060f010c061b11060118020f07120e0a0f0506030703020705 74
    0x1481d00500b0464803180d454040300e41c2800e00ca60306a0301d5024541001c522050f040c00744409890010300030916061503d14502c5250300c9604c00191010030785204107131f400000f20002e000101c2503100b8842e0754103042107000e00349181a40007520946c00518400082e54000034511b04580c2c01c14180364917550f40e00380035200d0014030700a06042d000c88038112005c01c100380d8090010303204510007580d415a2425800410807200f0700001c1c0d8480100359a1442e1a84200e000708440315032502202c16402c920710b405c640e005070540c0c02e41d502440d40d22000c80300f1308a0070741d115410052000c0030300c001040410007a40301e210141c502c90150300100d000340c4181c1d002d0405018a42e522003420084500d80f0380c0c01c03211040c0e9400c045400503541c50741c8100142000149981070320141500d900c50383c4203c41c4500c000b94080e90200c5281e010a1202d0404525003603401c035401c540d19100c4081d1113240400f0040d0b01c00d400c0d0001120038200080a01003601c40c18240c9a100f0554240181d44007440d0900c1490 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 477539235 1250 477537985 477538031
    0x307171e0a0b040201021905060925031103030403061e14130201030e150405030405090606040315050a1b020703110307060c020f0301020f0423220b130f020306030d0905010909 77
    0x4920811f10004101c0002189481038001c00c054a800b0360400000d0f06003014240c00100c00103031a400c0c20300100307008801c03c00702940028200c80c035055032035031060159110b1341c01e00054a000c418108241c08514060b42610040ae048154090f02c2c2441c80107160000b0880080c0c100340e41d5075810300c0e00035002c00c11991480c9544c00000707124501454176a940b0341c01070003183d00444c908800704016080c030340156400c1d2031348005021041074054043e00002c02000b803600c03010507101c400a41e0030781183c0c4071107440600b042c0c0c013030640141582015010700004010031402540104010800b481d488801e00351501c0c2d0464020b201400c0b00d00000340603005040561074003420008000940c048000e221a400703900c02c3c070442c15820160070801100d03501c4083e82c0c8980c04c8000d42c3c8202a40d120780d0007861140d100400318448506078441c1c410131114606000c1407000c2d03000081c483c2c0d510341004098000e00403480c0000c41d560a003c0000c1850540b8820020119101c1c096084945618500410 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 477540485 1250 477539235 477539263
    0x10507060c0525022e08090102070f050a05071a0a270807030b07030603030f11150106030c030e01060f051c050d050715050c0f0a0309020307171e0a0b04020102 70
    0x1a90304002e1802d207003024400320221700c20040341c4c0050080b401e181d820707901051400c0d60051007064204800b6113028100078100041c0b950f08000142c00141e0102c0f0003030609004030010030b1012801d01c2c1141c503052441c0c1210003107401031003e400428052204031038001d0100c2ca40000c0700544c150101040c01c21000000c10650445000400d04120016882d0126401108aa25140c5860301d003a0201c501c9400007600068200c403030307048442d0240e0a010034940502003200c69102d85004007c9011038280c2082000a0701c501e01060066814019590040d49071002004028034020094951030050b1117001e01880481c00d1410218041511800e20550014259102c1c2c01040304024025800752070112003001c007001031142c00c1c400910440d4407441c1101445444d00858100d80300f003a801200304c0900305600c845140d001600d00b404480700a01000340410710340360b001d60805050840c50300c2881c0c81d000500e41c161030701d00f400180640000d46c200800c1c582a803503a000407420000d00340111a = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 477541735 1250 477540485 477540517
    0x5090a1218050414060123040306110d0c02031c110703140409020d02250302060f1f121a0403050f07020d0204051f08070b0306131b050c010b010509010507060c05 71
    0x1469803803d80c1c0c140305117026a40e05c441990303856400340400302c3d00001d10041c12010703c401d1000862581c0071300c2c140e5000b810f1003814031292030b42070415030744a080103d00581000c54600307407481c401a885411103051f00024403840798003401c0840180103510002c4c041080d82002e00d03d03404484001c0303801a00303102209550715079917030140c480070b0f40c025104889030b99103c0e00d098040d0041710306450310f1150f159001c1c00341505c071040303160041040074080f404414012b001c0072403c0c03414001100020b0640c03190002c604000381c204031000c42c145400540403c02944100f00010717512404442e419106042c0044d01e4281c1030000c0b82840d0040840250401d2600003031050104940180d100e000301c10051a650340c907200c00c40036403111550711a40d0302840040c0301050942c640080c120040211726800060b87d0105101c611003401884132001000c01d00001e06200c20f17140a00804072a6a82801d243d490420950f00083c8284a5060301030606503941110441282c450412106402ca0f152010b03 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 477542985 1250 477541735 477541751
    0xd02070c091b082401020c030a0303090b06060a08010603020a0c0605040b0a0e03130b0c010b0a0303090608070509010801140102010b0907030b03010e0105062d060a0305010905090a12180504 83
    0x1da00180000201c103910019500c1c0114a807610903200d140c41002c3c0d036612440741c65120a05188448100e00101d415401404280d5049071000c2000717040350340c001c0d50b02045a0002e8104107421741e40c0509941e008500400c0743d007413101e40211803a411690140b400599800b981801144c07d2804242c009010b1418002480203000e030380b0721010700402840008104544a031401c661ba6031040c58084074090b90030701d100b000743e00c2c18079001c0e00241c0c1c0d240c5d00104008080304001000301c99150000c4001c56001d9109000255002156541c00101c508056180180c2100003800d0174805200b00d0303141100035403810300079903c02c0d0014913210b00082c0440c0500d00b40280050040c0544200c054025031904002c0070a181d81405054040c940c06044228100389d18540c00d0b0449a145006240b840070103d503404550301d0f881e00515000c0b0240d80c0029965042c02041c900351040907240c1b1380c0650140c03400790003041d40404a40080ba0f40750030301129625800c5090708522299070f002c280d000e840d00040d = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 477544235 1250 477542985 477542999
    0x2c090c060403120305070e0f0f120706030504140106080613030528171323030301090912020606151b010f1d0a0b27030309070f0503070b0f0d02070c 65
    0x12600f0592140c0e1401e10440d41c80360000c84072110300f58031995010170b00b00041c01450074881465680d070f100240017035152042c80f02e25949840d807941d02000c0040d0b502c00c00c10090100d084140c9141e0405000280807091800300cbd01b660310714000d05420380040b17001c0309600c20140038904a441600d1800c0c909414000c2140c10341c90801c400c2e8a02c840440d501c0505c20000d40c2c40484294820036035003c5d004c88040c02611a040e8001608816000125003001c2c1c100c1c59080030006140240380e00040070900c0b181501d03115a03c2110060880103550080d002e020042e6280c0c3c4500c20fa403480700300b25a0325074032061002c00c091400c2e020f100c00c455280070490b064140b1039800100350f070101412101c01c0040080c115a42d50000240043e2004420202007007480b40b188000041907502d0400540712103110740310440c1140d0060380c50841e564403544042051141903001c50b4024041140070f0721605243c014000414407500c0e40140407034100090242c86d40c0002d40c16900071a40004d414000c00391103041c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 477545485 1250 477544235 477544253
    0x301231b072909071a0705070e0903030a1808120c1303050a0506280b01020a060501170622060203100314030d0f09020a050f031002030c040e012c090c060403 69
    0x40a000c2e044541d0300003c180d480d00090300001c0b50905009212084c2e000c55a01c40590002e10085400340202c41c000528003480384600d90003040003401440da40c2c03d184840f00c1c119022250354407800358011030603001040320756064034800103c82c40309480e1540c6552a0703c015100c0c00001d090965010345022041c044009203010186216800319200703500c910712490516210b01008403c010610307110a80d01c1c03c0141c226036018201030040700c09061455503240c017030358000d80098000c50603a07101d503c0070039010048a500543c044610002000001c03024622041c0000c0e0040d001c00c1e0000045a44001c005010000550708148452001c00c400d0320b003d900c0c0e07408840400c000c50b0602e540c56003000f80f6441080b003450b0740113105494292800c0180300c0d18003e0101220781c9801582c02c800f88400b4140020740c402c202c02d94190781d5030b1b0b04000d800100054180c10002014803660081c0111080700d214111001c60002c4500b056a96400d191a151110070790f9a42c3c0c1010001c1000020031020704 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 477546735 1250 477545485 477545543
    0xf030a020111040f12060f05011202011709070b0f090a15020601150c0b07020c0a091b0509130b060d09050109020a0806040203061603180506060301231b07 68
    0xd8000c0c041000400c2e440203090007180200007906010460030080b5102034081e10180c42e114140100781c5040324011042124001d9021441c1100024950f404640c2e001c5500004035610b200312400b18209105010380da031060b03018034140d02000103008400001c40005542406200400d20700c0c410f5241c05d510b07550800c80b03051620241c401c00780007089500c0c02030070081c007000180e03450850420385078a0f980501040604090294001c07601c112440c0d0b207600c40000e0281c0b00c00340001c80c0404000c0303004516165074038505800c214050150b041d0564401c600741c0b03005241c1c8036001c6140c10b01c3e9800103049225a40340c0d030301c0706490420310300104881904801c0c1c2050085510800740c07559450116152001244c00941c550081130001d013044504480c240020070241c5400142060130b5074071b28030445900603040c1c5059009000b0810307145024007844c25658443c401d02541448868500b89859001401c08a0910002c00d010030060511134241c80c5c02c0b43d0003801300c1071400c080d00411001c1a03441 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 477547985 1250 477546735 477546737
    0x106030b011518030f1e062f0f041503140109091101050703171005030706440a021c050a060501050a050405040b060921010b0a050f040504020a080f030a 67
    0x141c0060f0308001000c19116085981040110505814a035110030103c43c40c0c0303040c0000e80440810b85004904d40c1d01c100040d441100c010040220013544500c40c040e8151340000b43c0b43c40c001c002400e5200c0c41c0ca4261801c8407500d1120741440480004198040e00005100028581503040001021340540d040055214058628107029007c090011101c5114240d40500894280720020b1750210304144040d40c000d00e814041e130f20142c0c4420000742400141da000c040040d0315140d00040010b5078000c0c0c460303041c5403000901410b0325900403c48142e940b034a180328041900754006014010560121030845282c600c40d464a8103815003400300a00c0140d5080301e25500d01500401c440d4001d80c1100c02480060b03d82c10f082034030380300400c4060700700e11030000d4004070706101002c82074546010000031102c01e02d0405282c2c020900c04142181c0300940c900f4800c000140041103162580488240f0740c90f8140c4001c56690b5860020441e000d0300da41c0038080d280701c0c0030181d41c417040b8084080c004044513 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 477549235 1250 477547985 477547997
    0x3020f011b0e060706110f18040204060f050d09060609022104030e0126010303030c020f010b0112020702041805010b090c07020a090c0309120f090509011508041703130c09140601030b030106030b0115 87
    0x1002840100e0149004330ba020404680c0b42402c07890084001d421568840400400c448005d551240103441ca07580c1b260035041d80100e40390090040d0a40c1101003401040784000140c6050381300100082e0000c1c9006040c400f201f9076204110041144803441c0c3c410048002c002940c4d00d24004005065100040005002e81004c000c020b01043c0151819040141e40f1b82820146003a407001c002d41c0081d60481e03125a440740d02d061803910002e007a41c0070340d0240000107110204c000a1100320000204403200d01d4008016400059582e1211202994024000044d00400303400080d03004210002000d845001c42e4022000029440b480080c01e4203819a2030303040e51591001403200d403000c2801031020043c5030000101c00c0902c501c98250340903014501041c40080c5209003a440d561055441000c0c0b807a540800c0710a1103030009100f4020000c0078010860861101d03030202c0c9025014105604041d1519800c030503503035094121002458100440002c0d55a65a02c0380c007002d50310306240008100 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 477550485 1250 477549235 477549277
    0x109091506060503011a090d1205090d08120705211008030d09030e2e020c0d0c0608010b03060f0103090309080312060a0501020d050a030b04140403020f011b0e060706110f 75
    0x82c0d00300544001d40c0d40500323004c0e01c0d0a1702d90385e6820b031000e0b2402004104801031004182c160340f010200280d80b4041c515165407452640c055031301c4840010708540c180036003004502a20304d11040030822246807042c0007041a12000400a0704003499840320503640300c04030741080e100d101640400da03164800c0c0c880b50781420141e400c2c00102d076146a45c20311a03007040021100c206040440c844408102c0348169054000441c00052260028078416a51820086001d00c04a80c0207038a203405450f484040f9410f40c0340ca03100050180c86a481050304040e2500c080b4402c0600070494036000c1c0c00594156604c590550b14603140040048034507500c2030001c1c1000146550010444003200411550f85a1903d01e03480419006440d220300c0c02074100e42da581d404850841051900c6005a120750702030701110844414007401e4500d005200d0101c582907101001d41d00c1d41200c40512181c0c4144c030855120040f60408800600742c0d500c02d03245010f000184541aa00c10707000506171f801c0c0c940302001141c0 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 477551735 1250 477550485 477550529
    0xc090a0e070c02130605151c092d020907020d020c060703091a040503010606030207060c08060916030905030307112a0402033304140f010909150606050301 68
    0x8681076400502142c120400d503009403c3c1101c0f0b203100c09500580c080380640d0380e1004940b42446418001803421340201c1d0410722440b1640f0880150080041c0c10b1007919415141c3c0c84540d014840b007150b03850801055071103a2440001c89042c180e80060100701ea0303280010001e5290f80c1c010007848014011056101c09a180003816201d1594060751000c040b00d041124040654641c095019002442030000140d1654240520f1014021a0360051784800c07503460480d003510070400c001c2050020740400c120403a01c6944046a010140e4081801341c024a6a000d40003010343c444050a28000001000000750700724085c00c07949850f20301100c9003030300d103000d040451201814152552002c0004030406e0751030290003868004913081000c00100200b44000c1e21441c0c42c0c2e210100e01a210340a012485141920458000c50301c0341c20310051a1030110340541d211241405400c3c140c81d030303403540c50042c0a0b03200412078108a803507008020540c0c65143c050802d8000f4411010312403c1411a50790310 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 477552985 1250 477551735 477551759
    0x5090f01051e033c0f070c06051003020a12020f031207020103090201110f06072010020708090a060e1318030806060c101b0201060501020d0c06090602030c090a 70
    0x407140c482c030141c0500004100003150744003800c0c1c03554070b4030a1140014810102c00c0b01d407100c10b542844a500c0100319070110884084024007a03603020600c4410000415000f84c1c0e9041800d070700090006840d0760343c0c03940a0000c00941c0011350482e81400000c201102d5009400c00014000c8550f180d4030b04001080568403003d080c4000701c140c4081c0000345c0154020b1f0400103049105051402d4075240e0400350301c0c501030340c91070f900c16940d03c21414010f00d0354010700c1390210090b0b8a490104044198442259900007040420700d12590000e9000d040c80300110175941c501e007000381030540c0541d441100921101601305214460480d15261580303400d62849286590002d051801d2001e24a60f101503507114801000d0a4210b0010021041c01001c203012902411904a000042101440b0100054002551008025a0314080b0700740001d03a000900e440d031514081c50411055000c0c1d25000001c1c0083c3c101c0100031600100500400d0f12a0300040c02015005507100c122040e0b48596032194 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 477554235 1250 477552985 477552997
    0x41a130f0908041a03011208181003091205191d0607030903030905040218040c11060916050603101a040305061302010320030a1112040c05010815011b0515040305090f0105 75
    0x3c4000787c26642d0005409140605400c0b0180d03666602d2502d10000400e0460142042101c00a551807882c54100424200d050310203102510b003082c10081400d080143e01c18640956005014540e21740305403010306044664a50000a0000c50b2101c06a184c007a021511070701045020402d012800302e083c0c01d10703100ba0707803048120002c0c1507420b003e0340e001d01000b4140d070242c030b408001030b80b101c1e09180c050070040c7d18000c010309401005041c0c0900110607d40005810052040300104140040c032900c0c4001036095800b040d1000f000d404000283d04030031300c01c179440201070303029a00030007a4012041018074071081c001e0300c05014680c4104040100c0c1120301e40320000034042840403418510b2151b102892116000e0856850110125018042000c0c2200c0c01c5a68100c0d44c90144465640320900e1038119135002610a030f01c8180d00b00103425030310540d0300c1401240c000c40841051010400990702011030112070342940e170409050080c0035600004080d40603003454001071980307511079401c95803 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 477555485 1250 477554235 477554249
    0x71815081e070f080c091e030c0111100e0f0604060204090507110601140a0314010506030d080f010e040201031e05010603061208030a020f040b03070f020606041a130f0908041a0301 79
    0x41d0220194200b03552449015110301107004e418012034006e610381c40c8803094035480a0300504030120100c1e0805103071070ba0a034551130400c8a41e5680ca40201c2d0f000941050f419007080c004100c4142c807505440c9020301c2c40e04401594460f44042c0020b008241d8020000e40c3c2401070240080d0b95842800d0b20800d52620a0004a5222000402c10014040000503a03070780f008000503041d550301c0d00c03001000304074000e02d06201c0e5554000d10545c0d11707081200214010349070402d0f40c8680380010303020004510510030900e104140800240442e80301e640215101012100354110781ca001c4144100101024082c0d200880d29101c40400c44443d00e01000504079408075205146640701d0015201a42061a284d1240c00f001d0001042044100340903502c80d15050391400031032209940024507041001d0441070245180c4007a1017114035a51619100c0d680b400e0b58110045000700340d000d4014500e907010000b0b16850702580e2410403030000000e10440d1082c00107212124000900e00040348000c1c400c2c08 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 477556735 1250 477555485 477555497
    0x10507020105070b09030f040801020c061f12020102010902090405061803030c09120f0a0516050a0b0405040c020a0c0f08150f060118050d0305092106071815081e07 72
    0x2404c07810000b40d010a940050300e003449026000e4181c00d4002c0c2e04900c3d40c030307500894140075046040103074a82c40360460340101505402c000c90b0310a21070080c080c0a1803580300455200659000750025907105601600301d403418a402c0c1407940d12034205440300703d5685c4040700c110070390940000640e409405011140c2d45403070405410410004100d04000405001d03c0080c181c403000180403980006003d00c0c00b13002204400c51031600d0344c0780030390001d9109180c1240c0a0006812000c2910103858081e10300050040300e171403091f0702d46814250001c1212940c1080880c0b0341c0f480700960011220340400f20707a19000258035500120500b203410011b260b03c0000054040d600c50f0100d11980325000101d8a0210380303440210300310703246014090707000c1800000c03103401c24186005d651104d038111010a06410548851458a408003d440f420030080510350081425101105405c01001350b42c0011501041d410005006001e040354140500340460301da103080100c0b140090343c41840c081e540c1e2 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 477557985 1250 477556735 477556747
    0x201140601120e070308030c0406140f04030f21120b061215010c170304120e0f060306040204120f0c05240d0b0904030e0a0801090201170402010201090f0303020306030705010507020105 81
    0x200014601c411001c2c90764070070b44c0b800002041c10071004601034010940000c2c0e5076402c018015000d5032003100c1589106904010080710a00c4120654094a0788201c0d039540501040c02d10824141c06144441d82e0580040004204140c000813442d5035500048414002c1103000420014280506d801032220451403800003400c2c007401c000b2613040e803101410040c540341c0aa4030790b0584802504011014604004180002d000c201c10500c917400b556890b00c8480c40c095040403500a03d440740c002d80c002c0601002007081c543d919016940909500f15101038000c1a6007410071851304132180c161042c000c80d6902003640d04220401c40e22012100c3c14840b001c00402d03030350f900941d202100000581d9034a03585520705980b6041c84038011402555030a0050b46400c041080c0c1050550090025030702d80450600141d030000c0340c0702012429404446500e03503ea00050b8050f10000800078584070b20644d89400b0183c1560141d0b001c1c007020350881e0b06c660340750300054620740700d0031202070b011a20074044 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 477559235 1250 477557985 477558017
    0x9080606040c050f0301150912031209060e0d020105040c090209030a031d12030c100e070311040f09030519020c0127050303040b1b0c18220b0402010201140601 70
    0x455940703401c80d49400751510002507401e161390340080c1c0088105481d0f010b04506a1640500704130f0184c150340c60078002e071540c40c9c3e0f800703090307a042c01050302002c0b40c030b5550240078003140340d000603078031101e020a6504803410313204028005c00c421030701169402000340e0b0100d80c000e10b600c03e4a08400c2c001d4010012a045914165a4400160b80e002065010704000240716200c200203050000400c1e4010b40e00c4280b1116168100744198640303959981c038019010721005800a01c42048a4209100005200407540450050107980c0d10700140141008880d00804d5400700c0209101e06940340d82c8100b03001482c0c0200c1e00c40048008840c001451070300e00d412481420401499605800c981c8039950b15035620109040d40c01c15882940f6058011910103050a2a484410302f5409030001414403500040c0001ea800302400101c2c000c0e101d200b0000a060021190442900d22603580c0c14a100c1091864801940441101c08900550030200800b100d0031160304440d01511050f1103080c50040300b981 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 477560485 1250 477559235 477559241
    0xe240a0c06090f030804140c150a09150207050a0b03090c0906181602070e01050603070809100204031b0504051b03090c130207120f0c1b0302100c060c0908060604 71
    0x21054410700d0307940e40e000340000c03042c01110300900d1007034844c91310618190034403c6000b0a071843c1c0c0140c981001050100d50340d81c3c5404a403a01407020811034482c420800c0845408490760050065100c0816120b0b440540001c0d44070300b280c0c1c2c02c4580e00c6c00a51035084441e568003007134032041e80c2c56208401187d15880e01e01000c07036200d00040c11101e80d00825441240d4107a809403080301c40440380c850f02ca10300c254140f0160f4080c2c00d0f101c1104140f9494140405c41a00c402007000b0100b150820124070104428024500c4147d01940c09645840e180c1c00e2803d100160050084200d6061a1001486080c41d0142074410030400d0314600b02c6460001c1e40a0b69540002c0c94101a80506e4030485203541e111036580003e61030207040140c650080e0324040c3c50103414141c905d401d2000041c04100403962003034000071240d510102c2c3c06400c40f40031101c8200079209400095100f03c0501c2c006c40b5056024900b981000c1c0215000d014940184000741d40d0401180549142c2e5004040060240d06042d0 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 477561735 1250 477560485 477560507
    0xd1d030f0a050a140a08060909030c030306451006050d11090613090b041418070e070201020a02070b03060d0f0c090501080f07080d090905130209070e240a 68
    0x401c02e14032080982d000c44c810b6038480c1d1040c5012608000070700189090050701036a00c822050011890100b50603040c079034a00004058500c181544000f400300c413500c9030070301803084440d92440c201ca4500c10382d8617802c20202011100d500b1141c07100280310160b8004a071000c942e05a10781e940b07054002d000400241c1510300000c1c0b03681c0410004800076448413001000f590a18552140060341040d846e00c0658008880445c803441c100740e2a4004070044451041d046042c50244448075070401c5000307420600719a014241030160b110401903050307010340042520140580c07d40c0d0320030361207008408140c007058466541001c0100340c1c80c4009100040144140b5010f203c1d208110b80d0385456440548900741c005100581241c1044100d40104000c258050300b8203802a108051010380c0c010005c05061141c0550f9540b18804070344143e6140d0308643c40c1a0b006081c03401e4a190041e00036004c12080d0f98560b00034080140210307034000070b004200480c201d144110303510f440c0100c03200b01c031000302e00307 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 477562985 1250 477561735 477561737
    0x1080c030402180a0204050102010e0c06031f0e2e06050405010c050114132904170c16050315091c020f0109060f0605090402151c020d1d030f0a050a 65
    0x344101003c42d00301c00440c0c40c8901411600580e840382094002401c0d9200004181c11359448100d51900540c0c40c0030560340d000d15224116817000854803e600c403001d0b400c1d4807001c009030a490601c40c040c1c040c0d01d0000418220713249401c00e0b0001e00c1e6101c06202000d44103150002e03205000038020381d8841d440040d0120300440022413044a81d40380307001031007000d0354504001d1810844640412440ba8443e40745980101d0748500000304483c400c04c081900204010010850754010780000720080e0b094031040304c0414100c3d11850060b03074425001c4502406114464441c004506039905000c50a0130320514101001d02482400400840a400446949801540100c1405ca50002824810a2584c0e8000c02012420460701ca00020442d64140c0020340540300c40070405c40940c03a22030280800c0c018091540e6581c0c0501084414060030243c40301000900005007410444c2c941c3d003014012000741003106488051208a1960703a116022002c08030001c180304080d00103006d5400303401c01d1589 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 477564235 1250 477562985 477562999
    0x60e07030212070306111e0d0f0510091802060f07030e0d0f030906050a020c30160b0712030c09182412021c02120f0606010c0201080c030402 62
    0x12540018842c8800002c400d259030f200000800a020703c41c0281d00308003070600b01d0076141c440f86503880721120300300b032000042d40310002a200c4c00300041e0741c1c811321523455031100801caa0301301044200751448880c41071402181c14110000052910b1400c8000c9242d40200750070f00d0402c80c0c22510000c3e0b080044190b0510085603103c5a854032101c0c410b1461510591444c06c032980e0320720703001c0c0189c1030301d070421000c129061201c0d881c0c517038002961034150782045590300c207600140010f0240c01c1c501e280460750161300035a0400c590202c000781d14800c1642541075800e1003074480e00d900d6071a018000c0003030880c040400c6440d0915010794020741c5100e24a191004200b611517003176800621502004041c180d80c1c58100301c48000c0c88072140901e0341e82c08000d01c644180fa200f0136145081c820000603100d0030040e002c0440940b510469454065409807800081a80000300280c844080c580384a407540105800218150700c039820840030326905071038202c800d84980300e0142498100600c22600524 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 477565485 1250 477564235 477564239
    0x504060c05090d1127041b050612090f120717090f090405030c2b080601090612060504182303040e04060212040c0f080714010c0215030103050a0b0114010804060e07 72
    0x172041200d00c200c494052150602410189082d03130042e001220a81111007850101740199600c65040760100090308842d805a915018940c1d801c0102ea68100c10b524442c00c0840d9008441034405031980c640600084003007804c0c5404015854440d050049074000001c2c2c41540392407034200e94035034100d405a41201c1c108000150094070b0224682003c1c140c0207441c5d140b4582e400e0905096240800152800300c3e030364107180c030002e041c010040c05070605010202e074500d508031032254070400003804004c005010200d01140c41c4010b03000e400170300b914124003610042007500d490081c1c581c421054040290b1034685024103207500303190040c004031102e680800441144020f6a0810303402640107060360447d0910f408940b110340025a446041c854200e00707002c204c038920640c0f90f4440e44400307003400d50107070109100041c1c90350b000c6102e50617102e002000100601c00006408001c6501c2003504071001d0b6201c0c40c0024044140c4032446000035000780024001481c1d6412402040c0490303003c60b500d4079 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 477566735 1250 477565485 477565519
    0x100c0219030806130903080403050d140408030106182d0306020705010b030c040c02070e09160603050a0b0d020d032d050903060a0501050d080901090f090504060c05090d11 75
    0x415140025030020b080d5605000c1d1030701d0312501c01041400c02c040c0820281c0200c0da0043c00e4441c0050000c1c1c18001c0108022900303400d503400c21114040c50140b0002c040c903152030040c0c4c0980003030080702d00041c000c49078400c3c6a100c10b403110003a140a41c0c00c04800c00f00d0316900c10318103d45180d50718080b41d8420000400107800d40040e000c081d11680000c1080c5c01c4c81000c1c10b140100ea00c850600c50340c2031412080e4941d4011400009641d501e80001c155030395501030062411041c54001e150381c21606200041060740740d4405409079903202805e000c05440c0e43d04000a03000b10100280d0f0041d521204c6800290286507000d5048400d070304d0341d451450800450703880f9403070700640f0705d40400d00001d1210010314007808000c0e401010342e2820011075043c800410142c41e140c04000b810054000741d1a50741d03a020300038000081202840ca160096107541042c0003402c01560125440c03030031310004a08407401801600c50720b48004c0c008006644041c0c48480800b207036660b166130003181c0c8200341d43d00b030 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 477567985 1250 477566735 477566773
    0x5030703060e0111160219060c110a0b070323030708070e0d05010f0b0a0b03010803040b03070e030601060c0302060f0106020d05090105070203070b1213080d020d0f0603050c040617100c02 82
    0x4040b0750981401e4034160042c410040d40324010f001c1e47d000720100901c501a00800003501c0c9a4003c40e034805c00c081404c0c00302d00404d0b40c982000c003c0060201e902020150300c4402c00c1500000722501d00c4060784038801c20841408140d401b0b10101c0e20b0341d070000b08950310540d4400207181e00103080c0b01e00f1907095140c079800c440e81007210048860702c40914851508014003520300070142d40810518640c900300b00103880e40a039000b80b24400500201044606205031064062043c004040d5503a07965034a0000d014800849412800344c02440300140d410305882c01c68a04a0b0b045802404000081d81340445050b409109261705101c0c0901111002d41c03010084000502845003031190342e9524810b918a105100518101400b0205500c00c80024008400d46e00082e5444a002d42c884070041f140f880600316200391104141d06d03240000050060006d0303201c620520a40d8100401d6071a2104900340114a85400026500845403055001c0f003d41c0074020104072072066807080c0781c10121017414 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 477569235 1250 477567985 477567997
    0xf090c130c020c0109032d0b011401090914060103050705070501060f060806060a2a14010b09101214030f030a0504030f030b03150426120a050105030703060e0111 71
    0x101030394907400440324940400c100c2c0008034003401c2010107185141e450b0050300e217800300100600000402998080e03460041840103103640210000c1a66865641d542101d80a0b0b0325281d001440c0d1181c00a41c9a48a01c18070100c010951003114881d0388940041d0050300c40541458100b0500b0080800407413000e200d6003019201011114155500c5c1c400300401f06a4044c0038a0320841c001c0210392003680c3c01002d00d20040428130005090b06684001c00580402e01000c01703002649600b2280400020640c003011007003104807100103650f204d04030f010000640500038601000403400b0460003040030080e0701e001c42c40c082c0084a180a040c503a00e00d40e20380054480c0c0000c05e403594144401c0640006400e0b0072010680f81c200400b800c45070010340d0724101c6280091044030118041020721240c003140604004045c04407004505104c0e01d030700050f50010b4001840384401c2030218050b8001405154100d5030010001c060240c1140c8030382c401020009054012996a56209299005000041c01d1 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 477570485 1250 477569235 477569269
    0x9070e09060a1a070c210b09070f060807081005030d0503360c04020a080c0c160803090a1d06060a0315181d0d1b0c0b19050a080f090c 59
    0x1132107042c140784c01c046417021504860402d110040000c1064400290740c03d1041e80c1050a070b91582e101c2d50b95607800c0925a030022890403030040e0003c01c400741c0022a90b4018003442c1d8400c0707987d655120740054003843c1d501805034140c00c404c00c0300c03001d644120301640d04240b4882422100700300c0c0e4400b4a003041c2079159070303031240c146654a500020909100325404400107a81c00e52030444070000c010b0640030020580800218013258405104000300640c004211080b10010f803581d8840e800c541d40c035082410554803401c1c10405c081401111814644010405890b09501507200c24040240c90780203560744c03408155580315050f840210f0341240e03100a001d282d8900390303c00d80414860041e10404a0500c00c02c070010003900000c0c0b0301c0090981200072a900d0100c15911424000c072880703c0240102615802d0f40d0000406c10002ca44010010441d00b004030505a081c0b0180c01e9a045c040c040407039020546000000f0703103508110420540c0b00003500c00340d031003155811001605001414603040 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 477571735 1250 477570485 477570487
    0x20d09050607140c031b0f1605030d030213060503072c090f060d020609010c080f0d0623010507080405061c1d07090903021e0309040b09070e09060a1a 66
    0x2003450741e00142c50702c82154108161501d05070441005560300c0c4a92901c6c028074080600380444c240405004030610b00e0107980a903200c1041c2d100200b03100702ca842c007480c1e11034011b0403c816003290280c401c40c0c03d0740176040e00304506145045400c1d00e16400080603502405445121030000c2210300c0810804c0807004c4030160700541e00d02d03007840340300c90000344801c0d42d4000c0b2a0600c10710313a0b0750628502010741d04031881656a007010004891803009000000e0281b200861450400c01c4250080e0106098804007000425a59440049940303200c000170901c5420400c185807403944610010404a801101050320f443c3d600e601141c1590f10100300040c038825030702e42d0070016030b40030b010b151000c1000d4480721028001001389140c48500500c03a0035603c41d0780303401c0340003054000e02094010101c2c0f030001c0c1c41c4192080356129140c1c2c1c000401903114925080345100c0d107241c0140664041e040907910564061903520510210110140c445548416240800280081510b0720241c41c4040c0714421 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 477572985 1250 477571735 477571741
    0x10e090a0b0607120f1d090f07030e030c1c0306031505060414070c020414010501020c09130f05071502010c05090d03030632030a0206070f030c050601090e0c030c010e0112020d090506 80
    0x18034003650100711030488a0b20030385e040f034107075134a403c0c0e030b90001443c40f1008a181c0b20f4001c141e00414410080304c4bc43c4c00041215142118040740102b51500c4403c1c3d00e4006010180e0118104c500034000213200840e650211200c0c4031017640107950100003d8000601740744603490b000c00001040720502d00180302100034100710b051500410840c01d03483c4554280359410400082e40b078501000c4524050191140010080b90310414801c6140350400b81c0c1d070309034004908023980c0b5030000c0d00904002883c180c180d010340c584148941102c038940c0e0360301e45081545400c2009034000f9201c2040c0c04064440c44003083c00104002449121b081c00b0807401d041c3e890380d03000030364010b018040c01c40c82500145a8000940c4401c0d0413203460a13407000010408480c2c910f000d603072a52000e0310180680c403036040041980129680504800c0c030607002181c00b10002101050740d06c0d000091041d00040003c181d000055002d00072941903200071802c05400c00030603452210488902d1a8140c440d40d1004041c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 477574235 1250 477572985 477572987
    0x41103010603060c030b180109020d0f1506020607050304030906110a0b0708090f030403380106051312030e0105031b07060204031b0308040308071a091506010e090a0b0607120f 77
    0x900c1d07140390000c0d01d81000003410000d095000440502c5030583c0309d600003545804aa80c294040e04210748461802c000402048100c3c035039000d92409150054861400841c0d400717405a000c1e44d101d1985a13542c09411420210210b0700c4e0504008074082e10320501c00740364001640c1c03181045c45400319598030080c1e80b0f003101d000c070700e82409031002802a400030401407010030405071046080300c802000f2034658515241860019a100c00b0503542800ca0b006e00225070380380c0c40742c02400180e040d48003881045480d103410303061384031b4034800040200305502405500340d40148091035000c4040c44107001303a14125481541c580d0700c140d9003101c0150740042c040c4100720303e0b41c0a0480150101501c0b03e20789045540d01c0b449403166003c00340c0861000714a075010030151100c5841000c00744e06003a4941d040c18100f42e556001900401c07140103105c480002c07040d500c1000c40700d80d0740c0c8008161440030f45640c0c0c0c181e001020101052074100804125220104518800810780380e280f56a6900032000c1c5100 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 477575485 1250 477574235 477574241
    0x10c080307021b0a0308091002030702090a0b040518100914010c022b0203041205010219030914030a0509040509010b0d1202070605090a03021009091803090b0a0c0b041103010603060c03 81
    0x7060610413003445130b041c000704900c0c005070b40500000740c4580c00915860076041c0c0c9540600e0600a5114488004021b03500c1d68903082a0f0041f40280c6090009480d00300094a01303089400c24260103901091103010703218041d4201022207801441c100c80c9401a480c0502c0c20f5500080028000d0b90000145201060800d22608466040c0410304c0d600d000710344a001792644143e00c20b05040440108014090100a60480380c04801056940604850005020303015091100040c1c9410705220003000c403062000c000c81d0007141d910340e105464a42c5100400c0700030031026010384520f40d40d80e140c1104580741e40154501c5e41d8004c1603110700074131031408007d00e044402c0c2c0002080000034403a074040b03601c982405506403603040342c03121720a0b41111404c42c1e0304c0f8004e0740515507060405001e40f510b00400950550070302c0c0070b0740e14003003010344500030180d50744034100c103a0000495244035400480c0440c00f075250464850401560b8955440d00003d00359001d64005a13100b90362090924149a0188 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 477576735 1250 477575485 477575533
    0xa0b03011d0f040209010509092b0f0e010912061103010915080d05031303030e0601171002031b0c1e0304150c0b0f0601140c280b0c0702010c08030702 66
    0x40c100d100e02e40303400e5000c520100410f100b80c0780944103100201d5034240050110481c510300901220780c281d48404006a038189904814801290990314200d6100e40b06200071800264103844100b441031500b9081d1030754402d104001d40392542d6865500903001d03001001140280000c00c0c02203030701080096030829100311a40042015484400c407008076580003001c0d81d43c00119030040c0f403550081c9060507400380810403840749a40c041d180010a8200080030003c0e20b2806040880360807000301d0b0b019004074482910f0b10b170641c0f8001c59450901200000060100b030b0241c00507600304d440300b406603a80351450120384c0e00341504082810300051101c1c0086c0851940d49103007101203610b041c0c80e50a200c040c0549904041550500040c401d640a41c495152507020102c889035600d4010ba107039070b2a08081e9160300810241c0e007100c201c030a51642000c4941d15082000c0c0302064032074803040000c6e544202c03412414452031ba4565800f141d54007001c5e41c42a030843d0090040f100000c2d40400780410f800e = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 477577985 1250 477576735 477576751
    0x241315030605181609091401051801110f1b2104080c100c030305041113020d0e0706050f0304020406030b0c0705060903130614070605040818040603020d020f0a0b03011d 74
    0x1048494421a150420141c1183d0122400003603074074071400d0850b041f40b41041c0d40a110740c2003030180402c80f8841c81d20b03a4449038500c4020000c026083e01c40b14042d10824002c1c501c0b100c820701848580e0f8614203207185203918148121068100d500e204102d10204011a07201e912030082020419440d0920003c440000110307071016580c07406d140b004d484000060300c09001c050b61803000504022182d80401c1090b41c00400803038400852111150195010f4800400610309000c03d000d81c03100002031000c107951040d02c420f0308205800c0303000505500003d01c280c1e07126880d008000089004200c025004500e100b88059964001d420410b18003900030b40343c1d007a03d500c10802c0342c4420100740441400c0d01d00c140fa01c1c42042031800c0741001140240000a0a050710f40f00138002002003810062000c0d1103240711204200341032008010031a0043d21010303402c40300c00d00d1071a0042c038003001c00d009400c3c0020040d580791615510040029002608401c000c01d11006524080c0103040d01c1046d44a160 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 477579235 1250 477577985 477577993
    0x618060b0f01121a060d020703110f030301030311070e0c04150207051e03010b030d0c03090b0f03010e0901020705070f210c05060903031c050f24131503060518 70
    0x1c0c0000b400441c64001114010b95190029140e0380b050b0504122040001401c9a880e1200d80c0e001100951100c2070840200f000025500f02241d808520310403000520006581180c1c030f5030310107451001c2c9104140c441400b8a100c0898001e10030b141c060f000e120507070001901c550a00c901103014400302410f0318155805140e04000e940da072080d0041e11001c281c040e416440a2103400b0902400f035074444958180955a042c01e2095802003034580030345e0203640c40302c80d004d5842100e51001d11860800c0c000e140c038204018802c0703075040c00b40c10ba0801d03000ca0005140903a11340350a0300f4400303190018143c1d010070307031400c101c5055805100d142c494041464402e400e8076503034030a81e20035200e10900b80907920100303443e01d8603542032041d0742030440a25028070880c0a1803600c0780082c1011540030f02e1504034500030440008100700c5c031024a000a801d024860408101003002e600c0c000c406618000740c880e0740c0e00c81c0c00c0d50b24654800055100c0c0c1c40101d09400c101650304882050522504800d80c4 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 477580485 1250 477579235 477579259
    0xe120f150f1003020f010509030709090b060108010308070f140607020708060106020c0a0e0a09080d0e0106090507020307020d02060d151401020a0b07080c130602030909181e0a0618060b 81
    0x104402e40c0100b201e41c115101001c40b030700030005031017a000d0140c00d96032600a1070000100741115800901d14141320381031080c101e40d40c040040d0780c2c601083c000642400c900b4042e07940002c9003400441007160043e03134042010300c0340740c00b01450144104d40d070f100140c102c103c007040b01242c01c20081c1d000d842c007800542030240080f03021078003580803840f424003007104090204607040103075402907800540000c0e00e140d0ba0b15482c40810003034000e81108010310740c6072190000741c004252103918041c81c2241c0c044c6180c512203408000601da15503105a90082080103a41e075001d4140c455140301e01e03410344d86004c0310380c6040003484100810103003a07810354104d800740100143c08002002d40c0143c103811b14080a84909204503d03a0007404000d086d6041c540501054081d000400f46c001100c0031514034100c0d603113880017604440c014141145503a80b000600c8004900448c450840c5007800700201c500d28911a1100e400303607518042012801e28034030718850240030660060440700345e03040d038201c15206 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 477581735 1250 477580485 477580501
    0x3050a0305220201210501030c0806130c0302040b0f120a0b01331b08070204180803011526040b070f05090111010f05150a12050304060e120f150f 64
    0x1450010b002410480310703005030810842d0001001c4d11000c165071080040c0c1d0f03141d1030a9400901c5e5801140c445100c1c8500148d079000d940e2265039000d80c4c1c004550b0500e1407460342404042c01d410715810390300c0810301d51030304d10f19221044500c0d110185803000b454407015500340700f8213100c4103030022030a69071402c0b10284d1600c0300601b1800d10164462070515802a080070072154140f5172038884d640400000910001c3c041d2141c09002035038000c035820051200406c0540c5c0c00c184046100522070402030004000c003030342028400c00382c18414104a0398583c42c400c05a1040c00041c0841c9009080ad0014003040c4640030452960202450500c0c00015032141300103405800780c03240075410003485c140303651f401b00317429000f4400c1a428004180004c2c24031083d1010150001d180301d60050f84048000a00c5807064800d80c2c0c0582c2e08500514941400c0480c21920100c100003401c4c5c112010f104948510a0f0400541c140c502030240549001801000b21603e80712025081d00505403c69050001d11 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 477582985 1250 477581735 477581791
    0x150a0c11030f090307120b07030b12070302130902120102040311010525020a031b0801110405090c090105040f0603020408010f0b09150111070905040614130321020703050a0305 77
    0x503038402c48032aa11001200300081c50b11146030030010b0080e56000f10b000812440c1c1160b1401141075403018402c002c10300c014402c04480d20300050407168810307001003016040400e00c6010110000c070b4007080c20502c1d6004503540890818a00d40c13560341c0003a041044c401c410284503014502482d0107490300e84400d40c0110302138100e07402820700610100001045603210a00e40e401980d01004028541c0d40561004603a8a441c0c890f0880c41d500307256040758941182e108690603504020208a416210030340c1b500c2003600100c0c40203040c07210070000411120b540c050b0b984000d218503900540d4a5080240300c0b8251400800f44003441d9092a460200540e55500c840d80e0080c91954565203604030003004994520000b0040003c0d13002d2140d004c80c0c080200e8000e10711903401740000348001c180c070707180b010580c09003103840300c000862117144440068801c00302c0f410590076002c0301d5041d00d550f1411000407a0300c044030031804a800042c42c0310905404d402a103510848408a43c08482a030351139101c10 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 477584235 1250 477582985 477582997
    0x2a0b0d0b012303091c020303060a06021906020f0c011103390304050a021003061e0f06200304060305040b06040504020f0f010c0501050711120a050409020a03020c150a0c1103 76
    0x401e102c04400155180c404110010f42e81c1c5032500d01450400c80042c000c4c0d100d0303000761200c5004400502c07000c6041800000c0800d1104217004641100c5030301522680300075001143c0344041e15204000203510010b007405a0b5540060100080c0d6513801c18112441c62803000703d0160715078002c2812440300c2e2650000301d84c90442c96403849140d9a50351480c0c013034237102d1140c034000c3d0b000703455003070141c652545580044e0540c0c192081014045010100d80a0016032501c5034411980c4c0300e1000b807000e00d114102801041072444980c99180c0040d0401c036040d034001d42c11020005c0c1c0d80d130303040000b40811102103a41103038050b18100541c2c00d241d0041490662081590341c0502c51a00181040b44d00c280b81c841c14460300b0200822040c100316100911015960000000314420728058800e094141030480d207c10003281c0b0f0f41d07480c281ca065070b45000b030341050300b00d10700f49a824400d2001c01d900610801c01e920140d5010a15a454a1402c41040f90080c1008100b04140c901283c1d509003800811152 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 477585485 1250 477584235 477584297
    0x201090503091302090a1e0b03041104110d110a030b060702100813150b040b1c030c080418060314031602060c0c0a081c030b0d2a0b0d0b01 61
    0x2050f4485107904040c0c890000c10a8201194443c00242c015074038040000000800038a0107a459603281401c00900081e28003404240070b412380c101c4546441c1d03004141c0421003c140900704402000703150119544e4042400d403124001443c880003543c1446966015601101d585052032120b40101c0c2240c0740341080203042c000000701207000b4014245040e040320f0b6100a03110741500c090110703080039050b9200780c10702641c07c1c045102e1003450140c0d100000e4903080101822100400d80b0101c0355400f203400d068841140070800030524403910100d40156440700071009c00e03454a03500c0c003400c408110404000311074106201d0a03090805801c03040c2091038040300c1880c1c55214036000c141c2407030104056a60300c41c00041d4001030b14100456040c40d8440506c1040c1c400b502801001e5003074960740750000340d101d0740094500e0005035103c50031a1010352846540c0486102c1c00e009011600300c20703000041c03010030105801c4400c40841c0070b070b020301450a02e450b884c40284c1000c40c1c8110694000441 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 477586735 1250 477585485 477585499
    0xc05030f19060b0705070306060504020304020907050a03150311010f182702040806010906080c01090e2511060c04120f05030c0d05120a0e031b0f0607020d020d020109050309 76
    0x40e2242040d00108080c040c0f2410b0280d0310009440c205d80e0b80c1505100466909090200000351481d1510980e4371481e0054064a9156110340c02185d45500c00c00304c4a041c5075440804590140c03542c085130001c0c611030082c814480c0010b400260030305d40328904400400c0310703200300341d488521444920b00c1101c4244024090018120004101c2c0f2100b000c41300c10b034070b03101160020310141300040c0d1504032240007200304441512030075250b0b07d0311036446405020481546003000a20560111142d0100009003841032030011188000645440800050b0018510800303d111040040c040c081c0c1000a811207240303464603003080540c0b03010036201c01414072811070690105004083c001c58000f80b40d09419100340c00302c0c0c00c0300501140c1080042c1014030b034150380020040e4550b03200b44042003001c030004604240c610303071184042d041c80b680031600c0c50046005200d007400c03041092500a441a4000c2c200c554031000c002840c2c80881e0140104580c102300e550804600044100e40150000760741071 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 477587985 1250 477586735 477586771
    0xe04020112090c05041e0510051c020f01080a140c03090c040e070501050a090e070201020d0b01030c170c0412060b01020d090312080a06260c01050703091e030b1008010c05030f 77
    0x5102200400e506c0368413800e003480e0800c05100d4070036a0080c20780344221484460355486521030052004a050000c0d08160040f406030110743c0904080d80d4030501d0402c012900c1403050120a204000a88201d00044004030034040e861030280300c4081d400105a60030001e21808031a5a41d42e025203108450611800140700c403d400c2c03041582c1c0015000000c0f001d00355040204000b4001e601400024444c0c070700e45542c1d02540e41c4030b4000e1100f050942d0341c0350144602c46010380c100400780a00340100c1d05904100004084100b28851005035002d1400004c100e00c0aa002a080098003400107041080301030b400d20000359891103985a1110901c2e00b0101717030340d42c9c5a40400070003c60300b094604440e04c61100c401180000d03003031503c100248084c0c4440c01c8200005685078051903800902185200109002e041c2c0040d054400042441641c00e4280e5030781c0d181c10840020540b40440d208001307007414030200000340101c82d508212440e10b43c0ca18500a07042d1324465101511815010561640c0 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 477589235 1250 477587985 477588011
    0x30906030b0d11030109050f0706021221060105040513020d0605040507050f070c0f030503031e13060e0102311406160f0203030a0c06050108010c090605220e04020112090c0504 77
    0x201080c2c1b582e0000844596071039204180e03071b8602403446000018450000703800b01000c0c240017a541814140210b540c3e00d2000c80007001036418004040034104042800006100c1d501e2000389022034200c0b1030016510404010785006481064000b240034034100f6090111641d80881110022003103201d2a688804651808005900b01644070b0103481c103071481e02206202c40440154001d0f03090681910340127002c4000d20f00d0b602d41c1140c1c2451040002e100180100300b2a810110500c90f0b4900010724084458004c001141c3ca144080c100342409941c0301400d400c407000d19007000c0d100032800c40580e01c2825000681318031400c122200310b100600c00c108100f10000d460a60b000d54000e081d0b945805400308000d209009900c1c040e034030b9900742000003039088030610805034500c2c115501c20070712078103081053f01e040c2c2c40584450a03210240c3c64945004041c040224040c001078404000d65003401c2c000104030700290011040b0180c40d10250b600040c0304441d0510403140d01350390104d01b00d058155 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 477590485 1250 477589235 477589241
    0xb2503050f040e07180305062a0f04150804051b040e060a051611030d0c170109090627120221070303060b130306021b0a050a030906030b0d110301 64
    0xc000c8200110104010030585518425a8030804c50381d070b45d0365a60003800e00e80100a0f9160b200140081d041100840d041140000d60010300141c0010480c00031020b00e00081c0150f2301201c10781c06600710104040c0b0480052a180e80070000017454105030743c2c14513840b001d03140c006199184a45614030046030b402c0b519560440c0480d03030000010350301e07a440c01b5180b52000e00412240c5000f048510b4000249043c0104072030510152030740002d600346910070701c40000500c0204441c00074800030b40c05000440e00c0c0540c81ca400307006d00410100d800f000300c2c5000030585940e00d0481303496031b2111440d18071400c880a58881041d402028080308400c0b10310045e418051550100040c2c2107401021501000b0b0110060006038426a0200700d13040c1e03240f10010b801d0148491145501303140c19030400c041100398010707088050018680040d10083d00030064a81103c12804a030340307410404c460b038149900030b5503071002443c5a003024040b003201d034000640242c062600040c5001220042d801098030254 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 477591735 1250 477590485 477590497
    0x1b06112404210c0201080a0e0601030f0203190c0509070e100e010519080103021c020105120901060e0106080f0606090f040f020d09050f07140612090f031903060b250305 74
    0x40840c102c21071440d0b001064040d80301d07030690100300e503034003c0b5441c11514030440425400323400107003c580e400c590750410f8010311040180d03454803d0400b071100808400300d0300c9540d140704928040c082c070710f23080900860030b0004000c01d090000c00540c84c0b031191120082d481c0740f4241031a100b1111182d02c001680c0038020322880c4640b030400f116a1000494015a019050f2402240c14144903c2000d418a6801b07581000c02800104140440d00305e441101001a4001d40300000114085465814400e4002026442203000480349000c0c0480b09030440c20003908030390b0903200ca030304e400b81c16004105840203a00425008954030002503821141940c16240d02411031032060040c8940780c10203039919414002818498000c0e0311001a04240c00d106607080080c000d0030311410b00e0b04c83e026050821400400e03480707041c0070741c094503c9840401d100600c2c18800d000c1940c5002030000740004c084880301d40085003e40410002442c80c02003004051a010444c525088215411403408482900a1f0 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 477592985 1250 477591735 477591773
    0x14010e040201032c0f0c06040317040803070321090506010b07150218031005010f050d020f04090b010609140a260f0109290f07020a1b06112404 63
    0x2e84c0b588191481364909004480c008a0103c50885990400c1c5503255451000b8180d4080000c0008100241c020840d0401d0410710040c5117050541e90003545045500107001100040c070760450740c1e01ca150042580c0641008001410401c1d07042603601c1681d240d00600642c0c41000307022400c1004c00c000041c5000940c0c18410f000c0d5144d000403007940c0503141d05150590310170701404883d09584141c40c8a202c0c100c4003c8164091454540020301c0446040c41809a80200318520005801d49850240d1611b41d4403c242c0d44503217626090004141d016203401520f113030300c0d9000b81c030b44850386c404c0004419641d0744400c440c41c8400e02c00603501c5035400e0707412010b00c901801d012000f0400065105841c801d00071b090760340000018000c0b04908411035144c16464401c400045000300d140504103a90203d25401117425441e078030384460580c0d4800a1004000c85034030340092101540c41502c800d42000640010704c40007000810b450076414986401c0c98022181d080024140300d41658101c000d9150 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 477594235 1250 477592985 477593021
    0x2060103140f0703300e0409020a03050610030c0614030c1812100f0204062111070b060f060a021b150309101d030a0305040807020319050d0314010e04020103 69
    0x140745048228200410682d400e142e0308050290428040144501c501d0340c1705954541e42c500031041000001c00d8058800e0b80c02542605022002800402c01c142c0a43c1b07126903016070117491850118001c1890b60020003c0100c107594007920841d184003900d0704540c481443c6500d5103110380c044801c842003440040e500c8544005901c901d540003240981a00c008400f092001e0504905580113a01c158030910000410031059921440b1001280d8000405080000b0424050100f60f500c602e401940003503903041d0340c150602485c2d1402e02510340300c422095aa090070700c1d41e0b030b9201a440300342003202c003c0b46c940ca020031b41c031181e601c00c9a0344d074510f074881d0710564890810031041941c07849285071800e0881e01e4003060075016880d40d0303030204602d40100019440c1c02c600c01c0c000c4000c1c04001e0012120240240418001690207000358212455414802c0010310260704103185040d00e6090802c090504c0c0c03565810340f141504981e41d045d980707080400d41c03071a196480103c00901c202000c0f5584210703 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 477595485 1250 477594235 477594239
    0x180c1e1a07080721030c050d050711240f1e04061103040309080d09180c05070c06050316080c04030605090f01050703060f0b0309030306090403050f03043002060103140f07 75
    0x1c00741300c141d0f800209180d664102c402e0098402c0c3c0807030380b9004280c0302041d418004800366500365006036500003200d1519100359044104c40c2850241c481180c400407500100840c07018504000000e640101d0410010a190400301c42102c00082d011000c901c0c4115048001800d104183d01b25018659007520595a0b91070300c1d040050030800c050184c40450700540803440c01181c8241c0703042d0151040b20345044041c07040c1c1354041004203007196500c030034003109000403004108203100b004010041a15001c0d568680300175010072000840440d00d0030700c50420705025029451000760b505030ba9004100140c40c0c0c40703582805160010184404030796609003810008c07500d07030540009049035001c0074441a082d480c0e501c072040d24041100d01c244603078001c2c00000c929103441d07610305410034044d042192070721100c0ae4401e0f240d0b5000301d8040c0c4490381450501e0782581c0c9402410b140b18a0000031101c1c041c803800340c000b0b442e401c041c80050043c500b015203590004d81d0a02203507401c4103420045580c156 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 477596735 1250 477595485 477595493
    0x1605040b0a0b0310151e121104030c03030201110c031c090b1504060b0a1b1406040b060f01090b0d0c050c010204080f0d0c0b04080c0a06180c1e1a070807 67
    0x10134902510b140040a5101102041e0080508000e00803681040c0c020701100ba010840341e0300c41aa22181e80c068891511035850350b403c000a0001d5030203a0070011110b41107003806425941c0c005c0e02e03054041e40c200090a00e005010040c0e43c09402c90f8400078504009070180080a801c0351240944101d0007174046c000c40100c0300e0b140c160040c00c00c3d10103005541e40c8800c5074002d40145039014002c40c41d00d649200520101842030001c1c0c0f48a50f20710301c200425011050300d0440300311b40450b159a050b5081c4040c074940060b5003204070000346424056141000100e6980d4041c03040d417044100c1d00c030a1080c5605020303105071384c0e2b82d01c0520000c54545580382c000e03581e109c100e00d030f0700c002c64050440328208251040140e0707000c81d500004142c955032110380e03402000c1c5c0c1c044101e5008a004517600940000d0301401a581c01900c0022465007a403414200001500c0c900ea211908081c1100f68080000207258560401c684800354048506520103221010b035100750b0704010201d417000141c4c10104 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 477597985 1250 477596735 477596761
    0xc090a15080d090b09120a050a0311030405011d0a080d050901171b0318150402120a03140a09030203060109060f12170c011d030307020f1605040b0a0b03 67
    0x514610038600001d030746410003a250340704220b0401c00104003c40030300c19070350004002d0003075400160480070201440c1c10002d0411070f80f032038201c4194000310300d45000d06a00104a0f915020024040e5180624240020304145a03e502d1014a16020000d099060307642100d510002c0c04140b080d9502200f051000801540c025280140880d070f0340c401c502004005a481c4a2040301c8210700b04620769010b003602511038100070602d14588612800041d59408140000e804204919140102038106407040009680fa00782000380c4a502804410020a074021003001200b0300150f4030a69528a001046a18420f25003010303404d403041e0000064141c2c215801902200c02c1c4085503c01940c8840e0112130040d010342c006005a00340c0c4c3d130820130000601d40282800b21140000140002409846081c0b0324404007c5403600e400200422441c1901403001028400020016040784c95164040510a40c454005e40d401207546602002c0e242d100e203010040a40346501c56203440e407030010025480 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 477599235 1250 477597985 477598001
    0x140d030305061f03240308090d17070f06270308060a050901080d030c0216051e040c12050a0c080f06040e070b030924060d0c0b0f090414040f0b04050c090a 68
    0x640313a1790800021240c074030142c04410340b07900000d0030f454070200c001002025140000280c8103c0c0c1300090103031840200c1402082c016100d90741d0f0080c844118285101220140c440c1d10100000901c060f03900712100034002c02a80b41d250400740f0b800d0300d4a0300850020304030780e044550080c0c00100040354600001520040c10f100a40d018000d005810f002244c89802c00b0686051000080e101400a458120451751600094031b510b0501c43e14014001001d07601c142c0780c9031000c621100310b1203c0c0540070b8001c4942c8080010740c140410300d4805001440807500130172100810201d400820001c0d900e41d00048100d05201c0c044589150b01c0d080100c402e94801d8410101c1441601c8001103850200c080c00404142104100c2c0340c0fa0347c6500038088000a850003c40b1601801c0c1408a08080003078040c5c41d484901488194513519840103001c2180c81e8004034a80d28080389003007100054649152030724055102c0003484141c1c903180780092034403000b4809254404450010052041ca181d40113200d = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 477600485 1250 477599235 477599261
    0x5160c081e01061a04060f120f050601030c03180611120414060106140406081b130906080f030a1b06050c09130c2003040b0409020c0601140d030305061f03 68
    0x4142c0c4c0c2c4000b503184400414003098000070040c8800c00c05d00b40601d6020000e903100f4140f201c240200050b48204580f50700c0b0550707004030769070003d0101950303052148654440d024141000040b5142010043d0007203440d10041041d6103031480c040032030184d0410384044044408500c800c5040600d0030113104544004410340705e06c1000300026101340302c4d821980d00c400c02d0305001c6140c242803103011501030301e00500c1d04400e46846c0441c4d44409584000038020302c0748400c60303220310500b4a00c0e0303941910342d1a441001c4590003401004204040030040300c0140c0c2171030414900c1a0050500740815004c0c00b580071341454501340400036020540760080a0318002203606041e540001c50907038007200c00030189100010b0100b4060296810009c5c0c1503289a13044c40110f0342810b40d01d288c003544035072090f0400d80304548c000c90f0a0580380010440f060240c0b0710705002100c50181071002c01e0380070040940213404c06880b440410400e44500c1c1c01c13900075075aa0030503001c0e00340c01410080c01404181400c20 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 477601735 1250 477600485 477600491
    0xa03020405130b0a14042d080d0f020903030f0304020a030b0a05070f05160206030c040305190302010b120607030f06030f030e0108060a0311060d060b0d0605010801120305160c081e01 80
    0xa040301136a00c29820710026040c1e03034a13070301d4860b03443c2c0329003049030f1494250212041050080d200c0300c405540804076071182c0001e9a42c0e04a0b4a0900c059030741d4100180b4806005200008032170b6000b1007aa1091640316401c142c0360b0b9201c2c0000351004c210f583c0040e20043e411000e01011202e1034104038483d103643d4441030394400d05140d04890600c1400c41107015144002d000c2001032400c9001180c000c1081515642016201e0f25181d05061204001d044650400c0818a003016020f0113261900e030303004c544602240d0081c416258070b800c40184420308240e42c4004030103444115034001d001650300300d80c01207268815850b01070400c051980960303003c5501d003000601c051814a1424050703d5208001c010180050310602006410010020101c030352120380110b072108802000e82400400307503c3c00700e0013915060015150400607003001304100f981403070100c0880e400c13404071609605406c0030002401c1a6041484448000340c0145400340200e481514980c144651240b125072a894020 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 477602985 1250 477601735 477601741
    0x1a180108060904020103050408091008100806010e070e041b052d040e040c03050d051c062106060f1707151e02010e06070f0e010903200a03020405130b 66
    0x1034800e14012109558400b44610020340117500c240c10882d0403600c10845581400c0c0c40c0000900c801c3d500d44040d4002680301001c10030041d05503c8802e001b0942d0344054200d65051140315030aa010043c1114140145a11440d0742625140c1c0000441c0e90802524a800410711100a0076503200d1400000b5404141c2850303000030102e0203c000344005c1c0344140e503280514040030340f004400700400039220380800e90340003c0810002d00c4924194102c0e99251540d0b103200c0d11705803001c084c110141400c601d2070201c1c1800300314440941059410050a180c2e6480b0320f05203007040291080303030405401181003072000a00ea00d0005110715403896001d00395051980c54450462050750351031b00d01000520351807e4080c0403000300d22000c40582141c800800c234001200f080e9440d221055a1420000c1e070a248a100815881841e1501602c401d10302411520301d50340b106020007128190200d03081c40c403041c03140056900c200c892401140c1c090824001c40c030f00003801850b06840c0d0001a0b841280403000 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 477604235 1250 477602985 477602987
    0x90702011a010c0f02060a02030c0d05030103020d140a2001020708010908070206090a0e19050f0f041203020c0a050a0c270b01030e06161808120904061a1801 69
    0x7007450000c0c035012481c400329034a0004452054441200350744102048a40c680503031103400050001d07880f541c00469990428080f114a040380c4d40d11480100031042c001800141d0340c0d481140c0740503411998039448101d1821400d410081c4078107004100301c00f0004001d22044500340488080d8009030261b80520382e881f18603d0981d4404a801800100104000d00041c03070848090508004080c04c40507035140c40f9802d404003180240c030000420a0707000c002c0c203140015402a142c1c400203800d011340d410300300807010184000c1c02400003000b0303103c1d02490071031071486030307064a44c4550748004545001c00343d41405a02c942c46080151501407009002240c900200d410205664540800041420fa4600741101c018003c81c2c03405810191611803072520700c20100b140c50f0040c1803403100004a507045040c050204c29409400a005c5202a0401c05c90502d0208015110008003814140da41c3c241c41d001800070001d0341c201b12484009021118200a95003010340b40554800c1c2442c038002000c100 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 477605485 1250 477604235 477604241
    0x30207060309030e04050414070303020a1560090c02121305090708090f1f0902040e030412030e0406030213020c07051e04361e06060509070201 63
    0x15024011071211305442c070481c01c01c1c0d40110342c004d014100c00d003881000000014100303d001e60050300141e000401d09400d01510500c17510100c413002104100c0910b048110311a07510b0142e48054681010075450f1b1614480030380c0703010510070001603107007038543c0810740a000f0043c610b15101e900c160880000c02d1920541c400c4c0000840590002c0203008002e00c421103055222020781020600e8583c0c0020341d6803180a802030040e525519825098980056000e10303100308400404265449001c0804141c180520020b4102da440080401c10301c1c16400454040c4c00e0901c0c2c0380c410b51000060000380714405240400d03059202e0f50781c0352505a085403c00065501900003c0d42c003880a803a09214a03040b58000d010098901007030300c0c0c174a03980300001010012120b281604e1080c1c0b000007601c0a10303007403240000441c4003240c1d090203004030541c0c140404491088800394004040c4142c0c003884071f20402010741480200c62681c4440031441c0c40d00251085100d0030b4000c0703145030b0100b0040c60040c0 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 477606735 1250 477605485 477605501
    0x606020c0d0515070801210b070e1903111206070813061b0203041814060d02030a0b0c18010503060108070503060a0918020f06070803040204020f0d0504050601030302070603 76
    0xa401850034052a40421101205480c1d0031686849a0715550300200f03e85a0700c07603c1440d103038a8103013403503140900720904861081c00c1001035081c2c0c031041400140d00307640e0450f04500207281003203503050508049110b015650112200d11503034074000108120852140030308400080d9950040413204182e0155102d6080d200480424424800181d46021140c0c0104815001d0b80d00030030f582c40404400610f8580c044040c60044e0000202800035040c8051300704160030b017a0108002816200c68032024414001c3d2800e0310a401d5507819001790341e010400e04483c0340d00004000c100d400d200e200400340da4461040c003490b0f2a540c0003243d055602400035a445242c06031201c044a07550304808803600c0e0300c01005254480c4d500c203804180c100c120310030050b0490800c0058109000140100f0900820230504548154020881c3c9800100400b05803900316506860258841c03041d40c1c13460015008181e0542112440d140400c001d10400060080c1240d000380c003517410302a11880c04030180c440d07030 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 477607985 1250 477606735 477606737
    0x1410061706060607020604031b0519080a021203071a01080c060307051204020109120c0e060303040b040303030b010c060f09150b011b05391c0308040c270e010606 71
    0x4003001035a00e0800034018040c2e188001c1100b8036050326a59000c5901c4800b11527480f100000c098280075504110ba43c0305103e0080855a800c007525000c901540c1d22130355000240607a00761020104500d000b00180c0e0301c031550000662440b031a10b50700d00701c807a0740e0910511364107204415984c00c243c01c200080300c1c060001503842500d014100c11400e0b01d48036020308124100103140000040c0903006480040c850383c86500458182450000b5900720000d01030720051003604100010005e40000f9000c85003103c0d07050401144c00a16240142c600003041e01c8090711207414200d41410400d89a8088075400c3d1080c403426200340200002901142d0720316840764042000340f242d2074803003060f1001102d061841001204d000d8801c031004c0c516100c5038210f07501c2c00c00107060a10556102ca0030000100700b0810703100031b05144c102d0990b080c02403602e000042c050000544c045400c3c03044448072a40640111101440841d400faa695410650030100352007140e460090300c100320a1060244408079586 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 477609235 1250 477607985 477607993
    0x1104060503012c090109030e1f0c05100513020306070311030c090d0812070906021903120e0d120b0603040b04021c05100b0a0510020d030f02040314100617 68
    0x2001c4003200e02c00c02c8002c11008150b104000040303401c8092107107a104e410f40c9400452000400d00c5d020388488031407401d2901c540c40703186d0381403009070030a0340c1d51011040b245003643d42c0d041c0600784941002030340e5541e800041d0802c400c116405400f081680d1044e4406d5003260415a5140e40480c11a0842520080b5922041020681403030b40440038026114004003038070000d5145030f451703110682c0880f0300300c12401d80000412020390340082055000744402d0015011010314500150008241d4580050a000441c0c2410115540079440400c4601008013101d1041e5098803001d0440c40210544581c01802c101201000c0e04003141928050303603100c500303050300380c66642c200b128482c4401e0010880301e600e100140081501080201c04160200f440050210300302d006100560050b40c00207409041d46142440d0146d60006054014100c2c51034005000200344606c0c00180c859075201901c4040051008981c00c480810078120203007001e4010022995961440082c28002410302542600 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 477610485 1250 477609235 477609239
    0x11706011a040f2c040f080a031b020114091f0b0114030c0703030b0607021309031101110405032b0507020105040f03080d1410060e04060306060b03070201110406050301 74
    0x81001c034424590381c00c500905040d102c1c8040303001422141d2100300030800044220307030608801c0e50103000c0d400b160fa01018140c40d0a88581c03100805460000700301803800504da500315486544230b441c80c0111243e0103900c03004001c1000f40600b5508420305000030300348002c255100e10000b1000f0340d0440440300803071090048205033005020915005040c40300300300310515960845001144242461603207103445180e103090080403220101c003200e010301410800c600c007594442202c1032864a000b074011810021341d2400310385500c4040308045e441d44c00d1400140c040c00080c1c0c00340c0142d50701607040f529140103480c051045c501c4504c00602035030f28040c2c550940701d84074030000c0031481e00604010f4582907070380346d00480100c8540d0050b145401c0106110032203000034000e22102d0080d003100a0158141402c08980000caa80305400c240004003841c00c28644942c0c018900664020404125055984000c01c6441e8412910107005529240c4000c9220b8040025101075491079500c86055078 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 477611735 1250 477610485 477610499
    0x40302010b10020c0d1104020301030f05060702010203040b04023307350c030f2808040b0112060e0307060c020f03071511130602030a0e0301020f0a0516210801170601 73
    0x1400c842d00360340070007503030f14007051ba41c946000660003148162182c01d4803603e6400c140782000c5000e80500116401001440b0108242c010341c26000707134046a10007090546160300070311441c0c09079480d00d240442c41501d00f044440751703000303006250700808001c01d464214042e141414203e10903966162046611001542c0c02ca070000f414214002c1c2044038901840007141c250140c10010f60822001c0c84d40c00b04041e960a0000220140000f90511041c0c509007a6038005030a5014081c48000754501c0810305d0602085400c00c0035a8450a416640c1c3c440071410b00c00040c140c454040ea01500c1242c4e142d12800100004407200a50011025a00c640d444010f50019101c0751145e907000580901c107084d40032445000c50b0004180c03540042da03880c002c64034050800c4145070b0059112782d00c1480325802190080044410081c01c5107040c5580b00020b24145d2004141c0303e201402c0031400d0003070300700e0421180c0004641c104990f120040f039682d035400301e90080741001c02e181c43c503a080302c1d00402c400 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 477612985 1250 477611735 477611749
    0x1140a03080a0e2710081b0603091203041b0806070503070c0f02060315030c01030b011d010c0b0f0105040f054308041406060a140a090f05040302010b10020c 69
    0x7080060450146203402500104111340044600c1001520725080c04100032900120070000c09054000e0401040520202031210311a0820f131ba0013804004002030414506000d1250070b41d02c02400107889003480d050250398500400310340e0301910001d081c003041c410340c00144a4440c00455035224075590710344d02c0031511441407500032203401855040042c01a960600070794414600000250000140e400c1050300e00381c042d07c50a0f0605141218261003642e203c007442003154070305071008044120200040392449081c0f0b01c0680151903000503c1130030022070900c24100c0310104d40911450304210002d40c11654113852600314404500e41c030f01c243c480c8a172004030341308030152169140d480d042421440c011807401c41c0080042d801c0010041041002681040c140341940000d069510344040802c0840503140503190307000c050b1481d0740f035003a6609900c07000905031104050000c99004050b0401a141c151000c070059400c0032078031140d5003403030b0903401c00b51505603009001c8064403001344502 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 477614235 1250 477612985 477613007
    0xf0203030403021806090609090a060e03070f0c06020709050118051f09060608010f0e18010b040f050121150207020111011d2e0e16090501140a03080a 66
    0x40c0414040080541d81c0d141308a440c1c1440400101c81601d001010001c050000411051150145805002000d84001041203016500c658002108040141c9480c5980603114000302020082440e030810021310f010601c1c01c42d20f03180c00304c4105036160248407003916400d00510300300c0700c1500c03201400550a41c103c2504086c2d1206408500d0f0598403200645441c142c001e6030459403100b104005241e13224146030300402800c403540d48150704201c480c447c02d03000540b84504205a006503560310710000c4d4020f00b640d900c000c000b00981c00c100316400015000034410f01c1050144d0822108028025500d05011943e1044070340c1171954413084004000c2d00840004d038100104440c11818601091080d640a811661030810a580d01c0d0b1260528041c0208c0010146201003030030f03c000f21f43c080f0140c107039222910f040459848683da80c5146403034070b1804615181c203024840040d0642055000702d0523640750000741c2c0080440c903024421164601d1000a01800d81080180140c5110345e8140316 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 477615485 1250 477614235 477614239
    0xe18040501090302070e132012030c0f010b030d200105070e130c0f0813020301050a1b0512010605070f0602030a0606020c0a180f0603140303060301060909050309090a020c010207052a0d0f02 83
    0x1c105c0b408030020030351240e90645827030200d40c00010a078845170020800d0a442c030782000024004001982c011030303140d06905004109100d044940d1002c1c2100450119008121a000810140c035201c400140f21300007098815009001e40d004035500e110f11402241800081070f1620400030b40c60880803200c82c0030040c11410464a80040c240050382e080c003e8030300440c15100081082580100307600000701402c0c00100074403008000c8414080c200b01036090465505041081d140c1c42c19046c035403003904100d100200010300c00002c10100d001264000c6d01510000ea00b2a0a00340928007807101035202e03801501344583e240c6d4001c1540c007149402485040d445d6034804035010741d4a0740c40d1348160b40500c07074030030150300040104500360a00b440740c0d90040c00a80d405029064035910b42039264494104254024109840001c0308140c1c0d680442d00000200310003159200710f5810601c3e00ca1102600400000e11101182103a552013800c02882050f8018100b01412030941c0e2580d01181400d40c080b0317 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 477616735 1250 477615485 477615533
    0x71404060c0b180706020a110d0f260a0314070203131a0d050108061f03080a0503072304031b080601051c06051905100303020d0e18040501090302070e13 67
    0x4025a0320130311440d0000e000c1500140301180d018602174090b0740d803440c15140601e8030024000042508144078600c0d00d0303000024615009848a007880e9481e0030a4a6414038010024002210703031ba1560050b80020050b00340c030407490f01c40c018100d8503407090290f0300c2d603852081780f003c1c4030400c0c002645055a801800030300c1c2c5005801d9210a05440c801d80c0001c406801034003c1160b2210701c0d00660603540000c60340f6074600c90460361064690b0056148030010440b0100003da02107019061344400e40540420301200c42000c3c540c0145968090f01044800041d150f1401c01c8000800c41d156080e80e083c50050921a0701b414240810210541c100411014050383c0102c0881c1d201d10070540103003640244070142d14120b00022090701d801811021103c0d1080104101080d03021440143d1032080e450700d4803400700f03203a00250b500039129040115154150080c0300c100403056012401c103502c02d0b004c0c0c404840d5034411400c09140c04a0320400c000c6041c10b030f4580011000f400e111042d01c8100010 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 477617985 1250 477616735 477616771
    0xf0a052109090106030b090c040e0a02180a0f1403030306030d18090f1a010f0905090a02090612062806081b030405070501030b0d082205120303071404060c0b 69
    0x44000d0030a9001c02d000c05d076100c013050361b9414403000c0558882c2e13540b01e411703242c2032500c0920308214000410651800d40c1c04a0302e003e4004180355030101c65400113160707516041d00d404501000ca0814410007000501014184184e400c01200703030b03441107a00402416142d26441420340300c85e03000110012070540075a101003281000e500c55001c02c0100c40d14001a4600b81003000c06520490041c0030303040c4120043d104101c1d5901003005410745000369004102620b4840040c4081c0c05005985903009030089501c000901445d5985031142c01c040341c4010100e001070300841c114051140082c400481d998200740002030042c4091a0010409059013160621500b80001c42e0b420a83d41103405c1e4020031400c0100350ba15001c1c003d01040c080340c9440d042110350b9100389103841003800c140c02841010500d291991840e064800080c580504400c035130981101080b038681c2c6c001c862f90740120300d02c0020500140b40031001e4a083d11410f485402c007001e49038440c82c03042d4100510070541242c0403101 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 477619235 1250 477617985 477617989
    0x6071e020307121118060d06060807030b0a15030b0c070305160302030c0d02010b0d150b150d0606030b090403031d1c08060d03090314030f13080f0a052109 68
    0x41d080105581452101e811495141407440900300101e070920a51400301c102003e19051758916421140031582c602c2e0b002c54900e06080030704155401480c1a0144140000910600340500c40c80307502c50b00380c200305801170f10340c0c581c418a01c28000a00142c100100089000203100000e24400340039043c16420240e02101c0000c0420b10741030100d0058002241308080c19008110300300401500c0e00081c440e9280c544081010a1b644920107008621042020581c2030307080c0e400003400c0c81c805000040d546420310307207002807984220001c4914618084000490324482d1240c4c8800d01c40052801040391203548040b80070b495610346944014a4104482d50086020480c0c4480b244060711428070039015903201800d079800042c40e184c0141000c01000380081d42c4100c85400392a484010f1803807483ca58039070703180b4601424400082c0c900002403420080f112284680c0d041b10f40c03000440c0e4840f1400507000b9103540f6059002041ea42c031812041984000000360000240a1201800d08014401c00 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 477620485 1250 477619235 477619243
    0x201080c040f030f02030d03291201060906031502040311040e031c0c0201060807240207180207020a05011704140c041805011104030c030b06010905040c02070e1506071e0203 76
    0x1108403044c1c40000d150504506090086442c100074a090400c907108a0201501032000c84544002c0310b05034080000500340e0b2604103840380031855000800c00300d6100c140380030040c0600d000030340b481c0d503042c5a0355441200a0003101c050700d9010800a81162840c024400503243c9100c0d045540e000c2844403415100000a500240700550003011035a40c40b40140030342101d48540007058160441002440030311074500450642c0318400008000e40b00d54010103d0801d0101d410943d00d0003940d0345083c0304c0480a4000d01202d900032030340103001a907a14011355030302c0f268040502c3c803500300a00007000704214085a05600080c8800d072480c0b03d420600242c2119014442540d001c1c180030103100500c80240f140100307915040c500e0301e00d820b065440e450400c0059102c010000c112041c00520242d00c070302410001020013030b03c01c1c400030024050103500c40d202d9000d00c5c10700c001c010300020002e001142c84d60b0b04140d00030b003080c1e11b01405521600c000d090421000e00050f0402140781c001030324200 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 477621735 1250 477620485 477620489
    0x50712080103030905030c09011404021b030a0305010608220821090d030c0c080c070e01090e010f020a0f08043f1716020c100314010f0b070201080c040f 67
    0xe62018203660640c5070281071a42180c010714000d07804082c0c00d038007585540c082075040d03d4011050000465070000000c01030f20900c582c0801e000422100716100c81c6000020b820225841c0e14240003903a2611021100030100700c0e0b0b54400c0501f01042412484000a05584942d019564080c9480401002c0383e11071840107000c800c8080c0040100205804203000c09111400545402e000e0300c10002c02c000e10610036010f001d030150074002a1058800401c102c01c1009040c0c80600440300c1d84c0da4040403006100054030100154201102429458500e2003110740c10301c015181d0740c03000d90b41000c0441c5c0c0400d008104551045101c40000c4545034030750148400c00c0d106940b8a11002c1c0d000601c3c00c070707040c8140003880500c5108580212081c000c4100260f1102d0ba00071044054480d160040740fa2130502400c8541200c21501c5113030045516400006e01d040c1d010f61400035599840c440140824164442c503c4950701c1407000300e00540c81000c4e000c3c2c02c024880c902c9400c0c2600c03022090301d240b500d5 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 477622985 1250 477621735 477621737
    0xf080a0c0602040f170d05030105130609060b1902120d201303150603080904020c1c0e030f120f09060d0e07050406050d2d391d0601050712 61
    0x110008100d000c0000d6454210a58803001401b85440e01010140ca14041070003111300c20004280d513040030600c0395101e0002060450418415165601c00107c8661f11480103400142c2c0c0c0b188400c440b242c00040c5a00c0041c1030307590302510740152107400d90010035104100394a2203104100c0005a1000032014092070a90000241a0b4a14500d080021407185404500300305007800c4c000c10106020205446072600700f99400350382c0707000d84035289061181055100b400100f00a20100c0b80603489050f602e18203105500710740310303240001c007115070300d420400d501c00700c04000700b20301030800d8041c0c0064888418060996414020300600b005c2c02da8014445110703066210034030800c114609070082c200206800d43341803101916076191688422250b8810101942400c0350f0340e8014856504900c085640081c84180510501d400800030140f0b810150304040441e68400c00000174010202e00c100c808006a0003070000c10106518501800104200c0c1804420300043c00441c481c1c40e461500c441c05 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 477624235 1250 477622985 477623009
    0x507140f1906110d0804080d0e101406061c09020102070515070317130b0603031b03030f0109020f0304120c0b01031406070e030c090a1d060103060b0d0f080a0c060204 73
    0x10a5402050b1001004443c040d540c0b144e203140506503004100207030001e40060546594980700b4085601500c0082c2d18608640302d10109541090032a80c4002e41c0c4a00c0040c134400603803528402c000c1c480c0180d40e40070445060140c02d918070300e12158844102c042c4107006035240e10b0380e030300c0002d0070b4204501e070440c10b60100041c0c0f280c01c2680c032524040500003140c030301c030b03a0038202404c20252001d003902c0b00a0005a10001058407a0360400503103140540750342054185d40715880c44140c40b60425500180181c2c0c4060010540ca0501d000750b91180070845c0b10a4155600d40d101c0d201c030100c0703174051002400b00106021000c9448001710344c2c081c6016194803070300201028a0949400c2000749140104840050706184d940c1d4041440c10f1912000c8842c2c40e0706031500c0c4640b0005041c100304d6809244c1e501c4074088003040000c2104c604a901440007007120002a50030300482c192407103c001c0801c8020341b00c41c070000354104090106042503290826482d19181e640300202c0c0d015801201076101 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 477625485 1250 477624235 477624239
    0xc0503090601090c0f030c17100e15060306091b0708040608060a06021c020f0d0c050601060c110d031b031107091b030e100618060b03040507140f19 65
    0x5003002810b006120f402c0040019203a0008000c140703440c0c91072440304041e210302851440c6c5102303807143c1e0200078007418264498100f80c800c110090000e40301c1c040d41c10301504009000401024581003014030043c4c02545990b0301c400c20080c01400043c0042c03402c00040042440001c144000fa003850752090300c240340e54605080b405000a4030040040d41300340c8180c0001d04c01c5da58082500600b00d40c0c50804100c0349110000c040e1f0900c0340018183c00b15109500c01104001e5101d417840340a103000b80c05844540c2d8a6010899045081900143c02200b5420109200c0e041c42d000440c06203000303140484002c00d23005513882a10104120503000103800c150319080380d1a05004030001007804200802c502c2e50b0310395056001d4030025a01c40c0a1699030354043c0071241f401d103e1164800ba141804000c55030300d4000160007401126501c0300070614008002c40c1011041c000c603401140c01c14005d040031883d200070308524010307690710950445030000c142d02d40e81d00c0e41080d0b030080106051000c40c0e568 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 477626735 1250 477625485 477625501
    0x304030b061807021b01020f10050718031106030a230603010f0e0712082a0106060509011b0606090903050c0f03030f070509060f0408030d0e030c071214010c0503 71
    0x400070680280e1044021050046543c0c00143d8000c420f08940c950170f003108141e50040c0d041c40a0800b090035507000d0740c0d08d442d074002c2d6141d11051245505442d4443ca10f0b65071034440030b43c03804901009200003007408401c0410b181c0803002e15403048150401141030420789080000780341c1000b80c00c0742c400b0314074000d005c403900c0c0030301400100446c00c6d0310400401313080004d5260b65401501c124803104181c2d80d492700501ca8490122602d981c10b00d5241c0032120017070043d11000e0044100011855480c003400030038031610810454510f08016560481072aa590312511810401002c084070320540d649400140700c4c1c4c00d80907074004140240c45035a100d100c02d034041410000c01e1107200e20b20350400c004000c00c1d04603c215151700b10308a03180464a070081ca10100e0028414401e242da001d001c007150001d103412000004100c00640382109100780051541040e81e40e00030303440c1802c0c8941000c0820302000d140c3e030402880b4a40600681d0030400065103c803801c41c2d590200703c10005400004000e081 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 477627985 1250 477626735 477626749
    0x1c020109020a1e03020409140102030705030f22062f0405011202160308090309042c011a040f060b07030e190b07032f061006020715030213080304030b06 67
    0x4250040b0001c410040b50b02103d540c8960901009201e01d50714102501030082c218602c50380e05482030003c5660781460840036004c1d1308215244000b610001d0002000f2204e801a41d80d0004043c07034000d01103d603903603980c40127415101e480c101042030700311040d61003804070403009a0b070809032000590740b00d090100040a454412440c4140c06004018a58444181c40e4842d584143c00d8078140391281c842d60380090851282d0000301ea0702c90704058040c041d000042e01e000d80c0704500c1000014032605040f036130134283c80400742a01841a06c0c0c11080b0703c503041c140c0000c04206100c210020b2f506440d01c6262980b0f404c450b100303030005000812641e4590800b449001e10048010103002d05031440c010582d4a03034890104014204820008039458010b04804040d64041100e5114251f00c100703603003410390300c0000b150200e0446005110010340c01c0e00214401b820b81c2ea034442001c50b1450041002e1740039521481128114a00200e00050709402c180003402c003a41c0b29549074502810514200031803 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 477629235 1250 477627985 477627989
    0x3030e151e0105100e01020703080c0304150c15150504050a0b0901060504030c03031805040509010911040c090e060604030b1f0b030903030402010806030c06040b0d06120c0603020c1c020109020a 85
    0x5107000c20070041c4090f5451910002e00c007441032503c84a909801c000403030409000e540700030004030012900c4000031001201400968102d841c0851400740c0590080f50300800205000e00302c001c10035401002c00c610303900f00742880c03e074910326001081c0e60f88003c00d003203c0c0100d80011540d40c7da06507503412442d11400e02401400c0303510f0301905007070a5403a440441905031100405001c81740d1056090740c4800b00d0f800d002488014400c000342d1600c28100313400b0f00424401100d2403000301c0014501403500b0f124020703400507541c0d1240744183c105401c0c004410405414942c0c170010030301002002442100c5620320504a0705808543c20340c000f40100c818500580003c032159000380100009010b00000f500c0d40b0030b0302441c01104a40b64080400c0c1000c0310030355050b4018100280125852aa50005285a58170f6a10420a940e80c0d412928005c1b420640c00601502a002c2e00300300711842074024049540c1c0380c4050340c4031001010845019140c142c100c96003d42d450b21044d9065240000510300 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 477630485 1250 477629235 477629281
    0x11107050c0315090304090b0409060204031a0615040302090a09020409050d090f1d070c02090a1401090c0207121e12021c0e040e010f0203150909010b06030a0903030e15 74
    0xf0508181928984034021b5015441d8100e0362000006c800c1d5030303150041094281c209108650b070f41d85070300700442c44c0000c07030362039520b403845000200d520303810f20301d520000c20319104142e1400c00e811603081040207107000e040c00e0410750b22043c11402503500da200d04c90381540b14034000c00110784d440d50f0140810555030700c0310300f100892040810510301594400000c980403282e80c03c20f56034419800399a2003102c603070045e40140b0b44508019440145900ca0324040722117a44a440d00c2e03a89848502c1510904069400142c020500802c01c010500c680506400e106d20101b4216284e0540c445403407454884040d40c01d0100340308420f2601c7c0c1c0600c01080000a40200c080402d150104c02519598004004500807a601e2045411040c4298850612095004010b66485c02d00074900001c440420380403900c83c0480c100840c0700840144030701c8035048000362049042d1307903a80402c4030040500c000c2c1a000d140e2030b00580030600d5800d10948014424412a0b20b4050a01740050300c1e0b02610441005 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 477631735 1250 477630485 477630523
    0xe09010504050c042c030d0b0a08070302090402061207120e032b02130e0714070506010515090d0b090105070e0303041206060e090304091b0c060509011107050c03 71
    0xc0b0710081100611010143d802294145508000c8240300640e00c80d0f6250490341c555004802d24404802409003000e040c00600122075400100844403000d880340711000c2e0301c600030400050800000080e4014001888142044a11451003160300302c03c94180000070103010f00842c40c01018411540002490307001513080400e60503041c0100341164030809040c1980003902d05416600f901101d41c2c0a4a51106045e082c0d035500240800b0072040e544007021441d00d0400d00f00c1d080f00e01080e525110341000040086074038020078001030b16420f00d0201d8850004024001407030700d442c01d420000764886e0b1082e80c807601c1c114107400d08440c000b603d04020801c41e0040a00150b81c000103503029281d10310406404206a440e000e4002c014940c40440500030a40030050303080c1c40840548221407030f420041c1314101c099400000c00810241c055400700384003c48600100700c60384c2c40a0f5202d25130311f00001ea100000c20280c01a60040141100d0385d5114071003400107820244020084194102140 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 477632985 1250 477631735 477631741
    0x51003050c010309050309040f050411030102250204020912060f0109060602030a08060a0e040c03122c030a0506010f05120d02030f0a090e040605011409190c02010609060b03010e090105 81
    0x200d9221035000354440d04141c1ca4030600b6090110510888417854002001000401c100e400b8540c0500030849058800d003461a0954843d420b040c000c880100c005800c0b2103000215080c0170b851a80385a80081e40c00030f5003803100d0b100645800b500340540900d0b24008004916001c9100303c07030140b050300040d828074103001040209035000401d030f40045402c0d0404000540e21000480c181128941c4001402da05d1301051106210a48040300c040c1d03400346040503d8820448020b4441d00c9841c0e401c5080d580712905021150601c0e0804404e5121000781581c9221031781c1e8407400d18242c02030b0441c81901600a408111620300340c050121403240c10405010b0740c00341100c0103900c0e801a5500741c540f403800000d200420314800c1654034090003594455801070704050400c2801070509010343d0300b04d2030191410105910700803090b24403814424040702c2c0c0c9000000c0d20301000c0c00030b41d00d49509544d290040441c60280c1c90060101410b980d8010640b6503150501045022001500300a840d034982014 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 477634235 1250 477632985 477632993
    0x16031d0f0109090b0103021306050c19050606061b160807050a050310050c070f030f08090a0b0c250f0203070506031003060c140307020604050d0504050603160c1a040303051003 77
    0x108508603500c2110000f44e00920f4030041e0082e10803104a070034110040c50000c039110313420102411904041d14211480f003403100d9031040a85604c0d0301e02a080703910160004030a0314000e0010400300c4144000c20f40040d83c201d00c040e00e00032901802c840c0c02900c0c205e042c0151b01c41042402c0051008440e4094000c0c64440400e4540711035050142070700e503c4000154510501350115181d0b541d115041081e18499421b0040200700c4410050b4009440400402c10110700000c03103580c0f55030040c2451500d80c49184040d40e00c1c3c0d1080708049000c1c80c110440b444569038910401322940d000742c070800b41c14103181c130415041c0862600308a1241205200707110219070740b03004010a4942c401300015500044070303015500009407010311401d9410000c1003101440d030214a07140030380d12490441e0360a080d00e503c2502c0340c0c062070088540094080c03000a08020404d22600c880704020305020000c007160f13440da240d254009804000100c0a0803051108059051103515440441050303440c070038901310340e9 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 477635485 1250 477634235 477634247
    0x21203010e07170415051003030519020c040c020a141f0f1401030807060b030c0d0b040606170331030f03020c04050a0e01050c0f040302120316031d0f01 67
    0x201c44104a1540002e91054011102c04903000e00e00c159820032031401e4070301825002071102005030040d003000d0109441014150022096a500d074803481d00b001481500c20140c400300300603002c1103203d041c50811a0ba2994442c91981150a9029000144a038109012040c2e40201d0000165116606281600b10709441c580340b500990000880c0d4040c0c03c00d1801d02801e81d2083c2109000d017504000010005c08200602c0518807a175000d07c2403400c950105503c031080c0010080c1c101540c1501c5400080c8400640350744103104603c0003540b00d071070b8100303800c0c0079030070006150040e070000500c0f1200c0c8401d0001c0210313089515222700007510351059618925a030a200042810f00f00a0001007014004d1207403a0011030050400c2040d441c190000a000d005e2000045003154a070201041c91000054122141860700360940d502e803610395824045030b1054007014031550302090100000754480f5024030140c460280c0d07181000c90201d804200701071410003c0191043d4a080c81105059801c95 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 477636735 1250 477635485 477635489
    0x5010b1e1215010e01180b01020606060c0304120609030813121419030f0606050301030f0b070203040e040c050103230f090c0316060f090b1921051602120301 69
    0x9101c220305180c9001c5502d2400c096115034240c400c904000124071070341c08007603190407107460f400807900c4080f503050014100c1d01c007001807a005800c5640012a90301317001000780010840c860480e8a440d545604030354184041c88021241c103510345011100349a80285a0f030b4010314401d468905100003561100b610016280c2c044080c8600c001e6411248101c50064424030081c039034042103620008040200101042e40364010740618000300880d440740300b1401d590503030b94000203081d6002c416071500098900014405011440100070200750140c10800d2140079a110700d0600315818142000501550000582c41d1050107042c0e00c2200d42641b04000140c01c121440d0190016481e514030707290030280d181c168079415201d080140c51405145404103c2112116510040e442659240c120784802c3e40303101c0c00d00c040c401448840c160745070b040080c02080740300d070402040c000304034450044500f42480d0304a1035141e807001009502000142c03011142d003001d102500009041c540c0c0342c192400f043c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 477637985 1250 477636735 477636739
    0x10608040f0f0f030f02060c0a120e0f0703240c050306040b03010e0a0302100c05030c0f090a030b010b03072007060c050717060a0f02120619090c03020705010b1e 71
    0x3100500d8240210880480b5000d50880c00c10301400a0608019145c030720a16080e02c0180720703110005203034401e00000da8060101a03030b80e8905400348010404083c1031a1140e42100b4040c100340d8980e002c4080004000944c8100c0c0d00d00e000f45038805041c0780c044880003810090a050a00307005082d54400300712684000d040b1741c0081d605000e040400e00416400312485003d10a008440d018903030000307000b02c642c0f01c21490512800158880c101c030380780420b44055210040501075800d0300c072240006002030385c90290401000540e00d84600d080010207902101e803d090000602111030b52155071000304034070340906c2201782c6a1540503665a0a013902c00e650402c07400c41c0307050080000c00c0c84054000c11517808039a01d1050384455030350322200c2c2560140480c618044600c4903603061030013170b41c01d202002034419246903140b4007803180a00404822102c1d4603140d04000c100f094080c8610952255603940058444d9110318042d030131104000c00c007500ca02d62140a640d242d2904180740c0440c1202 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 477639235 1250 477637985 477638003
    0x5040c050a0503101710050631020913020705010b010207140409050f0d0315060e01020714031906050601120624020a35030f0105040b0105130b0d0506060301060804 72
    0xe01072480b1149050364018032421880c2840607100d249001a0301d203101b4006e80c004004c0394480c1c5040081e07000c10400c040c0c0b0140c1505404420441d0032684044201c403034400c0151600d500c00c0002400001e00381804134019501040700740610a0912400403640030030f00080661078206403403507045200a401880c4140d80341d0303c64904000003408074030035031407001e0216680c1f5000c400d0060701070401b002c254040b400c0e80c4c54001a069201308245070b84010180c014292007820000441001041344049a03018070a41a06549c104c1e101c0c03603c09815030140400003002e0621000060400d0072000d150343d055400c0240501040d01641e4148004142040e090040ca42c50585c0580c20408980b46c041e000310131a042d002c40d4a01070411001040400012170036030550300c180c1c030322113601040d20180c6544000340010b0246040036444601594014100301d400c00c0d2041e001889001c5641c0c02401030f558000c00c50f40d0302125280241908500c040340e0140c11981001002041c0080060010306545a = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 477640485 1250 477639235 477639241
    0x70f0908010b0f2803060f0b091e0a0e0613060605040915090f08030103080403020a1d070309020a0b04060216050301090308160509042a0915050702041407110705040c050a0503 77
    0x840200c0755441c3c00c103403080c0184d0280d038030b0070400300070310b40c032141842c20b241040c964144e1f0f1f1405103807441c460048139154840300c0700102078244003114000e210b1050705a0701e00070201d43c4c900070881640304503d40000c648101d00140390903800d440c540e80c031190140d41401c08040c00610b03c01100302643c4041c000006084466081804d00e1454980003d032080d040040080300b48884440284240ca0094074041d0300c0329a103210058059070602062502442c901000c02c0c0454800d030010581e040c00101a8101e2036103071031003104294090344c85000036a218500710505015101100c00c010f0000f00c00070080300d010b5403000b9201440050180314030704043c0d480c070404680280103450f030115024000300070311f8400252209031501007640d00100c400038041c00607002407180498000345c46902c25540b000300c28020003541e064009800803640151141a94000050aa040184101c070287d42d804441411010103506241c41a000303507000d2824902602c1d00304d5086003c90703c40100ca4a0410b90b02e03a = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 477641735 1250 477640485 477640519
    0xc01180b18040615081e010b0c070509070f0318122304141c052814071a0f03010e06030c040608010b13051e04030c0b070f0908010b0f 59
    0x86041041d0a5000b8034004010600e0041d2901c55000c8015039105e01405031201d418420307000b10f40300040004078960500512851030404c000d800d10001d0f00c0c04403240661208001a0700e040221103190018041c244a2004103501d4000c100c05508090b6102c480c0c0e00c0c0383d8580a400180883c41c6c8414080400e80a0880a002000c0090070b091000f8010341c641d07440301d01d40341c00d04011001d140c0c400ca0403510307491030700340309040003a0b4540e038040010041d620ba58501000150429402d407590701019078081800b280c455200700010004a2018103a03003818150300240600d00c840b01170300c0b40381c420b000e850030303141c40c0c1c900720781c103440c8c0401401105644140000c0e10b0101000710194100341040e400003a540300c150000d0b6800c000407207a1008031004000781c80115401200c82d00d08001d0f021984240030000741040c0d0350031a01a113447c0303041e812251a00c0d4069603003074a403c0002074a42003400301c00e070b91040c1d000000d803140e60024020380f4035079000122440c1c41001407038824000031745c81c04200 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 477642985 1250 477641735 477641767
    0x30f070c0f08040906060f02030c0a1502041d010627060818010914100b01050d0b0406080d020a0203010c261801062606161b0c0909050c01180b 63
    0x855120b182103950750380b61544100504064031071040401c108040d0031010900100a0703e100b03065080007880d0100b078030303101ea0101042c2c1c950501d103600e81c200b1000c1007069135580f002030740140c1c0e0300710002654900100240340001e400041e100e124078a04025206940c2c3d030466800701c3ea802d14cc81c203542d4541000d18110540ba0030401840da602c0e2020307290402034841300321507250303100100381c46070300d26221303003010540344007083c0c0900144040054143d001800d0780071281d4014050400180c694540031088e180c00245526440580d01506590341185024058240c20340c1040c90804507007144d54403100400d80451845c04030400304040040c450700d400e0b000d221500c0c02010000d00c40240d65003000344094554900c040051445425101b9140d20005180e80c0912070801d203006070950762000071205044000d107800207a1423812950800306180c2e0b40d6647c06041c20f078900040040381c40c608140307080c90760003210b41885000c0e18040504a43d42101104445266012903aa404250b2182c0e0003 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 477644235 1250 477642985 477643013
    0x705031e0702101a0909211305030f060a0f090c050603150a1409060306041e030e06030f0613050103032307050f03070512040807061409040f0f0b06030f070c 69
    0xe1510b40808000f004c0d00000c48502c0a800c2519060081d48030b40003107544079016250f01c410711110310001c02d0300b40041000103110402450021a03106a01c8100080c1804031441d560f00c1660300010502c03d48444510656010311000601000500d019661b4548070050901c0b40c244106c0002c00010007208003410a20100d08009081c07803803254950340f00c52080c040d05940c4500402045000034258140001c07124001c0e908007580c0024901c8203140d041c0a1801c43e0011020042c03810011030340c2b604e41038081c0d030140120102d11440c40c81c1070b2050104017800c0b41c2c04001d40314103020040002c00e4102c0384401d0710030380c0b280d60748011420015500e4200d1264540040040c030881c80240b0109801001928115100740c05039403c00140ca500c030406401139004070070941d041400204016401010310b030a40d08600340302c8038240150000020b0494041c1d5440d10012900c80d44884407007211441005070604040303910a0460078508400204808020422028820343c130362010140700d040000810703 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 477645485 1250 477644235 477644263
    0x105150901122a020307050a1113051504230403050d02160b04170c06010501081305190c050406060507020d0804030f0302030702030c0103050402010507061e0204030303140705031e0702 81
    0x1103500c071001c29842e50194100000d000b000a801982030f9078404402c0310a900d401100802e038003406030b1900d104800c2d0a6a034140d202c11100a2544c4040507401041c1c880c40d030448510038050010700c2488240c43c0307192242014040240b0140090720540103e96410070f415151482c0c4070688820130900910a41c55038803604219036039a00c04005007661103d10541c81601c541c0c56006611007000790901814050140e03035004100144050351040c16010b510008101100030404600d0710703183d0400501c800f450084a400100742414030140c00341c0c5800502c001d480070848140b41810081c0301e070180410007840b400d0740781d04640030f10111a007a2409035420074801410b41c8107501d40070359a603110620490003400340b402c41080544c000d1080a1240780c06071a06494031341c443e5200c500030b05c4149084031242a41140a08402c01d4a10140001c0e42c442e8500003450802c008070305001040042203001008000c00810004403510f00c001c23241810010a07201c11a01c50b580182d0070840e085003421 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 477646735 1250 477645485 477645491
    0x3010e010e0a05010b090c12041e030c0b0705040602100b0a03140607090b0a0503060d0f120f0206010906120f050c15180d17160807050102040f090203010515090112 72
    0x40c0d841c0c000480c45400e060720a10082000d03125980601000300350071510404241002d2128003a05980660640c1d88140704501c5121010b030b9440143d00f450301c2254003607000803000842030003000300241c145a0002c1042c100181400e1074190001d55801031aa1046a03460312500620780750b0310303020081c80146a01c1005820219254000302e0f98908044903a140054811980050f0f038000400860384c0170900340d62504d03d10742e5010305001c03002401e20307001ca6000740100303800404984280849142c000060307a45040740074108000034503101c3c0c180c000c11200c500d07000d8100b1902c1525000c005800d9880380542558004608000c0e007051001c100c5250042903405505901c04a50341c001c1c140b50108203009500b101c158001d100c9079224544004190302052aa0041c1440b0000003508403419806241c07000e140703040e50381412a40244500300c070682c0d008201030168038054110795000e060509011403c542c0350200007080c1c58500100340175010400a094809a41f254150b83c1034646000028 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 477647985 1250 477646735 477646751
    0x203030316080705090f010507150509030a12140f0403090b0a020601030c081b01080903040506040b090a060c030c03030c0306051c060e1f0b030f0d03020c011407051803010e01 77
    0x40d1034079100c04681100242c0301000003801a0700460554800041c050302070012020b1050040d18168056003055410400700001c00201c0c1301640909403081c03800344d01a5460700c80a040140181c40c100c04031014031424210818500c012030142c2c180c2c0700ba4a4061032010752211705007602c626507140c110900c0482e000901080e8030740c00184003412680f1460000c0c0e8810f54603810f0a031215204a00d4030b05507901c00c01808082d40c891014942c101e208101907a24190343c640028515034041c1e03010550700d040200d10b5442514252000c05c00800c01c0381080d90707420840b07960062590801a030001d09244c0d8138038a0b088072900c00d40c010000b900000e4030011502c4600c2990800907070b07034000304a0f8601c2c10001441c40c80c0e0004100a5409003281029400b981c0c05850104050300d0a802166010b01c5403034840d00b00700404000100341919991070041e55070210505007401c1d150034400d0201c10508000070310043c0c0354814116620f07102e188488621a01e00072000a01410910000540075030a200704 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 477649235 1250 477647985 477648001
    0x70c020a1d161b11030f070e0606191404030b01080a20370b040807080c090a0506031518150412120b09010308030a0f09050d030c0c02030303 62
    0x12080611800010200c0360303a9101c24020441c0a61607080e070001d0064020032400d0b650b40740f142001c452198103080024165040807901d07081e00c0c141e0344541944000300400001002910050f0050001e81c0c81c0c41c90858644c9451500c4401404040108003c11105600f402c02d0b420586014540c000c9066505507903520000d581d6082c0ca82d8155582c40f048005840c002c10107991242c0c0c0c070040a8441003180f0b00c2161000140603450b840e81e0340342d01e005040100d20070b829464040190000340ba216840c1e500301315103640340140ea80c10241080e807002135401455a00e034544c042e40450310740340104d003550351500868113001002e03486403036040c40b22050200c10144030aa04280d40848030807a81030207200025a00c45040a40c0d0140104554660790442d40d03101c0c40101c92180110a03020580150100104034040826030055031010780c080103000c100981806510349030904a00c06002128043d2034203078a03204070710421011300d941d07040070201c018095121080070640040940e5103901d04181 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 477650485 1250 477649235 477649259
    0xd1809050f04060c0806030705130914060717010807030204050a0e010914010c1e03050c040f0306090317040201080f09150f01051c052e02160b070c020315070c020a 72
    0x740c22143c00d81404c02c410081841800705c0c074801c06004005019192808003070228650b005070708500035688a840c0100031030b41002d2201c01d403c100000401a070b1800000040c60f0701c003600081c42e50f02d004500108482040001d40c00c0a59070121400106134aa40c0b06100c02040144207419440d42480038040c03d026041d000321000c04000781c024440707900b9075007080312804c40c0d18140d03c0b01c50180400d400c2c031440c0b080c1c1c003880e0b11403a1103002e1840d00b91144501e2048a580703900c00c9501c2c54440540404240d4041106952180303082407002160034a580064940400100840c404145a0000a8680508218401044000c5d01480d04a82460040c01c001200c0c24001d0501801a07604110742454a03050b043c0c0d039981c0c1080c041c00c0c3c001c1d246030402c2031000301030b044d90601440380c45920324201c1d07140c401040c000c101c050030506400da9a00c2e01a65022004240409012a5520800160f1404180e18803070324800500151a541c900c14282d07042540c8806c045d4010482d4200445d4240111b6 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 477651735 1250 477650485 477650491
    0x408100605040b04090506040f050307020a24050a050a11010f1a03011a0310200408100f0b030316050102040e04120306081902090414030c010c110f0d1809050f 70
    0x1a81c180107400024080c1310656081c801c0042031940810005000300b2099145000300d03030b2040054a1070021150001071281080313800841a14100c01c0100401d0071440c0285d09002c81c250800605200001d080540710303002c1d8410380c606000109400c001c80a20a6101c13041241008200300f000512503c442030b84994041c148600039860710181d00c800901540d82500b0744100107004294503a548038944000d40490b41450410410f4007884130103d0500c00d01030700150040e1001000381900c40d094807002c1d10340b0030499a01c03051502142c2c003c0e0761004000c450100c458001201c90341e0b00c00d40f078440e0081c426907011185000c3c90405100800c4003070034580e840c1342c2c40c507035040c80210f440d000203984404185130700e03c100c070300c02507404030041c1400c03610f1690140c050758450320810700c03508807a421580008000381c2603940d00c20310842121f400c078820002c0c42403c032004101d170b981d0062a5030f54440c03c0000c504d050100d0480c0e648920703844040d4200c007a110050f41400541010000e90940001c15 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 477652985 1250 477651735 477651739
    0x339071a130215041a070510050a0207060b090114040c02120a050a0906020d0e0d050f010e07060212040e01032a030302070302040f0b180a110309061e041a07050408100605 75
    0x1080506505907003041520152001c241002c2c4080c0c45ca41c800140e0f41e032082c0021035079409101000c00716250b1a1113410b2050140e00f0001d690b921492820b2411149031a5003035100b2101d5200511005400d09044400c1d024142c0700018007401c80e0005a00d800701c00204602d070f414000400301d03a4150301c0000307440301703450700c0c0c441c0d82e40d044e200c1e0400e0341c807188043c0340080010820b150f590810b10300341c9014804c00340501d040d564500c05409040b03003524000034440700f0703940c0141801c014a80e410428266074018442085040038140004003d40880600c40903003600d0701022240920213603410b181c403000000c003c0741d007420b6a0300e14019490340303241c4c40141e01c83c0b4540301032f004501c0554003810104c0d220040c000c40f1410b050b0001005140310152090300c0040d6030b40c15626641d45110025409055044020b010a142211260742c0c00c01400700c0d842c0108215509000000b0b07160555522102118001400659510708044603240503d52007501c0c144504540c2201484076a44458251201 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 477654235 1250 477652985 477652999
    0x70e010819050108101d1902150a030e0d0203040e0609091203040f031b02060a0c05070902040308040314010b091506090a0303120501080d1704170406050339071a1302 73
    0x213070300340740300103a240e0031650002c0703407c1340e49051985000202440c42c4c99200401e0189059104001c2012580043c441040481e0b9940d41441ca4490304106201c0c00a404e44021450720b420440301c0034000714050301060141d8585804100f4074030080c84100202403003283d03010b40303a203000d0501842e90305601c401540410307220082400e0190941030301c0c6d140940c015108a240456600c0304172042010313090155880e0050440100c1c00504600042c4021802658040c0d161410744c00c01400c003080495581446d80c1c50030810040075218981c5459000076400c0c4411440c00c1c040020176081c0c82003451042d4010380d40403010040581152a241e0340922484007003000703a0304d50120399030b511a1034035100e010480390320102480b001031808107680b191042d0201001c8003a030498100068200381c0180d40400c90100c100801c0550301d103c000700c00055125081c6400c0420020040c0300c1480301a45018500c000030b1040511000740c10b03003115640a00011190b620b40851500038018100d00200e1027824 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 477655485 1250 477654235 477654251
    0x1406070e030d1b0309050604080f011b2010051e070908120d3e040506090603070c02030a052508030409150801051e060405070e01081905010810 63
    0x14000390045007884241c8a4880010f0000c203078004008a02d01c088003045864080441c2070780f00c080162008089040c01002c0d0b6111a0803920700b510029080764011709510206c000320f0300d5000e2601440350008000f100e1600d6549107509042070199185c0002d09401c003800d1001c4021540108540e908000303100c0103c0f03450b040400c48004900344214120b6074010143d408000d02d0300002080114200d00c3d000481c18885040e41c80c03c01d0040401c0843c20466003601011000755013000192600711032030103803803d41884005540c602036810b02e2801010007000051419000e1040c0c024600d4008044442c03051442c50520350f00c40d1081d40e00d803000c03205442c070f12421499959512081d0f8101c0c00c0514145030802c0d040d80024001c0c80300d00703001c0206508c000070b418007084c42024010324162190a134500500352000b400201c015100d0740c021894842044605644460f002d122a40c09180c8011140c80d40c01d29501181404041811211302c3c3c07400000307180c200050810f1020020300024400d0380 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 477656735 1250 477655485 477655489
    0x18060503060d030e030f0a0b0106090503061003060b1c060b1f0e0d050a020607030302091504120201200f0102091905031b03030708030c0306011e0c030e0a031406070e 73
    0x201040d00c03240d802258002c100700000303010746106000c00c40003901302c0301c9140390401d245140400c00b10303042d1340003c82800103001ca26030248104001c4d200582c0103242509010121010700c080303904c4042c004603520707003004803c0c0d030312050554100f580c40c202003120000303242481001041100c0300d091290b4440e601222039038064241004402906448a005192000003804850031100344102c9150040740c40101c010f941d1700c0040c0c07207410301030f40d00162510300c0d020512075400380500c185000e0352020b0200300461f440e2076a00d00f004603030a207040c02c08403a80300310203011400003440b50001ca0080f0361070348406002c1540a0f00c0c4078001103c108020400c3c00341c0070210007515000752134051f04204074007590700042e81c61440e1954800f40840c1e00d001043c1e100d60311140c0069500000d0540008103000b078540e885800c44058406c2006519148030306828098550a149c1100606001c40c11104401513552a141c01005541003650710510030780110303260703843d07075000c8810704007042c0810f032122814 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 477657985 1250 477656735 477656737
    0x601020d0e0f12150a06060503040b0a0b210a03120207020609101b060605280911071704051503090d080901094809020703020f06010303180605 63
    0x80c19250325424448040380060145a180c2103400780d401ca030030400c40405144040013074130300d09104d0b0818000203080c810408802e8545030340c0300d0420480144240400f0500407940a81c02100300840014180c1daa4004500510b00401d442c9a02c4060100ca21207481c60203d61514020311a036a6061482041c142d003400300d0203054006508550240804006c0382429400403812000c3c0742401402071031701e00d01030a0a450b02c0c650807a0801d48030035080000d0300300210015031280440404034100101d0126460b20090107205e426209620351550301d001444074003c4648264004030001a040580d0204240f25880791094074001c80f0304000851003500140142c0e406540b0407409444101c550301002c0350705c42d101400740c401d50355032418100f001031019858507003040c2c01c03001d942102e0200370421100520319108108090b904141c00c400400611040f00300985604520058480e0354a0408a107080c5105404010301d2182e00008000e2603008400c103440119401d051380011034841c0400c80355 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 477659235 1250 477657985 477658003
    0x204080c0d0809061c0f06050906330903010f060806060a0305070303030207060209031b0423010509070207231c03210f11090a12050303010905072d0206060102 70
    0x165081c04090110300d8280010404c880092510841408810302240106c81020038040c0849a51760707000c11081c100000015070254088844151041c0e00503080d032001c0301070303a000c840a05c003100b44403520300245000f661038103000903000704144449144c50100800070350140c5940c0d80301d120005040c0340b13803003103110b0b081c0e0341c0c030101a00c171892843e40c09030b029420100044400301e400b8804541c19440421441194400707104010303440c186480c0c103100c1110020780c101203a503602da03014003055505d004e41071411200c050355000b12607501c00354103c1c2803a54036007004038140600c01c66902e030820440070307510345080101c89800da4455070110310810305070000d1000b8045207400080c081006a444c00c3c02e0400b403000300010980340c03246060002201c0709458442110400400c500c0d2241c1001002c1e080038098581c81c180c0c5c40a003a4803056600c0c00705124204005849074001451288030300a212840c1c004212141e05102014950024011010f42c3e4400148501c40019541d90f100003070304a4 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 477660485 1250 477659235 477659243
    0x9060c0304030f2d03020909010f0506090f0f090108061f060806090a0b060f071412030103021009272d0e1c05030105090c04060813051903030204080c0d 67
    0xc0c541112000581d0090319544c4082d10152081400c554203902021007141041400d540c0147e441158804020398480103070410008140a10000d0055450b204d040f545240c0303084400d11000b10203c800074141c4071000c416250414101e100024440b2000603042d8050502c4502e49a184151418890f40c3c6226a01c54000000c40400102c1d565042501d81e0b035401880105002c1141018030000c0341d090784c020040c940d02d082c40091418280031031002607003400b51443e40507212001d4140c11565142c001804003902c02c03142d083c907000c0d4080c014250007005011002001c070040103145161180040c0031088007918038203103624400144032003140c80034018009044e60b010301124019500c01000100110340c414407502d6070b007a0105881c5401c4000300c584c20b03600e90340e4a6050038103026811401500c1594031000c1808103015280c0c00007000d5510904081c48100d4840260902308c1ca0f01100340c0b141c00300c012104e610304c014180d00d80c00400503120358004030380081c10a84140040d60f445000050 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 477661735 1250 477660485 477660497
    0x2060c0d1109030604032309090a021309150302040e0c03070303180f260a051504060908160b1008100e070f0602011e05010b030f072609060c030403 65
    0x241540c201a0300150048001004050400c01c0b61008640b038540241c0341940441e030b9111688126159a681101455107055405420031040401140174010041c2c40c800109401040103e20100140f90f500d005108210061184401450440411810f03900043e07020302d06107a20300000141c0005c200c0040c51001e002401a280303151402c54021050580d906500c40103407800040c150701c10304080b4081e007204980050010b074210308500184140c8009080d940d0800f400b440c000c1200801d0380000d14003e054021174560300c40c80c00000800440800901200f00851801e020300303102c2c46204072082c400c004c5444039446d03005c82d84106407801e1040b5072040d4021101101417440680082035400c4403481180d10303a03612105051034801180c1c00000040c1c0d5180001c03540600b070071030320007660005410100701c154101907001c04980310081c40030070008080741c0810015407140c261350055107414410302101d80610035641c0540c05064aa91099104200100c1c4013002c500c4200d07070185905403114 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 477662985 1250 477661735 477661747
    0x9020f010e060f0c06090606010f020d14120f07110c0f0607062003040c090b010e0d030216270e150403030e0d0305250e0d02040b181602060c 62
    0x4503010107420401d950820390900140e4010300c641400f80107591000e00180c95580340550304a813810f600200014104650305940130351f52a008603035040030758854030b0203072107004044a1950701441801d40004480040c00308211883d08080d80060003001c450380c90720601035204403080d030b0f92640804816840f40a41d484040b042c0f0b0140018482203100301004200403994103580380d6180d030101c00b07071113015200000b00001c00003011504006420fa200c0c04100e902c400c040020b0490202e08200c5000f044695101804c2c18004c0007a011088010300c1c545d00c00a80f92102100210781d001e1110000e5019000103401024681c0240e20003100400e00a0210040d80406e0700480c002c0548264140350307a0341840c00003d03205102403d00f046071914040f81c3e40c1001154013501124524448012181c1d07070075080282980000c2128018100701e8800c0200c07165800020001c1c56800342480d800814008100440a01054414030400e07860101004850b21140c00341d880d044100c40c00f6803030080070098 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 477664235 1250 477662985 477662987
    0x8030301060309030c05060405150a2304050f0d05041403010207050c09180102040e0402090106080610050f09130b151602130b130603171606051302220c0309020f01 72
    0x480359140c4c0c06880c020002585941380c1e181494020b4070b055a444c2c000e070f20020404030540d02c12980200c0403040801030140101c001c04001241c200e00d0400481e0304a02150a21501b009141c8455140200b80c172040c50001102819640c4540f092110790b00c2810040742da149018800e44040e990004040c080c03407483c4808010422800a25680304e00c0700072304240c0100d020901c003a00140c00203003112900b80c01c05004200307500405a0010b010482d9007420803032961201c0140d050701701d0b041d04002d9120203000340014014010a01c5c1c5541082da03801c2c0e00620320341682c10485400302c00703171000c0407542c58a06542e410352081411101900503100b00e0350006040030040340007111500307540000e1203543d10b00054405c0c00008104c078485602d8641c20f00c00e02141d5404070f0b200c581007400311858030f045d010440031030116500010340f002c0c0e036034000180540000344034008600c3d401041aa81204c03040c801c0c043d00d071440b0030100c0303510b0700e0940c540c5005c0d4000d03c00c90400e103800514000c000201440 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 477665485 1250 477664235 477664241
    0x60a021902120703030503061804081c230610080708070c02030c06040b030f010506190c02030109121107060201020711040902030109061503030e090609040b0c04031211060a06080303010603 83
    0x24080b40c200366410035a03008040c0500041c806148240d4919a80e0b09001080281001410110b0211011007400b440005449441200d6504100043c0c042c0c031003074442800c40c010400c01c0203102c440d8080c40c50308030304243c43e8840244518001c807621a11040c04140841d00684215031607000b04240700082000e40c1d0041207442c0705184018200c0b042c0000c4180401d0694000e0350141c245080003000380280c00c10440c061501600040d03030400d08010b200009614110340c41e04401d800c0c080c03a40b04241c1992420b40156807815007080311252282c0718041c0c0280b00d0448180101c450b8090800085040ba1040c000c442d403884c1c20015a841483e001c004010017000c0001c0120391640d62614840001481405655414900f10010401003461400c014101072600712489105400f100300b0092075558402003039030001d4001e601110701d5510744410300b14038402c2c1d0708058050942e82c119061003075444078401c00f00b5040e000070b903201ca40b180c40742d17001502c1e03041c0a000e413507810600061042d00d220f40c3c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 477666735 1250 477665485 477665533
    0x8100f1a0403120908010b03010b0310021612050702010f03060b0a03230705040f08010513240e0328020709020d0f06030605100b0309030301060e01140c1b060a02 71
    0x140d00203203455529518103400154402c0b2000c041603601070200182d41c428400c4119080342a4000d1201a08000019440b1a4911043e01d101a8007044903e1078000f18100c1004407a4000450340e00b840d80110003420036000404124001900504800c0b4080d03c03078080d210441d00810082401c0c10f9807120103501410401d000c64042400c1034a803420020380c40c080c560300541c42901c805075036500b00700c18a04440119000104580c1c1400b081c0202c0043c16044503030b41c2504000300c0500807038020b50903121111003841d8940050708051440c00d8408001c0014140034100c030f00c2c5049200c44036680100005c0043e803032400541c1044008205000c81c070780040c691440030801c00039000107a003502c01d0032104070341c0080c3d481c2c6949008010013814401c1c61500582458098242545040f00f403c980d684014013803c0100041d100c0c0c204030f964020007088070900c3d10000751300d44030414250394940d40c0c2800e03102c490000b12008825241d07810900e08481001c8074603409092410080411f60341040000 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 477667985 1250 477666735 477666779
    0x3070b0706020a05070f030c20030a06090503040e07120606080411040b0103110a1701080609071a0f0d020304050c0f03070e0c0904150608100b03010608062206030308100f 75
    0x1700000c40004000002d2958082d104e61601100600f4078200f0705d40b00c40011003840841c203100b410702380c8181e07000180030081d80d5000c000444c0c00c03142454001e0460140c1e81c010641041640c040c40085500290702d4440640350307440420a45542f09802c0b2500c440545010700682549201080d0030300341500600c5031441c1c181004115106004042000f5901c4580030000082e1401c0c5041071800000113190b0041051000030140c40c00c2072600c1c180c1710485842043c001400c851020b401c0c40110101f0342d0f0f440002414802c1c0c40f81048501c2c50007039801220111000c0c0581a44401d442c501041c0c032480211018009088541c24006041c80c1c0d20805040401d11070003d10a540c0c1554841c02250180c501301004003c101e440c214014000300c1c40a0456249070341d0b1003070184a6504103c0a40c0e04598a40c036200749952079a0000c61100146c42450a1032401829445603902400d6000a01120b00ca595800499901d04018420317800c103034010000c170189024410020104007180000c0325201d0 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 477669235 1250 477667985 477667987
    0xf060e0d09080d0212090d02180c0a0315030302060f07030609061401120603080301050409210f180501080408031906090501050109094a011e02210c070f05030409050603070b0706020a05 81
    0x2504580000707000f021a1002b00c0d80c0800102984840c0d414000c0e803031085034104042408138216034021b5141d01c40102450b09030318407040015065440b070307041a00100366150080010984a840c414890481001010701007940041000e07028100c5104403c00c6a8019a40d103081d41d0070b000070400600b803012419240c1c884440d84010592402103621000701102c2c3e02e6140e0718030400ca40161041404c0c0d801101140b0075114100300740d903000304d4020340c0540d200d1006580c17a511074044500d10102010780f00040703440c0680c042182c05403548014165a426218002c0080c2c0d1070b021002a140c121824100c440810305044000c0c01540d00b034840c40c0e2203100392046c400010034603c078040a10301004442103a4503902d0880741842c912920109000c44024250300e4082d4450034041c124800b00d010b656a075501c94002900d0000807825143c02c030354000b500b584004100d040c051307525007190042d03460903450000451a10701e000a2200d0031200d0380007001d41071a000d0740f641402500000c17944414800 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 477670485 1250 477669235 477669259
    0xe010c08120108010b1507030525050615030703020a03020f03030f18011d0906150f1314010c03140310050907171f030f060e0d09080d0212090d02 64
    0x3580e0140c803000a0319407994146600d030a4000d802d45004900643c01060310000c00f4261030100c0046406181c0c050600c82d0755a10040083c40610ba8018003010511450b06414003c105c0702082d854055101c07408009003080000b4100341e11280c040c84001d5105030084420001402c02c1d0622051000009065a0030300400381c84201c92680203030743e80b1140500010b4014415a0414404001000c0c0e90350050504c1e0100400704114207030113000c10780b083c09085204805a9007950071110640f84201d07001d91541c658032080e0023440880d0103414500b03032001c4d6002c100ca52081070030316074442d010341d5a40e241d00c502005100b030716800130b8201000d001084e02e0114007510350449603401260565210307201c031482c0c003400243c00d9501074910b00401940600525503442c02040040a4981010194001001e40c0c0b41c010300900c080d052503042030280c20014004141c0240c501001c8641c0c16043e40d1020a007580704a071109140c0001c0d480e0801d00b0302202205003084009210b20500c040c0c01c90701144 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 477671735 1250 477670485 477670493
    0xc0f0b1209120c030a080a0b1c0c03120507061d0a080307050f04170c0d0c0501050d090516030b0907080715300e06040f062708040f080c0d030e010c 65
    0x351040d0f001d81103e600009140e40c0050b03015420035031050b04940100942c0b03540c60005608800c006802e2008d211001d080c003410b100c070405800d0021a8031403d032444031144500040c203950068501a2401072801c0c40c00d4103515200100e021090a505c009000490307030998441e402504050069402c0040900a903c9828008070003040a881440c1d800c5190120502d8a40d15020a68400c54080d07a00c90900c0070001d00101803840584809003040d40d11a01c80f980500005c09031100d001e01720344110000c00c805101d42500883c10f590045007018099650340c40b40745e50f205d9451003405107684c881501004940e0901c0020310350040c2c00d10b020310728001080003a0600300c00c0b660000e000c0d050b8186940c00054014032070200a0800100070340201e1070030b80c50361030031500c0c0c802c80904896101c58000c5101c01810b0780b80e00c135910710b01940340c14407900c13402c0804480e0030600031340041d602e40c40760104038001c00080022100e20014000c1d041221542e4086810180c0d0020b12810b116882903c10001 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 477672985 1250 477671735 477671737
    0x2040c0c141c051908090115030b0601081b0306150409050a051501020c0f0427030f021204050f121e060a0f0b010203031807050a060c0c0f0b120912 65
    0x1040e040c000c101c031518420b01c02e07081c405814210b005000d02003009186280f0368115100589195041269103561800221400341035100304088580060340000b0080148400130b0b240604402c3e618100c40783c1c0c0f00001b5403880f01417607043e401d000e072090001079601d280c0403034016002c080b420003660619682d41d0142003a510150b840108454442d400c12080c440340404034543c4c00400d1004041240c0300c0c0d808144625884410240610b481d0b402c0c0709550f400119030682082003a003440e203603205050400400f45160059124018007036600200c5c0e001d1040320550b015540300814070300740c1002c91401c006280f035400b10b01c4038290107141c0d84130380300e5000d01d00407035404048100a0589860200c0c2818102d441968a0301034852401210560756640002a80c3d40b0400320051114240300144e02c01c0e1411050758030031644103c1451001c075002e603004a403161024400e408400009880b62a00288481c1c039000c1d4070cc112100b809421106241c1e140502d40020002c0c0641d030846486080c50982 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 477674235 1250 477672985 477673013
    0x60209030a1a150a0f030605150a0b0a090504050118020304320606060304050d0c150906020d0513021e0a170f0706021c200604150f02070b0402040c0c 66
    0x2020825004100b071002c0c06510314090f02804480c2a0122414040c0320f603074070400740c080036291540c1c0c1c0c000244021000c2440d800b491500a10724205156180798841c05d5500c1248a02c00140d100500020307242442e004060594030100c0c000b5480d1004074040c08000c0d08000c10a030313211030b0b109041101d4a01c44920800c4541c2c0a01e0300b8210000300340c8000c2d450043c0107841c481c0510020010800415004540280030402501d00441c1d141c140c2c0c2810309514a516044960540c03074aa0700c00e04004040d4001c040181c207841c001c2c0401d0f80c40340314102032042030030000ba4000c4030070782800c0002c90a140e050a84400c0041c00d20211948545c0c408100c040c40e40207031005039200f600e120094170360800041005000340d1004103c802000348102d001c0411412181c024800080900a01019045482c40310b0410b01c604a48443c6801d0070f003000c652543c5080c18844a1804006402d99030240c02220003407504030024a80544441d0f00b408000c5c40000740700b00c2000310078815100081d201e0081190 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 477675485 1250 477674235 477674273
    0x2070c080303010f0617040f02030708060708060f19091107050102030405070608061002120304020111370b0c0313050a0f1b050d0b07020c04020d0e011107030c060209030a 75
    0x180700c1d07041c207020f007070282c4298110304184802c0101b4103181000030400c550f40b041c1c0c0300f0380344181c45510340b010034034224182c1c2005401c2c1c0103500400c004954401c0c0c443d40320309800c0f541c00750a06208010310004c0f00020312004000e18818206004605880c1c1080281403895427015240604030b80b12942203030001c2c0d40840d0300d504480c0003082416800394916800600490b42009004003480000e075841d101c004000403d10300c042700040035680944104180499038800348c0d0202020003540d00310b50301c21200c40c0c2c1510b034250801c2c2c894900c00e44031818001c951002e14880d25481e010001c84640e0030040402d907032188094102400a8001d101030003041b0b06c201d1004241c4030300c0c1e140421107000042e0345481d1540180c1070420440c0d5130b2001e64421180c02c0080a41c60303490341c207012400d0600c02c00c1455003050000a0242c4543c0c41e40c3e00ca20441203405000f0017002c66500c840400d10b20441e100980010802000e07076001c0f5015500418107454014215039030780100343e540040382000355240341 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 477676735 1250 477675485 477675487
    0x903090a03080d06050a05060d050a0b09070e01080f0702151f1503050108030a12050402010c120c02040608030a090b25030c060f27020a0302091f06110a08070602070c0803 75
    0x80c910308440c00b50801404041b07681c94402402c00c40840c0c0b140c021980b6000b02c0700c0e207920202d5600c0505034440c11600340003510507100d5250294024050340840722390f490002e03107450b0009104070000110a0f01407102c69002d00310b640e4a9054a2900c50400360400164070584100c426426101c80d14083c002c02080003000d055000355003003d4201c03035059018a8640c0c1003081582055607024080010403011540d0000720340d01e0310300040300e000c11484001880a0109900d03544015001f42c2c039030950703d10071202403140c40e448001d11616402440d035580040b6804280500c11580d130301c00a4200c3d1001d804030381643c00031021451030201610310040d4046085030104006000b80c0e4000c2038001e1594110510000081c04201c11000503000040f4548502200c60081156940491800215001004a081c90034246101103d140300303003d0030b100301c911000b00020342c10b0054040c25002100100034012840080d02d5244255000001c2150780035400c000303050001d40f41d00d03610006040120011 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 477677985 1250 477676735 477676747
    0x712031b06060608090c100302160f081803030702150304030c051209040612050606060918010801020d0507110a02060304080405090907170307020904021c150b100c08120903090a0308 80
    0x3800c007900c040c2c141249500704130b06804191f12a00c2019003241c07498600165240010151854140000c65000300702d404054505420b10003200081c0042c0038000f0040108008200101907030ba205120000390005817103140201030345401000740d42c0c428080e0609030740d031181d5913541e2810100b0050192401c0f540128448800d800c00d8400e00001e095241ca00340030320005601d6495503020020b01880c07043c41e0004020756140c94511700c0f80c4082900d0741502e0720a503151603e1034040e400c40401d010f206403400d00010027240c030445400040c80560f401410b4030141c0c5400b801074a500081c001e440c190303010040000e0a48030483d450b0322518407640541462410609000c00100c00c4480400e8035600a0103100c025035251003000f0340041e412100c3c170b0444c41e00b80300717a00320036640c0c200e01a0450441800082d0188101d802801a605007142e03241c1c0c9080140e201030b00c07002e20035800680340500134003030440d03040300842d0107541010080c0e040720300f03120f10103000480d506402d070400c482d061404204 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 477679235 1250 477677985 477677987
    0x1020102210f06060a05180103110406030603171c1503290f09120c07080d1206060201180609020a080f150609040f030804081e030123030712031b060606 67
    0x1e2203400c03c104071140c0380303001d00d00350004005000d4040ca1b40c0c40040c10300505d9095a000354844032214100c114040d40391a507819014004080905c000d4854404860040c4041035070641200d1074011070700d041011503c000d5408000900801200417035001c50f802010000c035545051010004490840d9100c0703e01036200c1d684d00b4200007a1440c404440d10100707000c171641c808285010340c1240310380517540320208149141d203004003030340c0802281d004c4d40c154000041e40c0241248070303100c2e154206200d010703603a00d8101d007201e4268001342015110064503400052554018000d85c600003084a4603540d1601c1341d65061644040810039282e1110744158940c41b1140341050b402071080340c020585d0304e0103072240412200d80359001002c2010240005d030400808c602070b2504000319481e0490032000e12080312131103900a0007101c005021082540c080b8800910540c1d03c03113000075000e494034614220342151880c003c00750407030a0001002100c140c02401e0b144500d0340500541010514918001d0 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 477680485 1250 477679235 477679261
    0x60b0714070f050105070203030f0409092009040b060301140a0c091a0327070305030a300b040f0510030201110a080f0d020d180201030f0e0a110102010221 68
    0x10840500d40101008001e042d401d15a50001c8907002e0038103c0e43c0f0700540c4002802c41c42014024042000c02041c01f14900909902c01030503107104220b0020340b101d030124201e280039003200070250f0080e20704002800190b814180e081d0030a501500106400600c400000400041203a010100136684c00b0902c1344131b0751010050000b46a4000c080007004440d03500680306100041c202101017404070b80300c00d860040c010100300c203410000251240b56843c4d04d0140d0316540290251000142c01c501c00d2030700382450452101c1c0656040000900503c107249203034025001a40145600969a40c01510410968045c10348900c40b02240f0a89040c11031002400d03810044a0000701ca40c4029940f000184003542103d40648401007401e407900d52840060740a44036030400410060306201400300c0c0c80c81c01c10540d04142d0b100341c82c180301c0c1950100c81e5204483c410400010f450b0b101030101d0b400318280c2020742c0c11600e0184000f5141420100103095507041c01900755606204c0c0204120600603d40 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 477681735 1250 477680485 477680513
    0xa120e060f12040c1e120c080a030503010801150509060f060d0f050405070b120a0f110a030e1203090c040e03040915091a0609040b030717010c021006060507080d0f060b07 75
    0x4111071741d40001030089030300b00e41d100c3c0c09080341c3c0b5240c3e180d030542032014003200344004142d590704403144481349241c010440d41080c411003a203036081207100d039400d848200709a4240c03480603107101a02d40e21502000703000707298003c1494000c1300c2041420400305450185002031960720130b000c10182230a1401a04d880c2850384400d88a100501401d010720344100b40054100e544010049000008a480324000304140070303541406601c0000c525003041c0c1c040e000b081403801c1c004144c41400202e46ca209100b4441101d1004298018000048241c0352907400080d50101c130350111303401c2c41c0c1c91300305690441c8d004c0ca200021030000c10504100039100350041d00200d666585510f840c54020b58040340060183c1140a403280d0385030075508050f03480c104404401020408644074100004c645468003e020703001c681c000500410750760940e052000e004580c00c4810031380c0c03280c0c60072803903032940c0015800107041101c0b11a00d03402c041850120078024000541000c0084590710091807410b030100007085 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 477682985 1250 477681735 477681749
    0x102030115021e03030c03100504050f1503070e061011010c02070807140105030109090201111501061b05031b0a061a0f01030b0310020c1906050108070501020a120e060f12040c 77
    0x2c000f2032288060210940740c1004050701c1d503507129100d017490302400180c650802500145000c0c00c00c260b82134207004007030140941d04c40240d5506281d4042c0340d120821409030300000c0c8158000b0854504101c01200b408500a00e0710100700c2061a02c00ca0039908806036000c01070b803041d0004c0c23281d09400d209400080140c3c0b03201410084000c00064283c0c0014441d0120382641c81e0810415a4043d40d0002a0b01402e10180e41008059107425004040280034410004200300b401002000181f030103681d40c5074003c001541000d101a04c009295414664420f81358020b0300d10280002d02d090140d42200110210f14622140d01182805803489400c1006410982041c000480703d480118400042445a240250307031003030320103081d92402c00c07101964500020310311001000c1c0205a03003c98183c0d924401510368a5544100490761882c01941c043c01d41420560a9240b02d80507484695100358050861401c1082c18007103034820342c004a0000f0304807540e0b0001c000400c058100168090088 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 477684235 1250 477682985 477683023
    0x1150b090a170c040b010311130e06010e0d0803180a20010e0d030f091a09040e0c030d260106030e211e0706050108031c02180120010203011502 63
    0x382d04681d50b035001c03201d10441c020760303407450b00b01d09691080d0000039040312002080e543d200100850300190080510030380300d540c00740d540800c0b841e40c03003220440250407000307003010030540007a21090003d61001d8120300c0000418010000102c4051201c43c5009016800300c10396a940d16805410030701203141498108081d00b40a005141e4803902e1050a80b03800d0700d001425031482c14025540f045568108501c074283c10b01504850b808104003c2103c0001500c0601503005031000003580d0398012115107a16801044603100010700c110b8090b65141c84006207050310414444110100b46001c4c1c10410000f600c03250070301030502040000e0b011504c0c2c1d0b045011180f00c00010000d260b4040c5202d1a41940048a5420640c5d0215016546e245030884400c01c0503503541d43c0001c0d56a8400c8070080048407903421010082c030b6851082d02c048283e07210001114070094401101c050a41010045136039094590078510800240b0196000c0d00088000d194148440900a40f6011a117900c010311694 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 477685485 1250 477684235 477684269
    0xb06180a0323190b04030c05150c0a020106050d020d1506051f031803080115051c02040e0109060315021612031a0618010c030203040812180405070f080901150b090a 72
    0x1113400000c0d07020307406190524020041d440d04900740102a080c4409103040c070014002c04060000c0100a8035402d50001c10125540394184021172680d204041c0d80803030881000c5001ca0b088280c075980f02d04044100080070b07500c0703c0003c0c0750008141e20946540307807807003c1c3c001c01e241c040c400d9020961020700d00c00310004280d60000c00000050040d40000c1070b00b4824480341c14000c81c00c0c0c607196144a03078089031400c6030f400e0b18002034000c1d100320800300080d8000099000c6007442000281c80d08032800443c10703205262103901030750000310714030040c0c0b18408400010451080064080744540e69012a02141c1070103073b0710a4a0299003682d100e844200f1040070020b01414085028800c207080c144e2403540e00b81001d03821402135910108681c014012907200c0794145900501030705103000b940b440b45c03000c0c11043c0401c0f698101e030301d8008103040c018040f014600030302c10b090307100c041a000464000c0341003910040ca807406034081c100601000c980d0340c010345008066440501840000c54445030 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 477686735 1250 477685485 477685493
    0x6030609062403020c0111030117010c1b0618080304060603120e030712050715091503110304020904081b01020309100203160e0406150513090b06180a032319 69
    0x114444100302c0605034000b801200680c420340048000040c007410030741d129a51481089954242251a00c810b5443d04d80c05180f0f150065808002c0018104032000d4102901d81d1080c008052043c41070450005402a005c009144a0000c5200380d1040b980403403094903600c2c02c246005e581000c841e003402100d82e0300404a440009000084400c1c01442da000c22a1908009081800700e400c40c8241e103d0623031003004040e40210207103044480407900000c0c00b030303080718040781202d001100c04080c080042000c2005481d0284000d90400c1c02800e4051074030b41314001d064103800f02c1c54070001c0341d81d401108024807200d052128500e0f01206000561661a01e0000c0314100304c00f00640302c040c001404020714460b1a02d900c14009004000d00c0803c000c0e48000000e415a0407844102403c0700710300c0c0021441f600c0324040c503041c1d42c401800d4507060007420002c00e0210420740c034060750050b00005001011902e421948004686000c0d00c00301240d01c540030705814540c007103000090813841207507920001 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 477687985 1250 477686735 477686789
    0x100603030e010809032104300f230a020f100e0705090f040305070317071d010914010e0d0204050c041701090f020105030603101407030c0e0f0d080c070603060906 71
    0x314402103041b14159118039041c20305a224010303c8042c1840484124411900815062003003000ca4807200302022007040b080381d44101050015421400501810340180d80c150080d1445015030700640d0303a03885610100a08d03040ca8410118101030b1030306c0c0791201440081c40210082d040c00c1e82d050b105403400c0801b00c000b507000075000030b0412034009990800d141c8600d4440da40d9840061011071a42401c4038010141c1c00d015007100c240d035018459120240d8000c0441004a13000001030122514660b8015182d009001e10029001b1401400c20070041c4d65a04c1618802d003040008a41c0315030500c20104d112003242c100c01c800903850008940c000c42c08010704c140d040c035424a001c941da43e40e1800803c0c10710f1480342465503d06d003000342410340c2e403014006d41403189145640804c600350544000300e601030200200306420014164528045040c2a5105d4910900802c00f5130301d41149003ca45140001550291001a50341c4400388004a041d010700401040500211902c3c4601d82c07285c0466 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 477689235 1250 477687985 477688027
    0x1b030c070311060708031509070f0c030e0a030510060e071103040e06012c01080606040f031203200c100203070e010806030111070807060608060708011205100603030e01080903 77
    0x1510001c030b90602a81c1d40ca0101c9003079581c05010140c03a810117034107985407200c89260341403040d11400d0002d110144a08071480300728000303541d81140403c00352801c0d90f00c841c0b0b50522503004122441c02102007403007000320743e650b845c3c044c100290451409040074035551340a0411030811014401d04030061800006031020345441c2d940354241d5468400060710001800c002d00003211002410442c003104900000681418003a202d03c0404c1d90b400b03042005c01d1086000c0c1c03003402c8102460034004280b9400600c2c450b00110b0500040414145260100c188100503500b01c1a43c4000ba001e1407040c800c0c000300b680c5c07000302d8000b5030031802c2941010f05580c0f020501036042000310800188555800d400400c02e0551440c2c81664500d2281050a056070003031109948007801c0041c0095814400a28640702d484035648068199083c101070341d0442e20000d500b51603070301c660801e1301600c4690348035640045120791181c00400c003543c0005021114001d18902d00c0350420f200a0f0070740d0b0005d00072085 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 477690485 1250 477689235 477689243
    0x20f0a0506031f03140a02130516050d11040305070602120414040b030703150b09060a0510050d0902040c121b08150a090f140a061208090102011b051b030c0703 70
    0x141060034011842c0f0245038000703808481d80c0030300d103000524040360b24000c55001344d6805924100001c0c213642500d006450b015482e18841e00c90781450b601c540c0241076203200e50300300400c500e4152400c0000c9a0400d401c2514290481c0c541000b440350104140e1400071502c1000c075040510704402103078114091101036000715180c0310755050f20340d02446803101560303100c510502c0c0d14030281d1182000b80b802c1c00080b40108135020100d940340c60901d820741d048450042c08180808440001124250003421091207515182c0ca5060010380e03d0b4040c96115544540d52010381d00800240b0805540464001100399001c402000000a03404888503600459507100b10000a003050041a0040c80a40c8101c1c0c0e030603d408a82c07081d409845e004101442d20300840110991285e03000300045074181e00c181040d41c0207110801002030707160000340248100500000503500103129403500c5a90040100000056000400841c49402040040f00034050b41d0010b60411041c100700c10754501043c04003030 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 477691735 1250 477690485 477690511
    0xa081209010c050c12030a0f1e050f040e0c1213030e0603090a0b01081c0f21090803040b0402040507030b01050304150b0307090c02010c0c030806091005150304020f0a050603 76
    0x200601c030b03040004c000d494038094009030303a880e58203174843c1e125000418102c00082e0710250340d2002c144188181c2240322503600e400810701150010a03203140d4020840d4140c848014800005c0b00c150a80102d4482c2c0c50b034180680d56450081440040c40400501410701c21690900c0100469401201c050100d4000c0e1455552a128040725602d0002c1c140380017419001d81c8800480c0d040d002142d110601c1e26294907a0703404c0c90104000f43d4080d80c1c2010706000044100140c60010341030f07481b42240c440782c503031030006102c3c40300d44410302c0e02d43c805c540c2621a41d22607030620003181402d200e455409440d13441d0806c00c0c455201c0c0001d113184005000500018401e2100d8601d2040c140d000300c0c0c2000e001411112410364800500010340a2500c0c590059442c0c10880b000b828016a40303441115415a603618141c1d588208001c1e2150000d81042c002c07811414002c00d0f15211007540e1440703154902085a10307880d00344104101d2224100c4001d00a00c7c08030410000e646402c000e407034201c11000052 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 477692985 1250 477691735 477691757
    0x2040506011223070201060614030604061205060403120506010c030305040804150918061512150603020403110a141e10050a08091c0f0309020d05010b0a08120901 71
    0x484003004960001ca402d2894180d00c0007800300301c0070703500c4000d00403903490810390b13030b02c20006031300321a002c1c03041c40e0100d4200521101900c039090001d40d48104c0042c40000d0154070740917a0082c0c444c4044d01155260300400601c801d04d90080420082c2d00c10505080c00349203000000241000c0c030700034006041c16141c0010a0410001c10291809403528940c100c2080a403218022b0598100380304807840601c10f42140c0309020294011542590044101900e26100e101000c407849045200400045070b55400c1c0b02d840305980180c50340040859039400350310350f421410584a041e440c08030403885181429030810280100000015008400712400d07941c00583c0c0c0e0f5446150249804120340c80850076070149420303500900a0181019551f540403a240d5685c244a580d4040b1100144d01c403071301c0e80b0b0601003039030322884800116a10701c1c500811042959804100722500a00046850340d441e4950480300e800d1449202d0300034280d881c024203003034000a42d4210300f403042411003810449ca9080c1 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 477694235 1250 477692985 477692987
    0xe041b0228080c06041e0b13240b040b0f09010501050f040e01030f03030c02060910020a020c04020706090605060a030804260f15010b0c1005070e06070602030402101403040204050601 80
    0x1c1c5842040e0009162595495600718140c0c0310325084504882e02c0c1000505456840d801400300340101c0d034004080d10300d41d155076601c0021545040800c88021403c00213001007411030b40e14554104500d00c001060104601c401c11040c0c500e050b190034050915082030070199602c3c09a514111502030805598a1100d1a0140002d1007903402004541044400000422211a502c501414080c1d41c0800c071460310700d802246c0f40e00003075640d08035551101510740b2800b4650b90040400680b03030f00441e5601081a40418140d0700704e8502035503490359403080071007031001074010341c0e600840494090303c04038115903800d6518012400b400f01c2e40c1d281042d071031082280848040840c00d0350360044600d20108003103c1581c42c84250900441c0d4040403000040303e80c05030041e81d100c2407810002c1c2c44030030001001070b0014503006281c5d2080000603981c003084c0d0745a400041c070718640208400f41c0c5d42d18250041c446e40354120540001040a580c0004066200da401078031b070050381c104d6010415440c1c0e480 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 477695485 1250 477694235 477694303
    0x2030403080f030717040807120203090d03020f0d0503010510030f0f1a210a1e080301030308010e0112020a150c0c0b04050a09020a1704051005070e041b02 68
    0x200804407100014035254910b0003001440c807545842d95500c010040c8101c18903c0c40340103a07001841c005003807011000040000b4882c02c07603070010b803044900f40200c1c5c3d0001a103000660000b41c016030000c4075031400c60201805420094070040c2486441d652418000c0f8160300c1c07014000790201660380508148845650700443c8250750118014841d040d0400911f5000c404945c1d0840d1003061444102c0c0701e884e218008248034441180058944070b0015150101e0b1580700403038001ca400c44401d0742c0300c0001d003100c0c0070f035010390300a41e5129003640c104921001500c1061f006030075144048400140140d440040001c140c8048400080315074543d00002e44800344a04030081c41064111004288255242c3c003620031a1011100c3c2c44640c4d0340d560100d0204e00c503075451800044d01110300d5205403128013803200d42003446a000c031180102102113640c03c58400383d41c200b000510301c80000100d4907082c00b0b404440c20001070b184421042c0e81c0d01c0603554112119417241c413130204420f80100d69000340 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 477696735 1250 477695485 477695489
    0x10c0807260c090f03070509130215181305060a030f0501021303051605010806060d050601110111190513090c141204060c08040c06030207060207080a021506031f05040201020304 78
    0x1005001c0d042c4100c084065410026516024080c080c181414503d000101d220032181d01801401c0980c5407401c5a90028100340310a0b40c0001041c01398040d9000468010000c1c1424920003003140c40c0034000b046855100505206011030411003405825519212514103c95000c8450081c0354800e2400f107001e030041c201d14115034004894004181300b4080b460400e0292811002c0c0d20440e100d41c01500c6400045d26561741058041c4205492024940d003c0c5070880014103200d804080000030850a461120b0b0007c12101310100720300c80000c0030410b00503506469401c0460408031420b4440c81083d00510507003100f00e40700c0c0ba0098002b80a44008500310000b07411580d51b900160b200a41020b40c1610111502441c05c110712900c81c0c407644203031b40142e50190b00c0ca217805107803440c118013030741002c1c806582145d42080070304001181c51005002590040c1c01030810301f1944803000f903070381c40d00600f014000d8220300b0fa85c05400003240203002206c1c2c1d07034031000600b50b1a1800101e156001740e0f = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 477697841 1106 477696735 477696797
    0x40c02010c210b0a030303020d0b0603010602060411011817070506040b04120302030904050112030909051e1803030c1201060201090b040609021305131103010c0807 72
    0x81804024031202e210800720314508400001070303030401158400c030701207540098504041122405403040310308040343c00b24207543c5031290294482c0e6000f0001441d8840d10401c01c001a80200100c0340b920050815801c0c6107a10b80124000749032804285084510a403a000102403601e175048400362565007082504140ca054051044610741e0f21003281580414022040d450b2078511809000b0509001c56622084940c20302400d10445a0480019107051904000e03240b01d98400000c0c01c0b29240b0003400c616a038102a94030b00d0140c04642e943c15000010610854140e540082c0c12480e00d406103111040c0d0f40e03100d080c3d080341c070b04800007403400c01c84800040101c2c14681c020f0103241d002900c410300588400b50603600700e0320212042c1c01c0800e031018400062007910850603055a800f41d00030005802d2060020700f401c500104210208145100e5031000d01801c0c20601030f1030040 = true := by decide +kernel

theorem cover : BRFrame.Cov 477517985 477697841 := by
  have h0 := BRFrame.cov_init 477517985
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477517985 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477517985 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477517985 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477517985 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477517985 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477517985 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477517985 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477517985 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477517985 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477517985 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477517985 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477517985 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477517985 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477517985 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477517985 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477517985 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477517985 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477517985 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477517985 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477517985 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477517985 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477517985 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477517985 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477517985 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477517985 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477517985 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477517985 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477517985 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477517985 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477517985 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477517985 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477517985 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477517985 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477517985 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477517985 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477517985 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477517985 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477517985 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477517985 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477517985 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477517985 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477517985 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477517985 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477517985 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477517985 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477517985 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477517985 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477517985 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477517985 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477517985 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477517985 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477517985 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477517985 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477517985 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477517985 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477517985 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477517985 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477517985 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477517985 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477517985 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477517985 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477517985 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477517985 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477517985 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477517985 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477517985 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477517985 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477517985 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477517985 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477517985 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477517985 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477517985 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477517985 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477517985 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477517985 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477517985 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477517985 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477517985 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477517985 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477517985 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477517985 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477517985 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477517985 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477517985 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477517985 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477517985 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477517985 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477517985 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477517985 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477517985 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477517985 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477517985 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477517985 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477517985 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477517985 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477517985 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477517985 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477517985 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477517985 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477517985 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477517985 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477517985 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477517985 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477517985 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477517985 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477517985 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477517985 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477517985 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477517985 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477517985 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477517985 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477517985 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477517985 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477517985 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477517985 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477517985 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477517985 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477517985 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477517985 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477517985 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477517985 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477517985 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477517985 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477517985 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477517985 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477517985 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477517985 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477517985 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477517985 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477517985 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477517985 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477517985 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477517985 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477517985 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477517985 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477517985 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477517985 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477517985 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477517985 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477517985 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477517985 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477517985 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477517985 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477517985 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 477517985 ≤ n) (h2 : n < 477697841) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
