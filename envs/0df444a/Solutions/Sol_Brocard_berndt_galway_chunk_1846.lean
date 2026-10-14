-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1846
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T04:53:20.662297+00:00
-- url     : https://prove2.me/submissions/0735a256-06e2-4143-9dc3-2dc60829f82a

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 331834532 ≤ n < 332014388 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 331835782 1250 331834532 331834549
    0x70807080d05070f0305090102091e03070f080106060207050a03030c151e05160306050303040911040b0708120a050106120903050d150509090f030a1206181b050310050f 74
    0x2038072104006070b1078804400303004888080b1698002a203854005008003505208031265500d000b0840301e20b440c180d4052407100b2207149050ba0b0140901680003031940d030402840c10250004c0740012071001d08201c2c0007450030b0703096071002c1c0c40f80e8004402000400e401031b28080d0601d4021b01c004000700c101804060142148142c0881c2c0d55441045003061610140d0049000392403404130461000b150340703411019a02c2c2c50003510b42c9500100000c005a45d0070760f0085444507800f040803401d1646c1c5655108880e0002070b03046e20039413000039480342844c241c014a1071788100100c00400003275040580040043c0d5081158080c015030300d0700c0d030109150060017035a02032890964280001e0750071813424003c840071403058600804034100441c3d41145c01203590402c0c088840019400e204582c20111030b0f000404584540d102c4d5100350100d1200f905c81800c075103420703c00f1004210b8008501844848145003050681044020b2060040507103080080c50300711041100c495480348406400198040c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 331837032 1250 331835782 331835797
    0xb0d02090f0a0306150905010f060815090702060a0501080102030c0f160c0609031a01050609280905041a160f050d020d0507140a0e041d010e030306030c01031107080708 74
    0xb20303a024002003040304c0d58102c3d0360711515010341c01c1760017607403104440113483e000e001e00b50868078004828460390b0311441c6405d80c03108614011440000b90b21022840c004800c1e103003800107803c03001c2000740c129082d0048038014a1140c00851075850000c403030705120300525581d04602100041e1598126081c001007559140e080501c13015500d44c1c07081c0103072030819548011210750132012a01444808808401812100d02802441c80d00c90a038040002e1020400c3c10105aa031001d030000c00d07199003104005002e8094a40c00140609041c1405034400081d8007800c03a028564004022102c2404041805040f030b9500b0000030b070f0321142d803054405000b800000001ca40c40400c0204407950f054102901481c11038a40c03d2320b0180b204501e051030300c03500e003501020611092507240d250516601403120710a07242000340a4181c901030b454290742c6503442081e12584048140300300d0745018840004288803d0a003005919a680d901c55824003600a01900d80f14010440c4401e21081d0401c64014 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 331838282 1250 331837032 331837039
    0x807022805011409030315010302090d0219080102070b07110a050c01082710060602280201050c011b0f020a020d080c2b02010b0f03031624140a060b0d02090f 69
    0x5500c0c02c0c6141e907660703800c2107c01f0250044101c0c08040154080e200315404120090702403070b1903080390380038844520291400700242144041000910b003100b0710240c2880b5215000d038882906141360010403400344840745040580201c441c140c0000e500103030040c1c40c1c0c1400e08241806e659a01300310b504404d902c0080d80004100350181c3c419072500070444c0c001c8150103450030000d00c1e8407407504990301c00780c8182d849004480f18194134a0051000310003403c4038414940240b40a8000c0c0383d840c01d4038041005100c00c414840108411103400c890221841074940c4020480040141c000602605411502803d4484002003118090400340b0240c4907103c803541d56039403a0310040320800b0030340361200d03a20b000552038400148001c0c82c2c01c0030b0b503100c407500003002135082034100014144125814242202c00342001c0852200f040011040380c0c81d1410301c0000083c524000418001c68140010614041e991030460203025008004045d200c08070308050340182c480c0c1c000d401080640e00003509640c1c3c03 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 331839532 1250 331838282 331838321
    0xa17060f0d05060612070f0b070206070204140402090901020a17150a08070806010503070609152007080c09060325030606032109050603010501050f120c0a080702280501 74
    0x3800030004860f8000c000176100c440c0030340e0541141c0c540351011800b8680d0505201c0600700314103440750000d07007211800100307a60301d840d400741d00043c2101c0c0c80c1c01403000c034007504104000541c0740011100b948031941000a62412800040040002050f10084290074500302c01250382c41403246200c002c95032024000d02019910748911a5131400f0a100d400a02d1051000109850030045550012901c1d251510101326041414080101c000d1142c4c03101004510351a082180980c04043c81c5600e00110142400600340481c85003050601d00c08140903003640300031b10000b928001250301010755007078000c01c04868130700b00401301020301da4005400e2609001c804814001d400b8a00d84061014103407107c085000700b182510f101619210311940200280010086540202c005045104600c0d4100d40b41401038508000038a0068811080800011820880c000d40104880d13070001010300081507450034843c05120780c3d5038908a00d00799800c0301c15004d410008250091028507680f0740305000f = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 331840782 1250 331839532 331839559
    0x8060a02120117030706020a120903030c020c0105030f0a330e07110a0809012703020f01142703061302032a0d0311060103050703060f020a17060f 64
    0x19400c032034800040e0307035110800042c400c070501c04a41c1d00b001040e00598280003182c1c5070100250010f050600500065212442542c0c0e000e200c3c04003503074030079200005c0140040c0e400900d0300800403200c1341809010814001c12410398800703140d0240840f03102180d80d590710019070050740b0701310f00c0050384504d4014000105544025000041e50310462262610381d1f180d0a08480a81079070311000740c1500140008000f04062500400481c030041c1014905c2d04094190841455070b10b411100103400303440740500c11454601140b508983c000d18002c0104510400040518451020b000c41c101e40141c4a260090f80d050b40d2801580c000181500d0252a203030481800940ca040c0c1c040b4468000c030944401203451001207030186850460648041c802d0380410f0201b200703030600080d4244403440680c0b0281d81e01c1007006501852140010b0940d807403661820405582d4000200c0d0010307070041c082030034100e41c4a2411048280c03a2051039101c0d03180c0d075002c01c1c020422041c80d550003050010121 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 331842032 1250 331840782 331840801
    0xa030308011a0313030c020f06040611010c0207053118060b0603190e030c160e0a06030f03120f0f06031a0112020105072a0305010c0f080613060806 65
    0x141c129903041c0c10206020740524606001c070b01c41294520f40c080c196804903000300e0306c18503040d60010b20142515000d8003c400014010303420590000001540f419280148020203000d5813621501500083c10a10f051000103041c10b88040c2100c80b601c0e4440c180c0080e0f40d82c00c4240300b9114254041d081040c018403a0000d11241a000342c10349040d07080005003443c8d414644d01301c170700c03401c0850f0340f0308001d4900c03902c0304003e02030550350030300d2030700c400d1003444045601400080c003003000366030304605841e107040b404019050000b448010340500d001d81c00c2000c50301103410901420b03890325243c81e4600541c5190002400340806e40308410b8075180c500d150a0300c9941c80720050703a004903c181048060702c0000e2070310322400d006486141024000d10350040d4081d10240041501c07403c010f82802190346100800c80b0000c51441003186160300e810070a101c0d0030320070346400400c02d2400c0c2c9280c2c080d800b0003928459001d44824003c404900725070b42410307100e605c0310000d031200000707440036401d00c0c5000d03 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 331843282 1250 331842032 331842047
    0x50904050106120b03062202060f0d060501080108150c0c03190503010501030b04090203070303230304051e01140f0901021c060501110d08150f271f050f030c0a0303 72
    0x240250504c3c205030b44410307180000303d491290003840400000c0f00c02d0040e0300b0080a4440c41304a0f0070840c14000e402c075216030301001e40240017505400041aa01d4000011300030581079100c2001c640018040f4104726440c18003030f5902040c0110060307039603204080e0491451184404a02111800c0404190001d6002c0d004504a4100340e03009d00610044104010444110840c020f52650000c0000c02c0000d01a0400c061190030091001c9606014902c2d0081c0b6948121404c480503080510207803207400107481e502d02040100f20080101241d103051007071a159001e412a0300c071002c0140000c0314044250111440c080400107400f000d580003011010181c8440e015040c00304003c1e070302064400c1000218905208803035a02c2c1401921112001c03407111441065298210202c40e200310034030703143d40c69144000c00f070079900340d401030701401400100310740058111080740b514002d04c00c2400d45a10081020b0303e50480304c44d02c2d02c000c6040000d24200ea4021111f0708581024800414560013505 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 331844532 1250 331843282 331843307
    0xc14010603050d020c0f0907050906030a020a030c14031f05060a052a030d050604060e07080f2508090a0501050c07060606030207031d0307091e06050a12030c03050904050106 76
    0xf1103116004210080e600c503840c8031540c0b43c1003005c0d4855855a40350842c001c2e900700d10141440e903e00312042d40482c0c240c1d4802c42d0700003501b9400050191906616204200f9014403603c0c0c04860078211466401003480040c04081e0324540c002040722400c402094070100806008140b1681c89960034406869500190840c02c8207480390700c00020810010020001c1440854002e540b071f1040c680003000003094090310071900141d403100d000c40c519241c01c034000c3c05042151640354152038080012203154000402ca071246141641107001e0100c02c1100240600c8070b40c0c20305054030b80d00e41d00b10500c0c2c005005405800766003848280000c001d0a14010200c0c0d41c01110240056511210198240d01c5444001800601440402c3d104198191020480014000c007500c08441d900c440030340a45920281081c20b24800800b0152048900c0c0b15880c01068240c5c0c01c8100c540c54000d200f10f44802403c00582400120f60704c01d01018428402c0321909080140104419611401c006021640c0c0c0760313 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 331845782 1250 331844532 331844543
    0x20319020d20030432010603060b101701060c0318060e090c030121030e03010c0807030f09080a03091e0f120203180f01030225060516020c100c14010603 67
    0x100c00b004126440d02c100d03882103400c1400c42a03c02c80f03c50f060090001c2d00b0226041c90401103607038411241003030080000550140b00d0100d06400d400c010030106070203088078030742030040d82c0641030203d081405039a1f04503a52401d0030020700c0d80d9400c0544d002c03000500030850308a060000417400c140c00140d0034251003802e42d0140e0480d0303105c100e00e800d80c0c402800750705049c60042021f00310714801300c0c14203601144a454040040360105c4003107802c0d600c41401c00c0022410702802c100c0160752501c50308a07190001c01c2c060089403415210303402c0a105d14103440007003517140c2415409220841906115070041c2140e210f404108904224040034078505003120000c284460800c11a4800000d030341c5ea00042028402c00c541444c01000340d4680c46098460505400384480c20707004030700d03c101c905070a00080c81d281d903c3e0343e503162000c00c03103100070310440410000c07480c0031300c00903130004100d02c0c3c0b5075041d40c01e420b642c41c03081d80c20780e03c2c0000e041d40205164007007041d09a081c00107401c681c08407403086 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 331847032 1250 331845782 331845821
    0x30406080f09070909150203090601090e03090607020d0212120c010f020301030308070f091e030203010b010552020a150507020127060507140c010909020319020d 71
    0x914100d001c101540d10403155400484144084505a03110040c1d007407041c3c8803030b0003e42c8080520f01c184c0e00308442d00b104130b0300072500410080d00036024010300380c0d148001070761070401c65030005030407401600c030f000c1c1c0600c0354007480408548481c0003420601256404952002081c401c40004580c040d40c40c91149500b081061001d41a540c02900e0580e585034861000030b80e6811f40850b080400384100a0400c07100080015440c0010324503c0c2d030100c0580000040c00d802c6005060946640b1134406041000030800d01001480c250f0703d00c8a015441c01e41c03013805a00400c11b6142034801d0714820061000700d4042440014219200359250610039111500313801d9403118134883c40d6001c40c6040c004600104111001503114030040a482481e4041c03580541c24000b030b05d45030140d2103030890000302c1c2000861100380015060b45c5006004008000c051081e010b00c0001e00c048440e1245925003500070006c1220000344c03a004000103a1800e8003151503200d01003000c40500b0743c1c44007000d904040ea = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 331848282 1250 331847032 331847041
    0x121006081003020607061d0f120c0624090708040b100803040611010f090507030b0a021e090d050a06061719140f0712110303090a06050c070f0803040608 67
    0x110061440750780ca0008a4008600c0c6809100f40d40c1d2010200300c3d090b42c1d9a4091000140b0120907030304200c91380c40b0050002d000d1f04c05605160032000114240084000d00004002d01c0002a6495026032011000c00003001011210f81d01180540035a40c0d11900c054204604241d000200600c242c1c00b03200039841c140c40b0300356054048040c074001d14213542c00402c0223119a42c051420f1403404c50045000140c0d64620140205c1266002c0d40e044429030000310042050002102541d50001e0100c6001c51421510085039010040c80c5020000141c00c082031120069a44c409078203502034201040d209a24150b2403d00d0003861240188080c3c0d16031008041181100050f804003484541501003000c100203031a10208081401c41d4851070303105403003481010603801d12461005001554003203031000320f580342804200d079200301154042e80c030500c02d52035103650b400d040d170040b80e0090a0003030361030201c0b91644d1f042200c240c11101001d91342003030009190a0000091084400d550764403620b50304d8 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 331849532 1250 331848282 331848287
    0x1f12110909160c0204020a09080f0105090606120a02090604090510050105010f0f080414010908070303050601030f2706060902040605041701020a1709010f0509060f06010e0102100f0f02121006 84
    0xa042d001c0380006043e4010b280060070325038000c004c0180e2604180000782d0351340b40031700e1a0460491000000c0d175184d0040c0a07031554200002900054100e41c003402318081120b40c0d40e503900b081700000e8802c080c104041555521550321080d034054100040d01c07600c031101d401180103006c003071080c1e80c0041d4003401c0c0840308034030a0412541c00590740d5a01a09038840b61103003c40074030500c091041e40d560700d001c4e180008140c0402411164401c1d10082000d2500300005030403a25801c104043c00c03424421103c5590344041c1620b0010704d400c0071240301d0f0000600b0444001c100c41d821070041103100040200340560040060001c868908948030440144100200e0070b030b0150310142d1000c50001d110004909120002c26503008013014000951440c0c124041c40039118151085540d581040c81880020304585c2803060384483c0070b08048400c00c140c800003c0d680c009184903002d00705e646585c0d0038844501c50b04140e0010626403800e54480711103071549010f8880039955902100620b00e0002155030 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 331850782 1250 331849532 331849561
    0x918090601050118050d020a0504051918110d062c0105010f05090c0a020a0c0b0705010f09080f0a0e030d03230106020307020d02062809080c1f12110909 67
    0x3c848005040788915201c148944946d181a00701c2e13000310580d00229a503221403040728418040d81040c680c404580981003c01c8038803445a107070000c3d001d4090900411190106c0b1205400180c0701001ea1100504024004100c5520f8012032200394208a00b400c1280400c094400038428008105d02d9980b4201e241c5130103003034401c2a0f04060701500003420020f203907014100100d030740e0051743c42d94003065845908001040e00b2180c1600030200e00302091140074482c07086d060f007805504000da5400c640362401d00c1d0080322180c00801200043c41c40c4064403c0031401c0000740d018040fa242007813400c1d030140c0503200300c01840c1401100c00c90f0308500d00c45151f010078100c4030fa0707130081d40c50000941c080c0000b0040044050740c1059041120f12003c0720000d4400a0f1404021170303079516076051240041c01021035500501c81e0351300038920020941d43c1d00040a5440c1d16100100c000400355140664074640d4001110310641d242907a19168900000d00400c4c40d11001c8481e5001c6a584007141c0c01c040 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 331852032 1250 331850782 331850807
    0x40e0303060d0807031116031502120a1e110c010510030f0b0408040b0c070906050406031a13020d080a030605060406020a0b1b0a031524030b010509180906010501 71
    0x80e107150307201e00224024400601c1d1310f5009180440c0740d541a40006032804100c0e808640c0e030001000ba040042c4501ca20648440c81141c5006500d440760a9451541000f00030346406000c940c1c42000400b00c2c802c0c3d44806d44900001c241c01d00c14a40a0b2410305560b0b080b10505092550902c0d0001c0c1280c6904c010306070907240d100d404e880c0c0c4000c1c1074076500d01e4072000600403501038804010120f100e5030107001400d03c03444007400030301a041c02c010f1034100781c4540d5808980034504048091000440c05c41403d03d507401a090140440d503681c12050076a4455070303101a400103103040ca041e00744003031180200090710880c1c40c01d1162544c0c900510099204a128003001a0000c2c4601d0340081e0040c160190008070030b0703241000001c1400041a166400000c9480100350f031504114802000d07001c0181c001e0501000b503072044118829031998030385011000d2010503540304901030450380614184c90a5007406070444013062142e6600c1d90324214256440741c2d2602c100c0c800040c40d588210041e032190f = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 331853282 1250 331852032 331852039
    0x10e061507080f0d060e07090e0112060b0301020d11030a05070503160c140f03040801050c090a030b1f030f030318052a06030921120c160b07080105040e030306 70
    0x406803242c4810740315030040544202c140600b00042c502094a9000d940f001d40164010602c0d035052071000544084d0881d031201003d0070825004000c082e10b00700c1800c10b242e0300060081050361521000078028820b40c620041c405151a00c00419040fa1f00044c522030444d40104200d50784a0310700c1034449000450700707e841e900c04003005004041c4600c05242c40c152056050600c08084040c005081c0881d6001020141d4804a0104810794090142e00d8010b00c0c44202146005800302c08209203c049000140c418016080410700182c1003103e01d070185210700108998868592030003011800300c00340c054000a00b4440409901220007852001c10755001c401003c0c00d954240040115101011200d1100b44a89901c0d68480c1c40303d4004603c140300c184042c154071070502d5000400700c03404410414504000b070140403030451144007443c0e00720b12284030040d00c2c0c242c0082041c014082d0600003c01e81e16414003440754040e00100c10a060741c0c030407141402203010443c1100d5a0b40411a0388030750 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 331854532 1250 331853282 331853287
    0x908011104050f03030c070e1603090c050127080a0c060e010804020f1804050d080f040b0723070302010902150f09040e1c0c1505010315051f060206010e0615 69
    0x14900a62440c1000102130260b90600580400741070500d2600e42c080c581d0703121400d00300102200c0020203a00401e400d41010007010300640c03110a01100343e4000c85050002e10390004601c10080f91340c80308441d480844012140d80ca650303820b51100d110700412030301d981b0b144a01040307840c02648c04059a1506070f480b100c5d16a034a0302081159052490b909030000540460301240c622040395691065000340024650700100520007802440001c003032000c40124603041c4400a149000d0041e00003544d40707001c07858030b08043c0784022010030a0809013400c000003c0ca800825806411032104540201c03810210462040702c4950b182c4141c60901c2d070040d6040064031264500360f8000100113400034101d40c1c0d50610111800b009152002602002c100004481010005401608a07d0314091001484136514580c0c035103034429058201d4817959529000002c0c043c1c0c20015188450200740d01c04450035076a0758002a446400a0058010a040c40e10000703065060412103c0c2401005104040c03 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 331855782 1250 331854532 331854539
    0x6010e0415080703080415081311041d0114060a05030a020d08091801080613150b220b0a050d0c180608030301030305040e090c0a151707090302010908011104 69
    0x40105000081000300c0703000800045542c035410440c0201551040303589555581c14000182c0c00010b40348615020041044108485900e040d4045482d1644c001083c490345850b40c40003c3c041d180d03001d41040f03a058070080710041c424054100b0020007640b140401142c5e11500140b1012031118090150541d010074048401821311340e1818680c513000e076241c0e50030828050006030360743c0c1c40d0a0429a00701400001401600c07400d00c0b625030049140160b01e521a00656105404031201120003a16541d903200b0010a684074400c0f0600002c103164004611031140c1c01c0702c44000c1036902c441501a9000000c0031500b0700b0402c048076103041c0c0109a994035035143c00703c1c0380380c3d0740e61001800d804581c4404001030070010820245028512980f034030707610381d8100740e0b0a008c0030328010548100340e40030305d110f01c149480358445107052b2180340c5c904400340f10325a90182d0b40f850503101201303444c0c0c0e003600800c05c20f01d038003980a000341c82c400d9881800240d506c03c0c40714240c490700c9542e52040101004100b = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 331857032 1250 331855782 331855789
    0x1d03070e0601180e0709030302160f14010c1b0f0501021906110c0304060e1c0c06030506030102070c0e0f0c2107030f020307030902011112090603060f0d030f090e06010e 74
    0x103c15007408000804544800b40d000c21100f09071100008204043e9050040507010b016501d050441c034a000411305252070540c000c00031241c45144900107140800100591103002451a5560044040c11100d0110108161042c520b4443c13152411002240440d8540c4041075201854042e1003080074040925100c0074001d0088210f1188804010081c0c1480d0100501c094402046140c6800001d1f01d003802c20b01164141c0140e86105038002d14511100003045034002409030341c035924001410b0345d208000300e4024820440701400800708602e000810802c0003461511078580101c40b10802d031102c1c181c001c404d0154001206082000b11690803560402d196078030f0b0300c03d0440ca0041010b80e100c068000882e80107171a43c100190302e41d1843c90540d40c0041c00034075650ba40c00b0042c80c410b6500400380e981c0b40174804c04a4401c0c2d10000102d001366075141114415000c00034005103030000e00b0306c3c0207043c1000030b0b80854081541d00340009400c039110703444280300707040603101c1c00e20304a45203003003 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 331858282 1250 331857032 331857047
    0x908060a020a030b0909060702011116060509100207060209030f01050403201606030f0b01090f050d0f0803010803040e0603070303081303180602011a030a08040501140405030d1d03070e0601 83
    0x6402015604c00c0200c1803a84c80c2002c2c14000c09400028024070306080030000d0940342c01340710860201d50200807003c00444a11b09040003d07070404030000d640e4589400150920b040c60f07807200001e90020a038181071143c1c1c2c0c0d0040c10b032040c0440807a000020b00c021102c0c00e0302d5003110b000d0007150792542d9003410400004080750129090b00155132003c03000007511300c14850700b500148006541c9400882d40f210f8203226012010700242040268503180c5a1440600012809124058400903d0a00400c00c3d0009203035101540445103c2d2a5030f1200840c95513904948500d512030f0a400010618078140400c107182681d41641e5022110741d80c0c07201c481c410502d141320860800541764581107640000c0c0b1103090207403450364000b0652010719400010581d0620082038866040119050001074120341154119a401c3c20075480d44d0f042580c29a46900940d40140d4050082c2490107100c20381c0300200703824407400034500d41030032007007a014142d0303840e0980901580c012401000c0b03651580111071 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 331859532 1250 331858282 331858297
    0x190e0d032109061409190c1a09030a08090120030a03020318070f05130515040e12040909140105090a0213060302030a110306071716120216120908060a02 67
    0x7004110484180e0b1140110b903c0f021030784a1101c002c0003071003074000d0140014010440302a5182008804545500c00c2600e40381c031800524031402a8244c7c403802205080c0c2e01c6104004040d118111010305000c0710341d5100e103420311700081c400d0750440395103000c4068079540804600e0041d4148850124260029400500507010380ca4581e45c510007004420080e510117403400c03038070071024a031030300c0180248800d540f000c044820303040a007007100c000042d170300c03901c0c51304070403100411040821700d18141042c814849600010304006004665000d8a03001034100c240f1034100c95022298140501d070072204240c4007041c254001d0103114001d0300c0c01c41c04c0310f180040031403000240c1c20340e203500191a000643c90211000000d42d0382100c00d5140920a05d03900000340d0034094401ca441c0408185548001001d48111114080d42400f10a208010880c124980792004554810b014030f000c600d021021441100c86071130300b40c00c03620341c01d10549402c81110b05010040105445010684020313400890 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 331860782 1250 331859532 331859597
    0x106020c0904241e0207030c1b150207060818060f06040f02043302070b071a09030d06050a050a1701090602121e0f060904030311190e0d03 61
    0x707000010740801061160002982202d00042900c4500e500c2900340100c4c10006190a02c18400940801c2d0042c010004180d070003885814010807041c0106011601d94111003071403042003940f002001d40000d00c5100b510b10580711215503556000421008020220201c80180c01c0b04e03020502c200b030000000d5030040002000402c514080c0e0841c08100d0b0001c0e8040b084828038990880700c40340c1000d050209003882d8071a450680441c00c000030790b558207140703e88104101d00007802400e2104103803182c00d0030200c001480005041101000f81e590304200e036002c80351441c0520006461a00c590003004a60000c0c5c6a0003010345401011005419203d407030322180d5403141039500004225100803d02c00781c5540302c40c1c820741043c8504007800b00c03510700d40d102c440b16803406210050245001e030ba40d00c40400c4990358081d54440c80c0440180040100d58080d400011520002c0e050042510070540d020546e1400c081000040400020700c0e80042c0281c0441c40943c0c0e5282c9081e045421507000c3d00d24070 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 331862032 1250 331860782 331860803
    0x31406130b012a030806151c0212011409060405070801150201020706150e0901020711101701080d020f0c090c0a020a1e02180f06120c0619080606030106020c0904 71
    0x3c144080c078403074070a50041a01c1d40406014030030140c010804580081e030960701140c200001403869000c0e0302c00c86482c4039100a411200d61803c11072901160009482c00303800301c0e56540d6651042150841400d6154407881100000940600f024481d56100d6403c6030341c0ca0303031140d1030a1851000d050141c17407042e0865408010071808030b5500d00442441c14041006149060f1515100700c61441018008806603401080008040382941e229620186400c0344c50440c001c07030b443c3d020b684110304075182c8003100a200000284c8000082480f031030030742d80340c3c007a1440042011641500e170080040c600c0c0e803044014003c00d80c1406d485010f0714120800303004640076104140c130b481041c142c00c1034048681485940c02c2c0030440c18003240740f1600d40c0310852214418146114a61012000105190b0048403820f0002c03100b078000700000410184003030525640c0310300400d80803844105a210160224164502003043c13401c181c8112412244240d001e00018a1450208010908003030025259803124 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 331863282 1250 331862032 331862057
    0x605100c05070323060c090f060705062202040e060a0f020426030f04080303100b0906120c0912030720011b05070b1605060a0b1806030703061b031406130b01 69
    0x10002d1758007038078209034455181ca0120003042101030080804900414090001100240000851340e800c10501400005088a000700100c90b124880704060b50050600084030440400070801c2ea00a002e207402c240034807410075405006238800c170f216a100ca10040801d0b03640c000314000e45c0003002040041540d00c1c208102c20000340d03a400070382141015410001c24001000a100e5010008003039040d01d560800f00e2090000e40d4034012005410844512000011050802e006c1155410707140106030382c0c05401ca03c800c0030341d02c1c0c114503001c582240302c010458180b0280580c4070006034905940e41501700740d550704c86810001c6200340894030780c441c840000c02c20300b05001c007410040d040e08046041c2112581411440e01d0001b82403242d1b407510349092190940c489081515440d080a1100300700da80302c20f80424500492588090a401e00d4041402c00c03070900e10202604098580c0d0b402d000b40c840700505d159020000345c509641c07120710005085251007840d0405901c010301410701c000002070 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 331864532 1250 331863282 331863353
    0xc080a1a0f060309030d0603050f0f12040905060118080d0305100305060402060d0f06030305071209050f0f0102070e040305091314150d0b040804090f0504020303070803090304180605100c050703 85
    0x7c040d003045819070032118400c100704008202c4250046055002444c078a020850008054030030b90049041044d01e0f480001c4559008007180c1188184180806003204d07a100d50803520344421011100000b41858003142402c2144c507401001e9a400802401054407070703a0810045500c910201e00c2004e07110443c07102d054259102d00c10055001f0f80320b080e42e0744607900d480101380e20143c100800b4040d102d18140143d4888050f448a007040545940000c0302c50700005030b28050700e9070700410100c80110f042204041d807040142440e200e040c2c41c0c01000004078030840055400342e08c0480c0014690700b00040407105244500190402d000d42214404000c6442d0408518402c0700c0030b640140000804011490407072085070841c4105460030821170420b540000e84074419008040c022100c0400801d005141c240104d6008200b807038081c1c404c1414403078030040504514402c152003441c1100000d09054000c02c00030301201c0d4418042c040715402c655815451a41d400700340d8140d01200c0c80c00c880d4082 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 331865782 1250 331864532 331864541
    0x130803040507030212010207050c101701080106150f081f03080304051501060c051903090f150f0e01051b12182e081302040c080a1a0f060309030d 64
    0xa000d01c0c0a880b40034250300502c45002002c29802d145caa204204140200e000440c0a20445208942010001da51640200e5810740f5000c1c540f500ca060841c0006809401544400100c80c3c4111203200000c13040001600c1d2640c415132581c004c122201c00288122044d600d03907030b1810b00b40003d44012161680c9407800580c1007150300701d80e69406129101c9a101d00a8840f0340140383e1403400e100c01c80c02071745d0781d10745605141040009006040c3c102504041c019840d84025092100201e0f00595440006081c007011451001c4040707590721010320350041c4241c4614400c0d443c10b84400c0d140c44015403c403100c150074101140542d000e04178404400d00c9505000700f22401308800c50000140360981000701850000000505024014114407158841003962649040207030900003800e64030003003540c06990341310303400940c086c0c40c0c0880c51002c160443e04803401142c0080b003c0210000000808101c000c090340c166a00c00010301a09a4030f20b440c41c01103034080756400959007015440080c510035039 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 331867032 1250 331865782 331865791
    0xa0602040e06040f020c1e150c07030f0f0c0f03090905010b09040f060617090106081e0d0c020102031c060e040f03270314031c02040f050406031208130803 68
    0x480440091203607615241c010788443c0032800c0e10451512581200b21640c0d21000b20712545030310b4004414014182061111084680c042e923000b05003031034204c1402e4a503500029003140420075404030005158030075040701621004a48820300031140b80c3d04c54050381d10014004600700a1500004a80d035402030084900901e0000d00301a241d100d807908010946c0d20030200a14140d140c028100540b03070b0700c98044060001840e009150039210000712601601c195000700301144074510450008016008181540d04040710a40d41c946240050413203800900360b0010f4016442405000b0b860a003150144018820031500090710555540c00b5014080003200d00b81d0307500701c814141109140d008031104001b04550b158036242200801c4030310206401b03601004c1c15000748102682c90380700c03003001101c803449105403000d0000f00c078040c45800a903200f80a640c450103030301c01001134142024041e0303c043e00e0b8801c0454852008245040301e41d003c009094072000e414111038200416030081c01103016 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 331868282 1250 331867032 331867049
    0x60c010c03020d0608061005060322240c300e030403030e090c030114060f181009030515100f0f0608060a0e15030f0d080f10060f0c050a060204 63
    0x103c07100010b10108950484d80003e4481d000707181004260035520521303d0541c0c5040b40c2031500da4070b420380411000b0061024554081c4215a1239a00b4850074441d49030b000485e00b01041d08107541d050300350003034445001030480420181d9143d0001a085814211007101c80404014080180100d201d0b043c1c809038036290b807903600001424401e06911407c41983e0510a072605201030800c540502c03058441440340048525040040704410b40d101c3c01100c1209040380e000b16107421382041042c141659005101d0b119926502d9052482402072000c14103c03134228010b01b44070885403200e2400200300624156050b007082502041c04407a03c003824002d04014622800018244040940700030400b5000710700c144800c03081041842c800d480d81c40c0e0701207580c103581904004c2c2e0b04042440d00a03030508006013402101040a14654000d5610f0f04c10000c2805807035641c0c861040328044a0706601a034000100f183d140d0400c01c0d03018144034420144100c4c11140241d49503102d180c01c90b0003540240f4403 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 331869532 1250 331868282 331868287
    0x1e050409080d4208030405281a031e06031002130312090305060106020105061c0f021e01020705090f010e040507090c08011e06050d0c050c06040b0f070f0c11060c010c0302 75
    0xc001c0040c003c1d000203025210000d6182a040c580000c506a074501e51041c4c5500040001c00001489030743d86d200200744880000c1c01c001070240e0000281d8008032600c9039440351040d555011004803012650043c0800350143c010742202c190342c14003a501c1458510111409070400200083c2d80c0b00011000140359950400703564218500300b402d140041e4454000c681c1000203002c078558641c2152006682c0307000d02c842d004846403400d410100c00c0c3c1c0402951003a0341d40341c16860f040304404542110b0000343e0988092075116010400507003001e480d04c8101104050050020105142c406070300302340928101c441d803c0d910b41d10300090b0b80c0c51240d80d1001912b1200100140002400460b5501c101305d0001e070740e40380c14003000402c0c81c01000b1400b15420380310398000115a005130200d404403c0b8010076100701d482c103804d00d01c0d240d00007941c001252601d0500061394051150400101c050f40c82c1c4c1c0c0d43d1940901e41e450745200d080040b481c0c0c1354040700420071407195207400d11602c50b0341c1d00607807000f58 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 331870782 1250 331869532 331869641
    0x121207050609190c060807030b0904081e0f0f1e0f09090c07051c030b1332070305040305091009060801050102030f030606030a09020a1e050409080d 65
    0x741440320041c030f40002c44941908000009401d0700e01202690010700d8000c6003559160012000b03016880e107482e401c00c0c040400c0c0014807011100a041c15074080000d0803420b400e0040c12880740c03141c40114900d06106026044904450200070268117413412a590030703000e12044403102940c080200d20008a0000502c0000b83c20509442c3d42c0c080081c04c80903003072078601d440f8281c503905100031107103a006a80015003140d5000b0390000d4011030b0080c0c882e0151004500d62580201a5034148000d203843c14601e10340b0681c0b4090462240c03658020100103641c4030902d00b40e0150038064421020700006008800841e2184200f18406055945d1820380f420726013000900843c106801042c1190010054495154081e00881c2c0d081030080d10515079a90701d8180e80d400814050000960000c102c0234000340484091459031114203462104041d0141d0b83c204120840f0160300c0010a060130601c00c1c2c000e40f03850b603801100d0b100f00361640c4c1481c203203501e20003041c050036400080e505444071100b02c4 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 331872032 1250 331870782 331870801
    0x110d0509040f27021f1704020102120a0c060b0409031d01030204030f23011a0d0206070203010e030a030e070e0604050421050c0f07050d1b0306110406020f1b1212070506 74
    0xa40c0792142c5d40310400e82c0c00701641009005000d045100b0525800c06400304085910821441545401d8460f100d600c0d01c0300f801c40201034018615080d6040c83c03c003410510302d458a4810802000d41c1615003154000070302c0307072004100081100b154140b41d802d03c00007012601c49150b0548003407265410144403100b02c1f8948298024020054080f60300d0150250081084000e00102d42c103400c6840c100c014030301e4400030b000c41c445d808000707400d942012420f58190000002410000855841c20310016402640541c4d4587c868854041840c0301f460110b1030a080a030b2119400a00130b840000d00c03000c095407000b83c80c2e241841241c4c00180000340b14030030a4001d201450440c080d60f00900101c6242c0800694801c04030400508040000c2c040c004003045007510003002141e000401780081c02c00d040111032290010320130000940154121a0070034100801e26000c003101d01030101310410f1456081c0800c60705411181c11540c8141c11051420300c8185029180071071145005050b07a18016a50 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 331873282 1250 331872032 331872049
    0x161d060409020d0507020111030c070c1a0712080903030f091905030405040b12070510111b0a080627010603020904050a0303110a0c0f061b0f110d0509040f2702 70
    0x8174411039251182030040c1110880071281c015061300111a1904010704002001201d2070f403006820500480c030710704491000c03801511440c1d020fa0004110790017445016945103100304d0f24501d01d6041000050744611400c8100c64026240c4411202c1c0c2410712900110b45680a40c3d0994242d4004902040f40380b50900440d212441d05490501d002e0000c07240141d130720081405030300e10402e850301c44506613910582c031800490440710106e8131100c1c0b15410303000c202c4030362990b218040d4103c0170000c20070040000368180188104507151820000c0041d0404040703807030440350f00b555500c0300340000c0541e90300800c03c0e001c1c6002c0c0025210480f410300d00603003103800102c1d0031540c1901c10300ca0201655008202c041c80d403900441d264075060b80904c0d2a2000704070300c60203070114140c3d10ba080c509050340724507003c0250b2015183c52003a1010840c0a036540c15440e1054400100100704100d13131400c0581261503106183c03403011408120f518100b49512810594408041c100401c0120a62a10b5050b = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 331874532 1250 331873282 331873291
    0x708040b070c0314070201030b0613050f0103020910030b01111516020d05030c07021c060b010210020408070308070c03080c0f120301050a0608091005070f080f161d060409020d05 78
    0x90500c01e201d056038000c3c0100004c0f010b14886040d01240c503009590082e08440c00c2070700c0041c021079841030034080b000d0b0820f21a0240342c0c02140140044809540680f08442882000901030f0701036140c211400c4000c1c00c150f900c00c6040007441d211800d801c0208014594021808103030701072407480e120b090300e24a66107580c0800111340c08003210b00161030304001101e4000d00c08000b9540d440c2c40f0360000c60f00409142d800032089a0203494050184813682c2d120075820a001da003510507440408107034500f40d020f1070290b035481c3e4000000170800640c01d00014035440d441a18a40201607070380e19988903540082240f40f045800064403d404850140006650900c84007030403030a5504010101d070001c20280201000c0c4091040810b0240c00f08000310b520078408a0000e024602e0203001c01460028480300c00000300b0070700b030003040c3c090041d0100280324000440011402e401500002c641b458000108281c09050280341c0d0780303003526400010310107007881c250056135a46201443d070044550040 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 331875782 1250 331874532 331874537
    0x13060806100302060703140f07080904290d030e121612170d090f03090f05060c03070308061341191e05040c08030c0c010f090e0708040b07 61
    0x1d1003840160396440c169804035406103401c80071300c1c4010b000f0032850705c0342150030082405c1c0855200c0410440400400301940165010700000c0401c1403512105110400783c030380030b00340040341240d60f420004480f80e803290091800440c04048000880e4006995215504c580d8208604444038908800b104400412001118000224450300c40060000c40c003007a10103c00400a4500d04050340c41c1c00000d0182d810947e20b100800b82442c0142601513a446000078154000b0000030f181d142c00021382c4c03d080324000244d40340442e6641c0072600c1a034018800b030b51103002040e40c039003001414801c101c1c5501b005004180c034004503484180707400e10703181000362204441c0191300840c03403200c001e441c0d0070180c4440c0912007442c3c84000000642842d4403908080c4600b081003203294182500607a004a005541c40f401d4036445421040d228811103801000d10f0344100d5030b071450355214009151400110345001d00d030b559150086401d2550081d1603400004030a9000d000c248009800380e07541242d642d0 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 331877032 1250 331875782 331875811
    0x40605010c05190f08030a140106110613020103091506180504050a031107090c08060f0901050904110609090a020c010b0907020a080c1c020d0e0105120606030703060513060806 77
    0x2c0d92102c1c1e80700d000c0000100050349040c042810003904101901c5455400b00d0030f40d0702c03481d1034101400148280849181c1d00742e8030200000350349004d80786048816a004010302007503075661680c501c81a01c4c0803412030405030f8510401c400315014503400840c40c503800401190303180c940307514810481040c101c00c03d0068541014040052400640d9034111541410f003011010010310196081103007603400f9521103030030990b0380307440340358000c5605100710400c9410908148403007080c003918240134003a85400449890202d40403440c15001414550710041c1141e14080c0040003196502100b60b6583d4441a00410700ea04400030030300078021005404d9440c1d107410700d0704400007943e030081413a010300255800104102041c0b0184100304900803a2042641c1d00e15441000943c1c496140515000241001c036894070158806d01c2210200a5182500c040341d0712014104041548080c0400040c07543c0c403580003515460300d03404006009800080050f07218540784c00c90b07080c018000c0c200009030070701 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 331878282 1250 331877032 331877057
    0x4080d03060504020414040b010c0606170601090504170706020c0d050421050705040902040f1104050108070509060702130f060b090a2903100f0801090c0603020c0c040c0306030611040504060501 85
    0x114110411b0200c412540802c540c8005001a42c0015070200040d000c1420250003080c41344416a0ba15071361080d03d82101c40c246c0e42c0d44850000c0313503801e450061042d480401d0014504420710054442140980e40040c60310b00d10b100782ea441d0084005030440800c1000c9802c00000e81c4031400f40141c84110741d51203441501c90703510603403512018090544900e648520410541d01d60360704c982201a1110320400c06035030311f04209e56060700148140d0380002c1c03203840040c209034802d60079903c1c05000a4031181c00e19506a00700011001404512510b2036a40d54100c4c4501c411400b4081c01800004051903858500d07605000209107a50861860800b101c0b00041083c06261348882d0134060300c041c2070f616138940301c10011b583c0c1c0d160344c41800d40208014010440940650201464501c203241a80103d0754802060b010303802503500c05003c61308070340200305c0241015004031000d0350b07182c0360000348141c881d03660b04100c90a42508458064000c10240454140391041c400609070901b80400b41104 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 331879532 1250 331878282 331878299
    0x40e1e0a1e0510081204170a05151e0711010608030a2a0b0403051201090b01050904110d0609020912060f0c16020d2603060607060b031204080d030605040204 69
    0x2a151010300700c550b41d034000920000e03141d102020140c610344059070703807008040d420009907400038000e055031058061b0707545921035000110265490740c0705018180c04020300405458a42d402070560805001d40310502c0e10700790942c0000c601c40e605a0712003071800c3c00b500180d0381c02c481407504000b5042d0700070041031304016001000a840004004001c115490f9006100d25110364103580082c4440f603161b0610040641000140c115400750650941c0390780e0ba11540308040c1e44030b07201c509020480400101529081035001b1003041a903c895440c500a200041d00044070a1680001c4005a021400025516140706c40d00d150480d1000241100e04040c0480c1c8406035018040c52801400041c1b420084201700e030407200003a40007861045514100e08051090151910450801c010101c0705510003400e0a01940c1c000d03840507103954148400356031040020402c0e8290107a151007114540c480c12100103009001800910000e003e2100034030344c000c1c0503183d02d0740046118074014802404441c1 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 331880782 1250 331879532 331879571
    0x50714030903040513110c100509011a100306210614070f051e13210503160f14010e07060201060b0702060904090b160210050603100908040e1e0a 64
    0x1601160603003920440c40c04d45e18010120b070320f410315043c0c0d8045902e0031740240208071001c10410200041c00550f403907243c1a0300700c0301c01f00407440390740f004510140c0c100c0c104420075111410a40c02c0003d030f09601c88110050311822041504407200400b00d520041018501907200c0f4592100e1900a50303080842c4003418450300704404d0b4082000c0403400900d8081020307085031820203060000b035603a080c184c0c40b00104c103485001d000c03407454031030004107030100c02403000403010b83e0000040c50030803a80c040c1039034600104000540300b00c1255110400455240880c802101c1e07042c07000042c080541c00100360800a0b0303640042e040d645846420004008000102e030002a411211039664000c660005001008403d030702404c07024580f4100000000c3c50308203008000c0554003203405410100501c0300c103680044a42e150180c10051109440840700d80040c224280704a00c031038107290b01c0310b600c440d030020200c8401010008020003190581d0040780c000c3e41095022101340008550702071884400c4 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 331882032 1250 331880782 331880789
    0x309120507020d080307050a11300403170c0d0207061e030f02070606180c0507061505030303040308010f1205250902040602030306030705010908120a0c06020c0105071403090304 78
    0xc00001400e400315a01c125182e504030703510900d81502d90038000001441e9401c00c48981e0301080b10440400717840d4100107100241682c02d2140004221003a42c0c05a080d10440c6204006e000400c1c40f0100004416418a003d10410242482d07200d10b03900603540e02e0708210750708500554001000a10905501044510003180d82c0c458854940181560403001002040c1104194600c00f0404070200940c58200d501100c40c900102084160346600c1c0381c08803180408441c0108208200c4c0100040d901c0c0c00c1001040240000c4420030360b42d03400440d05580c800c540460015410344018444040803441580c05400140584080d03031000307940340c5607100781100d149e142960001d800459542d404036400c0f009849201020754030b0315580c0201a50b641c202703640c040d100703000350000420154420030600048030001030050082103c0c165000c1442c2d07010803480c40403c0b062440642c00f02c3c0c000c1c001041d04803002d0b40000b80da441d007100020481e614907030000ca10140c04009001400b500002030f5020b6 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 331883282 1250 331882032 331882037
    0x506030717070203190f020105090f0d1b0515040c0f03030e0f0f030708010f06080a111323041a0705090f010c230609031201091a1e10030912 62
    0x1282c8030798800f41d2440c0500da03139255102540940d99a4500d60002c0802650407080c0c00a00c0151101140c443c1c03907025184240415600851186044c2c5219010b2400280680c01804100c0304007925040c0c00c081ca00046d1114100e0901d0900c0304004020f41c038100209414070450f1072060440da0000d00710298018041d03c940000381403404103540744070603008805001411903070704c242e55800d554040e18040074080041e034505000000d0406000c23909964103580840440c00329515001000781c00300007110441c800564030b4a41000c8841e0f49901250903542d660104000c500d49841c02841c183e6440209021500c0c000e000d201500e50060195007541c041282c131502464041c40040311900907080c8050b001e2131107000c0b65080c1c24400341c2c0070b40d000c0341c0c6031040c1c5490396074030300c0a90359038401d0b10b40c40c0c405802c14000400c0450442d5001400a4582c0d21880c000320b0660703000255203000c40001413103040c080d40c04080321450505954115943c080c101482982c5040d01c0e440700c804034420343c040a = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 331884532 1250 331883282 331883327
    0x4110f0111071e0b0702010c1112010c031a150f03090312010602150105030d0c06050711030f04030309051504091d0f0115060c0f06090614040b070906210f0f0608010f0605060307 78
    0x1180d6500000c2055100300e20000c0110030750333002c4001c02808a50001c5108618200b06030344031030178450140611500c9042c0c0b8507140403030003081554964401481c1001310f0006128a00418000401c805e00070401b90b03004240700d032000ca41c02032240350107a1010b4402c0c0d00c00000c402c070458002285010854205000240640d42d282c03013a20a40c466800c12210360000082c02400740040300d01410960b07000703503603542c48d55403110188000164141525401c0800511080021140d01e07004031449400130300741404070303000d0f03049180e103844054007425405075146c14912902c1c8040380e101d440104164501140b020010b521118054404000007170681c0e91200c42e0038042c030030340381c01505441080034010314a610f001c1c288078103c1c41c801e403250f00018007820720010b545441540e481220196880701100c0701e14a2a40120040508070716450707400341c0301d040c00f004078100351007503500406040001240d1490305e0700b02c1c0d508440c0160000c1c1d20407401803090000d050b9108071038070604030403850740b000c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 331885782 1250 331884532 331884563
    0x80d03020c19110d240606080f090109080a0c11010e10030509031201080304060f0e1008061302031f090903051c0605040603060209040e0604110f0111071e0b0702010c 73
    0x81c600003004a400c0d030000d81803000c2d082006948030b0400121314055503e0301d417403010001302c00e0aa5003e032003503000080d07003640800c00100d50b0814103500641c90000014110006070f4a00c45c19822038500c00c00410b007401807500500a6011800c00810700c00d00e04003100d01d80b40700014982880f610b02010405070340708006070340e10f081001151011441461361950541e9900082c65882c3c0c840d00513500050500080d1406837402022a0400114024480d68420030880011202910000d0201d68481000425411001840d01c010350140050200140742800080049144507600c0da10480c03400d1310b40b4074290040f9a00209030340e80b0500b52440300d00101c00e80240c1c0340190055401c03041d44503240140010801202e0350084c008428151428010f4101d0307148107940354102100d004e03000101014040c3c442d4580b8040700d8058820506142c015070100100043c5015190f40144102c12000d240403006254003001640041c40c1c141511807501520b0f5000030038085071303064000c0c04094070034100c1 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 331887032 1250 331885782 331885793
    0x2d05010b16050c0301060305070515030705040909230f1e070608070c05011e0501290a02120d0603050f1f0902060c0a030c021509060f09060403120801080d03020c19 72
    0x83d820040f00400901426499081c442d840701fa030303407049522944c1c4400b100a42e914004080c0c83c0b10790a41e0720386504081c6056101e1002e4981020100c275401c0c81c45954901050f200c00da40804100700c140140304851a0b000c20714a09140b40c00000d240c0c00c44561800040d540c0000c84009a0707842e0304e4910650f8590507003c0c0d603810502c2000500c0c95090900380c0101180d440d07035151001c00402d001f0b11490340e03142c2c0150321191050750202c2d19a400030100c0052141400010907a1490f184101d40d00503407c8550503095800c82c0002c51117050b290a0200144034007005004101c0782c14001030709481c0c0341082c0d401856a14003071400c40c165111308029042d90380f002d0035203010569a4013611080000da2a0061018a1601d0102e101c0c060b02c9010310804401c060941c0c0d11004064021842c01464080d83c0d43c46030004140558495001c2001200213900503040c01c0840140361a041619414800d104d400c01100594250415206206081940748001030403030f600500d22800e40c80c21141400e19 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 331888282 1250 331887032 331887043
    0x901020f0a030503041a0129040b270f13150e041202011a010e010e21070314010207020d0f050f0d020d031503030c20042d05010b1605 59
    0x1440060300a078030603001810b41040c002e512551040303102c904031700101c800d420f030042020300658010141d54002002c4060b15010076074403180201d0020741c206580c802e11b00c24640e21640c0c0740d0f40c29824488000651400c0c64a80b00c42c641000c460161801c80001c1c0070502c18201088007149264640c00349104908802c4100009001840c1034808107161900300000b88180d05001000158a40f9202a01c010600a00c904981b135050f9561404100c81000440d100c2030421602d603400700c800150790b28090038806201180404400c080d1200074510709024800c030f11182a05161a40100181c00050390780041c080c4da803983c003051103043c0400508003a0b2419015a41d00c0f402c41c441c0400880c00a90002103400c0031411a070750600801d00203c0186400741c40f1480014041074922000200081da075440c46030309446002d109441d81c460150005040c2d56000b0502c17000315584102074200c0c203040c2d241d500c0701d410340e200d024052035140c41840e801c4c6110300724202c20040001c50102c010000306010 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 331889532 1250 331888282 331888303
    0x51e070e04140609070215070f05090d060605210307030c150c0201051f08030318121809090a0309060e030f1e1515010509150304063608090102 63
    0x1003040071540b642022100d10710700351221031081816030000f400062001400303e0b03001c03940e41d000080c1074442c2039040d26100300030349555007072050500000c1c04a8903091400040e25008500128000346048240118085a80000406d01000401d200a44c1c6c0001023107031555981840d09401614031401c00104018526807401c10035070030030800191080e415008039003c0c0200300010b09910654a8000c8869040380c03081e0300746a0010701c0012084514040380030b04015141e029910048220702400c6c1083d844003450841805158800001c0c47c00c003514410341c0090070100500c0c016231540c0f030140102e402c2d03100e414200a410106142d080d00c3c184000000d601503642100c1842080412070004032590340700d002c4c1c0354402d540080482c8604c440740035004845412503406009403113001102c1c50f50101440a800c22405c00c1c00b40c640c542c01500441c0725034010b81c0700040700801203031904d81c424400c900400d81292100340f190103003407000d800186401e521154845e582e165040050b03040c50011203 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 331890782 1250 331889532 331889539
    0x3070f2006070c0515070507030219050d1208010b1219020c100e012a0521010b070c050f0a05191703070b0f0415020c01140117070801051e070e 63
    0x18140d0030040080701c24401e13128211000518800d52100c03007240340c040d12401a00da903024440c20000350521000350307804004003160000800d078680c4049803042030540e400b152140444282c3c00705d116804000c2038050104110014580300d00544182c034000009030841d404a050f40c910b580e204402981152220f02030541650360080c041e1000500030444890003115650030200c10722261200501c50100550003d01c83c5804080e030194100d88982024040c00c101180c48141c460b40580f000e40f81c54000e0100c00b0640c0d90710364444c0380a440020075079000c50301a501e0030070040710941d1842510416070303c00303488140c032002c4203048000700c10016610442401446509060007880e0210080110f180901c540ba00307140c81e641041000e0100407a000740c80820b101110095000b4643c004181c3c450b054800802c2c85030f5100515a02401c080c0d206509414543c049105071650034403040e4000c01c44079000704003a1404101000311201d046034150711082004000500320350149403000414a0041c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 331892032 1250 331890782 331890787
    0x901090c060906020114010b040303050c0c09040b041509080d020d09080301060f1106010f0504050c0918070f021c14040807090603020a0b0703120c020703080f03070e0303070f2006 79
    0x3084041c1c0380080318010f0304010350902104030244140d07200010304039400ba5501914161454404498540100e10180c3c81130058629464040d41c0304404075029a00414250040f81090302d84094010061603c5040050a000d1501c0100e400701050381c82c1e1a008800160342c030100f02681d03100400310361b1303001003c18401000104845521192440c085039180c0c54451100c21001d182c2a5103e02c00d10510310700c401d07215024805820f081d080079402c100c40d0031400707040010300300014030f0b041d000341c540c0d00140340d0b080c040000c280da00c220700740760421240c00500100d034400d80d11880c01e0101140b0440c14816000380c8016030100d100e04840040118a007503030b1031141c4072103666000d859544800d034410944d00d007003c1000b40d128021501c4480e41501c856003c111081150009001c174000028254000c042001000c10310343c070000d040400d0f803e42c05036aa0710703100780080d089407000b420b118080d920038840c0310000781100c248072840700d8000300340e460301e0340c6035070030210306103150503001a0402000f = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 331893282 1250 331892032 331892039
    0x80a0c0e2d010e0615030402101101021605010506041a0d020d0c0605281b06061502010f050a1506110304320405070509060d0e0604051b010e180901090c 67
    0x10240d089041c1c0f0703d444180100e60300c0f85030400c003662103aa410a00b01314000c01c0443c0040c03400050304400801c140c10103801d5104101c50442c07c91b0005e0082c032170460510030030300301001000e2103115841542140c4c200500f03651680e40d200083c441d11581809150717001482022365907440d01348031310036a01881100c1c2841d2503400050036500100501c86014859a10044a00c4044d5024440d11141c640d5600e01441d004491510003002041055521655580002c541050150042c2c20802030a0700045000e1948100b84004c50700001c00000b9103134603010254080b5002d0a000d00b08407642c907e0700c5142c2d2502c40400e54114444c0c1d070310100505800178010034545802c616410564480b003009645405600d400303000c03d81d0300072518140065010003c06003a46425030281c4502c110340d1a00090209150124500d00039003a00c0c10f5a40c4c1d17100898030202000c01c031a401410030300030301c1c00c000555408404910b0380c0300c1850050b01d02c503209100191500720250b101410054100412201d400c0c0c0d03 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 331894532 1250 331893282 331893361
    0xb100c0308010e0f06041a0301150302090105060405060a2105270c09010b071403040e0105030d0201020f0f2b1d01090503040e061302070506060a080a0c0e 68
    0x44440044010400c40e900006065000c0c1c0c00c0340f8071a40c2a5004d003030459850904201c001c01200c1c07585031510607030907036a0031607480c2440750030104042a54002d81d4507003140100164008144d1046100e03403002c010600c02c0303440700307010340706405460308180d854035041c002030001c0550303a40c221032121443c1a003006804500c103008910854041042841c0200c1000d58031622201c403c1e00c01900b00e04000300402043c4400c100400d180d5004643c046e130449040c07011141154404d034403a01d07000050740d006102a10341408a40c0c1542c0c0075000843c90149040d03d210164000c0e504510f4501e1004128058148500c120310981c844c0740007020a110794820000340003c0503808040c03104d03200aa0b0b003400d40d003001482094002a0090007e5040c1441c1060389c8030b1044008040716000b0825008c071406c07211460003e0a030851148010700500d28054050100103006607014284561040ea012408111050f080c0402c1d45c45400b0300d08030558540c08222465032482c00100849084007030440032202c2c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 331895782 1250 331894532 331894547
    0x30f1106041a0c070b1603020f220b1806160210020d0909060807090207110d080a14030403120905070b1305040e06010803030a0f061d0601090608160507060b10 70
    0x3942d0181c040035031240c0300c1c96409030158040003400341a03a0f80100342c0c04028078030903140f01c0c0c88501d0050301d800d541d104c283e29140c10803414040b0310100202c49119448170007488034082d040c0d025001c7d08108025525000003801401c5aa01a0900003140f0034840c980503680304101e60041d00d5000315002c03000b4003c1d9104003c1c1c1000000462848001c104a4080e0081c00c1c11104d2070350040c19144d041660b50710080d80801c0c0c00301d030704511b1030078074003010303200d1010542000c0e005000c880d860b07a0140c0800b80c0b4022104500c40442c8008000b000002504a2001810300b010100005001c419504c0e119291040c242c00c104140320740890104283e550820110040d2041070300c05000070f2212556065a0311001e01541d5515082800080c0d107540403640220700c184a5030f440440d03000e0b80c0e003031500001d00b000c00400703100c1e00a042c108141940c109560200806062404540b58589140c42000040900031004200040001d11700107014039a000640f007004010721f5070b0142c1d44d60305000742000 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 331897032 1250 331895782 331895813
    0x90309041407020a0204020f070c080d03050c19050702040e072706120b07090e0103030c0b09060601022802060408030714030c030304063918050d030f110604 69
    0x101d081071041001580945140c074000c0009400a081149040c0e08210283d01316018000c3c45003c140b0a40c408952040141ba0040100c030015001070941c414006054800042c0102c0c40c1580400040382206042540c0c059010a546001ca40300c291500c001805403c1d9005111740034800c00c000801d00c88803405d00c107407845481104020120301101440c0080c0c0742c0034810354031104200e590344404a40c500202c00c1c2d01c90003500e4520407481d1621790b030724030405082e0015000644c40b200031208000c0c00f92081c0c0e41006010005000615043c00001e540e0007030480048120820002c0074003003600341920807850b65074020105511651240d100c682d4039004150141c0b68502e140300100e80d98000030048940c40c002e0480074514581c0c0f951580030145c10720784031580001048042200c0ea0020500d801d0008070002104010b40c140000002400103800210150b54912424010000f55039a008130ba00e03041d50504161fa42e1000e5030345e0079620701c060790342008080e000b0f0303504000410040708e82080d80d0 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 331898282 1250 331897032 331897039
    0xa17090a081204090b06070501050c0d0f15090e03090603090d092903041a130209091f0f020c030a0306060f0507021c05010b0d06060e01060c0c090905030909090309 72
    0x2420395075040540c0d503490348004501d04010410081c07010000325008070601044c0903011030300d0b004042c0e564500b101c1040700c45185801e804038a207058000740f0302070644400c42040c410300190740840e155080c003400034401e002e245651032440c074504003014800d4030200c1d500203048544a241c130a14903922050300c070940340c0001d4a407000103d0103441c4034141108265407890030154209044441d4080e90b80050800e0b2628411844400081d003440b0800d280306240d08444066119141d00c18019062405050011180c1203107059800c0d01440d5443d00301c00c0b045240e03010600e00341280c1c0000091094480c1c014082c00001130300c4100a4041d040310048070519604c0070f9003080c281108850f035004682d402544000120040c1e06880c600801d640c0500340034600018681d4240000100d817016070308000c80e407040e00c1b40d00411083c107440c1e051500414050614480242080d80d886400350114081c0f201b407940e844200e079092080c20402e0352400b4902600e1403200c2d0520b00b4002d40d603a001260460f10 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 331899532 1250 331898282 331898299
    0x70f030c080d0314010b0913021b060609150d0c030b010618061b0b100f14090a090302211204030518010309050303131a010e011d01050f0609030a1709 66
    0x10300c034441d105403044600130300d80d81c1c1000c2e401c00c110104250f10402402d940488101008803a400f45d80c8014842c14000400c0394040c17260a0640c0c5081c40f00090516202d000c02c41e003040404d4890744c11007100e0460031034022064032018a40000c40c50300541000d4554120b00c00041842e6401008000c4c590122580c0c8880c00c603900c0c00100c0ba8181c0039070b9490f034540004009500002c2c04009a1a00060465900c400044c1c03a00c81881c0080803a50228060403001da002c04440d00b0b0404c026a003204240e80300788010710681c1c074083e40e80d00c052118000062007400203e420010020203480d0305002174000c640440c142410000c1054000d002d0420002c0884000307056190b000c1d1103110300d800d605c03101560a60b03680421800f00c0c4104400180d4505510306040c4d0010795000c51001e01174a5090025420b5504100b84003e01c8500c84d03b11101300c004001c0140000d603600b01c0c214030004411130389507903075505400c0840e0910342c0d001d80043c0314407140707144540440740d280090004080e06544001 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 331900782 1250 331899532 331899553
    0xe03070b03010e090610080a080f1e190810053c040513020a0b0d09080705010f14090a060908190206060f03010c0806300102031017030306010e03070f030c08 69
    0x444c904038414901f499202040c2a000036060038081d01440d52040b51139400c04c00d403144401c20b41101210701a824010000307101c5517194050810000304a81890100c0052030041801c1e05c3d0451580a0a80710b0803c03502440140780020110746861801c02050b07141c11f00c0e120700081d03c540c0d84e04c272000380b0650600c400984400c2801080c2002c00d80c00426800080c0c1c41d00203400050b0348400105410581c6495040010a07402c50042900500c02c10000680640030b803008000c03540c803000201e42d159400c00c18010300800004540e0b13083c6030042d100241e0103850785045202d038030507800e0800c207403a1101d002e0040160040b1304180300780401d0b200e0080c44104007003018200c81c9070a40c0c2c400860301c10008103845007048413681c3c544040701d101d086402d0500911400351100100c4003500d0720384d0000b08011118220181d07640040c8054130798103407050301102d52540c03640401400701d0b04124111100ba68965020001900101000100c0747c01103600d0307040030b641d081070b68041d224451080c40c5041 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 331902032 1250 331900782 331900801
    0x71203050717060a08030f120108070303050409023702010c02030f04090e0a0204090b01090c0c020a0b070f1e03021204050d14010905061008010e1c0e03070b03010e0906 74
    0xd4498826952000c0608010059462404601504036030b0403a181490205010808000803c00e10705d0b040085600c0e201510314006050038140c10080140d00110070400029030803000307a4081e610540b00250311080c0d4440d10034030030401700d04100d03100801a00300c10711000340a80442c020000980c024401540c40b424280d03901e206007210600b2000d82004104004692540201c001c048000309494401c4e00c15000070303041d12982c0d5016501e0701c0007400100103030030305c51186001ca00360340d082040c07080941c1d40000b54860502d2081000e241d00000d842c41c00c001100d814841820740c4008034194501d0042c68454499403889011805441541e0484200c840d981d42a201160002801f0411041d41955111401e005410591000307640b0b500c000d0300001c03c180f080a10891000305052441d5241070394641c25a2015500201507402c0769075850503460f072a0a00c184004182d040c2104e00200180210345800d41070740c007150321013102100120724400105515405640271504540842d200d08080 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 331903282 1250 331902032 331902041
    0x31a010f0914010915030b120d0804030503091c1809050609070507020102030c0102030f160c110618060304060c1707020a150e15010501021c02031e04050d08071203 72
    0x10385021900c40c0a003040301040100c954600110306141c0310420544d155001c4940c44401602c000110361a13030180400d500703204e1104100088000000d0901d41d030005005400900040c201600f04a00000021841d440402504a15000c102c00720000300e050460010702d140140c05605104030300d40c00001910010b00d00460340240c800800c402003e440f42d5409480075072000b803040b810750206000501009101f0320146d031040030039103040e071039500d0f0200086000d00c420704488420300800400381e10205441e88805a0302c00c1d0190351850751140089403d844008000320b0280e881b8200100304020481560400b0b070741070310103480d003250203c600c02c081c2e034000b00c0840350400103a0100e0303180004560114860460a8075840002926142000c0d043d410107240095000c402c1401d200100700950b41080182e04981090047c0d000c03d40e580381c0020344034407828440001805071162825030240429084070000c1c9401405406645a9860040c4030fa8204040540725500844400003841d80280503 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 331904532 1250 331903282 331903307
    0x90105070311040e090a0c03060c080c0315010c03140a1112040501021005060d060908030415290a270f0504080708130905010b12180705060f0910031a01 67
    0x11a9400c01313052011158440c01c000340340d041188156600700c004100c2000384040511f0142c840400c5031103800c8006411528050845070403d5010010030104181d100300030b0004040c05d207002c0c080c1b0002801e0440c2c081540c500e806640c03020014558140030b0700a00b80c0301e0b00300d400794191a040154610300c2d85080c065413041c1d601503000b259401d02ca20700981d00c919401840140581d401c40156103403c012101010340403280704000005000a01404106a039080340c5907203014030150004905841103115507400c03408490116903041021540d80407140f00213081c1a02100c04109601644040c0f1018080061000d080c54030388911513480ca180a11840f841e0810502450501180d4641c0c0d40c903401075000d4011181800c80105003850140940c6000f080316030300181c1ca0b00c8035403181c140030490103020b02c407110300c3e000d0141c000c002d00810181c0c100c4408861558541c40f851041b025940300300c07090a644942000710031182c1541590122083c0c070044650701c3c003031058440064400c04040c20 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 331905782 1250 331904532 331904561
    0x509150f0f0f04080a0312140103021e130203041109070305040b13030c05060702030307140301050306130f0b070f0f030e28020913020f01022b0c05060a050901050703 73
    0x442206290780c040010704210840c2003006103015641e0fa504d174108041a803003200040c0303820703041000400103030040451201810104031810b514640c00a4800c404441c10712060441c00200c0c006e05941d240039118103084810300540d52071400e458002044000c3c2e41a8900c5440307070300081810b081c444c1c030800780320307e9008191401507140c0801c21820700c1c0011b181107082211031416080055000d002c143d00030205a0011900c90078920b50250181204a41c1c48040c1c0106000420803039a0008840c1d801c5510300c0c8000502c07032070032701b040c0d005200c50311005080c1400084c01c0c400304d00c0d40080000d000d035041da654843d948014080c200c00b5100491100076080d8842d2244c40840244040c5002e02c6441c0c2000c110b584403243c0e404202059070031554840f0b00c0c0400044407066082c452b4001080341024800b60443e0806400c00d103400035510210300d5030403603002d61000b036201d008a4619110580110031229541340c04a98080540700840d00840c07203500742030101d0051406809032800c50340b00321 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 331907032 1250 331905782 331905787
    0x607020f0307110d02121608010228030227030606010e28150203030603011b1413120525081225150501061b06150b0a0509150f 56
    0x80d12801c0b142c04070700c0030741a40000b40540d4140165580300808403035094546c00340c42031001412441c0c4a55640b580500e8007640100010040311722200c3c000b4440f00c200d1a245883c84c1a682800c40090242001001a0900c0c81c0d00065034002c8449215410040c11021a8070580c0c880004480d105070803c005a0804c0c90310210441c6125a020314803090801c4a2500c1d0f01503690744201103203200030038403000143c0c00000c184141c0f81002c1c003800c640d01d0b0001e051484440d182c1c600c010704000881c1c0c060300101e6030210348588500a03911100c00100b075240c1c0811040440c03800e10684075901c024600310406942100380700802d003010303d00b4084454510207440315910782c1c1551042c903030001110b01c1c4000807480c1c4140d0440000c2503001c003403a026001001c003003a09056250b00303c0e0b0068000605210b4480403c681c242e070604401c240240d880800401c070002b000c7e016403400c0009402401019002040004005a008024250b03014044601280742ea0720000b5800742446824600041c88008 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 331908282 1250 331907032 331907047
    0x6050c0f0301030f03020c0a0609080c1005040605030408040e1005010315050a05040213170f07061106040f050a0c030b06180f0619032a0e100e060105040306110c0607020f03 76
    0x820b51942135000380103941d01040e940001070381000d4107401410100f0951001072050000421542078142c006a5000c90010f0308000301074000c0c000e80c8900d02c104540040080c00b001104030550700203100228070203103a4100112400c20310201d0b80202400a842c00c100b104400c084102400200c0d20003800181c03480d801d09003400040d40c81403900e542e21154401d00011510341140c4040014200354001d0058404c006110b142800b0481c5e014208000f08981e03e10240c40d404644503801580c41002c0b02c600300ea080c504141450000784c1d003d40311984108000052220034140e451184070100e404030090f0202811088444800f40c60141c1807001080008800e82419903015003030310b8044008111007a5660360b40da68100e02000c0445903442c550341072480b441c000e5410180681540124110146040816241510898403480311000ba012010030000d9001e003007110040d5030041c80c20300000da20300d03013042199405550200c04a2151000003170106201084c031400803c41c040146207001c48 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 331909532 1250 331908282 331908293
    0x1e0c0a050f04020c0303100512160501180e07120b01020106031703040503040302280e07020a02010f120e0a11010201150e09010f0e0609010b0105031603051b0c0a06050c0f030103 78
    0x401d10240d50440c0d400c1100e0350000f9010405503200349505000d5004080c1072038203000c1ea074000014011004e03032007d10710450491591030000103459003841c04403c0c9020b002e1303900284240d42c0c2d2101050010000c00d2103900d550281428001c0c04a40e0030500005081e140120300b00e80b45484050800c5904906c100c1194460301c0c015508140a04c0480c3c0c00c02d61a900000c606010301404030010020040e02d03a0004420181c2e450b0013044803030300041c1075242c180400394840070b104200038104201c500c0e501d940140608021000c61845800401c2600011b2112503580c3d92610b0055410700100345058155610500811192121811402c007661b4984854180d50100c080e140401e59500c40c98070a0070109240700b5000c042422500034403c9084c841d0506085803002ea8a85040000400801c5003070860003003044e400411501d00018940d40b14011078203100c881c4001c80a070080c0001d2943d4900400191051b010360103032200f007010341c4403a401d2403100d00c00e0300120501f00c03100744010004280d = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 331910782 1250 331909532 331909549
    0x10f0b0405040230070311030601082e080703020102120c0309130f020d0b0907020c0102031603020c03150907090b0a051201020912010618090b0f1003050601081e0c0a05 74
    0x4c21206809000c185401c20b010302811415030b019800240d1002080400c3c2d41c980502040c80701135180c03540c13444c00c040000800400005000d14005201c51040d41103104204107000703c03608696454240c4107407074450094844d070b05488140d005218605204070032500480c00c440d29418041d008510309010801842200d44c450300e102d5800580c2d40a0030560910b490004150403c0310860014544503910304014007000c010b8001c40440d03000000c86031140e60008201c508911748504061a44140d1b0301d13040f85001c500e0381c1115058011041003690741e4042082581c0580c00c81310940b41281d4458080d00c0896202c51811640900e191074100807a090400800e048803600e18005447c1015441c089030407044c04108024441c0e5440b18104801d4952152404035541e880c20b061000b81450385400d00e034041d000c0c1c4403d110054280204a00500b03803d8003a0003140d21406613038066a40f00c1a0b03544170300100e559410391003419600074590071008150700014071002401300070071504080502c000d54 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 331912032 1250 331910782 331910797
    0x5120105010e132d0b2206030212060405010b090906040b071416110402040308120a0e100b010813020102100b010e06073518030c040e0a0b010f0b04050402 68
    0x10540d8025003410003440c0500c0080c0b03860b0406440f0484ca4213600e410306501404401c103105898280503908594800844080998001c2004010340450740c404000130142948008d5002a40c41c07800c410040003c40d020380304500541c0200840c500400a0209050040ba030811964000000060020b59109000340d00f049984ca00550301da68080e150f440786a0003151903448581d0202c50010411034105083c0720395031400c0e00c065003880e15541d1205141d000b072000780c46101c540d00c000160a80c0190740300700f6800e180380048410949a1529200040c07004051440c0041d001a001403110b600d00409218030780e0b41a40100a800c0004100c81c00402e4181c0103141082800050400955541c5010b06211801806c0050b51082c8aa1080141c080305084683c406d02d601c600907480c2e1131540040d42d080b0f262407240302a84a900700c0c00a82400704001510741e0043c640740b0f000940c1c18001845020f490310a030701107100c0782d0300d50802ca00d50f102c0d90b01c0b401c040c0702c0302044284501d05050b000751100 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 331913282 1250 331912032 331912039
    0x2030a0807032003070b0c0f0706090212030a09030510090b06040207050a0803090709060510140c0703020901030803190902030d2708010c12020a092319060f05120105010e 75
    0x2160a0600c0450703440500914a2081d03101041c0c410a00c98241b2585420202242420785050082e0004005078003d051000d40142e43e00d06001096407680c080820542c00e40b002520754400c1c2c819006480102c0a000c180c6140c1319010303030788080e09018401d80b4035407900101d08003010355038041000007950001c0011201c0703000d02c800c40c00014441e60041c501810000c0043c12a1509003640e0300308491a07684081e100300300748044659610703002980034032060401481582c3d02d901041c001890140306900003074200c501c54000101380003e60b0051405001c02100f0110b05190303154044040c0c580b58000658140c000d2a031102c821805400d00101440100818071541800c44c4d10038024049a1760000b81940d465031012044207030b03c0000300030407041000e0b0071420590700b5400101f41c446140204c98040354400e00707003209808041c1e00c25400100003040200e503d420084401e180ba01706100b244e0204100907041100e8500442c1074501554036400807200d04d0b0320740b100444280811004c0244c2 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 331914532 1250 331913282 331913297
    0x20306060903010f0209010f0c08032e150f05090f0f030a0b0408030a1b0c060c090b0c0703051006081908072013020a02030a0e03010b040606030609060f0302030a080703 74
    0x45407001c4c021a40f100c000301d200142c54282c608005010041829144c404010600642130b0024680b401038a800c2840c000c280490b01c1d145c00d185512a40e001e0781207080c41d19541000107502200b0b0324079041c140481740d80f40780900804480907030303580c020380000c10340c0005060001d24240c18101002c0701d035010010200c64800c105610340703819590080c1d41c10740e810440002003000214080c054100ca00c00e880030002c403040d0310044020101480028010b000d9621100320f4240c0c1442900d0260240ca00d00c00d90990301c003d4800f1090740c0d4006484116101d02500c00303440700a144520802044903030350400303850307900e01403049010003511045080b03994140c180000e0012540e140d041303424044a850003018019440000c0022641e01803881c032140600401002d4040d0341e001c410f450038100da505007180d840c481c6400081c0546244103055400c149024070024095904d03801110032074078a071000700202d41e00c0d5400900c1500d281c3c000650903a01000b0300d40e0010700c00d64020720710745000303182c13044 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 331915782 1250 331914532 331914547
    0x30c33090349060605040b18041b11070501210b030a0c03050d02010515010c02010c050a08030c091507031407110907030606020f0703120f1103120103170307050d02030606 75
    0x419000c44088102050b032068104001c00b030a40310780000740c0200d0500c02d0505191001c2d0944e140b14100e071162402c1168081c04041e500c45400c80c0408180c01440c85081403810f4200070080d131410902031078070b80b19070000021154000d4400e54807034810000445088440e00e4030b160003030441c100341160507106021041001c50035462506014610400284c02c05942c52039000b82035130005492402d100500080345030700c030382e0410021a409031b42800c0c41e50107072030942400c60400c40188405410b1240000070418411451002401800c0c0e048414480140d100140c1e50381c5401019070080204031200b1031a80c519001801411240d4450f10000014080500103d4400e003410f80d80306000c6501c07640184481c076010310032080200d100d0300040050a2550310341001400f00040c5420600c40700c1010a17050512a82c101c8103400c9038441103a69a0001320600310895000b488181c8070003450403048103a032410701c000c036401405c15030785003400d06020041200003940080c10403036002c201040340c0d4 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 331917032 1250 331915782 331915867
    0x1030e070b180306090c1c020d020d03050307090e010b12100305030d0204091406030c041d0a0506090f03041805060112180309080a020901031103030c330903 69
    0xb804402e407001c084010b030320204802d0501c0c281010744500c080c2e030802d6016007080c1c0c03200c400807502003002d81c044030450245030001c51420301e50010041d40140b84410003e050580010055000310381c10b542e42ea00c0541c0d03881040c0001c403000c4c0202c4d94400780401502c2ea044207500882504a203410080c2200c559903503079180e103568000100c0e140f88035004102009070910621801a1325001030b40c501070b107072400c080080d88071035003030f880144101d03a200d030312400c400000b20039480d404075800125948a01c46041c440c1da141000c4a03000502c1c031034a12415207002c404416a41155500e07800c4180d0008186482801f90000400742410000d88001d04a01c05c0c10500440160410110140c60403c00504004000c240a50040500c40c0e00a180010042e1144070200341140c3d044901064414030542c000707800c51040300d1207510070380b003044c40c0409040e01c0c040081c140407000d0010f4200da03240d040442e100700135040318103184030f4105108036150f0066105e40180140c1208504030020f0218103101d = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 331918282 1250 331917032 331917037
    0x8030a0b0d05060a060b04180f0605040905030910050a0c17090406060f120605030c0915040c0215090a0b04140f010e1b0d0b060d050f06040308061c050c01030e070b 72
    0x5a50a80c410300c20f0048130310301441081d0103403a2105600d40f42605084800e05001d07840d0651600721075a030765802022150a0b030040d0044c0100401c14030900c000c42c10140d13625040006200c3c03080e038160321181c0f82d503801102180c103070001c1c9860f2101c800145864000403c245903039884500042040f03010429655403027200080c0c111611548121b514003000203050360002d81c2c42c1880d40d854082d0a00c525038000404094652080f82c201d4000c0c0c0c0c4901c2c0310b4101030511101540c0090030883d0a6079480c1d00482c06400c3c0450600c01001e650b5115880d03155600c044071005400e00d00c032040070a0110318400038100c0700b0322040e03003214459030f801c1d0046421204407109181c2141c120030b0456001006d034030190612010f00701e513100a442515202d20841107070281c02d0358071504aa02d001c9080000500c90400c10200f0481074034480c0c902411b02034a05072003101c90601c14046900c0300804e00100307074000c200140d0884c004242d07910038100154028030030200000c00c18800c01c4400241001c00900 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 331919532 1250 331918282 331918309
    0xf101e090e130308090601260102160302010209130213030809010c050601140102070b030c040b03040201020a0503030a0b01081e070509010e030106140901060503070c060b01030f050f100b040e0408030a0b 89
    0x1000c00b45000c2401c1c02009071501400c0f6012581259004220708000754940e08002c910b800852101003241c1803503140244180003c061482e40581401c0e01407540640c0541909030041e81d07040800c4402d40001001c9214202c604900c0711005030080c004501483d028001b0030806040c4080da01c01942c58a91501c002603001c88892100c00b01c592689581c1480440d008001c810b04103421400d00b0000c8040e00d00440c01000721000003c030026066a108101800a2030303000340139a0ba03a405c0c0384241102402000c8100c50200d141c1c0d00100e2150582c0f8191500c202210800456080c1c58810044550343c0c00004e07000d04100500194100e00d981c05c1c440d010040040401080e1071005020500203c2c0c08164031a206002c0d0920800c0322180c1c202e031591503500d41c0003000041480c44400180c0040c90118407548120b8900000c10521007d8499528003c2c10340d1001008181d42d0740480820600c41c600a8650f01307c1c003078000c00e0006811402940d0800214580804c0800400000c500c10705540030 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 331920782 1250 331919532 331919551
    0x807050601030606050103022104030504030b0c0d05010f27150e04050606060301061407080403060509160803130e04050f0a080a030c1706010c03020705060c0c0f101e090e 75
    0x40c010000c000d940d100d2400141800c5c00c0c2036040910600340312280c0c0e903550b424501009810000a420980300d001118045c1d903125600c2185428200c1004001d41c00c11130105000c94038010021562a01c0c80c100d0300c1c101c0d81c0c1d850700d400164261811104014044046507803030580c5510040a80d14550cc01d80d8000d00407040f41c100036840e1500b8114039022014120501403a0704100602043c1c0d8040c1c00c0c82d0704c40c15403841c903541d11105460045418401d44e130000e42150324001c14070a0312840410394051403480d02440c100c2d91a12059141d80307030701c55852481c003141490441000b04490304400300760701c03a000d04240c6e9107003c5546a42414000c0403e0125503a030f100003042d20301c3c03d800d0300c40d07880151814034042446805182e0200d04611000d0700040c10f104c000200c0d8000c0501c01c100c26405040c004d401c0a44400c020a00241e1340c172014400385100c1e04000518001030b00f410030822000d0107803540d6141542250003010300014801c0102c20003006030940011403401c94044a050043d030108 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 331922032 1250 331920782 331920793
    0x315190612270b1f0e15090a050405150115030b150c010c091203050409090807410d1103160308040210030b130e1f0e07080d0f0e060403080705 63
    0x80c81d00407400b040080c03861031300c28800310b04c012069000b00001c1003a22440f0303010102546400d0707051991a5280c6220b5980801d000f01004440b042c0d030b401044c011480f60f0b0445540c0c428950110008010074040c0d409114250002100c1003031080d0000c000800000d028038003c0d14001341c101149078400d91703846000b69140d00325950b0b071a80c49130504008003410807101007190741a54004020b07100c1c274401c0b229055182c1303081c04144400c0d0402c455956500080807910740c020004501c0e01e07444074403181140807a0a08030a1b00102014003a48000c003030a1018140d032504c3d031082134585074002c1d00410040d01c014040401c1404070341d403c03a00e005001e034550017410710b000c1c81005640d41960060030704241c2440703105140358542030401584a2900140071850060060307015262005100816104c0b51300d107003100d444640c80d688070707080001c80c050544880301d403104841640ca481d000c25003c000351003140d2403440c15118401c048600d03207008001074585a074949844034190440c0f081614144c000 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 331923282 1250 331922032 331922111
    0xb040203091c090f26150105040207080d0510061803021f051e04180209030604060b150f0c07060e0a0308030a0605091e1f050d02040905060c0315190612 67
    0x492410f0b05170810f4041c010005c0082c06c540d00014160180301c2e540c02203402243c42d004001c0030000303603108400680710402c220b2038034080388006140c03140700d8000413400c042e0381c030044441030710f00080c10341e81c0191071381c3e94010014010f03082c3d0804120b6008200b10091003c84007500c45090007140194020522540f2603040001c2d4014000d8110400041288104602c205c07540740855215070154211390b00040680c3d984010441d482030603011101002000103007081490180d80142c50100305000444603125142d46060301c00842204100c6c0e03101001c42410000034440f00011070340058240c0000c40d100c0c1d640c81c04610b07040342c141c035504080130510b991462010041800154452510001c482480715244c0a110482e000c6002d441e00402807401c2e24802d645403500640520780e40041200c0c86403034070342c040100c29041a90b049520310b0b4815842d011514003461281040e04400d41403814640ca414410358180141c10351121046d070302c03907805400b00da03071418065440039281900c0070b601440 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 331924532 1250 331923282 331923329
    0x8060402070c1e050d1208060103090506191104030b0402150903340e0c0a0c0b040303051006020303010503031603031d060108010c030509030919030602040311040b040203091c090f 79
    0x41c6600304e14015400d01069001050003000d040d81d41b82139605200160385c54420040b8050024403001600c24822001805000301c41c4240d0441841480c030340420a405003e12801880d1049120144c91001c518000c200546480201440400402d0208501e03008011000c2030401000c8800303141c4203a190300e104c121100c21440782c800130072061800204018100b683e5102c080341d001e003080c3c0c004200400c0d00b0342180d00403035003403000c0c5401104403e0245020b281c01405080104c46075444041903420014881b070000094905861005002d1414040f00400400f00304038006416000c050321421004078403c40d02c034081140380c4906000c4c000a40c1015105400d5075581ca2200e0704043c82d250421018200210640b80d01c10360480313011007805000110030321406020340010b002144001800010051500001d9200340d00986051040d00011001c0004900040700d0b900056004200740580c20b66040784500007003601ea0800600380341d00c0f003c8030007507481560004541c065138440e21118401 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 331925782 1250 331924532 331924589
    0xb0604080d0804021c02010f081e090115060c050607030b1309030e0a0816171606030b0406050103060e0406111903020903150402010203120c0412080d1d0d08060402070c 74
    0x4010303640010900c02e107a40000d104082312114003042042190114071604c8868100d0540c010601d8980d858600303003680603d000301340c010740342c3d0000003c0c0e10002481d54010707880c541c0c0558200000e411283d95100054001d090707101c0400380e000c41140030440f9100e8542c4a24940980241e41d0f0068503801207040c014041c002d90445000d41d8088400303080501e6078454148240c4e0402d940b0407014000b42902140381c22341c0b8201d1042e109180300c038007291301640365105200c41c080032901804240d641d035005400702c5045002d07480051b4201c0c1300190100b00c3ea6080801c08400100c4080e107842007400314220301030066056a00042c0d00040d040c003252804000108054218040c6000103040c5540040d58a120302c0300c0c5942110440000a0041418227050350005c20040d144803141050a142549660b441040000070452802d81032030300c802d003005103074054a80801c0c010031901c1500d101c140c030a008024030540e40b050b001c01c1902e000413500c220b04002013010f00030b80440840002002c0e024034 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 331927032 1250 331925782 331925809
    0x5070c0e07200a0303020f040305070e1906150e0f04022208060705070b070e03060f0405210a1b020411040e0c0909072f0607030b04020f030103060b0604080d080402 72
    0x12003002c10340b40d03a140100d10700b64003507854100180d6a60f07410071036000c50300441c0e0025020340a070560005806196079034140c401c54901030140512011461000c1c112080ba0041142c1002c0c00755020141c0c50003100ca043c00000010500c0c881c0301c104800040903a8803a160090141c61240c0100880c1208003488402130304821014025070b14003a20b00419900840310013030210a5240045443c41c0e01840c1840710103c03024055130b0076443c00041160442c0d600380c0c2c0c215002d204206400501d8144543d458800d82038404256103010600b02d02100c05104050b6203503003180d41d043e00500141d4a501c03900f881d030f40d8112420364865103895100007141c80000c007290203442040120030441e03a00d076041d0301e501440500b002c134294400760080d15410f500c2034041c2e000c0c1010143c0c50114000c000961244102d02699088c46950f003114140800d81c003903050303842100e141c10300061000902c2504154400c51020340b025041c11354609126150880c000c007040d001c1041c10b42404154204440c80016a = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 331928282 1250 331927032 331927067
    0x2102010e07080a1e08030f0f160f080a0e01020301080a0210210c0c050a0507050306070c030915180b0a09050d020d06051f14030d1e0c0305070c0e07 65
    0x741e140a60094444a04400080c0f4490722400c14141c031504040104441580001100e81c580c641802044400d83c81a107000462100e4000000c0304030508d00800d150454065642a5205241b06401c3c0c5040d2409401c50703943e581c0711203442d08106e82c2403014500030083e80703008114010250045c40f02880e00c800c4000d041040010110360700010114a1500781744201c100043c16404c04003084965a00400c07000304617010b19501c0100740100000d1a5003607400440513108561150a0191030007905c4c4040100858848841081001c0d500a006420b80e885414a0b08920311803148000a00d1440e40003044d101e0000300311a0301050344002c1100c040e15090b02c0c65210035220790009090300713a0440000b8600c0c1c2d01c5d40c002a07040c201000c0c0120194402200703540809448007001035240c8407080007240244034501a00d00c51034420440184450b0069240106840b20b880040760702000460054003403003070410040f800103c0a00c441d0009081d10b142c0880c06050861004002015610b80d0240d03 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 331929532 1250 331928282 331928293
    0x110304120f0b1803182407060b1c02010c050c0910060f022103060d0204051003030305090d1b0c121505090f0303071d031005010302120a030906080901092102010e 71
    0x5403890b000003140e000401a4403079460580a2100140c00c0002d010104c415802c2c8000100300c5c46c40080001d4140103104482c140a0424880d0901035880300c03031019403a60210300c00300c060165002e404a50b00c040d000d4025140380882704000326600d0007065a01c40016013500c034007000b92550011051920042e203201619580e980e8298030b40340980a1510742122500010101e80f0a503104035001100710750207001170001d45003c0902040c0d64155200640100f800c080014541c0d600210350780b010300003141c0f181642c076441c0603105e0f4582d00c00608115032021200c1c4010074400680c800040a103072003019030f40c0c1c42c0300c0c824021109954020308101c2c0c0c0b540c0409a8a80c11240100980c0d603c20480c2c074100324803024000202c44006240490f03030b5054040c00400b1000c4800642225041c3d80c02034a07441c1510480810050b62014611030203000910700e00000c0c030090744220f10440d0004007850011984606984510140c002c10b0310300d46840140c201c0c03804000640a008200d07011400030054072 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 331930782 1250 331929532 331929571
    0x40c052106030d050d0b03060408040503100902090c030c0f0d020a0306080313091109130603060c050c0303010e06040207050d020f0610031109090106030b0702031804051303110304120f0b 82
    0x83d41c0b03044601078042800030120f604030600e840c0354040304c428038008080724454201810190340c2c69100b0300540b806409145e0a03181d20980700e000380c582c8243c0c040c26204c029900d0640c890280d40024102071003211082261801190028001d03008008203030100594031181c5480103801c4449aa120160a40041c0010705010b174401003010212000701602158000380710040354010700c6110b9206600401442034000e02805c198803001c20340344140c03810805540c00c1d05090340d25004030061103807158002c000620040700b01c05802a000103026201608000b429030721503050440d40c04480300103030300c0440b002000c40c00401c0f40c40e4100540c112a070709030350708544902d00b40c5150703254140e02035408140861004032095002100940c0c100b501c40e604c900300313044000d40b203078442400019400d2a5807907003e0285801e100d4a40241c407103c00084500066541c169004084010304081e01d000070b10000800d102c003458648101c07889a1914507990031240782442c82e00c90f000e03004914804141e007960 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 331932032 1250 331930782 331930789
    0x170105160e0409020f0a030804080706020c150d0f050a05060a1502030406030e03070506010605040801060609060801030f061506021513030801180906060b18041523040c052106 77
    0x2140303140050b600403541e803000e0300108002032610303207803140c020340035000010a100d04280540240d50f20791096452150382c41c1800ca0f5070380a1030480d543c0c131198008801c0078203580f640050116400124021402071403103c900c10888600f21054488180c50b0710401605103040380f80d05000c1c00c0c1d480c070082c00300d1205a80c020360340e000740d01031901816512540075058102c1041514041507100c800c44100390b07107402001b856504680705038620f6609004000c640d440c0601e80410a4540995890049a2842d102c4400640041009031101c1355924110025048928100070180500360000c1c00301d50996101c01c241504020410741440010f9000390740006d91000e41d150440d8242d007882c03031345006100b450b07000801c04034000420561030104001240368030303040600300607213009420101d100341c0a01804203850661080c030f0988510007a003070101d118461041c0000307815854044181044007004a4204c805151070308005c91004a02403110002c500c0801303500701c0f10006201d42034140903011 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 331933282 1250 331932032 331932047
    0x90f071b241419140a090b0108120a030518120901020d03060506070f1e0f2f09071107080102090a0f03030504030b0c091c030305071407141617010516 66
    0xc01c0e4540851a1640c040c81080c0e0401d00804019015100c0e91341005d0401030028029000104c404200103000083c00004c080780d4400014112500e40d450403680745000c4009181c01030200b45a109007801080000c4820840e00c3c100781e0310401a19a200007980000e03143c08950042202010308220041c011511a002900c140d9030b84040788051026007480c0141c80b0580b012080003541c03140003610390074806085e21750b0030400c0c01800344600303c0c000341b441c4c01d900403101c504d011664401029103800c0350910915140d40640720380f404086507418a030b105801c0c0507095005000d160340204001d01a484e269901c0b400800b040c5051035800c1d85141d80c0900640981c1c030000d02002c0140d0001800010000c040300c0360705100070240c50300304800c982ea10260125070034050b00081d2030080000c02260248001520100e40461444d0a06c89141e540100341420000390001d180140001030020208001c0b803400a0182c001c00c28072130352609030065084503c000c01001822888010401c642500700c8032 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 331934532 1250 331933282 331933291
    0x10902030a080f0f031005130506031c020c1e0906030109120804080d090506040b06032d01090b010e090c15090409020d140a1a06090f071b2414 63
    0x19810340f1200304401c0b5010b00e000d0030900201c00e6100200b00180d1303040440c3c400c0b043e1101100d441c0341122480140c0001c581003210350a0301544045510340000c106c0d200d141d0500a036174411507411048150116140100704010110f03030041300d1140da0b0b0a442c0130401e9590040007a8002c004d080b20a0303c401034510380412003601800301440c081740502c00c4c000110b60251400c09000d1103405071301c0c5800b0340d44800854007500c0c110b17100004580c244c0b0b00401d003c4030361801114248403003005c54103a0841064100d01d412401d650701d403405400601400c18960007440801c01031035403840d20101c101c3c1801545c066103407140071001c24481f411810b10b400e03110003580c16940000c0c01400e034030104011348450380c0090701900c540b602c40c82d0f0110001842000d0700b07200f000210b2000310050207a219200043e684260322040d00340c0000c4410f071480c980d0b0740e401b03221490b02d1820301e641580e0303036070800b081002d05890035407410068004110011440e40341d90111500104803a2400305980f50117150007a0 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 331935782 1250 331934532 331934543
    0x20705010b03210c0703051b01030c0309080d020c010f09050c15070308271c110a0b010608040302070909030903231b13060b030108070b0307080601230304140f010902030a 75
    0x14a07601e094504000e4800603503400000c0f108c21401e0450f0081070001c4841e5101d0010b818040b00080fa0340c421f0084008040e40511010308003985070103400080d41244141049540d80c860f40d00b10503182c0b90268030191070103240a0560340290405211201c0392809040364008410006840001e9010400c02da015907a007000c04100f0807040c03c5602c480c014001072045a110f003103100c14140808500000c02c080841d101c00e00030300042105241c507280d05500207826040341d400100720117070240b403010f80d01c14403d02c145c81c0d00c951034106801c200c481c8041c0941c0050712040050040200c445050310007000300f003820020083c0d0131000c40c3da0340c0424001405c3c02d00014407448855031166034030801440c065130418801c680d1108040082074100b4442d403241485030440009060b40c0300011680034119075a265445580c0700c40c010341e040d030311319140e003880f410b07001c07244152111b080e901860045105010705201c100305c0c2418a0b241c00544500d0b4900340e45040352240040c1c0e80010b02c0300760b465001 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 331937032 1250 331935782 331935787
    0x212040f0308011e26010e0c09090f030d0c030908040303020114060405041e081c0506040b04060f0e1b030702010e0f0f070504050a020c06040c06021b090103080c1f020705010b0321 79
    0x80317900d004103211906816890b41c00d0030409034440300c0102e0810744240041da0400495500c4114803541c0b401c064a10b50000d400402c0040d00404041e0055401c4410f94200031418040d02da0b21503809034002d600136001030350354841c00f07240084000d4189030012011103041c405030800e92203140740000c071218880f000c903114442420401c404d100607100c00203824004120010714003000c00c00988012542c0300c0c03042c1d01d440242d88032480c00c3c1c4036903016192400c10580003a414a08400002c460107480f90400400c0000b1031105250250300542c071a42d46607002003488901350070b42ea480c004040510f007555401101d41086400340026000044540844010030107441e1240182e0003807040b51286c44d840d01900c0b00308428498503851600c1164a0355080361042280d03103000c001a00803409040b640320000d500108089002d100c09000000254001d60b8200314450342c45070346000f500c2c0800c00302c1d941c01241a605000080c0304000801d0401c0d00502500f40e055800c0114125941c140c3d20070741d240c00b = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 331938282 1250 331937032 331937069
    0x1060c11100201110c0f1207050c06070c03050718180209160c060507020d08010b0306060315030f2d060103230a0b010e3301030c030212040f0308011e 66
    0x1d400c01c1461306040c4010554030b4103440756540c4c03141d951840000c01c0f8401c0d102c0c07406000746904225040b403504013000e0441019018100200c950107101d054810f0038403a0004804a10180303c52401030036540062160a151056000241c0f609240010785050009403101d000d030729820b92161f031003000304101c90030492040c034080e51200d101d10000340c41c092410041210b91a00050003101c001420f4480d40150b03079841282540381d1108880d0705400c800140040341840c1c00b0a0411004104000d040d10301d4800b0060001e4545031201082d10f0b95000c9003408500710702e0301c06880740006041e003070160201e50b0454480c0e5440f000001581c0d0010312031031040b008100c80600008043e10342c0324142000b50359649001007042001501c0440d502114001c80060640e12101d00280b80d4401c04240040d03909010015001030040d103890301c1c18950200001c5a07100c0c140300c3ea031441903114a1120007c10058100240410b40503005051000000030b05514042c0c59981e207901281d900e45414804d0582 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 331939532 1250 331938282 331938287
    0x108060103050711010e060405060c031b30150604060206010b0c01061203050d0605010c320709060311040525030617010504050606011806080a0603020d150501060c1110 74
    0x481418844c1e103502e4180076056840c0046031a0703018a0041d000c5a0064540c041c220081c0c0c40140d0302c4c01d1078602c015640382080d00d1458041c12640c1d03a2002160040580825598680c0c83c100810914007070390b1000b00075466042c0b401058191600351001c1d401d041c246000a540d403801809440e101e0710010038018a0944e09411603c00341421000750b00342c15000380f4001e00f4030717000803086a0003182840c00100e2154407851111450f03903008400c0e1912246029441741c080c841d00d1410300481d0901c000850382942c81003054000034500d41d14000b80349450744c205018180c110007c450310a5080c0030034031840b400c4102007107526445032002d91034041080d80f802c2d0024516580308031107100340c1d0044007075a504198000c0344101d004d1404d840265580600443d0100c500b907004105a60070403105010302c0c1d100c2c4028030f5200020541c002042c0740c490b00003c07405482410102c0b0255181c025540710070f011030194a006040c541414002003625548110f400c10382440103600074840800442c0c1000e2 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 331940782 1250 331939532 331939547
    0x20601090c20101103070e0405040c15022d01050a060503031e04050901061e0c02061b0a080316020f0318010f0e090f0105010306050303090d060903140c1b060901080601030507 77
    0x10105404100d1a510304e032a05042e42c00444000f004690390b1000450395060500469100e60b6200c981d10a82500f4004060000d0500780204811484ad000c1400300c0040c6140511040c0700750f000c2d0302090300f00315903202c0d800d603071008000c102c800b400d140003002151000800d07a82c0500794083d8003480020011409100c80c001d40d4003c50380482001c0001402a13000502c00c40c0308010900c64580400c00c00000380c1d003400507240002c0d04910104141080f80b07041c8001c0c44400104031013a1002800c464035001c40680050310030403001010b80c0d00c4520081d80420910000c036110f1009141811000c0d00b0300c0c03006400000c046030600c10800d50040781325224402c0c002520200a1250f00f841c10a000c55002c004001d0013087d010a00d0301e8000f0a81e460000140d030b110407401444c1103501c0840380d4070140640220070048060000110034a91a00c2180000e48502c90b145802028a030b2090805031001c80600c40e645409502d04001d8100c840c0d038410b404940c420300a0034017051580320400d0484002 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 331942032 1250 331940782 331940803
    0xa080d0f0513090213120c18092a05090f0f0c0405060a0c0309050d080301171c05030604060f0e04060e03130e0a0c17010312050f0316020601090c20 65
    0xa80c5050000f00d0708010300d6010b0042481042c4611890b161070b00c0310000001d1011501070a45401c08504010700f08031150304007100700624034040b600e002181d0700c2d0324401140d4500c9010241e5440c1980c041810104568802858211400b500604106e090205561400741803a20380b003a901000030751500e019070481d8024100946102d60300c07010351400800e80040040201c000810f40c00c0c0006280c680021242c5c0103503041081b161450b40380000b807030070391612185040c005026080d5001f298880c0905d4115007184180c591039980d20340300c1d0400084600d0764001410740203000e081407161502815034540d001382c1c021030004290802a2182d4510b01410300b0f03e00006900280c0851215a0013440340d0290341d620f10140502c09090a0664850091546484050307101500400c00306201d901c00c4440004681806031a100c2800c1407071030f40358412110076103511000315170341d118258100a010b004014111042020a131503c00050003030303110300114640c003860900d010900c0c640500500b202c030b = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 331943282 1250 331942032 331942057
    0x50c03100b03130c14130b0114070c051504290304030302031e241507150209130515040b031c0908060906010f080a05100903030b0909010b03010b0a080d0f05 69
    0x10381d40e40302040020705c403150048501611024020390451802030040f8064a0310503110400104101020440c0079001420282e03040a0000000642130b1154000c280300048080b005540d568181b6480d10788410b4101c10856690003213901c580c0400e5510010b0300e40082d07152401613545d8445a41c054110340c1111441038444109906019005482602c401c2c192008158440140942d140401118084410b40704084100c20080f140c0000c2c94a410480b000c0111003006003080181e100bc0b900b101c0f00b03002034402c3d041e560411710000300700d42080380d012840c04440c240070262145c00800e841c0c0b00078a40e003403d2044000c03a80d11900f4001d18020012f0907041c4216030042c41c2c420300980d5202000e1241001c01c141111010071864000b02d80c0d0807003036401c0f01c01403252a5032200e00d40c0040094600980425589440f0b8049942d40c0910950041c0c900c1c800100e1078011450070942150800b046540c0300d03070828072041080c902c1c04203a051700f140a50410080550134620103603024407518031000072 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 331944532 1250 331943282 331943303
    0x40e181507202e0501123002070302131a0f040216050a0606050a1a090d120305010504060b16121103070f0b070f05090909100e030301030204050c03100b0313 69
    0x101d09000f220707000d1001810100046041c00300c0b001e2011110300b80600d9002c5038601b000b001c0440c82e44500c506a400044404c07030050010700004803000f40c4030550001c010f8200c424100b085d85044208036900c84e040340c000b08480c0710b120705003c00c4000040160f5014240302400c0c40c2480c0d480b0f42c1a9046690041803030604402c081c40c00c59111201d074141122007620302100800c180c1400d42240e400d4994019030400c059403504194103c541109251b1580300041840103070020700000420710310078a4a0f20f01184550421b410070081d10020b801c210a100802d0101c1050540000141c4001329044014a0340f031242442040320009449400d03ca02440001a11410011062811110b55005840314446a1680e920460b280c05580214400103242807000c0020f51400028540e00a036480c801c031581802e9240c0f41c00709881e8010446051600040300410550a00380039841d44128145c004516515107104d4108514006001e0310000000100002c0c4640c6a00503a425105410444409 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 331945782 1250 331944532 331944553
    0xc090b0a05130f06170402030c0a03081903020a05090108061c150501150e10090e0c0901031107050d05070305130b0408010c1d011101020f040e18150720 67
    0x40c40355000340c4402e680e01ca010071002822800c0070000c0010740b041c0741d0710816442e1882021140341d64010b403050340c1c5400765400d40c40e5030342e42d40c0100300011403007041c2254448440400070514446a0301c5400c3c14140100610440d4544c4001201c0300e950382420600c2142d1a0100401c0464034105420079041c007100303a0b10303c140b29990403801a00503d011040c0b003035a80390b000341c2e03590348101e0944601103501c450011300c26240034000d84c811003205291550026030f443e20783e00315062095800901072000080d60444a592500803400400319650007640b82200710745d10141c9e28a840b4001c0401c1041c003152031000c25104a0440301e2540d84403001e918055210220740700c1c81d500c2441350030030780c1d840c04c417040c2c144034041c1d4411500683e252590711400711021004ed10490750f9a4030b580c10955080020352440701080740034002030151008a50303810f14003441d20f2640800310403c0c0068650044004000d0035900c1e00d00c941e80319403246800d12241050049032a119519052804418064051100d = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 331947032 1250 331945782 331945787
    0x50402240f04030f05060907051806060c06191a0607060c120e06062805011412040c1703070c120c0902030f0601140a051923071a06060304060c090b0a 66
    0x1003081350b000d14140c40050712840b031810340d03404080c0300b25500300c01f809a4506100c2983c0b040741d0341c8500c01a04091a01d51429072050800c9130840c0c081c1d120481c4110f0b501260005481929445810781ca0001e500d1520040010154013900900528058507140d03030000c224401c402c82110025011400c1c010f681204181a4845604a51040c0140032a003ca2612202c0c00280b2681510443c002d44001ca0b041000450340e5102500705882d0940040049050124103801840d109070300400e4401145401e241c1411403450022081e852141d005001002c00728280309101021170f5100d00c0e1248003100d69143c92980c1d06d04542c406203182d880441000701c1c0c251185c009907c114030907660071900c10160b0420742e030640207143c0e50700c2c00103000b070040444460032803c0001c601c42060412220040183d645014030170001070a8682140000c80c3c01810045032502d04401d2440c071400c848458a04400418440c2c080100068819034444031070802240c00351b0485009080708042c041d54803045103401 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 331948282 1250 331947032 331947053
    0x414010f09110304080702010c03140f0403060b0117010e04030c062d15030f02040b0402030c0d0c0504050d12170709031a0c07081b0106090c030f050402240f0403 71
    0xc0650751400c103500b140da02101542202c1c070036940400c00c942052450b400440f002070802500b141482150198102900d51100c090f00c00c81c210400d10590381d50561a058017500c820044613818005a00a42030f5402c0303440c10458103403100080b10140e581d48605049550039040c80e0040e141d0b91600900018200d6070705420000700c108002c4041d030302d86000400c0c004039910708a2904c141c1c41c04130300c1400081c4a03038a108610301d0001b440844c0301407441c80000d08030b0b4010741b62120780c100001440720030720300c85009580e100702c1a4100a410701d4903010205003203050022009110f0309000401400c0365001d2580b444141d40038613101c04c2c2901d404007020b00750209602003540c002a0303800d0114500003050030032600c90b4403090a4682414220350341c8a641c0d400c01d0350986185d03038600b210b42c4001082445010010580c600c130200318001180030280c120341c9408814000e05013407000300005070f2184c929000b01008015500c0003800080c0c446040a07000c2c40c40781031080c140007e400024841501c11 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 331949532 1250 331948282 331948289
    0x31003080d09030806100503181c0e190f0b0f130e06010908030708040501261f0509040b04082a0d1e0206060d0804050603040c0305072306090414010f 66
    0x251144136031a03407801c11001d140001010000a0006c000241c04a98640b81e20305004482c01c2c1103480011003100361801d0410b19100000000e0156403110503145089142c21200b880350036510340d0030314104049150703401864068404001000a601000281040100c40f800e14150321964000c584911025200d070300103035070340b41c0094180b24003c03881ca40040304907411251700000451400b440c190064030f001514010b1a0607004000e541e010b0001d20756080c4c184221281d0f4020401c50807150360410b502c03075517504400c3c0180c101c9000c201c0001c000b00c1400780c0181c1c00440e03182e03d500b00701ca090342ca9850b0480c2482404855a8900c400c01c040001e85060341d41c074640c451280301641d4100880c4501d01c2c0000402c0183e2000002c181c00d030414030040796000380114415403415031940f01003625903005130307001c40b0a070203502000c2081c0601070103280090b080c3c03840040f1042c08908a040e00e4180050b5160740f00d0000020409000d5403581d01c11910503a03a0110403080d503a6a00440c68458003510 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 331950782 1250 331949532 331949537
    0x50402070c0302130c052718010e07050702010c0b0606090301060807030203010f0c09060e0607080c0a1b081005100302030118030e03070b03040f1a150312040614031003080d0903 78
    0xc2c5030102c004414002d800403200c2e00c0d03950b54180010f121a441c90107102d021107c0d9284a22902d0a030b05444070449860003640c0c0b8920045554500741d500e400080006000c50100a018011030300180e0380720710b8880d4240c2d000300701c0041507211080081c02030f02c60210a550f066217000c00001d0760803000716414007240d000f100200004000c000317050003500d071903c41c20b10000750300503400c0c04094007512241d0000d64014142c0c42c100b145135502c480c06680001c119103250741c064200001006185010000d01c1000b4021074411035181940d5150b65010750380c0100b03c50b41c1c50360001085c11201003800300045400500070f018036204281d070919140714000e0142d00182a80904981d98200040c030b039411207130f400d0342c00c074a503940707544070003c41944204048030f0714881c00c86100142814070003e64000c29070130720385030381800700e501c109450041d0500c8181008402800208100307034002d110030314406065040a9542c0e660f00c280000501610340000346401404101000007228643c44501100e100c1d4 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 331952032 1250 331950782 331950799
    0x106170708061305120d090507091e0e070605090103140c0a140c07090b0105120421020606090606160f060605100206190c0c05070e090c090c120c04050402070c0302 72
    0x40e10450398191402074050b24545c441c1650154000b040c00041c18a20a2401c0004481d14503958490405113654071028500340c6507a1070243d2040e4150301c0c1c2035440700c05401008071030810320170031717440300190f00c106400c0c0440480c040780d859000f40c1182d0088501c604413a00c032464982c40d100c0c017030307040f0300c0328400004e01d0b440035101c0102c01e0008035181c000d00d000040030102d1902403002d015080b040a850304010701400541c0300c00f9843c480141c02030b841808855031310b21200820040c610f00042030102198402402e120b0725454601d203a03034000c10240c902c01d070337a1540e20813501d2101d00310300c000400d0760000703202c440280182d42e4081c1050f503000315099080b0f100c5a0a00302c0c1e84a4082d161440b14104112809089898551201e01448080c1c10b201c4070703041b0300c0d80701e260424000398440c90b0b28412440400c60348540c103020122250104490800040c1060043c1d00900d0262401c4220385840030070114400c2034002040d00c0c01000020015980c480c0c42d4a00a410502c191104a0095068 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 331953282 1250 331952032 331952041
    0x120a02090c030a0e0f121e070b04050c0301060f050d05070b0d02091306051c110604060e1003182904060f060501050f1e0c030309060103030e18010b0309010617070806 73
    0x106485d15003400301c90003014841c4000c9160ba140e0340c40206092a070400c44c070900c02c408100790010780401c0e40212243c0141e0320f414100b4a0078845103e044c03a20991421030180f04041c0b02440310030a4400503039400064142e24a095491300f2a00e03041800700e00004105009061903940040c0304030001a070340f0f9807148a1051580055030814001c07190700082a00380c040102d03208a0f81544242d02941818440d0b030014000b198481e4426000381002070851603480e107003428003400d0301c040641e492900304140d0364850f0306e0310314111100c60001c000f140740b21005c400c0712002c1100002850700103c5480c4080c00c0034504a4000c01d42c0135410b1401d075062610000b4550300560a49012a48685049180118042540010040401d1440040d0744144202280700c4010006188521340003401005554114100604047c00c0b011040e0f100701001c480040001102d41903103811104002c40c0c1c05d4994036039203070680c0504201d4000c600051030f50050850300d1040022818210754000c2c059030b00384c3c1c65 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 331954532 1250 331953282 331953311
    0x40c06090e040b01090504030e0405070e1801052107050a0e07020d111903020f061509010b16030509010e0d0303020a0f0c080906210a091103060403020606120a02090c030a 75
    0x4080b18090540c000200040020010a170407140d801440303498a41a1103416800007400c42c7e03800d80b81c2c003000a00030084942c1a050810510306100d0400101c05069854800040c0300031800003600c1d90b180d03403440994840545c1c100a020046c00c001007000c403440d40c64501d0056400c008480301801841040b640c000024050700c15000b100c01408040d20351003a00400a032262180c0303803411011881050011fa50b2a0800e11285020300c855000c200500180c40082000100c4181c10018950b142000941125002c0556800c90706601d0308000d41c80d006000f00583d03500d9110304089410054040303010041550540c02441c4035442501c500c440000b036400d0440d5110041d600080008004000385001480c0c00c102500700341d00800c3c00c8102010b00e08001c91000401911205a80f5443c1c03600001008582000907000c664250008c058500d0107480082d80c584000d00540d0082d48500248038030000d09219404080787c0207402281d00381007110200b03050703038000c4910350003682c82d12946000546 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 331955782 1250 331954532 331954559
    0x60e0a0c050c12031b0f070c0e0106021902360901090201091701020405100f03050a0209090a0504020406080d11070e0105090c16060f14010f080d0e031203040c0609 72
    0x802c600080c1040d0011501c501c80950001d40f145211001020001ca240c1c0c1c03130100100781c203100340c0c119151140070780d251a04d0790500581040e00d0442110005104035607002800c45814245c40720701c0003142c03034036002080700300d8104031060300500c07518071504000c070315803024600c03200c28a07040c0b10006545200169088500419000303001401c3c2e1103003003010b07440c0401180740400110000515250b928000191032803101d030410800f00d0712840c0d14030910342e010301c80c103503022414082c15403802e110000040c10682004140046107a40c81c00401d0954485502140c090705070641100d080c03c101c1140074001e00100080c3c26a5440361400204400d50303030240c0076040303400241a00c44c0b6502c4248140200b40c0108201c103809586141030480841c6140c05110b1103216402000154401c243e0440c4403000d005810010380148203807000c00088030009442c100b9a8400d152011100e141540000d081895015450003192400310601050001d41040e1000702c580c562205241a9a202040034600 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 331957032 1250 331955782 331955797
    0x7031103090609040b04140f04030206070201060e040212010623030f010e031b0c09040308040605060f15090d0c1d1b04060e0f0a06050309011d0c040b13060e0a0c05 72
    0x116050220f0811800e00d908682018a001440444c02d00204410240c054004507181500151284140410b141c0c05000c0b16402010620003440a80d05241e82d49140010281009010716400c07002a460391000b940018050684841083d4100084c1d808003032400107500c00041c464002d1076000101c4d000144900c01206035858051400e144030340e61800d110400f03241e240d0030300340101603d96100d0755841028034480c2e4401e44038000c0a00b482e051030001c031600108514010552150319158966aa0702c1071100701200040c0c0950300c0202d0742c04511001041ca000801d203544443d03021035101d442c1c889101c0b0711440c02648000d196038640e081964241c13481144811040c04002c2030150300d02c86c10501052090280200d400201104040f480b1080a40d1014000580c08018170011900130b008030114854005494140c0000c1e907881246c85000040803680300b00c0d5194110f00e02516560610020121000d4040204a0b42c680c1c513a200d1200031030714890105d03d024010340c8114090000c1d034008 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 331958282 1250 331957032 331957039
    0x13060801060602150f0c1303050f06070e030c010e0415090f020705010e06100b09270609060a1a031f081b040212041112070f1d0106020607081e040302030703110309 72
    0x5c0c0c0c5804038812807541c48501c0c000c507106201d88000c80030401c20030440782100304100003064585031800004100e140180002803283c7c12080d60078005a070301a030810b05500c0300300d03400240010310a014041803101c5a000080260401c02540341111040c1d016154550140000740840075604605a0f02c03640100c49450007140700e03190034014031003c24081d20365154040c0c4404070311680201035000d4011040d8845042610200400141c1e0805140070394019200f81c42c40c410103410007100c440040c0541480300805140813002139002c21140b004207102020481c2c92481440d1030350101d981b10000b8180054889182640168a40c00e1502c2201d244a01507848130701140c513142c3d108140c7e90034540c81503511050000301c244400405103c904010502c5e500020382c0c051800d00c030140c0f030100304401e4128050b43c040041059940100701a60b1103100c41c0703400000c0d5580c02c2a20413040c500306420b2580001c0744000c00080580000003803241c2c901030388803416201c03080ca1140b660f0748607203000143c0 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 331959532 1250 331958282 331958311
    0xc03192001140a09260c0a062118230d0f08100905010b04030b0c030709120f06150801051503030405040b0103020f0f0a0f0201090b0103030e1306080106060215 70
    0x4540b00041c0141a41e061103242c240038142da507090000500740b020030a8600c80c070704056681458882005819174000007592080786107490722a02502d1100c1440800340300c0c9042009481040308544e00c000b0421030050302080145480342400c0802400c586504880e81e4075214180c0381000740025040e99501a5903100151041c0030402211700810151240e40d061500f10b4020501003914080e003406851100b00d116151413450030014141070340607101b1030700b1800401c244410103500c6030342c0c6000c1d10340200703007003681004610704021010071500000d042c1034034200f1442070240c0301c12922012651050020320a40d02d078818526440518442e4659041c3e000304010032460410340c008400e0214141401800c041c2d40070004541503008121050a0660009140f20b00703507003041030082940e001f4402027084500503550381c0d0350f8003410b000240501180701d0140d45a075861500404000da6603150a1000e20354034200715000c1c101d140110310140c01610300e4240103412054280e8030034401350714500e9 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 331960782 1250 331959532 331959557
    0xb03011d0f1b060a020c0d12030f05011a03040206070602030f160203090307060e19030c06180b0306041a04090507150f09051216030302160902190e01020c03192001 72
    0x80d00390f0040f9045000d42c014910382c000ca90f42c0d21080031221a02440301441c3c400a23200c402012589110200e41d01e091806005210461003100c42406001c004c481440d80c0740c80d20b00010700305025030364008056500004c03c01805070303035160b0501c0c0502c0b20240405100d95181e05c06907181c0c011001d140d81c05601100040043c2c42c454000804070f5400a0801c07030707000518000f62120340e4160707001554800f60b0300004001070380c3d00c80c41080b80c180c0c0f62401d280070036003041e150180911014000e44d100300c1e1105603135812107280000321002004010402c02c80c82450789800c0d5100d221921a920502c80b00703505140c51036010788040800710b40c95550300103076181080204102805140040340e124402c2e03110001e03803e0001c5000c10040c500940089c9264880345040801200d40342c0c0144400d940184030540300d07105051000c03013104146040c890802c401c4440100c3c40d28100905055151048001d00d001041860110080e014002c61100c00b2040e100b81058000b5652040d030940042c076904c5000 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 331962032 1250 331960782 331960789
    0x806130507120c500312070c0608070f03020d0209060301090c110d0504030f050f03030705040906050a030c09091a070309060e060907030209040303090c0906061106280b03011d0f1b 79
    0x100c40495403004104014810328010a24106c204040303103e038900005040c9080c458a481448020021b41ca404003580c64403000c001c00304c88003000c2c01001e05030041161014540329805440420b04054126a142d40c0e640c103451001d441c00044410215041040301c00c04942d01003421000200305803944d46c5090b00d1581c6440e10507002080907200b600a0b007036041c203214000d00055003e13403403903629142c490341440e11001c102c4410b544024810242a9000c10000d43c10801c09811552a4030000a52a11508200c4003000b0380c90307000c0034003c0362401001000c0350594050740420740583c5082010001076041d60780ea0b03c0c002d840300c03801944102001c1005282010849611500c0303480c01040b80d40b100e580e141011715658003c1d000301d548a000a2010710f5100d031031303107014189890040000341040348071456242030055281c0b98884510316101065a85030300420034044004d4003c2000d12544201d82040801c8101d80d4226805104010698614009414a0034502c9800c2600001580c10200b = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 331963282 1250 331962032 331962149
    0xe07030920030a02040e0c011b050601140105070f031d0405251202070b1b0316050a02190503031503030f0d0b0109032310060806130507120c 62
    0x41c0d5a0611991801e00700503111405001741a1210100610080e000100054111111009241d40011030a030203040890b0740061064115882c4202c205044515040125214494508094032aa040d03034044810942c3c00450304441c078401d40800803000105100300010b807a015210000c03440400c00328090621404501200a4011424460810f1503c0400b1006031380241e801a00c40d01040010400c2c5240c11321000c110550280f407070545036140510204c2c005200440802c000c0020101e060f0380d90318001c10501c00060000f12006140c1e0015280942e070383e42c0200e41c0c1410900c0c0c0380000520504000094602955030b441109091803219052903008200d0350000604000c001c02001010421041e90307220781e19036100707494511070ba01150451400c1d602d0401c0d40c5c40307103140c038004200c0e020340840c0b60384c3c01c83c7c520005205040502c0c20450300e8040340381c00450035084903a01d00c1e410003256a84000c04c480000c60390000f50b41403e5030038009a0400032125080000c5011210314810000c0c80 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 331964532 1250 331963282 331963343
    0xf030912030918180804050f121005060102070503010f0b03010c0e0102060703021303060c050304060507020d0903020609040212091b010305060a03030804020301090501020a0c11040506010c0b0703020c0d090e070309 94
    0x1000508002e049005804002012002e5407517403800034040c0100d00f0145c085030503c0500b030700d00b030040100600c43c25580b035903500c1c07000c02071590f01c2002c18070503031007440a440100300013002441503c9402d00e070300c4020100c225015101b50700e80082251064000d003503c0d014180c05130044c00c215510310001350081e40c80942d15001031284400d000c00090041d202c0d0303000c0c41c2c00555400703459142a00d080c600720742c005000b820a540c0300215040c2c4159011080100f0b603a4107980b810b0f00c1c7e0506074003080203801368030003186c110b806040402030501800501054200c2454288001c180341c2d00005504803803040e549036400403401130081c00481e001d2240640c1040c80607000081100c03ea403a142e007207030840a0120001100100301c1024860319000c00480302100711000c200a040a6001808640050754000d014401d0f60b4009851140650b040d9110165010301307441d0140d01b0000700802d1181640901c4110004440200d081c2501c039100303909038079520124a07030490130342c078034501d104d07a030a0704 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 331965782 1250 331964532 331964579
    0x70302040b070602090f04051603022203060e25090b011b0309060914060a080702070e071205180a080c01020903070b040503190b04020904030e06070f0309120309 71
    0x800520700d440040200301c0300c0d0150400588850400d410080b04031458441c00b8480e90521090003503031003084441d00b00710180e50800594402c00003004100c0f0312008410702c10000c89c0000000144041a00641160384219094407003906004440406014500390a00c070b405415a00500003480c15500c5244040d105043c60051041c0201d410290021030b01801c0780061130107030b0100300300c13604801700c1c8002d0f043d004240103000c810700000c10482d000e61000031003001444030100d107111b402408150090031001d800d0480c10319242602130700003017071010b9542d2a6884d007400a01ca020b44c542d143d103010b040c110f0242c1419189900e60b21000c0d0095101000c507554204541c9296036801c0110b2030041c030005891640712032803d401c15003818074041c813a441150b110504240007900c8030340e04a5019a0455144200307449900701180c02d50003802004c0d8108030005410800d0140c524030004c50340d840b0b9601c000340c80c0e44035a10842c0c0b130210460300401081038890306004511014031500710800351303107 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 331967032 1250 331965782 331965787
    0x10501050d05060a0b0a081608190302190309030503030f1e0f0402190803040f080c0306101206060f031b210201230f041419090209041b02031201080d090608070302 72
    0xb02c80d01f504203035402001490100d2900020442800300b405002a80752000006035200c480c80e0310301a403a425034920700c0e076440040e043e00e41c2c105070094400401031504241181d441b45071140c0c482d046110180d9610003c5081c3e2003010b0f0f54034441c084800d1180c1961011402d80d52103590074050700145180103501d02030321580340420026000c00c0500700400c0d0030030100d550b20b4138240c400703400d00c28040710f02070007030300480100415000700700d080c4000c0700d542c0014a484860039050800c02846140c1059004203005400002442661001640e0007855400c0380203109540e0340d00320649410b070301e111412260034503045c0c0d00507600500b2420ba0140c98558041c3d80d079071610407002420742c0301c2034908a4842d00450203004010b055118601419000da03642810320100b00780c1c1010051407441041d550320380004503a042a100c0d50047d441301c00381c070010020031249040d0702a403039801800041c4100140300d000003c0000000a10034464041a200c600c0c446060890031078500c0e000624900526408 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 331968282 1250 331967032 331967039
    0xc03030318080a0e2701050118050409081b061909020d05010e0f12030906190f05040c05042306040203060102150405031207030c3e0f010501050d05060a0b0a 69
    0x700402c01c0301c146079a004000c541c0300e0204100c54904011843c5c039070a02e00031200051183d001d016043d240242441003d021141c100b001c80c00200b07400c119001414190000c0030004800d002d0b150200c161140c114807206045906550340600300d42c809144040300c12a061920081d600c2810b03000e0024041c00d510f0303405a200c442c01d441400341500d41c01d90100f0070804100c1014000c1c440c00c1c107192403495240d0709201075040c0d51480c000d030440b101041c00301406030080055512600100c200c1e408144103614160801d02a0150302c7c1c401c2038080c6041c840030381d181d0b00c6c1001e00d00ca5208008289100d0713940324dc0050000a400c001c0c181419482140003c1d40f240344605941c2c1c0c821071282004642c3d480f00c0f400e01c5106000e0240c4203800303041c01c148281500d03c0e00400c3c0c22020b00c03008060740b10407000c007002e41444000040f444172000044401089072911002c01d54079050340680c1f00a02c05641c0c1d40e01481180c180c0078001401c140c0000000c10510411900210505900107010084060b00d = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 331969532 1250 331968282 331968293
    0x1f060306051617040b06010f0302120a060501030b0103181401020702060c300d11090a080c1008060105030a0207060f0f020d050f07052215050c06060d0c03030318 71
    0x1010759000440ba004110070a1482d6800b4464421207845000031015500f000e50b00c104100c4006040035040c030900507400300d026840303607054031100b0031100b1258403613080408000b802000c96000e6a80000e0400d80300300c60650003802007240d804514194602c46552507100c0420907081040602d00315502004140c2c056500c02c4040d00030720348001c025128940d403503100181040da1940300441c1c0398200142c0560040824019201c1202e10501d000c00c41900e46c0e29041d06510665104603030040340d440c0d001c150703ca40091440702030003080c0d85040ea00d040d800c800343da13440e4048480711b000036020400514085900c0c0c000c0e003a17a620500b00482c1c10b10603812040251400d40401d06103045e8081401d03000540c3c2ca00996410400c080e40b035140318280034200610350310610140c4030742d401c041100752402d245107002020060000c5856441103403c80e45000f0300607809035180e030300b041c440c000c08182503203060495028100c2c0c1c07143d40b82820a29595055019090a0941b90598410b00000101088 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 331970782 1250 331969532 331969541
    0x2100216050f071e06050d2406050c120c120a030f180b07140306040c0c0c080102030106090f0819030c0b010e0a14040206030403030e030c150106080112051f060306 72
    0x190740540a05414101d4540c13204008803101042500340030b81c100012078020003201c9016a0390340c0c1c0890b041c191000180b512001e40641d041414503080704c0001c1c400c2c2d0260203007120100d420251140c80c654a507448200f8006d13180002d416411201032000001c80403c020f1400e0900781c00c02140414291041f1411150390500303200f41ca50350010701340200441400030315881000c50038901500d65410740c0e05085800000c04103070065542d4405007807503a009040d14414242d000d48028921610351962074080c0d01700380b04280104540c0c8401080c4800d08010340001d44054400518850b8200d414090401e9054003040e000d02143c0c08221000c50750210034180604044601c80c0740c281020f0206004030f80d5461b00100d00030b440c502c14040141d07112011690420342510b800b00759001d0545041d030942c45a003540907018400c001e02e0b403da517855941010304880341d5407518000c503070303852003654038040240d440101282c0ac84040c84801180c10030310031042ca425210001030080c0c03a40c0c3c45c41e0889 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 331972032 1250 331970782 331970803
    0x301060203030a0e2109120604050c1f080402010c03120c030b010801150e04090206270102010b090c120c0f0a050322021e031216051c0210021605 64
    0x5030800020864640c080f4003130403000c0c0800100804101d10b4084030007100401034406241402000036402041c2c1e65041c046401000041c82030318014106460080d9031000d920710b242d0b0160101513080c150108141c9242c0a000c800394840c001940c2d560740c011035550700300d81c504501f40a03000703081ca120440c0c0c0384200300d140c12003910b0004e0362001140014001c500141d0001014200c024808014154007544000c0010002e42d0040788640c041d00c0050258001c050100b414851002c0c1c3c0511141604001c80c07111003000c0c0c0080048420f10740602080200448860020b800200f0400240f80780a20720940e0014078107a103103041050b03003203854484d94004044070001640100c00d118001c01031404030005075034007400e40307400200c0b29404030b00c082d41504a4070009050304012036019442c2030210005418034401e1441c0d0b2507241508003554480210310aa510344100280e20360301140601c2c020042134255001071062400d01c00500000c0e60000d40c24148a40c00d40314907100042040006d003144 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 331973282 1250 331972032 331972037
    0x30c0303051e01030f06050108120703051308060f01150815010806030f1009030e0306062409040f061502010c0207120201050702060403060b0306240405250306080c030a11010f090b030106 82
    0x5e00c0311078240207064840680000440d9001458420350047c0090101c99a450349428000e441300c071044c2c1a4480c65409902503c2a401208100306140c1c0c410440d643c1038480c0004101d400b4080c50130111507654045400d90f94861000300365074003960086042c42d6000720020112800a000d407001d40e410900340031800c1031030580f41c4202070105130300b03d4544450075401b45c000700b48901d400d60000360302ca4854109000c0150301c46142c0300c60950f81070104c44e0b58802c0600103011139003070941e2030001440c09124801000345202010540c840c0706004a1035039040c90f50051001c58107006408414145614040741070107020009140180c890601810013035004441c00602c200c201e1040c5410004d0040042540d40e4004524410600302a42e0814920905550025041d501d510306082e01050f80c81e80f558031230604080d1144141c1d80747e0091400c3e2504142900c00d4450503a00f410f984022489004200400c0040001c4040d4032071640b100307001d01c0390724048001c295200455131851748281c000000 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 331974532 1250 331973282 331973303
    0x20c031c0c0906020a02100c03091a040f0605031b031503010f0209120312011e03061d010f02040f09020706180f05070b0a02150c0915041403030304030c0303051e0103 73
    0x1655040390650004105600141c404a0b40306d9000407007482c04c0c071542001313000840071307508141803003038461a01a000b59425040c503441801c290207000c0e040b41c07150344c143c4d016900300455102d1095064038080c4940701c0e14200007584007411413080f0340005007040c02101c2c2484800c040c50b5002d0081d10b4445801e110010303640d111583c28444034010038445010707994400c1100d1a01c821315110a1411581c404100c401d048450361035140c2c0300145540086c0201e4200f200a101d040800303a00000c50046c2900200892450100590140d001d244980c840031800300400700100c090300c9d0001d180142c0b0405000a040c4001400c42241c5c02c0e4502c2c5c180c4426184150f00c1081100c00c0011801030081c0c0440541402c2c4288002580c03180c0600550f680304c0c1004000c905442c0d01441910044c40004015503a1241d032412412071031703000b80c41069245555072171810300c5424003008590145400d50f0304d130064003549460640c0a400c010340008114401c46107040b10300e41c0030b1683e80780654410000d040 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 331975782 1250 331974532 331974551
    0x16060b031510050102030c0307060b03070b0d020c010b090105030a03141e041a07020616050a150b01090f0311010804080702030a0b060301141623030a0c1103040302090604020c031c 79
    0x18038141c10b43c000302d05552040210001880c030020556141035440800440c4172280c00700880c2c10082590f0000310001070100b0b800e543c044260300984109070314403001304030001c000c1040118901083c42245d406420042010011911071905480152040f6000501d0208240f08808020000700082e6035a0350005c6401c0c043c64410303240c1c2c060000d03440e070f560604111700ca4000440903c50707105081c0022040031900d00030070005200c03008002d40c201d24000d68800c00b6500480c041c204103400d1600042400703d000c40e01000402ea07210580c0c1e044060700344208200b034019242108094403e540482041c0f0860005070b42c2080380290f040d106006415490405006044c03c7d03504091548002005030300030400104c1115400d008079084518003102c0d0709007145c01904100c3d2060300d044450382e00000400200c030034242c00004002007507a49010114283c0b00c3c3c1c2949038000c070f0200a5002c840503010403042d290580280c440b0341c2d11001600d291800042c03a0100c684169580000e00b203480300b0302d82 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 331977032 1250 331975782 331975801
    0x2040f06091e05130b0d140601060921350a03050a020304120807030e0a06050103050d0c0c060e040609020a030b040f0605010804061109100915050f16060b0315 70
    0x10040b004401400080078107140002d0f1021031a110420589595803a1088040d543c0b80b1070b2804c03540c0c000305e449610942003103009450316424041c60300480c83c40440081c0c05200c400140c0724042255500e44844660b03503a440e140e0101000060943c114001e800300903e0041480d911a405110500075503034138001c400107419110010058842540f0500810000c5000034040c0c0d400c0c02118034000b110307695100401e40c010301451006024901c244084c0d00200300d21648007506a900400846030b281c0d40780501101c085203030b020003c01803900c01d1000c018060142a40d40030a220040011072038036155001030003284c0001c014040060303103c42095219052611070074007030807201344080c0445414180043d01398500641b00078007840c2e4581354869200c0c03004040c0c03030100d6801041d85044400c40b00000b04031941d1030284901300703903903040c00c01e540314047c108640203052040c18250a24001910b4000187c0081c0e20584429441c0c40c8038109550301030055440201d41d50400107c10704200908 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 331978282 1250 331977032 331977059
    0x2d06060b0403050309040507120207050102030f1807090b0a030f03050316050f0711060408060739150e0106080120030c03040b0c0c0a06050a0e0c0a170102040f0609 72
    0x105034005410030042c80800e0021085941410f8165004102a01d51540807110021240c4084032042d1022544004010040d0004d5010340000c50701a1000d1b1100319180f07100b442006000041540084400c00440f4915000302081c40401000c0d805030b82d0b0380b521a4121500c240904400065000040007080c841c85003890500d0486031610a0900b15180380c0ea00240c0305905014128054140c102e0209554500031a4040d120250030f0f21001d040100010f00100c0e4a01c08240001030300c15912260892602582c000050100f400303d00707028030540b41e00b01d600c20781007411110592995890b400b406001d01400000f05403010001403582d41202e41200b031003690140c00c604500c030800c01d0019101035103095030b404c0b03900481440d1250302d400c0d031400440d01c5842130403282401100052818040340b64041d500c5461900414030102d860300c121192502d210300d1049900c05002e540c20b001d135120030480414034801c0ea0703000520b07040c0c0380e03145148030400e240d01460004158900034028280329001 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 331979532 1250 331978282 331978289
    0x1a011e02071d092415040e030a090602100203090307060207060b100816110d030203060102151501090e040c060305151804050f15070c021305180c011b08072d0606 71
    0x441c11541c9690520110f000001707170080650b00141c3e21070700503ea407035500c6080122450400c40381d0300c0ca18000c3c0504045c0c1d0302c5c41070394003501031307540d21302c1d0104064000c407486043d0350702c007070b40c9800e0b1940c2d9000001d4004003016610195a4102c10140d0f4a8905007807024030f901d601c0d410400d280c034403c146c0c1c4915010305c000040018469201e9000c40c00019035910894807401e000d62a07a03201c80040345809078686070110041c20301c4042c4080580000412034000c1020303070300c06036001e442e280001002e01058074020107030703841c603582003090b144030394130407a00b069171200a00744452140c000240071188060462100e900300b241400104007081103488542d0006001910740300f000003a016916250045c10401880501c120000442d6507041c1e407070314107003140c0c0c1080100707003801d0400e0944000c000884110500c9117901080c41507004040d480e50792841d04800388080095962401d249401c1035030102c403011040003000016010f0224040c038414000d0802c0c03401c400c040d040940c1641c00590 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 331980782 1250 331979532 331979563
    0x9130606060c051507051303030e040506010504030b04150f09150b03070302031b060d020d09150e0304030f0c03021008160e060d020a0e0916031a011e02071d09 70
    0x42140c00022004a4940b00c140340c040e150700c0131551007070300542d1140b007461354441c6040d2080401004040e04a81201d4140c8003c2c0d1302001250f81e25001580e1a100b1404087d002080140000300082c820740c00301101d210303015102003061b900445031001991202c0c401181c0d14070000b0441c98404045118000f4a400d040b0020410185150003281d1190445064140c8280308000042d15075291802121200940760400310740d02d03100e0031404002010100790845070b5503202502540c3d1241c150144400e002000d2000d14900ba02c0e50303503030801c0113469080441398940d140d10008090f03903c600f10b522080600d5200c0305860320b003500301d0b400c0e075004140040040c046541015051900e4070015100c00b0700745c2c82070040e60b55101f03a8040e43c00e000d10700e60b001c5d40192040c0401040c1d8160511842020805807030074400e6902841001c100c0385102c120b00c80c001b41c2442c0400b0040b0a050348420b850b11101d0040d5944c2503115040148200c512481c2514240481d1701881005401080000c20502c09030 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 331982032 1250 331980782 331980797
    0x60e0d140910080c090a0611060702010606050a030e01060e0c04030308180c01030207060e070b13091406040b0613031110030902011e0201060b031305010c14120a0b0913060606 77
    0xc0000310300310902c081101c108580f620008070b58951100403140000c000401c002c900941d01c80c002090340408402a290074000c140100d09120700502400081c4c1e4800d0b02c0360381c20020440021801041003041060f169920703054001140417040c500a405500f43c00000343e41c850460a000c0e0000001526201c0c2134085084000d400c1ca9000c40c045040e20801d10700565030b0754107402e00a0142c1115860140c46001e4150300281c1001080d006010485501814001d82d907070341c0b603010b011a40c480889206000e484000120385240c20307881020a80d030000e05003402e10840c00c0b40700807000d1190704119030a02e03050b43c85040524210010120304203480c0381c28005a00b90b41e0000f0031000c807021071900000020726600240a000390081c0000e018400c076540c0d20303031502001080d080b649001c0103540175440c100b620030030300740324004041031209c15002a41c90a06620442c80138000e00078000c03202e280d950007030f40440d1740c0c5607118280102c0124020805694007420090120b0b00c01358040b4082c0550f0 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 331983282 1250 331982032 331982047
    0x2060c0406091203030209030f151501021b04090b070c0c1a0714030c030c010506090f0103020918011e0209041a01090513020c0a0302060405150f0121060e0d14 70
    0x2d203041581d250b109262084009443e081c0c010f8090741c40f100b981402050310003190290006103031a01c1d911700c4500c08070701da1212507840c140700c1c02000705540181c20070318010703140d4880b82865500300c810242002580c400641c440d031182c94000e903020400203043c88024401c4c010110703e200d0140620b010540400420310401841901c901c490080c0301100f25010320800260034025611804503d106071390752242c040780e14034002d1004503140e51190000030082030703c000000460700c1c103880d4050800d0015490705d14410b6801952070240c40499901d072680600c0403000c0401c1d80d054480f00c141c1c050b84404502040100761056517221910803018480c42a4003607911034107010031200e082c2c0e489000b01e100b40041402031310804142400034829040e41401f010750003d0054403541c0558240c07000c000c0d0300038003c1088042a600302c03031301501000c01406810480300d1b0440f2150034640d000c1542c0410356690707900b540d542403010003068001d00c4416034100e81060070541281c01401040b49410078 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 331984532 1250 331983282 331983287
    0x418030206060103022506090209010803040504060902031b13091a033a03020403020303040f0f060c0803180c1503100f08071707091107060605011121070c1502060c0406 74
    0x75044c41c2d46e9800c07410411384000340320386a805000038503000340c03100c01d0302c1da107500c010355807940940704850007244ac14400242106561080c0e03401142c106101720a552070142c1d65200381d07005100c140d80c2c1702c1c0e034001d00021058800c0c401d04840050804090034040610400c040c20820b00700e00c0700c0c401c00802040c2c0c0f0030745034042e8000c01100c82404042d282d8143c200030210003e004607000250180700008010030203c5802da0807008480340038114845164070f0f000102c9020755408001040d901c0184080341020003101e1150200e60324040c00c1b20044140100080c1c20301900300d0303440382500000002c1c4904280342001d181c028007032001005071854075043c410360f41c442c1030340700f101c0c42d50781141d40080d040e40090250310010880301700305200c11031102c8141c4619600c656000c036041c91802000158550051800d2046500046d0180c52004201c0703245800007100008020901e4400b00a10000507000a00d5030001d06616545010035440244010f032078101e018200c83e4041e841031004015a65 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 331985782 1250 331984532 331984567
    0x80c1302031b03130c170c060a02100b0609100314060a0e0f1b0304050312060109030206090405040309081609060e06060403110301060b1b0d140720041803020606010302 74
    0x400d8005095032a03558004d2003100030b2030b2031070090002d48140350000700c090100d030703a044d001a2204107541040f9100d8041040034402c1038191000350b04091b681c1040100305910181c840d01e00070b45440c3c5003680d000002030880e0300d100d48820109a0302e4248480041080320001d42c804415181c520340c0c1e41c1000d00001802c9001000541d9012442000525070041c0a6402c4c0e00c3e44050070000780c890405160150700ca40168142c010500b00c07980001302c5c6988078070604000c03a44c0140181d8680b10f00d484c00d2002402006200b5014030411100028501d10704000e50400c1c0038950021003c4142007081c0c003401e58440c2e0707100e80502080340d020300c0030070307628041245c0499510920780c803000d8000002107805803841e9071103010080c00205201c0788480721078a02c0303610500b034401520049044880142c541c8507505400000e2580240450301c00100d2000e02200a090381031400b03d207684044001500740e070441d48820003c0740b2103110003001c0580422140340c0210302400d003036017881182c01000b0721b40d1 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 331987032 1250 331985782 331985821
    0xa05090c030a080c01020405030a030906080709060903080a02281103060f160311190e030a03020709020901050d020304050c09010b030403080a050718081e01060302060409050402060d06080c130203 86
    0x5900003881c103034044d0f802d40c12940246005400d4500004031030030f0140400340701c0d2151901140c402c80001d901c55200b010704030243c59040e1244600581192103204554205c1046a011b61140c808c00ca0030784180486501054100c01c181060302941c2441c01040b481d5028846500030350066040c0b00c155440c3c210301940c02041a05c0c0c01c9030601c0130303500860152006200300c00495500299000340d204c1c8003c0c1100d0460769540394441d85c01000c0c2d042c10381c0c4407030a03034000d40184c01000c0305001d0906a44c00401c5204414900641082c19003803c074400c990081d9011600d65200c20069038040c03c01444007401441d0081410703086107072588005d48007180c0184080d00340c035a51000100310368095442e442000202001c0c20300101e07103036031801d9500e945801c0003081c3c203000b02d8001000f0071014040c00040d81d5010349200e0406150804c250050311016104980c0040180018054410b141c403410004101e01c10040038061062400d10080109200c050301e1018010002c021108603c03d03084000e4 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 331988282 1250 331987032 331987043
    0x90c0909070b04080a1e050a02040c1809061d0f0a0f1103070906020115050d060209011112070c060302070b27030408060f07090e011a1608030a05090c030a 68
    0x6544400d503450400015802c007484281d40070a0100b10301c000001e0b60541c0314414241d100e00110401211703260800805001020343c0d014124107001130600e600115050400303800c0940300a02040d082e80041582900240009551810304015445404810b580c007201089140c180500304101e90443d0340078020311904080c1d803200d8010905c00035907030041c0e142e04074103501a5101d0511041c004c203501090700c10800190700b8a4105819000c12411240465000400c842d009e0030381d0750744100180d00140710042c144000c41d0001905081c3c2400389940284450354541c0d81c52490f80751403d6655150381101c010140b042c400703180000c144200c030a80003c224100340b48405100c0c2d200d15060705c5e403013030200401c0c00301041c0000d21a000141c0b140c01104828065122903441c1c04c4101c0e1003030100e210718074010410000410182c03d82e001c0035800d8544c002e15462a12450f0300382c05d0140d240f000310444201300e0001c200014001d06114003604113040c0405404482c0c090800a55648000a00a0803 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 331989532 1250 331988282 331988299
    0xe0105240910030902040b1e0f19030b0f1003020105091c17040608060d0206030f090f011a01020609070501050f0f040302040c0201060503060a18030509011101051518090c 75
    0x4003408050155800004000c040e2292081a460020064081c0320303c202e000e039080c15040030f520b00c0c7c540d0f8414082c0c0d00300c000d108402000d000402042e50903411040c2d40003500d04031108928408203000c14055409241c0003041800e00032918030710781e0401480405001c48140c000d02c0140e90010880c1e10302801110b4142906445d0318031140c180c04050402442e008883c01d01c001c46c000140080e000700d03507443d00d58103aa81d540c13070140012503822070340007036020804000050015010400d1039400107030040c1154008240e1100c590700b12000020b5508501e1201c2c004e1517020741e030400056500c0340e080b1015000e024940380000e00503024040c0c000d035950001003444481022080165002103030002e005100c80407011201a00914181c0103443c001e000d0309001070811a000d000c2d0b4240da260b128a44e014052154600316160f4101c00101410082203413041e00c2181c4013406102c0c0681c100d180d04e810003071080c2c1700b0004d215602002c040c410003e040200891a417000c00c60160b102ca05607001e91 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 331990782 1250 331989532 331989589
    0x60106080735071107083c06040501090b1f14010c020d1214070503040905071b0b060a060c03140304021206040308060103060f0e13051905030705070e0105 68
    0x1215868100c020b034200c68101041000c49035021400429019225003965800e0781c46001a0741c44a403103548000300100c400320360990001d0310840c4a0010600660003001f4560600d082a0401e001640d00f5a0142c0d15040d458040c42007201e202c40d00000e942c6003440004104150b03d14040c8120b200700f05080c172169002280d9a4040ca0101940e642c0c02401d200000b205454550302d80402410300400182a0188101d6505004800c41d605150041300070341c01d01d8a00151140900f0008081c4030401141d50101c0d00403442d041d110645181c072600448049103000403d1003084c810326407250080041d00f9010401083d000508075404004009025549541c0da0010405a8007042080d0909115510420040c0340c0e01202460007008242c2e420300c0843c0c0d4880311080c40403c1405150309007184035010410501c1429402d6800d02c2c0b1032000d80300418079a012118110f0550003040d5400c1c1c02c000760403c20004c0074801c80004e401d81c0c40c0601c00c0e80d41040c1c04a0300c400400841c0b01c183d50750301188107 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 331992032 1250 331990782 331990847
    0x4020910080a0e0a08120108030a02120903070e090a02131e20030906091603120315030516050f04020703020606120106081204060f020718020d0b06030f0403020601060807 75
    0x182800c60003811105040290301e060107555201586010900d0340c6d00c00082413070305c03021085881d0020b0aa000380300d180024007201085d03a001019456040c424200001519400a11214422080390001c0c0c002e10715580140520040314240440495242400d01c108004442c5980d102c115108440054849071041080380d1441c0c1d20011032480010200801c8021000028124411340a507015100c801d820000281424040c0c0c2c0001041c0c3c4a00c4024841214801d40c00700c10040b00f030724060200559241c8078641070045401428841c0401742c00140401d0401e59800c2d050141c05580441c40d2402c5030718000d45506002c3c24a621036440030b0107103141803400350001c1d80038103040c1064600080c110f022190080e4801c5c409e4102142c0b200c0c1c466003e460020406001b1079a4041d8030fa40d03050190300f0141700035800310b103c440f801075852400f48401d80b00c1c48041d600c202052881801c060500d800d01030b1505405030b10503070402c0101c00400c48182d80c8100c4061a00040001440500c0818000c1 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 331993282 1250 331992032 331992041
    0x4230a1a07020d2d0807150b15041a0f07030c0203030705010f0b010807020d1202090a0f0b0702042f03070915021c0306081b0111070609031104020910080a 68
    0x650700040700603c49050001c800300d49922034001040c6111090484182d0b00c4075241800e1021308488018002c0d1800b01d07121a02e101c2d000100080009482c400c018001400a80041d50000110314085001c0c00507820b032103c04c104d0000740080301801c180d6078032184200ca2207040802020803020b484903030119241001034642c2150b01000a110745140c591903c8001d11402e01c8850018046030045a42d460010031304600740034080d41c0c0e0307581024840c02e503107000e0340c8081e0b92180c002ca1180c00c00544804440d1543d806003c3c03401855940344070500401c4250b803140ca1400d07150400038040c0b4001a120710a001005102e10400252640e680c4542910115115805a6044078038400d5241d45580d0202d2628111400c0609510021800301c0003101281d0550007420800d034418180d11452005503092400050814585403851445d5508528240107280d40450003048824209004104d10821030f042d4500b01a281107040c54240c90000b001181d50171038943c00d00000070b01041405072142c00 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 331994532 1250 331993282 331993297
    0x7110303040b040909050106050d050a060b0f040231050907140d181209060f0e211c020307120804021305180f0f0703241104230a1a 58
    0x103203c2c0c0f1281d4420020b005803c1c001821074840d483c240021825240250300c119003150020014881045140e0303c0c58010600d090a09510a200d00d0442c0c99683e2580001d00b2030700e01a0b400d06610103403007801114030230f06070000c041412240d180140019191092100e500c00c01c94609244880f9807080c41310041e102d00794154a10604000c0e001080e91920410201424802c00420302c4001d07140400300d840001c14010240000c401034400c0d0300c540c0c03290540100101004205103024102480c420071110840d0804001c0c61700b04c1c1302c03a0300041151a9448441d041240042c501c2c1c07507401c0c1d4036110000c440104101c00d0203c0d183c042030540d00c0d00c20891784104556601045a818000c118094100024444000504c2079910300840b00d00c01086e9800f100041c8402412503506680d20290111400c1881c10494020818141c115494500442d00c180c0401940303aa5220700304120010010404003942c104c09c1019090b149294440015403402c40741581080c00c240120b905c2000f615100703030398 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 331995782 1250 331994532 331994549
    0x210d0608010f060302130b06090f030f03030405151003050309280305100f0e060105040b01180e010501120b0114160515010e0711033004050a0309050d0203030711030304 74
    0x100301d00c0e0801c2c1c1d50b03000720141d034022a41d070344c0860f00d001c400384107841c007561750300360080c00600c401e15180c00c04039940c0401000c010244d0307030346000400810386560000c41e015544c036841222440c1c941198500300b1a00040000c80e10f1801900319292a40d4a00c2120705460045422a10340a5501c00910250264020180c400112160340e401c2c059901c0955801c070384c280d103250125545654400e48100000200d4100240c6070b10303803900c400c001c0180714044040781844040e48d0340740d00d065820501d11004d011040400c055075410800010302c803440bc100344a0403d4500750091880342e0b0403000b881d544101d481449640c414071a15908440c0b185888010114412000414051507441903240c6c142c500e02d800d072607426583c0000844565100301d0307503080305030410014802609440f2441a112503e1031a0100301c12100d0151120603440880c2c0944141e00099182400c02d540302d0201c80051008890702c480810705074000070f40302d10801c14000c01c0740104c0503000c2c200c2c1d00d00f442607400034041c09 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 331997032 1250 331995782 331995791
    0x1b030f0a1d031609180218060103021b0d02060a0b0f10020115090615030501061d06091806040516170a0f02030415050a0908190c0501020d02070311210d060801 70
    0xf02c4440b10881014000e410a050034034013501080c0e01c01c1040c0c2400b90ba002401c030380901100005442c101a40030740b80504041e020004442108134540036070841810740d40040100f00f805541c02410448080c01601d090703818841020340954400c2c292391a640c8003240c0c10706081450380c000b0303401000541110745d01c444c50048001a440b01c250301190483d2103443c441c40c03007002d110300b003107040760b400340182004901303001030090010303071949008400c903003020b0140341c83d04e003030240054810391000a03058822000e1008226040c201801481c3d003280a020b210415050000c10151050076003080f504041000e800000d042034490b03811a6489414402c400c560b02d040c941040405050460308003402c450400c3e0200d1200d013041e100da030088641100c903960801554100a5001400f010313840c00c00c21a0281e0040e0114800784000c3c100812012401039841c401c926003d844c600d020010f114691b0806184159202800d1a80c1413500b800440c249035501c2c03036184518001d1003d900300203065032a1 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 331998282 1250 331997032 331997053
    0x1603030b01030b120a0b0c0f0a050a030e011b030b0301140601121b0c02030708060f060409021909062c0c130b0307090e010509040210080601140706021b030f0a1d03 72
    0x42150038401b0701409451085640707103280881203108224031544008001c01225000510071009441400a1441e01013040440d4003d103509441050310310564007a03104219903074132501407041412600090b0000d001c005c50710780701558140c100610190510a010100055040141e40700e400e00c11581086440f070300720404801801050150000c82c060720410ba400705642030300047c071a1041490550180303284e40c80c0001c1c00050319040034204c0c0c1000305080601010350600040302c0c0500a20400004c0f210b140400c20001021026140400101c00f000e0080c1800d003101210342d4000403001449030744610007040110034580503800800c4913440401070040700e40e03020f80c00e1030854500c0c0740c1001142c0d803150300308a50400d0680d8000d40c0480a040c00400c3d050140c0150b541c040c0050600c4123000800c100e1620003588502c50440f41d040c0c0c0040c01c0c6a05802002181c10203c1440c0011810003940764601030461094155107810f01401001444030524030b10340300c200c3c55101600342c07000f104a = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 331999532 1250 331998282 331998319
    0x120a110a0305061302030d1803080f07051e010c1704020d0c08030703020f01060905090a0201081909080c0d0c0308040f110d080307020705030c01020723030706020709060b1603030b01030b 82
    0x86942c41203119001d1500d0f0501494491504231041c82c8581500c2c0905615550b244519175021400071106140148040310100d103003400a08542141081c5a213202040c12180e642141e0300302052000380300064210f0f00702c69a89000d032903881517054541501c2e6140a00305178022010340c0d4400380c154440019514200756010814044004041c0000d00006407504104426204106d86024480c5c1c0010b0342900507620400c41c00d44c1200f81030348503058501c151014030054400e80e030015036500e54002185040c80b40300304140004030718545802c40c0745507030580d001420007502820240213030400c098031030140b112103607a4450700c8900800c2c0000083c2c2506c1e1000c282e800844821025028040001581d1f0401044032200f9400c145c0c0500503050034852460000d03181040c0d40d00782c1c440c00300306200c0b943c1c074104402e1003d407207940c00824107a854040004280d84168018540d602c3c02840040c5401a24004c01c0242da0383c10b082c0820b43c0140d0400480044c101c0c1d403003d652101100614240555 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 332000782 1250 331999532 331999561
    0x2031e040516180501140114180a0605070b160912050c09070c0b10050f010f02120a09080d0207060c02040c050d09210e1c0203071a0a0e120a110a030506 67
    0x9440c01001c4c0140d80e83e80003d01005140c034100750f80411600c82c1445000c0e40c03c0001000001d02e6108070800c040200e80119040102c15000403000c0f441c0080c0c0c2c5414000d0600c1440d0f03008080d0351100d420902c0084000f07020802d18401c0c13940907044282c4200030800b09104450100340041c012890514205038002c0040c1c0c2c0800e030664043c01140040f0704400c041d01046015200c0c080d010f00d00401500d001110074164002c055000c50180c4074000403d60950703c000c2c00f481d80560307100340c009410701140c80c1c00e1241e00030512040d0741c0b002c1c4080089a4000c154010540c0d01240c000944202c08101544c0e10f110b41c840c20f2a00c40e15041c1d02038200304002000c41011444166640d410810100e0241c07241d03840d9022880c0d002c09094010b200c0503058080745c0342c0740d0744042c1c140c4080c141e031484103e041c0c20422004194a000100c1c0c1e8440710381d031284480c4c82078030381207801440300000c00b103140d902c551072068080c001e4110504510758a03140c07501160019035000d011121180b502840c20700550 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 332002032 1250 332000782 332000819
    0x20f101112070309050103090201020618070e1f05032803030204090c0c030206070c03052203080c010e011a060307080c0c0a0f151407050c01180f050f0102031e040516 73
    0x40041303801080d154440d1181900c2d00b903040c2c00414607a103585850900e0300d008510408050701c0742140100f19101d04014150040034809091041d1b0748846490540056054000d24000d51012407410000380702c54030052400e03152800d0440440e489400c007140a48a07a8019800050610b40c0401042e03501c440c0080303515000350300b40d4403c0d48464030308503103000c0c4094000d800503c0601084956a104001e0480e000d048840040d104540c2c0e40c0e40c91401d90040c000c2005203075910100040100001c1c010018100e00100f2404040c00c0c0400004100e80009403051040044440010308d0a032050000c8482402c42c42040391006209840c100e00203042d03000f021260100d042e04001c1d0749420fa070154042c1c12022031900d0401d0703910742030115560b030825808034140d50748070100c00c10080040d42e0011905402503c00c102c0407001c42c02c0982c68180d94821900842e03104104000303c011701c10144900c0d25440024000b4980c4850910a01d0812600b5002003030190800e40000c494040c0890b541d5007 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 332003282 1250 332002032 332002037
    0x206160302031b16094808070c0803040c030b010b070507050a030206040e07020a08030a1d0c010914210607140717030a0f0504030201050117010504020f1011120703 72
    0x9401c0044070264403504e00500310b0340724964410f4180301144c21600710354503000014100d48075221660050340c0d0a03154039030b001400002d0401d00b1282c8402040c0c00c0d0b480081b500c0c14105810b0411a10003020030728095805040e0380c802001080401c0121480344001310307003203110790510b56103138840903440340e018410031100c6105070440011241007a030882ca044940041c0218282440c1c005c40b0f101000000307043c5030840c0107008102c40020306040c060350052034201800a40b06001e21b0009480c074490b840c40e11800d9108035400326441ea8083d0355035055400045d0460078100d511008100140300c031000e2801606000d110004da00b020004150f07114000aa68148080c40c12500c902281d1147c441c000d8a10000d581d0070010090143d00110b80000a207030f40000e03035941c0d0700c52030421149d0568003100143d440d0801040b5441c540c0142880d29041c0800170040c0d1300301a1f0006080036440060107000d450a002c2c0656601d00511000c450140d0008c10b844684204000700640f9620401c1c00300c01 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 332004532 1250 332003282 332003317
    0x30e010b0103090503030105060a050f03070c0b06010201052512020c0f060c031003082503030f11091c020d0813050a09020406021e07080f01062d03030309020616030203 74
    0x540c40b0340140145240c2241c00f4500c0c503400e12050200a038007428120301405010050101400031050040d4412410380c3d841c0119180c003440c0501d0054006440e071811681020b040c00746802200c0801903d0301140303081c40411519084003607507060720351200c0000051001c6080c04003441d02090005070017007008140d84055445200084441c04140c0e4850010b40c00440188005503c81e03000b02060391903502c6810099038940100201004ca6450440000e0f0311046208008103031401005c28180c503050700c140c1800c2ca0507012840b210107050007094091040c41188040d0b46070308500c02c90941d04202c0b070300c1d650f80c210112180c00c110300384101c3c0d01601600c8000100d108a501c281c3d420b0f20a20350182085444c3ca0811158440080002010f01d000b114030000b01c055007040303038080b1803180c0800416020f00e01900318605105402803802d5001064110344ca51000103012502625458140000d2100130381c00400d240b40078203003244496180c405007038018150004058020b070803400131203030f8 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 332005782 1250 332004532 332004551
    0x40f05150105042612040308070b010503190803100302120d0f020c010c030c05120d150b0c060112060603080a120f090209061c1728020a0b09150106030e01 68
    0x403001d115502c00d041442e20703e01409260800c2c07134a4580052000c3c0300480340130b03c00c05c00d000b000d031382e001f070340b0460703988200203021010881c0280700708d40180702c1140588110700400000c1022183c1030a00140070f80f80000024600103044001d14000e590040d08424030103006006544e81e5001d00410140410300420000c0300d8584006041c0c1100481a50b5549582c035241d90281d4401c0418001240c407405009100303201c0c071846402501540e407941d0703000305105041c0212094100101d070480090f1170350402041d045840c00041d0541111507420f003004030b02c45e803030038040d004001c0703900010031800c2c00081c8985c600345d00051040e0002130a500800042c4501c14849044482c0d200009400c600d04600148541c03500b1804c1406409416100d910105010f43c0c856071100002c1d1281e103200e101c08241030f641041e504032030781400003c4441c03040410a41d400302075074030b40d0074201c014a88480200022207074039080c0420b07100e03511006090010365841d02e0022b40a00030700301d021031303181d0302e041d4a00 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 332007032 1250 332005782 332005787
    0x6020709020f1b2505010e0d050307020d0605070306060216030327030804030c120b07110c0405090a0c062109032619060e060909071a030601021b06030a1a040f051501 73
    0x50032903170161030f540c5c2950400c1061190b020fa00a0003600e480c0003e00030b070005030300c54080c203401c3c0ea0301c5503d00080310b140c442c0700681103807441d400400c115803101c020b42c4988102e0100c0c10342541d4150070007400d81d00119010840c1c103098040d10140660000b000001080603000c00340060704d110304400310132991150303034083e11000c140b00050302ca01d01c00c40c00b140006004400b101590000c2c2c01c25104c400c11140d0200d001d4030720580703011280394030000821040c00104050440a4022844d14403014000301d03410706116450003044c9a141a9142c10b001c0405003e000b4030424041c0111680e03004c5440714a100808101c12640100c111000050300c00440455102d1103056840d0100369800d03a443d00018040d4040005040801920496001141a41010006c00260b590b24110a41c1e01e24161000a0900800e81d40c40c1110f0381682120845969030801500d61201c0030407000119500b2110110f44540c260800044e003051a0442e50003247c0900c0d040544100601000700800d800140e004 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 332008282 1250 332007032 332007103
    0xa0b070321050915151c0501110304021e0604180f0b031f151a03070f0801050a0501230310050a14010e01110102131d06040606020709020f1b 62
    0x52012500100c1d1901800183c0041d80ca80003001c840a0340d9082c5c003580003254904000640d41c241c043c000c85102c90410000f402800c03c0c0c400780f58405815800d05902240341d082204020400c070301030140d441d11064a4820680740140340c204001c0c50204154001040200031480703500845905000c00b000e0319080000306948140140c00100c190703c050034200303800a11520032503490118006100081c030444045054520b0000d00c80f4450b41d80c05c1c000350140440421040d103401f0b0084140c01001244d81c1c0d401c4420840d034081c00c00405100c031540c0c4c00b1541040b1541200540c00020080c000300001c1c20f01c4e0b031001c0d9002650078886981d1941f84410418040440780b40c00074400d95070854007540301d90010100111994009802c1c15a40d807582c8001d0012500f12443c120072078010b807050f04500c441402e030800c2d01a43c0801299003060002501c502160142600300c0d03800149600c0c1015201d41120b4850091034507803807041c0d2001d04103c0e01d50407511100ca00c220f001002410320488072071308 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 332009532 1250 332008282 332008291
    0x1b0102060a0f0603051c020d080108060711030909070206010510021b06210a1509050411100c1406040b01060219060911040207061410230a0b07032105 66
    0x20400e55940010410107098030780e51000d0b0b0385450b20b0340040000c0c5c08000303240313a9001b4460300944840c0401c0000340b60081100380001044090001040f201201107802078202d1480c1c6401030b200c106680c0d00f81d04e140b082181c46904100f10300c0401c480300c0d501140250580318101c81c0c801040c3c4051384200e0359180501d4030741038240c0642c1f0f20f038404c40c6030220041034080700e542c160508030208140f80100070101294090003690300c5504601104030041025070240c8004107041000d4103250301e540380108402400c85024903600c58807031039444e018050140d0b40399442186035032007248500a50f900c40500f0f44007298213480401c00450307042d0002c10318404102d0400340c6005041099180c80303014004403007050700c1d105600c26041e0381549132030008001c0f6500440022aa01c840f2010b0741350549002851010800810041809101c2101e01c2c06960b2090800045142000410005d04410065884a08807481c0001c2680400d0b400840ea400820300e001c09551002a0300b506a8068074004c54 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 332010782 1250 332009532 332009537
    0x1110a0506010905100e012d031101032004080709050631020d020c03191e050702030c0d1a0604090c091a03060a02280801120302010e120306031b01 65
    0x14014072104a05904c1103500c003102c2ca4040500d01e030ba684658814140a030806c80072242c2802c3d01c605800e64070290010b03860300309200c0303401061840d00c9a08000c6140000c1904054031034a00c107442d01152048014905c800540555586d5625198203036210214030454041509160000b0450700e000c003141c9400d9800103803001c5d12590106140501c3e44604503441241690a01011980c1c1c4128405440030720300c1480215503d034084000440d1012110201e01d08010b5030415642d1680c203400c950040260045c24600c0d10f5000c6031000a04107030b1181d02e202d400100344a50a8144a80c2c0740c034008000e11221284510360700c6000c10300090740c0000030094244045030100700220700180d40303d821100152030f40704c5202921400003d08064065610f074170480c0d00411401100400075020241d2001305440c550440103082001401c85001442084042500001c012081c0b500030741024540310604004e03183c90900451461801c1d800c01c1d01c003036004e88119110780c00800e0220b10134501c0d51304140c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 332012032 1250 332010782 332010793
    0x305011a09070f02010f0c0f020c09160c03030209030f070513020901080402010804050a061a01090b0c12221d0c090d06050a150815100303120c0c021e01110a05 70
    0x1104281e5000f4070081c0e0000c00c642da01d10700401c840030301d071160180ca400684c0d10790741e40080854000b407402c0e80e00041c040c4030389440c80a0100003968200514410441e60405d01c8031645141030580090041c02d81040c0c040c021000d1900c840b2101203401d000f5540704803044094a807940e5805e01c100d00809a9540c045808000410050b6003ea072406900c40c0c07161086450b1119990f86003000c0d160308502c0111240c82d01207000c03881c3d68103c1d10560160808444140c1001c09a0207116a01d111024054401042c005031401c0580410b00032048400d40300703001c510606a03a25031684005a490404c45489980c03003010502c4154040200c420440c8010400e070180c1d005030301c441c1c000f1715001e481400c50359511410b00081c0c41d20381d8583c0c4c004165100c040c00c032950007100202c40010008010610005081c4800d00001360011201c40284842c0300000820740e10341041500c00c003e00303800186d80b00729030007403038820440d01c40304000c0c504600713a8a401000f007007907116a0343d130b0503c043c00401c0354011 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 332013282 1250 332012032 332012041
    0x406180b04030f02040e1c0e0607030e210708031804111c1d0c03010e0604050a0b04060b060c0c04060e011a0705100c02100507080c220801020c070305011a09 69
    0x85207010b0f03030074002030001408501149080c1c0c84c1885142d40144075110103e100d1081c1ca0300004082ca00d107000395107280c500482035034001c11040a002c0d002c2d1194551540d0030012513041c00001c002281c0140850b181d043d140c210490b81c03908856010b40003440f000301d8024941c10035004a80d9000101d41c03160381070496808004043d0310846401010047e030360510000c0c3c0456601d024940c05000c04054131403007400100381400c5d61410b0004048070f5004100f400f00085000440303000850300103e01e00d42a44483c902100a004c6691041d64031000110303102c26202c4001c5584107400100301c0d02000065654600800704d50001d100d03010020010f01d04002c01c0e82d031400b0040054030f1107402607a8807681451150002c0310780c2ca1030200010703031014522020034403030380c401c1640041485c240490a0300d88039420a42511a079a07500d0240c14202502690510042e455407020f040d1890003075481d00803003060725030b507a1158802a1025800c05041d4000c0301170800c40c10031a040d001c1c212051941e1b5 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 332014388 1106 332013282 332013293
    0x1211030706030b360709091112090c03101121010f080c030c01050a0c0f05251208070f0b010321030c080109051b07080406180b0403 58
    0x3002d095030208000344a00c03520203c080d52413051100c0d03039400c00c200c903003801d0707039000340d243e0f5041103044507000b05080043c00340080002c2c1000362603502c1c001c0142d42c6840000040f40c064212341c2d8000042040e030b80080080224221a09241103c1969904455982d0a040c203000114020040c07028040d1040c509000f03240e0300c0300070041c140301140080e0305c0714402181c0f54180b181c005a480c40c0d2500980d1a20340091304489000c80d050200e04100340c4580b0b448040318110340d0b031039001c03d011511500c0c3d41410f85c1c110010400100405035102042c0e88c2c0400c1013075401050508151002400705000d99002e54031401510741002106c05290401001d61038108080c1424110a0b0600300c0d4051403045c11650f404a000c640e60b200c0c10760707020464001400b00c2c1c0f0184030007e0f10500b8002d81c0d500400c115043ca6403003445800c050042244408001c0c001c003145628200006c00c0881c1 = true := by decide +kernel

theorem cover : BRFrame.Cov 331834532 332014388 := by
  have h0 := BRFrame.cov_init 331834532
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331834532 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331834532 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331834532 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331834532 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331834532 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331834532 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331834532 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331834532 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331834532 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331834532 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331834532 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331834532 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331834532 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331834532 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331834532 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331834532 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331834532 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331834532 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331834532 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331834532 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331834532 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331834532 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331834532 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331834532 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331834532 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331834532 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331834532 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331834532 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331834532 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331834532 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331834532 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331834532 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331834532 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331834532 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331834532 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331834532 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331834532 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331834532 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331834532 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331834532 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331834532 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331834532 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331834532 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331834532 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331834532 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331834532 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331834532 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331834532 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331834532 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331834532 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331834532 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331834532 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331834532 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331834532 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331834532 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331834532 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331834532 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331834532 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331834532 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331834532 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331834532 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331834532 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331834532 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331834532 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331834532 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331834532 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331834532 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331834532 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331834532 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331834532 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331834532 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331834532 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331834532 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331834532 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331834532 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331834532 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331834532 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331834532 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331834532 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331834532 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331834532 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331834532 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331834532 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331834532 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331834532 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331834532 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331834532 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331834532 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331834532 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331834532 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331834532 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331834532 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331834532 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331834532 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331834532 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331834532 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331834532 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331834532 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331834532 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331834532 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331834532 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331834532 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331834532 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331834532 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331834532 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331834532 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331834532 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331834532 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331834532 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331834532 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331834532 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331834532 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331834532 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331834532 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331834532 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331834532 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331834532 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331834532 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331834532 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331834532 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331834532 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331834532 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331834532 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331834532 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331834532 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331834532 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331834532 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331834532 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331834532 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331834532 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331834532 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331834532 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331834532 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331834532 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331834532 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331834532 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331834532 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331834532 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331834532 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331834532 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331834532 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331834532 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331834532 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331834532 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 331834532 ≤ n) (h2 : n < 332014388) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
