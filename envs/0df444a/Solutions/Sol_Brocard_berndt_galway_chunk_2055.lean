-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2055
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:32:45.280985+00:00
-- url     : https://prove2.me/submissions/6954c288-71be-49fa-895e-8794222e3695

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 369424460 ≤ n < 369604316 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 369425710 1250 369424460 369424487
    0x10090f050a0b070311091008072003131a03010e0709050a1404270305032505043011150309070501110303070c1410020412050c041506140d020406 64
    0xf0b25042c40030b003114105c0d000303581c490100100040014000208151003600f0010105820010070704011030b07120014456006000320403000841e250586c136154842c040074140c20141c42444200010101c0102201c200ca06480804c0f00c0304046890320755056031603c1c0541c1080c3e9001d034520501041c9000d00c1e0040c6080e07000100d1301403001030714011000c1032040c400342e03880c0000040e408800c00428012001150481c0444030151002081080302081d6001c1d08a030110028400103020800d00d0005951009080d00000c20284144e82a0201c409101090200244011140c0c58400050741d00c1d043d5140900c2c8000d040d45030f0302c2c6020000283c81d8503440c000e0a010842c05006010105000800d40b032285289858040c014081074a841c1e400c0611803695600e58450100018404903071070000d04003c100307400702414192581d01c1d00034105064103040c41c0c051450024112210714132980b1035400c690f040c0c1420014480500a41c824910a0102181201d8000a0000b48a541c484c98940200 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 369426960 1250 369425710 369425717
    0x50d05150a14070804030206160e15070302061b07110f030d020c0a0902070809120f1504030e120c011101020705190c0e070816030b1003050103060b0f0310090f050a0b07 74
    0x143d69a18040ea601c030320694000c0c00582c4800001000c6201d050701490070300c07a81d13080030b02003622a94000360500c081c0e058941503845001c03903158101501003000c1c80d082035129000f80d040c4d0700c0c02864450300f4018180702178050b141c8441020304035280c1e41c124840e42d64000c3c0540d8050138a40c1c40103542c0341302b0405181d005100c54100020300741442d1003078807500d9510542d0036280001803410009240d1556400140f14040c00900c030752200000c0140322542c0229001c15a00c901e41810003400c408c0d800b811103405400c1e01210f1a034040310200e08a01111400d0138100b4003810382026450090060000c020080c0c8a51442c92008c58120700410800e20f200c2c1c0f24002c9210f07110707490300f0402c000039240480458507180c0828510075134101c603110460080c2c50001184a580f1000071030980031070241c280420382d1500140180b01260140f40d040321829100c0304001c0714130703070b0120365101c0c038020212041e0303903031a1348100c100000c140c00010010b40000c22100b00d40b599003481c1040c204245e0b140b1011 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 369428210 1250 369426960 369427001
    0x31b0316090801090b011401110703060507080705040e13031b05010605030c01020a0308010605030903071205070510061d18030324030705010806010302180316030203071a04050d05150a 81
    0x4000b4140903111032660300501110fa5070f4a85000303c0000541015214144404030003600a007c4040040320003d43c040e900210b91401c085102902c1407601030817a908006082000307002c4140014005a0840b5414a030f00036462028141114030a6080700210507c070781c0c040680b02400303015004501580c0c0700b10191040b010310306005a94440d80804002c001c80c0400e0010043c10f8000c00107182c1c40301c000404c1d80d00c0e240a0759941c0103c002e80c80d0029011035800300382c0b80f00f0310000b048281001c0300035a030700b000228200030400d10810358206050360340100b01300c00182005040b2040528001074002140c2d01e9040c00400c0c0240203240f52420300c002e00b10881103003d5403070005040720481e10182c41305140760311082d00440c06507012100d001d4860300c0c0102c0f402c03901d450822a080b8011820500908820308501c105410801c482c0d003c00081c1d00a440d00142c4c0c0c09a00302207800302c07142228003504064481c0fa1060919000c480d03a420030a0350074041220b64041900094000c0b0b0300f07500541c60 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 369429460 1250 369428210 369428219
    0x50a0212220902090a050909120712020d08040c090209010c1514160f030902010e1008091e060a20031e06040516050901180909030206012108031b031609 67
    0x490103212130309a8016010003040015003055502c440d0001d04900945480c104000025141070707004010482d0b2140703120039035895050703060140481c0070f00503203080c0c0704c0381c101500c80c0c5842c0b040900030054565070000f4004074507801795501c8100213500c68405040780321509150b1000b00103194004400c00c04140c0040c1030350a952030084002841600c3d038036083c440200044005000c1208101d0521104a0503240f140ea10700080b01941030a9a07220711551030301c1a806418519800003024001520802e190700907000070078080d502113985880010603501a8000d900c050f18664040c4c1c40c540d0b4008144041c03042198890000d441e41900300003002e44410090200700c60045420b07a04245040004521139031044000f02440407051400c40b822144030310082968400c5c3d5400b40d0700c080d03070b0307000c0141c101501440160f00400034500c4030020101000310721208550411070043c1841c00c000005440300440900e00d28200b80c0d40290680c07246000200d03901c080341002c800d00d021501803200042d = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 369430710 1250 369429460 369429479
    0x11401050f0a0c020103060302030604060b10020c01021f1409010507030b090c0904200f0304050d080405030a030e070f06020a05010f021806160b041a160f050a021222 73
    0x8030850020001c1500d414000c8030700320341d980c80c10f51040341003640728480003015030360400485000b24001d500010314001c09808006420f002c600a400170342d0071a41c18190641e80201d00c0c1460305801380c0031050f91185161301480240300c91038140f1010500d075020300032203c00c1540f0661040e08142c60030042190314100b04080c0410032100c010b0605010029410309042c0b40e0000f51030f426074524403141c050048a101501604405003003000504c5c040208824000c04220030a542100c0b4148102d990800d5242c0c1910791140b00c2000c1e0515071074100000c50352108200e034070010500c515041d4401a103404009440342e403114070649441d0700309030110b40c010381503108070750071050403420f800c0307541c101d55040c0101600428401e40000c212700104d900460000107869105034800d01712221060b09030200d03405940700191900d48455559507a0343d90040d04120160032103841803c002e51a9204488224030b004858010a95050804185080d0101c20398001c20b0003620300c5c1076100001604da54941 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 369431960 1250 369430710 369430717
    0x61701050931080412111e0603040507030f0f02040f06060503150303120c190305162d1809020c150601090e09070302120606010c0201030c021006030b01140105 70
    0x10b1800b514890b15004095021001d030420891900404410780c252903120300966400552103080341c04070740a0480d003013140c11020b454106104071001c03200014030100000c112200400854043c26001010800342308040000324003e6030300c0080789101d100b56191018050100319002c0380118142100403035820300364043d520035030708113907035207411907403100341403000c0c604000c45554060208000c40c2c2c1e21102258511446410300c01c1449030789220f101040c2c085010b00030410800c0529020a000e4403070310801599010108516081507118184500b200001248920007442c030502c565000c0e034181c0e088003402e082004802400c000c42a9111028030507481520394404080d0400c10b60291401d030b00200307942d0004410300d40ac1c1c0005032181085045060142c92601c030591141008000714902000d031500040100c501800c502e061000000e0985a18240002d040c15160b01034003650074400c00c03100400e01d0b1340358024040726a42e0300340304682a000303008500c0b07001d07011100414a540924200e = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 369433210 1250 369431960 369431971
    0x61409030c01050a210c020c0d031215120b090c0f06030c071403070c0f0b090d0b0a02090d030903061a0105040b0a030b1e01080106030614060f12010617010509 70
    0x41d00e02401c1840c0111030543c00302281406100025a01d10040481845504900d107951200003440613100c160291510072050103540c0704a608003c15070000358005142501d040080c040454201042800852602c8568004074024603544d88218180100d1101090082d0f41003003c0e2603456043c102408042160039034680d421a40c204040b031504000d0742c00400035140100c00100c121801086110300390352040005442d8000f8070b40051154030304801861009007440d428151420385042c0202d04c40c454003803000b1305a001030100080c201100c1e501180c5080100a21000040c0190b1034007404074500ea01060303079070303919040d101c40d00d4100380405100090b0b01611071030308292801e64180340c542d00c1014103034100f584541400000d5201e07240030318516259220742c807403000507680004005190503480a401c050503d501041749009010004003007010a0700d85941d40c803440c2c85054001d22503803031076501000300300c400010481d45c401a1003a800d070f4200001d5226903a200100042c1400035a403 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 369434460 1250 369433210 369433213
    0x60a08030721232a0a0b0907080703030c060f0209010c150603060f06090e060f130302070305070312030b0a0605040902070f020909060103020315070509120a050607020607110718020a05070501090c06140903 90
    0x20444041804e00d41c6060340a4108400c540c022602c0d2703014642084400c0d801100400d50704000e0b1010400903001d128140c007120001141032525401c0001c2401040c181c024002401c2410303840090255038002c070014507000303802482498651112500242000e100302d001d810700e4141224485400407807498001d2440c9410121551101041640c1c910b0744c00000f20294402e0050000c001340c0c051044030015801204001d04520784070780d019042d01d5842170394034400d096040083c01481c0d00502aa8190b400d0481c00503154070361407030718403820442d0000280d440030140c02003118070200000c041c1e05a03842903081e02e40300d642800700380000041c282c035170f400404c0040c03001ea005400c0c603c901c40b0070b1604e0780c000c0b140c0300c8a01d503d9580c24030405865901c010f0b0442010001707a0380d00010b10140000107040104030262070803804151411004100b19a0b40d42c00084080c0954451400c2d290f129030050000c118401c00b80c9400c84030a071032803098201103400030400c42d100a840c0000c0e02c005910140 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 369435710 1250 369434460 369434473
    0x50c06031e040302160e090703030f05090a0b0d270b0703110a020705041107150203090309030f010e0c01080f040201030e011e05060a08030721232a 65
    0x410029030002000410512282030301001c03000100c400240c01180613401038070800c07109000d0000c103240d69400caa07802c00045002e01204c410300040310300c00c03039825140c4802076008520080350a0b01c1400d032030b281c1c40b800715980401c01f01d442c04018a00b0301030001d010030013000307070940c1076401104a40100101c14030138044a400b040316892800d0b480802450700190f940248404001d17182c001d44c0e416401a4400e05081c0004d003843e10442041c071212907001802c1842c0c3d42e6030030102a40601d5070729502600400410480d96081080c0c2d00310107402000d443c5104030441c0180d000303200d02042c0c03103094440c000c1b80002650245030142d0040c00c250070203601d03507600c580056014041411120400e0766a640114070340c0400501920102800c04601081e181481d400300b110f60b15007034000c090a0340040009500042c3c44c240200b003111400000c038004404050810f498408058141030500b01ca085100b8200000c0c18009040d0b60410b02282e80030040740d080b03151840c2c240f4003a00712031903001d030 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 369436960 1250 369435710 369435733
    0x102030f090d320309030c010c2603090105011a0405040513080d0c090e06060928031406070306230a0f06110d08060a0b0a02032205030d0c05 62
    0x1500401c56104081d2940c0e107250565500c1030325115108911511003200d003281008034156005241d4510400b02005500b401442d40000e0b4035044070350a0581800320200c60f01e000c1081c00680c0300796280a2101c0c40c2d0000c8444a000000340d80700302c4d0841c080f94a400004151180c0c2000c411010055031044a82082c1c00c0c041030000414002d0307c00b0f0040e0051203056000604800020714602d50741040c042042900140003910009079504142090001001003120507103c5105407045072404603200c20101351411003109550202620804803140d484034044240041ca0701802100c42400f41143c080b9601d4441c1203046510324004c20303284802d0890101144844004c040400c0c035802800040155a031b403070700704400b500f0b981c0408041350030280c0300e02d0181814090b0140a0519040804091038101c00042031203002d801214a4000c02084c41c0c26000d2080080d01c7c0ca82c0b01d8070078100503c0c05002d9039100100811310843d8807071f00c1441b014422062241d8200e01d40c0543c014001d00041440 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 369438210 1250 369436960 369436987
    0x90804030b071e090609080a0f0f03051b0703171e0309010b061803010518030301120f200307092304022403061306031e030216060806090106020c010203 67
    0x7a05020030820b42964a00303d0440341c0014401e8200a80c940081d02440d100b0040c000da011507000581c9a084524103074042019800380b41d00302640300c1c001208000c1e40d89410b85182c011224500c6a070500090006894040081d404055901600b2960010704090552241d42d10400e2126403820240360400318001360702c030f4061a0800f0846002040c05e492590102c1c0e59904540034500141401e101031f240603080c28071889030080768807403034201124880c41b1003d0785c2e4031040c450313024800b81109285090006140e8804143c56108a2030b648030284150444005080323000c00340e2090061640009850748248201c0d15912840544408030308442c1030000c0350420020400d0380c010001400540700a10000c1c080c4c01d9191050218544a00704801402581c0800745034503840c3d41e10b0090b0a201064180d00300c40d482c1120740c0e190520205051400301e003004406101e81c01d403401101c002140d660b030843c84851040c0000d6401c0c50242c3e0380e82804030b82d03841071010481c1c0982c004000c0842c04601 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 369439460 1250 369438210 369438233
    0x50316020102010b1917010608071502070e04060902010215060a2105150f1005011704031e020c120601060f0c08070510050402190807170109020603131509080403 71
    0x14000003510a0303260001c204803171007050b01d0040007119001c0c02d0200d045c0125032598240d440306d000304161414107030141d03036841c214001d80d40168032002c02d60380c2c0300d071082140d08050000b911800540d402e00b850311402178400402d08034054010280024081843c2c00801403050b80010160b9112515003c040049507103103610019051000b210440045001000110341410b42c260b5030204d40d282c8503004910b03002001d440c00b042c80301d0595080009a903c500040005c080d40390209040ea1950b2800b40c0e8040d000780680901480814280d500c3c060b00440c10340055801030712020800344c1c01c80710f02901d0300c0c800d009450200d03510101040d00248142640c407541c0b480740d40d130185005102e4541516001001142c20901e40d150b00801045041255441c003400c0402c05071199090304041850751144c1560040072514010072704200096282500a1784140e034020702456a00e0605c4d0828440503205008207a07868006111019054a082c0c4580404c690700b088800781041d06566070b450984a = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 369440710 1250 369439460 369439463
    0x80904020706020d380607030311130305030d060b0c061308131e0803130e0919080d0b03060118020901030e1603140706050f0912070f03050712050316 66
    0x16401d01504a00030400d12460660000100d9035001880c02280020118640213100c0740b850100b60705e24044544401064841c0f40340e06003004075100225111414072409144000e0300e10031b08a100010a128020006000c00c00300074105000403505ca1041c1c0c031039840350085203042075204070000381220710310b0101c8a440074031844030a0300d840380218840180c0c144d02d07048000042104030740c2424900311ba000328001894408040d60804590724200500441305124503582e20301c008000a85046052007525814465a0f5100854011030f04145403190000210b500e1304511305540f2031424500042c109048410701c14a8000780b40c540ca481e84084d40081401030306264482c0007148002c7c04c14017043c0d8060700c12800d0581c0e40d514609180c1080e65015140f01703400c6e04200300902403030394050111454510084089a038407040e210100302441d03040042070519008542d40800d0840b0100380d020112030080c01110030064844440c2c090318214410000c106600c10005540e0784a80101c00b9040c19 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 369441960 1250 369440710 369440723
    0x90e0d12020706180b07021e0607030b03070801020f03010e1b04060f120203040308040510020414120f03040605040609080c0d0209060d020a120209010f05010c0b100b16140a0809040207 81
    0x4080004d02410000c1a80e901150901d4a481c01c2141643e810402d0302c006880114103c8010100c1d40d810640303502025000c03404254941c0082c55154504100400041843c40c0c0215902ca900c09a050100d030001c0c002d840344034450340d0220310307071003004400c204042d1812542d0b5460540780c480251090982e004180080c0f090080b0351a55204061010354810f6001c1d403502007140c07519103810342c2010000414118583d205000c140031f58080040002c0443d202076038400145015148958a04244101e1511062100240108403070f54090003a000310361b0183c48885065172559800764840360324140e4280c01900b044503400c0075140450442d0b4020300080c10800101540d50041081821150801e400e6203100744a030034110f0a14840c0c040c018080118054112420003000070300e0f001e1901009080400920081600040c130859104014014070200310b0341c90980c1840d0090102a015041c0da544013080d043d5020048082110b20303840f40d000000c1c520703211228080000a40141009a802 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 369443210 1250 369441960 369441971
    0x90605030c0a1e23040c1107050f121b091b090f040f0e06010536090f0a0f0209011509050103020c011806050a151d041a0a06090e0d12020706 62
    0x404074040c1130703031118424103640c01a100c5010080c80107075100c4c8200f4104111049810481c0e4402c013203507240994500700c030141200a0300a0000d0030008030300491201c140501e1883c20028a0341c40b4041004000598100c51107076103070380d00c140a10300184507040b2043d0082003000114a413a12840488040051001520002081c40481110314030000c1c03040c181e104000512080c070b4502d96003018068401c0d10005600e4003000181a4a04001650f618618080c0040360f048041400401c0c508155401202c44075019400d01d0081010242d2043c2c1c0141d22980001c02e07400710b4000a411440c07020744412041c5890440110000d5102d201460501e558522032001000420041c83d80c400340114000324090a12035040707c21245410300d120400790506100b0050707002200c0103a441c10007000f46d0b445a550341e50825011604049560414510104040101200c6998086000d940c241c4000304100d480211405658410080b514000301c4e01c146120040310202e0703001000b116120382d0300481d1 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 369444460 1250 369443210 369443219
    0x207082413051b0a12111009030b0c04030201080a0e0c09070504080708010f060503010203040b0403030b0604030b0109020703120b030a02090a0e06070f08070201051005040c111204090605030c0a1e 86
    0x200300303d441912040c00000181000c0302c0c03411940c0d103009041c012107511000841c40da14034030541a0b14940304d000b0701000d001405000c0c062182d07500156004044104185048884040f0131360203400102e0200b00e4000c04904030769550b120380e40301044217000401e1242c003d41c0420850701c8004204800f04502004041002001440114014891079001060003100006048207903003842c2c0009001383c0c414410000402c1c4501501c5401c01d40501340002c440c0254004240c017841945c0000c2c061628000000406484541c02060300901a0340c400e02500c10704040e820a850440354401d80c190700000190303000d46002c8043c245c028006030b10004a812040e20001d04250003210040041140229640c50b20f03600065455806031071440200018908046100b18180765070042e01d00071a074483c200c5409034010102100e0b070381c0c611400c884c4111482c0ba02140380c1e074068000c499280d1300302180022036080000b0084c44e0380000800d02141d16080c44403c0d9210103d2121031050252490720005 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 369445710 1250 369444460 369444463
    0x2030a02040c090e0610081305030d05040c140d05060a0b011e05030906010609080607050a0507020301150f050901051305060a0b030a0203011d131b09110a020708241305 74
    0x60b800c0d0080c0d1150701d412890300500ea085050020141400355101100706020b00342d02042c40c0c1c1e48405400400141076a150034101d14501448440720046842e00d03041c441440500e80c612030840c4c0c3c1446961551419100c20f0082c4801c01e140024603c0d401080404d00e000c03000d0300901403405062501d20454603c1105c2e819040b100c100c400804960b0002c00d026140070b040c0728090260106d41016200d4600d49078549945641c000e10321401c0100205010103042d00c1001140c0c2010b800070000d2114512004840100c4201c0388074092894403020310001d42400d11b010340f1812079000421070076208580a07200302c05481e0040c406644070840000119000812002640c001d4050725001601c075130400f40740100e0184c9074094001614500310400142c038001c04030400703c5a07409200803100c200b1228041c2c10080c1c95401c1040050300f000d0007200207a1111001d04417040e425421209100e650300d1801d611008080f041c0040203002014070007000d800712010070b82080b14101c50703d1400c1c1c525290316 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 369446960 1250 369445710 369445721
    0x4061a04020310050f030724050f181003090506010b0306181e0a1a12160602010f0506010903031205071b06050a050f071d120a050a0611120a0902030a0204 68
    0x24006155403c00e005500303255410080704903068000340340030b87c148100d8401e643c003010360a02d1904c0d6810610b03440640300303400307441c42c09004d0031525856001182030750fa114002c80c03400c24080c0c1110019a0120b41c401d020300d00350300b90000b014040c40d9082c510b611180b544010304041e00161031040150150040800d00ca200729628211a0041681d040c20749134122000303407486194905124105c80c0740b680086030140c0e00002250800c2e0480c003290324136400c14801845c1180d800350320810000700c043d010340004480050b40c1200700859607440005440303500c110f00010b000111044400203c400c660791080ba0452580c1c2007404112002c00ca000b203803042c8002c0c00b20340c401d46400501c9102403c3c0d0043c6500107c4120307240b0014506140001d0900c1643d0080e040c00b171010f12040c2d29292940000c4404c4100320f601a02c101151600340107588243c82001292010320b4039a40c42480c298000981d105013806009603556603c0380314003480640300c4e040040ea0701d4040c0c0e02a1100580d91403003517 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 369448210 1250 369446960 369446971
    0x24010c0203010b03191104091e020d02090117010f0203070f1b0507060905091503030f18030601080703150903020a031412160e040e0a060c021c170903090904061a040203 74
    0xd0641170101e6141c100041000481020b004038146100346000640c0c090044a8154540a0031014045640001003060b452410701a410030200320012030103003d944840c58440d001340700288031100441590070100e02c4100c40407400030701c81d000e0b5050804c1c03103414410011000b9040542210320262113090400d50036621290100306524020407050030800c1d42030364070490078480200c1c0304101d10042610380c4103041542e2524040041c034035005440c41d00180907401c001a044411641e100c4030f020342e490017240000d4411011a001c41c6850007400c2c003031118150340c1035020709980700040c1d40644030000d4104824141c0071061021100e10700014520503c140c015100410104d8022480901021028680035000f5402e2041030003050700000b501ca4182035124900040510381000d08a080c5000c4151110b0b01940f0480c480004651010030035410321440c00c0b01d00032544400c00820f0b9a4030680704542c2d000071840002602180341c550080c4001c181340d103882c4050164610014080341e004446 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 369449460 1250 369448210 369448243
    0x1201020f042c040219180f0e1c030218090a2a0c12200a0c0e04051b04060f030b040b0606091302091302041d24010c0203010b03 56
    0x1070412006159201c0c61003019034000a01511014481882c41d01c084000d0010f030140111001d1820703141c40c030001c3c140c014400c01d201d02c101101c2083e1b4020241151211070030200c1e04054984440c04000714196200081403c070525003a081c001054001c0c1d0080280320442c4081514541c04980b200a100c41c40f8940d50000001d031502898004e0500607141c85003c5030324018032511130011900040c0459900d508007141e510017a05446080303418800d620070300300303601070074511001c02d400d0b0000c3d010002a200d051004010398951110740081d8400704d8000d011a44800702004031800312580d00f89000c10081c5c800f14800342c644000c0805842c2030341c4103c5020742d1207401c000a00030b5140d0f400780c000340125880d0349003c02c0400050707100320710084034456007580002c18050550780c149ca02d19854440b00019501c0d5907540c2a20441018240c064480501280000640030103030009013041c862605040301d403c11403000011100403100207002c98040d07584503c2c59000e40d408020402c040c1030b2502 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 369450710 1250 369449460 369449467
    0x90e06070210110403031404090c1805100c03050d1401080a031101090c051306120605040501050708240f031005180d0903080304030e09070522030f0807021201020f 72
    0x3002440c0100102407400228070303181c52141c0d503610010440d42200e0b0940b92101e9140700407201813145109690190f5402840c00c00b0301c04520780c011b1014900190b80101da201d03140e940c0c9050007600e00c50401c4080c00241a0004100085e01440107050310400611000503041c1401070103150b081020f80240340c0907030002d40c2807410141e0189001888120f241d00034011480503941d8440c40120350b00925220f600c880c002c14840030260703070202001380080700c0401e00305c1d9464144074004140c207540540c0c8650030100002d03807039805045c2d41800b82e5051f45e1950045102246041801e5003041c081c59400700c41c04a500e039071075804200c03c450340742c1c8040380041d02e030400c0020040344c01300070120358082d600800805501140c010360040c00f2250400201640d9a4031460f04036600115901000e900c16098410f0115503580180138008640c0c000c95502048481c1c4898803862200c1071100906203030b41c00210038000f40c107042c050640244040d0814090240d211200d5080e41c212600a10180c400803 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 369451960 1250 369450710 369450721
    0x6050117010c1805061b06011e080c090a330f050904050601060f0c060e0c010f0c080d0c0509092409090d181802041805010806070806030106090e06 65
    0x1e1084484201d00760501c50203d00456118554540003480350718425007010440b03011003032021452880c00b0001405513400c56845407040c1d2801e030302d201b41ea00f4601100c0361000c100810f000842c410703102d100425401d0b0380e9075603241c250701070030b08580500e00c4000300059a0080c829146001a414903458410304405402d0450081d11008644d0007203214400368800e10002c40c1e0b020503440d040d2542c6240c01e0504000f540021389045050070380052aa520345141140c02c03800210f41c0da903008609903220050100b482c0e1040704d000034080c0000c1c0c5042d404002e40481045507502c2810b1150440c2091810000c00800003009000221120071a0f171406c422148044031040488021108003213440c0703410f5041c241b065a41d541071640c0f0050512002c0e004402002e0ba81803d5100145034807030b0800c01304424034174604003a4015100f0120000780c0b14603d001e0407040c078094141600c02c1c4000621013581d40302c1080380d0184000d49515015507035124080340c45210760184c03100e1000404000d01081c1401c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 369453210 1250 369451960 369451963
    0x9030313080c061908060f06070f0b0109051e040c0e040c0806090a0305030106111005090f010b180705030a021e25020a0501050703090b04090504021c0203120304080706050117 77
    0x25042c1da119000801c204002e0140e8010080715012103481c08030314031380c1c0d0040800c03902c0c2e6000045982c08a00400c0c810208641aa03001c000b0f1032240c16500710999980004409640c410748203016158001c0840394040b28850302c800307510078002c2030b0f00d0f002c05a03281003000920b18152001c0e200454260414802403c0411429401c03103124001011118000d8900030900e0006000d0582048500007141644c0c0008010004c100d504c1c2c81e1080281e81400340c8065655050001020300b60b5003410406400b030b28110443c010500c00303c0c08846100e544001044940d5440102202c02c0c0700e50030b0042e410802d51000c0031015500561000c1070740c0c3c080d200c1b81421411031036840e4104c8030700c0003c1e0003001a02d0b03040b40102151428205a500c409141c40c2c282d8224140c2d4001907522400490001180c4840e6003000b4011402a241d08178490208080540c500d40f4880000e034140e80404070b60031030740115900075035020340a00501410400aaa1a102a20004c1e40200c56003000c0c0f05040c013200c0700 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 369454460 1250 369453210 369453223
    0x103180c0b1e040f150507030512131b0611061b160f030c1106090a0303030509010e1501240504060806010c061401031707020a090b0307080d08011e080c040e030903031308 75
    0xc040c18a58200b8000760340c002c100740309444111400d03000cac00010030656080c00e036030540e2050703101d041c02c1c0043c0205170702d0484000c0c040c4551000114461403644003101d0104110340642c0900550030a07108802488211070343c468004034642c0504031440f80040f400400c5000c81c030030304c2035880d00c4014206040c5500001000321920388280380802c219603550340c4025101e42100da00d0705002c00c0c01e59400948900501400103803094501421031421402c2840d0b0b80084d05131480e405401c10020349a41200030401e41d40d0900c1d00100d14200018002e403400313a02116802441450150a42c61076035440900351680700c4070070104010403800510804c0b0f4201c0d65165254a040d5045061441a400190000800b4031072003111540c0c550080980351414441c880c0030b072121900b180c00b8680140401850300034244908210054441e8101c03000b5000c1441c80001c441501008100b40240242044001d040002114404c1e1004000d2400e454030184003400c405582030282c2c0006034034100c1c2c02c1b820183c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 369455710 1250 369454460 369454499
    0x306050f06010e0d0b090c040f020c010c0206061804022d12010c0c060908160503030a0c05072d050f0309041503020d0f0501020403020901140103180c0b1e040f 70
    0x4401001565456042040407900c0e017140c1e1019082e04d40030f0415082068160300c480d000350810410550350300c1107170010580918020300070002e40185241c202d8403108107840e81503124200791800081d9240801040390480d0004111403a442c40d41c200c40b0800126a0a000c00e84220345006040d1038034004810314600d1b00000001c0c40391030076080700100711041c442c400810f0541c0c0c44418105204881040e1407001429040c5d140c4283c070b080c14025070380e410445042007002d0500104280d02031082064502c03280d8080f807035100013010314000e80860004203204481c200c0f204a20740004c03c004000c50022800480c000c0c555900c410818402500c0c880000288861340c1c54000f08016140c0c080c01500180d00030b44200c1c804001c501d446806807003a80e04c06036201016500202c0c0c4450401c40c05141004240c07403c1240c1046e003043c44c00300725201e00f4042c002c0c058101c01001003026913001041d02c055640000e0f403105003200311401c119082500150b040143d006820300c142c1c05200c10f06050003 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 369456960 1250 369455710 369455717
    0x30d0504033609020a0e060c0f070b070b040204020c010f14161409060901200601170f10110d18020405010f08122b1401090605010816090503070306050f0601 69
    0xa03500200c002c1c411200d2158443c029800642904510701c920302c40c015038840100060381d92100c1c0241c0a41c0c7c0c1000040b5031813280100800050001c40c11070032200c103158441401f404696540c2c080000a401c9131891071010754031408207400c0324003540710348540f40c904031b18a0072650030812500481c00584008140601c600384180c1e401482120003076480003001100e000ba9140f96060048403019281e5000c0c0642280480414000c208041002c0741a03c0e1041d00b0220300390003500c1c2056a81d010006d65003ca500040602c03456175465410441407542da00009030300d011040c1d0219000c0b15a03c1c402c5c0019000c908802100714501405031500601304002c4c4041c040d400c05c443e103501c9411035040c003c1445800036207100080300c0e06011005c3c58801041d4220514042a0050003422008000d201c528621074004a40070300300d4070481e41a280180d41e80499a81c4614030040c203100c00c0c003c50000d1059454001880d81c0d41086000060f510400c0049882d04264810403040d0b48044c01c01d9060 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 369458210 1250 369456960 369457037
    0x216150f1b020705040c0903020a08070e0c040303080a050604020c10050a240b070201140a0c0201020c1207060c0606150f0e012a060b1e090a0c0c0b0405030d050403 72
    0x1c0960000b0654165001218002480144820152404400342c0d00094105072162000204204d011900c1401c0b211341d43d000006559450010500701c0c400e901004010407408800b0841c04505940021350200300940700500c0d00044c100f65616280000c0c20450000d0703150020003810301c0b00e50040300401d12001c0c100c403001642c0005a1080300c1114098401c142c0e00c04101d07079055a01c61840e0020201c6c0303428503681e07030f40320f804402842007203d008164054855201c035442d071420526403201034a1034041c083e01d616420000d0455450740c1c2101c0c00d449030b81d00c6840c0442e110b059450304000702011512850050640640050807030074500f00924180550b44400003414151405440c20304c81c1c0c242400e0103407400e20310b465001020204555a00400c40103102c0c07134866130000711003545503421152012a56514201101503e400f03800c0c900000d504202d280c40042c14207400f268100d4440e400303a0303013804000f0f100e45084803021101940000d09084820070000d50251160040c0e0403109811f404 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 369459460 1250 369458210 369458261
    0xf040f050d0506061002120307090e0610050a1407051b090f10060f110f030c010e010509030910090b0307081e0411010f020118080409050c0403150216150f 68
    0x701c4000052059020345000c417003241d0658420b000f40c00e410602910711503180d04201000412001ea10700640e04965800d41c0440c40f0340c03510305902e159000040d5500c80c503000c0c0309001215000350303414030144140e105024241c0003402c140b04441282409080b00d10a41d401141040308014018110728000006034080c4600d299100c484001503031740c24200100055002c0ea8102c3d1854812000032402c0d004542c280c007030103003003c030080040c2c1d00404000d06c8840403c5815600b00c40c2e0640e4040342c00d44c030030008042a810850610442a01035040001200e551100d6444071a07004403180c00000b40403200300603410000c0b89a4040c1541c030503e16400a151503650040024210606d40c0d0600480c94071070103019200b50400806940c84e00000071a1204034a064160350300319024058880e0f0400c4009480c02c5010b40079901140e8100560440c1c11502c50211030096000d03084522180301d01700b00e44404100940044507100c2844030300041c91000da142040100d0344001442240307050025461007 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 369460710 1250 369459460 369459463
    0xf1709090c12010b13050f0a0915090c0f08060f04020c0304060305100909020904110402090406090b03010b030d0f0810120302030c15010b040306050a14040f0c0506090109031b08030f040f050d05 85
    0x1010344200b610b98030388501d01f000014100259580c00740b904142000b0085045100c0250b44a084480a00c02031080c904619400d9400d41d0703562042c2000101c54074001501ea00d40a251006d2600300036100510303094106c1940b50942e0b100c2c1e008480400d88440a01c007804c107060280000a100711901004400c54550002e105944050300180040c00e05510064441d03407150704507540c201c40100f0070402140c0d0703808c240c8060130144c007075940710b9441d0142d4208541400701d101040401150b984014100c0c010340103813a141000341c10104070390800300e404030302c0305441071103c03042e140260000d44d160700300310b25002e01d041a06000300f480c1920140c0100010aa0002910141e81d801800818196a108118002095a40d1000c5180c4404505000a0080071542ea491707840c06040310355241a20348091204a01c0740509050010303070030b0315081001c10b00103400140300c408a500c514424950b0b9201c1686160080305110f000044000340420100e0b0960800600901c0251201c03400c0034903944495 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 369461960 1250 369460710 369460747
    0x6020f0606102f1c09080c030a1b030605181608060a0b060c01020a0504080d03020306031e1e011d0c150a051611040b0103090f1709090c12010b 63
    0x1003040103000c20845038000f407150802c40300300400100b118080b6400240f040c4416050620010100e0001000420328510103c0c0700e00c82d548003c0d00401c911402ca903203001410030600b58542d0510819500800040c0d0300e402800d000c2c4849503051003082842d054001c1c00c000c15032140401350100e12000308044000070404541c003401407c00003a500c2c10394008180b09103e500000703003141d4400600012a00d40100103042551209812034459000f15141a4102d100a41c0c05540c1640708030760381351100d01c44112099800b03c80e4030598007007191801c0140d10020f1110740500c4903035151007032451840c520121560a40310303900d0042004000c0c407004202d507020b203100c0e84180d40b80009010010030f4040c44c12030700c50b00382020441030101c0282c10505446202c400d82103100e42d05100c04044150720074010703079641c2500104102d08202036540c0e002d10704e600c4009000d100080902c00c0c51002c2da25002e040784506842052030740d031f42250034882420080160000200701c842401000d00358480b092a4 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 369463210 1250 369461960 369461987
    0x309060e03010c09152003030106090806091b0604031a091c17040c050604060906020d050f120a0b06161e0503041e050d0f030f030614010309140706020f060610 70
    0x284210041059000c41d05480001c4c0105184101100140e111401c0000214100c8038107a2f00d030b10001c1e440d000001c0d02c44c0015100d640003548851007022055603400e12809910b00b00425141c85c01741d82e13545514038400d00c1c4007101c481285d480c0401c0113044041c00803410b41200c03c902c0303010140c20540301620703e01690489801c00300309480054100080b0780d000b00081c00e40282004d031942e99581c0c005003000310034040c0070018020303498000c0e00180582e0a0f038854241c80c220080c2000000c00b040d0071840001080848000e03110303610054030351602d4006003840980b411080f410030407903040080d842503800940c00220b403601800358020a030702009031001c3d01c01c40c0c08520304500d0030b84910001541941c0000e5441044040550100580b044900f405940b10317448104203c0661081039040720181d11888001d00b144140c0404d8540c4a6842110b100e441502145e00c1038500c0042145006460b400240250703124101d1500d20f42410444254896421144d83c2c1005102c80350042c08041005803 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 369464460 1250 369463210 369463229
    0x601081605070f0213110a110303070905220f06081603120f0c021c03020f060606090f04150b070b01080303070509120c03010509010c0e030c0904031b0f0309060e03010c09 75
    0x2c5400071956203002100c88000705c0b03071003445000612500441e05074498450440800c003550320840c0d01620100a4138880d21140d00d80d080190314020521480341481150149081403003510303094225041e00c150b001d4000b400000250841c20100b44501c0e001203d05d0000d07001e1450141007000481e03440b100b203030500c145e207007440418400140a0f5448428180002d5224003a80c118100501d060a2000c10090003036003100c40d80b1022404030780c1c07a410180c8500f500420b040002902c503040c044854400c88502174400540c03c0700c20036007490004005e400c2624074410000b000018480d003040704c28013504c040e1001c0d600c0c1d810702ea0400340c064450300c00c941b8040ca26411881c0d0800d8011721074813400c4076000c3d00922840c584100343c54000c00b203c1030801c4c0410319100c028020b9080026081c01c030a50054004c0b5040c1d00c40d40c401340d075840c2100740c60010502040c2c28000c00a000005284007143c4a91560903c1a040c0400981620740810b01103000340e1615074150107040d480794001040320607410 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 369465710 1250 369464460 369464483
    0x209090606130806090607080a0903020c01050318190c06081302041109062110060923150910080606032a0403030e030f030c120901090f0e060108160507 67
    0x64409042d148194001441c034018a01080100311020a81ca4880c018682e100e00156907454403da0454404d142c0140059101c1c0306500055400f840003150800700310b024005000e1800700d01986080b64035661903200c2c40701c25540904208100c82000054012410588280d10707002000910a0356005401ba11480d2508070703100450070303500115545210058011f590310140e002000c00120031112074100300c1ca65900c005800705c28500401015245142d41ea140070b68a0070f0740400c40c50b03006681100d03004500c0350340d503d01d40e40d880303901e0203d030303060f04020759210343d507030410041d2846160a000381400070032401c10440f681c4000c100ca80c00385010700c507850401907540c2c0c1c980491041080c00010510700203004800d06810010f007c07000c20f411070840e0044603018100f40d03140d00031004c110140750b101c581a400c1320807440014000e007003418034002c200380c0c0da144400c0c01c5074070465011414140d00380050090303659000c0001c540c85401044280624507240d00c006003588581a0302500620080c0d = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 369466960 1250 369465710 369465727
    0x5100504030b100b0d09021f08040b06040c140904110c0f0c01021605060c0703020a0b1201090207050c010f0203070606090b010f0903050606010513030c080f150403020c060f132303010209090606 85
    0x41461040c0d00d02665241c00e0058a4040060403c2d4019100bd0b03500803034001c00030303043d0f10301805100000301c0c040d501c02e0940c1490b00945101604000c0055074040c1e1940e9046000380c040c9000750000703203600702c0100b10079501c1c40381050074007001e03840740c504541050500380390b5100c1c00c1101c88211a000e403600c503238401c5042031240c281007450f000203520010f1424009100340354800500b4010891346010708040e681d5402c504128032a1076001050b0341c02070491a0f13015070050300701a481c141180162442c1503025a64072040703440c08e40004030341c25030780d0090b80ca582d64004000b03034142c48039080c0411842c1c2183c90711a80d911000302294100600001e541d040d503000425990f000b550b001461250b45a00c81d00346035298000c84603009540d128070a9501c3c482e0b081d20b606240116055000f03005020021300521010754496402062200300c204145a440100300340300c10f00500400450354100d8100503485206103400045203486a8014442d45105540b5070109a8004004594103561030541 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 369468210 1250 369466960 369466969
    0x30604150e0a05010e01062304110c0d0503100506090a03060b0111030f0301030215040f030f080c03030a06030311030a0905040b120304080c01080a0525050405100504030b100b0d0902 80
    0x1c0c44007a01c0740108640380741002415045038081032031800080c0403030b036120340010004290f0b6002c50041030b544c01c00c440e819420164006030302e10480801031890126040d8441c1e1501140058100001e8000801c02c0856108d018001e0064403040f900d5034035240210001a61844c100c0c00050002aa20b803800030a41e0b0141c030060444030281c80903642c030740c80000d01c41241c540091200340c2c01201041d00d4104c806281000301c6007a03c01100401e540203040d80c95800402032072020403201404100305590309070100300080c5204800070030b000702e54682549002031051034803090344806a0710034003400b0101d640051084043e03942c160b0340010403071480c0b4001140c894ac00780c9030354018040001c0c082a40078020404104140e42030320380e00c1c40da4441c408074201b101ca04450003104003420010601c048507003084403811307040e41d61034240e0501d41c0303510000f0012461840c00c8408120700090030020081036904082e40000e20661044445181042c05a00c5200c0d04038584005aaa40c1440045658 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 369469460 1250 369468210 369468221
    0x10507150c09150c060b040c1209030504050d050c01020d0807020a03031104030602121006050909012702130603050c0322061e0902030f060603030418060504050403022a03060415 78
    0x40f00844100d2400d8141020b0495107620809075084e40c10310000d40214107080c0211201c070b80265640c0412143c0889904009091180d0100d0411404100008150780c860f41c4e03803103006010340701624007007259600181c5071203407000f201005d0040d500c0030405042d030041101c000d00c503003501f0082051a1100800398903071046400061006101091411400c040203800038400c00055410941a544548090742d1900070701d40d903103900c8444a401803148135403240203a0840c8a04c4080c070905000e00e5010303402a0f0704410900d40340aa045141040740075418020560008407903549a4518202914024050401480801c00121034020900d04000455001d0132050034100c0c01c20030b5801d090601c12010b00184882640700b840b680f2054000c03540003081003401410010021840c040c50030000b60f00035100d10b000d402030907554641c0001e186d11a8041d482c4224440c1d40940700d54089a14403e4500c01d08c2d100782c03500900381601d10303005070f2000201c8542007a00028904903484915a060000e4107 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 369470710 1250 369469460 369469469
    0x309090c02060105011106010b18030a0c090e01150b09010503090a0c0f15171612021204170403050601051e1009181503120c17030a0605010507150c09 66
    0x6141120108415a0102c1e680c2d05030b070826a0f40d030400c00500c600b903940d078003c01c0c0550018135500b0444007070054100d041443d5080c1c809000d07251100c0258488131085a45584000d801c00d84035148000c07101c60030300c02e4040e903009140b654407049041960500043c01070307102e0b55040c400c0c000042968071404008420b101035014290712899500c034240102c038422180308810844e5419a40014064011300c030714080d012482040b240984c1d5015489605016081544824892200c0601a40c400755000500c51b010103c00040120b040901c0c0811440403130326080d002c682424403050001480200e20740341127603411507134003105d07074140844401008041000d071503020444900030b2110343d80140b0048205e0b0311b04000f6100a0343c3d039044070025141a2400c1e040a0781c03101800b48000380c4680c00040080c501858021084401641d83c7c141328200990215a45a004006c00c1942d403101d0107410050030013880c0160400340d0079910040541040f8044e1242a40c44246c07103402c081c4140c02240041 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 369471960 1250 369470710 369470729
    0xb07022209030807050f0a031508030706060509010b0903060705070606090c0f1403060a05010804140105071e09060804020405040f02090a0e07080a02090103080307050c07090204090c0206011802070309 88
    0x181034a4580000515031180c0850110f020600041c50690040d4145d0f12240c02c1080355a01c0c0c0f280d102c03403c03070051101e210700104038104500c0114601c1410005864494840c403000503409003004108403001c84142c0c00f020500b00f0402030310b081c0c0d44001c00c1064116045041039038a401315403800c9000fa0080342c01104000c1c1c54801c0400c0040c3d40300c02144803441d210340301c203541c80d0300078525081184411038029400c8001140b0400c40ba52207081d080c2c0d803141c01082108444080b0995883c2540e50030b9a070300f000203900c2004080e00f0b0b10769100350000300c2c400b1f0502051541c900311000e4003001d4001c2c00a88190b0343d900c002014042c40c0b81880c1e40855000b07040c404107103812540320000b84440c500070b0b0550700c00c0000104481c500014600704440e00101f220300185e1a6940742d010503030000b803180081020a000d40c4035098000c00005010b0818281c01585440c10669071b6004ca44000000104540c408401081001d400b0419a1903401d0304030809a9107a100c1d0a05598160b40ea50000254 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 369473210 1250 369471960 369472009
    0x4240b060d05060108060f0306160e03061f060305190e1015090609021c090c080a0803180309090a02090d05070b0d23060913141609150b0702 62
    0x400120b40c0500e00c07580c8240c0b52005540c94070002d01016241c4003424942541c02000414504036841d4250034480030303140380c51003c80070304001203400c01200351140c500340d681d24a01d071007010301007100e040050102451700b0005494005090124500e80c241c2c0707011030319940e0110307200a0800340001880340c2024841804040149031101181c11441e204164026181c2280422109114004c03222640803105407140c550308401c80d0000100003d800480d0401d0000100107000c0d80e080c0945100d080c010900a9140d05d803003004210000604078104805400421421056995007108039810000034103005848100c01408a076880c034032810094103d12492100103074004c5207500420350425000c8007801444a50b80304a08002d003068401c0940d039408070005002410510180c60340001e01c2c06100e07a040d00291100311105e00078000030399140d0481c544004101003444200402407180c410300300001d0007030402d036601d10001d600454001d9100054200190742d20020700010248094200104 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 369474460 1250 369473210 369473227
    0x30f13081b0706050705030702190e01030b0601031802011d041d0102070c080a0b040305090613030803041202060702070302131d03120a02031b070201020114070210110304240b06 78
    0x251000241080307000ca10880801080d064815810fa03103145a11030001c50810386643e0802242c030640105031451007a00c0c4030001a041d20f51341a81d802140508110302c0c00c2d049c481c000506036402441c44660030950021000e0060741d00420400c4807006070700c07602c00030b001c80a0005001c0c1000506070b407058032800794600e4018106600620703503244103131010150a9600c081072500d641c809040a0000e604a100041c0482d0180c4010540500d004200c0c03480c1120384550310a00c0b080503003003910100808030400082081880c02c0314035119450005010a01c0c1c00c2c2002952003629010017406041c1800300034600e02400d41100300090426528040800700e50100d199903600b280d48196101d07400c86021902ca0503652080b68002c83c14541650003401d0100700f00340301075001c88004c81c11076580302d680c6078010b018503c8035401882c16031302503c4c070303038100080c008182c032010300101d18103103410824040011001d9800148250300380101100328402d0043da03100501124100c103420090000d260f00 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 369475710 1250 369474460 369474487
    0x30c180e0105160e0301060e0f041a070c0201080609010b0a1101020705060f10150903030f0c05121b0309130b0a08060901060f0e130311011e020705150c030f1308 71
    0x100441950703010305071343c0071408160070b0f10481e00c0303260025101440401c00f408020003040da03010b805803480383c03040c1c440ca40007198100022125000000c0d0b101410400315030384448180e0300000210b42019465040c1603d810440c40740349191810303c44c4008282c10340d01000e40681d13000c01d80100584010f1310381510200440001100c0c0c1040c4002c2104000c900003007000300c600300e180065580d0101480c1181d0702a0f0f034080c1045d04100501c414101d043c00040c4040180b01044815410550f1b292103e1910313088007000d14a248443e61f802c1400044019118007509059003659044c2c0841d5024958003c01d1000005401c488804c0c0251420401030060540162086a0304400c0101c215966407a40b01804201a201e401642840000080110388a40e0300d512100045000003c2d031284040b0742889800710040050110036000f042487c00d005c4284085540c06500d2090f0440c646801103240200744001895a0035854400021410554511000c0d0022591080c0c200d940c4603a0880d142c1c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 369476960 1250 369475710 369475741
    0x60807031217071704020a091a010e04060b070f11060c0303060a170c04050a0b04062634031403030a06080c1302090d0618030201050a020301030c180e0105 68
    0x2000c01c10189a00c00b4050605100912460480c1da0782c0901200c0c43d0003400e030704880600140da204062910100e00e4800360701c6400c815001660075450541070031400942000321280346548a03a241540c2044200c01c850f0403514000d07070020480c8013003c441d150005070120300d13518079038100001041c098290a0000000c5010b000101d45286901e9650f680d00760540030141c1c803107034081d000300501c40182d06058000a030403103603404001c40e4481d20300c0301007011512203600c40071500021a0741107040301784003c03000c281107501e68060040c0f040302c00b01400b0148005110203542e0000a5441180c00380d40002400c09903038070920f81e0240d800300010aa582c2d40041d12100b115a2a0240c000360517000005c40003800500900007202c0180039440100c025041101204d811201502c181e000042341440b990340c03d600c0001108500300b440e42002800c4680090400519520410041c0003048120000bc4102c98080004482c501c4545181c1d4015040b50003074000158280740500490b0342401059 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 369478210 1250 369476960 369476993
    0x27030a0c030f031704030f05030702070306110a17090a0813030506070503150a0509060d020f090a09030f030207150f0f0e0705030c0108040809120f0307053d0c0306080703 75
    0x2800f61082100365074500c82c2c0c0059170005e002c078181100041030180100302841c0e000e042401070360f04481e0790780c542e0380950702d914001d00804800040c03140c1e160307034114030901110f00d0304c070584100f5032804284450707403060b01e40c00c040c0c817003880800c103c030540c0f5800f0102e40246034440b00391038072400c2a260140543c0c20684202d0400c001d644200100c074142f0080303050841d00c0c0140060380ca03846400a00030032603500c06040e0380241401c4c00218058440a04103400782c1e103c0e203000145d8040c03030304000f4062006000c8000c2090b004010b003c01150100b40e2281e0700000302000042d10380300e002e01c1c074001400080d00d449400b90400304445074800e408105407007220415016203201c400c40a0044a03242e008590040a0190074000e0b414242040c60f2280185c0204004951140324603074881d9295070080a01100c0c1a40302503058802551404104402d01982c1050701780039201c88004075902c214244401e8141c0c4c1da441c20798008142c865004240103004001c1070701e403100d0302c904103100110082c080 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 369479460 1250 369478210 369478217
    0xf08010e0c310611010510091a0d05060a050f010f0509070e10021b010315140607050f060402041a09190f090305030a0c0c17071506082127030a0c030f03 67
    0x2044c6224000600542c1c1c032079101d0b001c4000d00c0605160000004101c08000031281400c0903841c80080e844140300c82550a0140707000384510715081c10040c00744c0c0c0300100809103045440700100f02001e011026001504c4e000c6900040356640c501d4202c0360b4103a00e0900c1c980c02100c0211098003690041002307000580f50b41480351040414a0042d400d598a4181081051200d44001c000e20b05515090706038500005048500c3c045140c0c442d41d18141140024075850f411140c01d010440c6801e00c100344e110b030a200400a100c400c1200081c481d2070008141a14000b105080d10396813101e10750100010040341c200c100700c044064100201550000ca5580310724a19106411302d03000e018281000e502d5030301081c0459a198104082138150300f0070385049601c070442104040c1400c0b1140254005131005e48028404d024900302122a14882000500c245980401c035003100340d503804403120030a00c1d50b4412441400315401c0440d191013804c880c080d1620003402d40200810000c6038504035400d000f5a03 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 369480710 1250 369479460 369479477
    0x5040f060f020418020c010b04021315230a030608120a02070f03020616060605130203061c0209130828020708010c2a14030405010f08010e0c3106 64
    0x40903089210318050005913440b02c112045036902030342c00074641075060380004908106003c0201d4181d802c41d03411142094070700141401500a076024003d082405c3c0e2400901c0b94006010f030000000700c28001c810845000291040440d009421583c000c0000208442103c9011a08a00707503400226002006024403040003030306110b02150401540d400914003850040700c054501700c0c80d00e10300d00446925071603200000d00740e510b0070200c90a070034000320056a03d05d4403504200c5c03020b0881008a071064414543d0401584424041560051860104843e400c4c600e040504080c015800d0715503402c04540040380701115005010f4600d0301c0340d81c08a4284071f46902500d400d84901c4905000000d00b103540100300000c00d20754040034404d68520034900125181ca40c151041c1180070540c41c254400242081030303503480030041e005d6030480d151040855042c6111300240c41c40181110726201c1c0f0110b501100c010040300455a46000141680743c400b6070f9806040c1c0e4564680714000101d43c031003 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 369481960 1250 369480710 369480731
    0x503130509041703190c0210110a170a06050d06060306060509070206070503130f1109060a030c03080309120d0510060908100f06082401080703030512060d0605040f06 73
    0x7103503424011a03020b84540700c0700c0380740c07103500c8035540008000d8100900403402c1c42040f000e10340300f9150038000c03d5000c1d2600f60400401c4000b5100c62140c400750f000401c000c4034540683c00440c0581c602d041d860600000e84507445107078040c00d1142c228035808507005d055003040042640c0300c002100d1040606002140ea140d04100049004841c0040503030440d4001030300151094009580c41886484d411180e00140e480d1744c41c120000e442c0856101c052050f242c201803034500c4140d640b24800711290740b900c1d429940c9a001c181c500e4400107201101c003002107003890310140002c4011100032480c003a1030b00380501816010304820344104452118008010540303a03c18414041030310722540007808920300f020318610080c03030740044030304d6401c0d604c40d0081800c1c60b05001e010107074907400721100c070f0385100d08202c446081340680c41b00d0001d900c41c88017040002c0e044004d0b502d0800000b400e86c580d40e6203040124086103000b4800900711880d00080004001428a82d8281d642c016003003081070400341c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 369483210 1250 369481960 369481969
    0xf0f0301032006030712060b040905090c03060c07020909100e0715020105040b04030c051e030c010605030304061b1e0b0f06030a03090b0901090902030f070f050406050412061805031305 81
    0xa8510341c120f40100006403c0c83d004601c0f1106001e095400010a80d580d203106c3c40103030f0041d401813489185c03a9002d100c05040200b01000520a08501900840c180705026140b10321032018028011115807000500011042c01100e40f800000701050022004030b001007030b11050b49003c3d03070417807080c0f4448603090a80705106061003941c2c4444182c41c07944803618203a428054001044500e80b00720032110008440c0c03034080c0180141d03044001c2d61212401d251035820340e0029003199000303910a0204000407a40032003000c2900e203102d2018150700d4014140081c51603000d14100c0e00c0f8045480e00c1c0380800005950030f900c2105604000c403096200d100400d03480d00001100580000c0702007405101d0742d100350006082e024014105158060b40e96040c240503a0401c2321215a1503407880200080c3c503802001315800f40185240280c90b09062110260950003076000d01182c0c8540c1c0240c25080207116404a89140341c05018021040703030b10302c2c00306d40d268046100030014050310303040003a16040 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 369484460 1250 369483210 369483263
    0x1f03020c06070513061803080f0c1e1203160e0111070e071409030d050c0a2f060a080a09020604031a06130902130f0b0a1203170712090501020f0f030103 67
    0x40f5000782a10185140c5655030150420388960304c9c111400c01003d502090100800700c0c031004824490181c0f00c01c2d00c4411401c18a2a001d50589000c00300100324218062215454018105040010000c6e840070700484460740c110317980e80b035944601c0c1e2010603c03229410706144540c000307031f481000e1400600301c00c445d1741c080e14410540652000c5e99540c140d9005a0140c41440d04140841d110f0310340c07946031012100c0203801110707448050f182e20101910b807652140d8505190a554544c40c0491f071301c90040c2507640003085000595582d01004046550b110304070b800568104201c40c0004004014000000c0415a4001d10030400e44041d621000c0842c05217828041d0000e00f00180010700e00782460140201e03a13a447c64880d80c400201d041c60b50f500d012000909444442c0c007200385841d00d070242100741e13640320041a0340e09800030040790b00d500a540704256184a0300108a502c5076281c01400381c05944800b0704c0111003c201201c0c080c0301d100203107040380c3c01200200002040340c91054803108 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 369485710 1250 369484460 369484487
    0xb100609050f040c03180c09050708130b090307080307020c0310060b070605270304090c092102031f0c1b02060307080c0f070b040506151f03020c0607051306 69
    0x400610180b0510b250640c8454164480d904000c42c0b820302650585450f200303005011207100b60f03c0da4082c04031049610800e5440034060415110340c0c1030408591005681e01c1c9030007004071900710b0014040c0c60302401646c01080e0b0104440d9120301b4a810f001e91622104480c0034040d205540d404490085e490003010211010007403e1031410302c00b6200d00d8003800d4003c004008a2186214568800d405c003086000c1c0194042e0146403160304000030300b8151000da400f01020000040414443c10170f2008401e004070490440c441d4800480f440801d0610707a20401311100070120b02450381e504241a040200000b4913507586030040c0c00b96490b969240e901040c0c0103900500280009521180140f10369078010800300324032824481b20800c0007003a58000c02003140c190501d001800200b1008004075a04102c08034500da185c49000008284500d00b5504940c8007804003d0314000128041e84c115650300d5092401e41e1410b02d0840b10140807540b02c041c052030140001d480c00240030344a01042610700 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 369486960 1250 369485710 369485719
    0x7080103020918030405061306080a0608030d23090d0e090f060d1a091501233705030d140414011b0b01080106060f1e1107030b10060905 60
    0x544a40c0f541c542c140003102c030180700c1c6100402010403030b50388903c0038104600e0410b080c030025034100319004000d500301815800f04281000000d01440340e01006480d17060f51030000c00100b180c1010501042a0000c448580e5841105014000340400120302d40150590589030201101d90800174007003841011a00007140c45040320200e100c520b894200040c60502843c0d20108000c03020306178403540307041501c0d0300d4010750202c00c1c0300290281880045004281001c40409071082400c1100b661200341d62100d0b00c00c0a007084801948400003c02d40030191444a42030050703010741802505121582c050213200344100999818040d10a08240c00c50300030142c1d245003014984101c4030b18a2031840d4519040c00403a01504041000c012000d11769180204044010b552500349181d0031141203400001c02c200c001e01034802ca451300300315066034030000c2d56482c01c10308880c175900b100d00c03841c42918491280102c86002081c0f020250600780640d20541d0600d6080e03642e94025101d01205110b4690071 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 369488210 1250 369486960 369486979
    0x2030a02040c051210060210090809040902041b030203150a0303170c0d0203150a0f08030708090d080309030a030b0d0308190e01020a0201020a030f1116050307020d0308010603050708010302 83
    0x40c240381d00100515255400c0003030405100513011401038908a41450840350949000c03c005036041000e8440c015640b0b0080006542e00c2e00d030001903210300800c580c015602c4080140464885078130102058142c0400880407603003000000700a544255000c05402601000000035442c080c3c0101e0202d0307034151030700d9065111004c014007080400a202d41e02404052010b0515104e1600041d40b24440168030150f9001500041088803030150b08141c4940303812150600c100700c4000100da040c0c03600301f0300268440030a080000c4510f4103510005051860100a00903501c2001014083c2400f03d170b2010f020100381c800500513462101d05010700090441000309020b0a1f4202404010615241c400301d00d46502020701c03030980e0700c000c14110050f94001522441558140710761030202501d824240310100d01001000714602070b100119003c0034016007824104402002207440725540a04003000c080300e181005040180c00b40b0035100807904150020303d82a20900341e080c1602e1f0f0051040b0031 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 369489460 1250 369488210 369488213
    0x50a050411031306090813030201020f01090305040b0c010e030d200a020703020111211b01020301180e160620030304050a1b05120105011a0705070515040b12041e02030a 74
    0x2412440c1e0060314045d07510340fa4140407030700400040c43c100000e11900c0958510b075200080c03810340c0580c0d24001e143d2400c1101c000080d80801101c1c11109030414664075064800359039401000c894151074040d2000103440e00e00c02d40560040c0003c00800101d1141c4031101696030b101c0b9100780c1146400580113100284010342c01030100d42c41d514141c6045403c2e000001c1d00190704008485200015001e010640300b8441d203001551030f0700034046000030750441d450141a02c1a05103130140248446450300c101c041d8001d400c1081402c81e540140d40580860b42d200b401810299000300410401244c0c14011784071043c0c00001c036401030358818010000702186444d41e41c0f61588401c200503446030034940014050b41c42c0ca12186211a2500000407294585101e000005a00f901c004d82400c07014081c14020420108004007290710559240c02d082010118002c02441070f600300480c03030940412140050f1030040b0100b485184280741c400702100303482070a1140240740701002503050380044840f10 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 369490710 1250 369489460 369489481
    0x40f1e080f030a031109090709090f06080a0b04080f040b03010315051311060c1e1504020307090e070b1c0b0108011a0903030415020f15240d0219050a05041103 70
    0x800d1700c2c0d1000d401400d02103131000054945406680620015200c0d00042c0700c02c83c2544501070088072482402c110140c5040200b980b10740582101500080380324000030140f002940c1282c078910140e00286079295101d1541250301e400a000541d030792030701d00b0044211390741b903881001e008510654040070092060795071341021004130513210f9040a003d2282c1d0080c1c042c00c121031810b07041d1031004c000d210400400110b15004140c2c0c565100303080703180140000741c0c60109501d0180d03200b480b0041281d80c800070701c2510f411059803003149810000680242120a040c3c3c0c0207804001034202405240d03001d0004443e0b0070310a0003007000325448801401140b040d0803000308950305000d419a800d065a03181002041c0e2100c501000141e00105032031110701005101c1c2125441004595613200d003095524a0f01074412084142c0c10104400050a05503803816200449258002e00b0f07010030f035031702e1844640c2090407441494060300f604400030030140b40034060040c0c00a185222142035948000052 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 369491960 1250 369490710 369490721
    0xa14060304150e010207020103050a0b090103120c0c03030903050d140f07021804031806110d030e010e060103120329010c0f0f0b150303121605040f1e080f030a03 71
    0x480d600340402081e0964848140a00c060303c81000000680b1000310f0300015055900080612410b9850b01c5443c4400c1c1d40e49d44102d0b41503980140d80c2d200c015015100036101c1e901c10550140c000045508c00104165000c1c0440040c1c074030174019503501c09940ca00a54003880c0b280e020390391008007440034041601c0e01030060403405000030908001c5060707003840c3c0b49e0a03110658080d40010103485046142c803075107540c400c00030952407610021220100e03c00c59103c105100300c1c40c0816840ea505a0261310094001c080c00e080b80c0b601307a40305565a8900300c20703418058450440030904207008019440f001000d0440ba220108283c001c04990810045404144040c400c690308510340c40e810010641250303509a640384628440c0e40c0500708950710004007860000002e01c41da00070851941d2030002d500d150343d08003800305084070141803d10000c0d01d0724000e5070400b403980320740e000c2c4c0011300000d400c24401200e80c1810034000616125492961201140b0841110503402080b00d405407c2c8a41e200 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 369493210 1250 369491960 369491963
    0x3030f010314030403080d1d0a0c0b0319050a0c0e0d020303120c0f07060e1612060b0301020c030a020c091f03030f0c02041a131a0d02060919080c0a14060304 69
    0x1030b64900307501d03546c5440c100e4024462040b1a156128407030788085500d0300b602170702102c03044018104001180d072480a9540e250041c0625004040041150340200c0c2c8281314080d6140d01c000d000b2490411410300090120b00c1c1303101c001904840004075681841010560043e03006405149816240351642c80c40703120280800c010030710204449800d505901003d8181c0364850140440c515900180103450010014642504030080120800c40000c80410000320180d010001080840d041000a8024019503d202205000020728506a59408035100160003130455000750340d511003080c40040500342d02d2111031100c01c0e441041c03002c40d0191707011050040413803806150700b6085a011405841504a6412110940d81604001c51400c4803034009800d080c141c04108024888903110b60441c40101490f00420b000c2c1000c2041d03454880c2210204c00c80a0507080302501d54040c0c1d03400e980c60500c101e40c0d441c02040001800c91800801c000d0440f1400205450401440b9040008540c0701400 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 369494460 1250 369493210 369493213
    0xc0a0803060d0203011d010608010b0609040c030e010c0921030e061b0a0807030e01080702070909020f0a0b0307110c030d0f0c0f0602040519030203030307050306060c0109080901030e03030f010314 86
    0x501c2006913000d00610300c80400780e401d9080c819624280417030a6980e5500030440d581d042c4400345490751251003c0d144106012a03010903505401d032401d40c001c2003541c020a440b075080c00c100c140f00c00e411001210488182800314220b9140004a0000e4144040002000a0411b0410715118903200c0301800224110340351014441d6460140b89250168000e012900004041100418147c208884000000d800c1c03d00100c20f02e0b0180d002910b03082d25000b000c60320f5a448070000155294125140c80321507025000c0c0280c0e27611054140640d410031101c0d0030024198000815960602081c4500e0908015008100140c003480741134484401407518401005040c0611a02040e02200d0202080e13005450040e075550a10f4288441c041c40f103001c5205010b500d5104000503280001129804802c80c40e0041d1240c903840b00240e801c0c0301f160200060b035070030903021200748840c2c1001481400e100f40c800f045440348e040c481703d8403404100d811140f541038050041011540c030022541c00c9504010 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 369495710 1250 369494460 369494479
    0x201080414060f070f0c0b0c0c070e0a020c2503121b0b071116030813050d030206091e0a140c060a0806191a0a0e041e0b060c0a080306 59
    0x540c03140c0381140894a0100041100302804041a0002d0305d40407008140d181c00100001a519601c00c5503034054504406420000b413200210f070414042107004c2c064041d5682e070076042c501c8010020f900324100c0508180030341000c00a049450490342c0c191444130842c0b83e614685140c40e0001c0d8010700c00b650b8814000904065904c40c02c1f500016024035116404503d1f0354145035000400b03203001e280f4425815400701e20013a0300405801d100d030302200ea202d0900c2c0d5031120210644072000000e0303445a40c000d840350010008041c0c0128145115550810407039000c4201400c4000052020700c4440b61070707811065000f001314110b0b0a0a005c401e1046048500044c018804a4040c2e4498048100011510f01c2031200d64a0468040d81502100c0e43d08254030600b80500d0400b9002389058a034007025000810080440c040c00400c1e03035106006004100804050094041c202c0f0394039400c078001803400350004e0380d901c2c20714282c4128092030300c020264810240c1e1014036590000e0940c960100c42c62 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 369496960 1250 369495710 369495743
    0x30f13080f0a03020d0c03181b0b04080d020105090c010e040209150f0703120507020d0f090905070f11070e01050609190906050108130201170a1e0b030c0a0f0302010804 74
    0x9000400709450b00c2c0c3c1c1d006030b0f101d6520300010b04443c10754059000301402d2010a4640c9a81c0074000c2042642104816003d0018400c45d0f40c1c04900ea07510a0301c071400080360004802c0300c0070854140c891201d40080c0039136070310000c00c141c5850034000c40d14045403032846020364604041d400342c58880405415a29101102e0300d02d11748640103e56040111000064070004040d07000021241c0342a0381d510900c294100060081d4543c111600c002d4100842e202400c0b03282d500c189602c034020610544100000e0a04120007400510408460700108000c0b0505101700e20f00010300300101c07038141d102e042d81a400e200411025520420032140d101003800f40280034881c6d02072441004010100001136614500000907120036002400c903003090100003069000b60342c000e0344c81c04145101252882560780c60791490001480d8100720b100c19219400502c0300c4184e101d6200c8640c0030000c030100c40c11116000e0801031555203e004000c10115460300c200019401908030170b420a00c108e924460035042d4 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 369498210 1250 369496960 369496987
    0x5030a080c0c0406170d021b1009120606030314030f0708090c030312090c09131212140105010e0a140d03030207051507091202030604020f06091002030c06010b030f1308 74
    0x107500310320300b0481d901170700018890741040100d080101600140c0b543c9040e882c10110b8070000560748900528121405881c49407040181c90098040c80d01c40c40e00421443c201440105414003040300403802c0d0204c50842020309105880c41456242c0305d14003d5130341e202c1e080f00d20f1440901825000d00c941c01b0000d4050f50288040d0041a003000c28141032071400d10100343c0b40c0b89640783c40074011045241031025280064045850198012806040010405008903868001941c5084489203403003140d40d440002070001d0750403036200340e86880c0290608001c0184404d224401c42144201404105420307081c07031221090020b0107410014109441c40d16894205181072210680e50a000e01c20089070541000da084082c0c202c14420f1014a40c072039003c6075403a40b0150000c2d200304420842c0c81c0c943c1e0b413004100d80c0c05041c0074100b1350402802c4040a566904000300c000d4843c01502e0000c60045000c00075030b4072500c56850094415240c0960070784080080381c0c41580c42603030801482615202 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 369499460 1250 369498210 369498221
    0xd060b0a05100201090c0f0f12051e060a0507020c010f0c110a0b1309020702060d1503051002040303021504030e01180f060507060b040e1e0106080706050903100605030a080c0c04 78
    0x2c6070300040f030306041c14a0100021611034002c6406400c81420a11000c59a240c4500583c2c1802006e291400311131704145141452442804034948200100d02c1118000400c1143c004c254142060100351100703034041e0389401c082e48185000500344440d9208584c07007500c82c0c0c0c1006000303406035620b05046c080400d01c0d2010365000801003c000140c1e4a03000101c022a030310042600c03e20071800c24807903074006001c038852917400c0c80ca01515101003500010111004400541d8014200da10002e160500c44019400a100546c050300805001010884030441c11612407541991070705120008800190340c0010500000c00b0540300071100828036422015445024200c0d03034803110b8490303041703190410036501c444100d94021401c0002d505031000c0001106440300f80c0c0a48030391b20022400456600421081d0305c80c003518842c92100094141c1c0000081904400030360036216a60200101c0109581701e40c490150180d00041e0a034011420820103810702820f032034140c1340906081e0300000c050b0388 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 369500710 1250 369499460 369499489
    0xa031e0c0506090102030f0c161203023703020f0712050f0301060309022806140c060f01050109051203040504020a050d0912092108070303090203031206090109020403020d060b0a05 79
    0x717600009126845500c1030183e5030041011002a1401c94449410300b0500f446010092105421002c000000c078000e4040e58a92103844e02500303204002d69480c4401c0c600d0032046406d4512000c043e09424030300c240200c075000704600025078645034041ea00d005c024602d1020207000c02c40140580c00704008400e001310b0090803640e0b80403920490500401960b00061690300d510101803c08035810004c0c011500003c072a03403410070482511205440349102d101e03840440c500f60040c1810030804040c40303904c060694a00b030303960b08c85041d219400e129120741d1035024502950b1040c032081106281c190010900d00c2503503d450750501d6481c192174820f81d01180402c5810ba4090880c41d0045a4040307140b20040c6100d008458600070715080710443c555605c1e8000e07080b103a00040e02414140250845d80105502404403555180d050031410511001928070500c11070040d400003c4d1854240240c4003600e40041c10000c0d00709580c0c1d2000000c06c1a82c18642d003010403000f0005030751f40c9603058001c0c81e0 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 369501960 1250 369500710 369500713
    0xc090f1203040e16030c1106060d02150f1b030a0801031e0602030406290f01140c0f060405010b09010501080a0b040603050708010f0f0e120a170c040905090a031e0c050609 75
    0x521301c01e00060295070100086a040103525141360030704001c00282150021300c04c3c2c0e004c105070740706800814042107241e249181000304c001200c0c000c0111090050030700505181d442030200f5007003c006901e902c030741d00c0500c001508070340052000c240c2440003407450368001d030400241400107a83e20012f0360070072203003075601990b1140c080340209821545221a00307130410002403181c40c1000020002c0c007490b140c40e030401000e44491202c150340c4600701c0320704015500071240e4102440e40322581c0ca0804270b034200c8595081046060f1036041002c405030503110142c46190459448d030030500d00520f0b400e010315910039201c56001003c82c40030b115140261080c180041184000001c4040607282c026400502091804100001c000e00102d4080e500300000741c1450b60721540340a01300d800c0c070540700039103801c140e4078401c0c481b0312181200103108036080325006000d1740d40d5400d030300794480c480c0d201c000d0003180840500400b0401303801c02090220040d400c191207210204e4844501d00307981200d14414030f = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 369503210 1250 369501960 369501991
    0xe06071a0903070f0609260415030b0a08010504030f031e02070305091503180f06060f0a0e070c03031b0906050c0a0f0b180607120b0406080d02150c090f1203040e 71
    0x9100324220b4043c0070f6008420b007c60040e03901d11000c2c110b07114500c6920f50b01d10107014000000784c82070700860260000100011885170306c034070b17445000b804c0a03201100071441c1c0c607411041d4580213000701480030f21540c516003082100c3c2c174856070295000420442c00c02200300036001c00795584002c103000003242126000c3e00c0740340051188070410500b100c0d184050340401d03c0c10318050301c0010415030000d025500c0310780c0284400081802d04541e03810954450161008010403183d005030600040b41c0255418082503401e00c2d551600e4400480806001564002e030a004031401a0020030440c420344040301c1510403039496880f41c4c00c500c01c008840008402040c800c0c030700c0c0700814050b00700b08010041c1200303041c140c03030203409680f0f41c100f60713580a45c07074155111041e41c1c5c90b40700c280100070030000d40d401c0150301d01d070094a880704000301030700248648020444c0041090141c4008200203005828411403060410003501001a810030345440204400308494008540840c059074440720700c02c61 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 369504460 1250 369503210 369503213
    0x5040c180501030905060a0b0105040b0d0e0d09140d0c080f01020c0c06040b180301020403020a1d250309051002041706010603090f0609050f1b010e06071a0903070f0609 74
    0xc0c1100c1988080d04140c1801400008500f010031400c2c0c0100c454100080c40d0709403c4010380e01409954030440c1443c602050304103140100340c000280c1c0c01807820949100b840d40c035800b541c01050500032440a10000704d507111050511003600f03420b80c5c0c043c01404000302d544103003591070801504134415080e500883d440d0210002080402100081243c14506050a003450394009000c0c0c8a01000342d00100715850360943c030300b0750403030b4044c45c2c0140096a81c02d440f410078400311094444030400392039810b00044d40307401d80401840702e80303030f10074008010301c0c09891800c50150100c240181c441e07000d040c100e01580f2103070b44001d01c01851155002e0000001000607a420004144c0c0700005042c1001003440c0018030001500c0b03002580724000040c15415414020701e40201c140b0003030020b100711625860303a600d00ca600c220034041c090f80d41d191035081540500403a4054248010603d03880541d2032170542100d03004496004001404407810071000e902d4400400c1d002c442c0a540e0150394100800 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 369505710 1250 369504460 369504497
    0x602070812040605030705030a11191205040803060d060f0603050d080109020a0507020d0602130e01140d02210a051c0e0103020a17060a050402030405060a0e0f060a0902010905040c 79
    0x180341a010401d5a41428a0024003502502c80180303a41c1c01c1200000004540381910f600600b014030840035101d48400c0814802120200038100f000c0221f00304101c8010b40f00c0c00341c09000d2086510907529410340c1c0700c5009006001c00070510441e0b499845860b4111044060b1040c2c1000b98010300c010625940422006851081d040e001642e040e401044a031118981003011514200d0b815100e04440c601141804c2c5c000b03002c4c80b4211640e1001d14140003031130074200000c5505949100302c030080091a44410040460301e051802504920358908102d503852141840c0341d142281a8155040500556500340c10b10714200c0200450282c032201c02003016500c6102104c40100a0904525010319840041c0000070100004d0030b84a181000050350340d12421482d200a24001d0000e5499040c030b45081d544400e000c0b11a004103c2c503002e203202d180c240004041110b0b002c0c0d640901140d8039028140741c00f03800e14034020b86c1802002d900000f12501e652003205100790480c0d8030b910b0078140301200f60 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 369506960 1250 369505710 369505723
    0x918060f1d03190908430807150c080309030f040803070303060501110604120e0409060b040c08040c0b0c0c0d050a0b0c041802160f0b010806011a0412050a0203030406020708 76
    0x8108004030f10790144a40000040c4582d4210300491403004444e44000c59070341210340709070346810066204001071502501c0144d2086c02c1d1200b01098450182d103403000380512455040306180042e404081120204503407100454000d012082603070b1a090380c07426800792075030007540050a10b80c000126107043c154503104a0b00541400d1822007203004140381c0c110b030303900005040580764440c0c0d80d1070a0701c480e018584401c0300f40805001842140b440d410040010714140c074030b940c000c42c20594400e048901c61034a05100c0c9a002441180035030803e140461107402004000c1c069100e8041c00b0450b40e40e42000d0914010301c01c070f000b880d920109141410020f000075000d0f480450090109200f611480303601140070741990080143c0750304007502e41d445d0f80503401c903024010850701c44558003407251092a1034180c922210469015176030b100c0c00c001c000418041c0299140e03005100610901003240c04402d1854004c270212020705403181c00203821648140c0c01803000d039008407003c0262180c1030100 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 369508210 1250 369506960 369507007
    0x9020c07030308090703080a1808120a02060a060509011203020f060a0207021306030809331902031603030f0b120c130e0604020f031023010918060f1d03 67
    0x242503028a91f40d00c080140c004c0201c0c0500344a41c0d200c4501c04003403129080401480c03100221820300e1007580317880f0400d500081070070303006019000000d4110040d03070181b46e041700c0020b03101540c07581c0fa01011081d4000301e040200d085000e40300c1260a082d0041001a0207088036150050307480278039204010090500440540440c0d0401504001003503a1805554401308103850044c0354403030b81520007030750342e00c950b54550100c003251a20f03001d2800b0007009850a030290b05c004200382902000c050f643c0e401804104400300051005000001348260040901d441c00e091000c43c00c9002c2d00c0000e524200740075640a0a5400100c188541e40303440d180c840500003d4990403c404008210390702c0e2200b400030030180c0244441c69900465031010441e2044040d510401006031848010b10301e254030160781e01041c080500400042480d81107031040070342c050302c101c01141d02100c0c2507030ba01000e8500300314015102a03841d851100800101030043d2410700d1681c0103036544580c04081c44400d040341030306 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 369509460 1250 369508210 369508213
    0x1b0305102a080402062d03060301060608010f0b0a030f0c021f0b010903020f01020a02060a030902090c480a1a0c0f0d1107030804030905010809030d02031009020c0703030809 76
    0x301c800c89150407004240d00030f90190b0300b06941d2504141c2403140c01105031054a42940c000203541e14040d283ca02450040c48202c00a00c4400c4c2d4910044035000b4081c0902840c180804104001c1010380c200180184002810045100c030810407807107007111251100000560045100c0b59040945510740385240d42411004200c8201c43c000000d24104160100902607060800c2078070980e07000300000360805500600c015651195483c00238043c0820350000c84c0a41d842e000420581c02c0f000069803445400820140a041c00e6a465140084c8140401102c08007a040441c190061110100010303120074000074400c2001d2b500c0d1104101c4a2040907011102c040c605001d0f644194004807104211800200c640395110441007000a00d00302d40d40408100001032080701f015007040000b0311a41c0030380c851100c1c480d610030040d03408403421299603c2a810400010482d04515400385800274142c2030030000540d2111002c2d000c0f03038800c500c8a06240e018200c01c008250344681e0031540b2010940 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 369510710 1250 369509460 369509531
    0x9140604052802090a050d031218030c08210106030e0f0105010b0708031b040f03050609010e030a03090f0203060103082706070305090d0209010b03011814041b030510 73
    0x2e5640410746800d1140b861540000d07001c1d14669566482001801009240e14180c400300e180140006d110714220a1395182011405850b880718040404500c80d0943c96400704501681d88003142c3d6440007914101110200000d690390030145010580600426103000542400b214805443c1000450314454503a041c01c00500c8540410010750324120340c0030f40703540d8807915200c43e01c044803003840c1d50741003404602040008161048400c00d00449016406a07906a185d000029007a80c6c0f400000d10050341c000c00c1010442d51089d408041c200d0b028040140060500c0d60000b802d240342030f0300541d074422000c40c2c0c50b4040074948014140024ad00e480c02e52100c0c08030f02c0030403024040c64030040c0900c1004200f102c065141c0324141c65015500812141180d82c4035158400240c2080c001c0003081c44d40d490a00005040d1840f44003071108000c1035903502551250f0b00c180321000034003800c02c800d200c5108004001070341007045c4910620f16180c00b040112140c11060900c40401001c03040144010 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 369511960 1250 369510710 369510751
    0x9060e0a0b0a0605120d03020a11010f0f06060c020a0311040204030b13031403090607031e1e15080a0209090a080c0c01080f010e0a0905160e1005030111040e0405070914060405 77
    0x43d510301c0c55286080160300c0f030707080b12012b844441680c1a40006942003800814080440368044c0d00448540d60040200b1600c078402200c51110505009400101e080d4091002c2150340c00c88084510000300003600d80fa840742c2d1040e00c46e1070f0940365088100603a08064040540100501d5100da081741d90f40f50541c50038180680e0b54490140000040c0340e0307241b84204072000504a100e0940d1008003040c418100f1700308101c8049001c0100707818000f460000c1815200b50400040350071100800003c00400700b0603000c10929290213803251981e80b242e049040009002d070f20181623580c14140c0906403901800001420042c40117010030780d1526507100610555009900041d04076400c03c00000b02103a0a240c1907141501d40d9810805000f0007040004903d415048103d10424014a8801816568509141c240c4400240d1155082410b00c41031014803811107109034081e025104881d29645c1d500c151800b02c07103a0282380c0d54030000b00c40422485041502840c2d400c42c0b041001c505115902 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 369513210 1250 369511960 369511963
    0xe04020405150d140a0804030b091501050f150409060b0c1014130c05030f010b041d06010501051c0203040f050c01020a020906060a03020c011a030d0f0207050409060e0a0b0a060512 79
    0xc00c5004013080c80c20b002081502000b0041c0070701196010003040c0d5944c3d01c9041c2200c1070001180c42040e14400c2d810581c2c0450301e00d1014034121480074259102510841d000c04c66a4040c0540783d2424a03424000002c1c0178030917000b5000200302008540381e54100c0d8190b20360801c003106843d41c1d07036a0f00700501c400f422030119034500d5102183c00302c1d600c0481c001d450416095802a80195451b2243c1052183c410b0010b501070310400714225001c00517040001d60681a48080c091840050f800a90040040d94010001040c4940c06240e03c8554854035000c21000c9800a0b281a180481c00401e03510030001308002c1e89442c40e100340002c1a51031820360000b00340c1d800040140d8050070f000b0401c09038490194058070f0b00d04920318004c0c00a041410035165011080c0e5040c13500c41d01c500e51800961600074141404124820f03401741040e1070404003407001419071a001141e50560325070302c14001704014858841403c1c0300300c0b81c002150500003c0d0400f0340b2a5900300501c03c210200c28505035190 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 369514460 1250 369513210 369513229
    0x80a02210604020d05040c09060509010b07060209060c03042903060901030323041d0c070b13021c1515060e09060f100e1003050601020d11030d02040e0402040515 71
    0x48464492034039668007400705001e80103000c0340d0885203081c00144800c116045407020207540d4500820840543d451040148000d000c0c41401d0810300108424404101290010540207002500e081d2800f940d882501c0c2c91640a0b900031082d164031400032802c200403085032400414120424030f0b0031410180001400904180b0008061202d021060b020b803c2145003200d206c1c0025140f00e80e01e60380c4d80c511440120101072090170251a01c1000121003444001c15100c4480c1c22858003003450781c841719142c0c110042e0000c141c2e40304685840e040e4110385052064448503104054440b081c0c00032a0854054885031955040600c40c40e00302840f440d03034048000701a200b0101c1d00c19105481f10004104484e618100fa04d42111324812240c041d56007000f045102c1e20b0095819120140320f03040b00b18212003069909600507081881d0320780c000e9114120005d60710104800b50707071600001790020303003c80c2d02035480b007070990f80e400081005501e0688112a403040003a00391840d00290680040e13900c48 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 369515710 1250 369514460 369514507
    0x9020d0b220c180806010509060607080313080f0301081b0301112703010e0d0e01031a21030a090305072102090a0f1d0d090602370c0303080a02 63
    0xa9560203840d501503c21a4081c09204503000450030341615100101d4940209005140c01510010080780390350501404590003d9003010120b401e51b21184e0203030503a5014aa025204441c06000c155648580e00d4021402020000f000b03044079100e080a00b03040251109680740310707074900021311060b0701e440401c4400b00c1c0d00100c20282140405442c1c100c440b9448420181c05600c2c00965151054001461207208405a22200b0072404148011416240c0b80c254a2500c0340302080450045e04188600e8034040340010030101080504504081c41d64221030417100c000b4010f1f500800071b11006106000140001e407003000d4445004e042656040151000000e000e40c0b80700c0002208100c055201c2803510f61003040622105114048907a621702041890501c0790003504101c074569070003482d803401100d1882e0003070810718071441072a81c2c14a6030308400c001d640d00900703400c5143d80401011441e030103110f15072084000c0d05504006164540c018900c000041c4100103080c0041c0c14041c5082411 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 369516960 1250 369515710 369515779
    0x30d0318080f0c07090b13110d05070f1205250207120b10090b010c110105070b010b041d01060c0f0201090503101d010603031e0e090109020d0b 63
    0x350410512051815440c000140040a002c40c40e80004001c0b40010049800c9810884030300f00c0e11201508120345c084064190f104c0406103050305400c81c2904500c411032581c0c0a135034103244120398120f02b5603004232a01c0300002c0d8005002050306401010b00301190041d1142005580b8001c0d598041c01164448411a0b105c5501c11800001d8420010703840545107070000c16446054610705140b21072000d8980010f9040541e10100b8038030103a1164801c0303400142c0d40c0a189111603240c00e0450714001c0c8071141040410403a880c0441e803810070f090b000305030070109580d949250200300307080c0403000ca1078008004030b2880108006c42d800410030a1280c0c100380442201d070002e00c01641c0f07d446540c0200d402d401001411281400303154000103282d00c91081c0c0d2452040055411400c03581640002801710703003810049021040800c607103607a00c1c0d0301d41c1001f04a4502150005055043c240d00801c4074503000103540118189500a80014450550b08102981e21011003100781410500020b20756 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 369518210 1250 369516960 369516971
    0x20307110f0604060918021908060f181807051012060e0a0507020c06030618060d060e06040303060f1a0705070b04060905010207050a0e0f09070503010c030506031b030d03 75
    0x503540d8100a036505180020b101c0d6a446540360f0001e8814182489500d2910b4480c07400e0180c180c400d802200c01200b80c12603d420341c0d01310a4070603a00d080340a40400c0c0c120081e11807004864441c0428010b56104902c0114030b60303d0400d03640e400040d07245103a050150880c0d00b080150b0f031203000260b4541c10103400d0007102d09184071032400c0140055808100921103040038811900100d51200d80030360401d601f5115110711b120288512480207407007a54010744072001818418910701c0340c081d04002e005080c0e414081291f20307440c00f0340c3c000c00001074003030b0060000d0004261309032186c4001070108481002d901460008042040d80c24100013040031000080d40b070041110030302a01d0090320405112948654072040e0042005ca02e6020729400351103040004181c9103040b6040c40300300d51400ca22051103540e4820340c41c4030514040c01c0880b061080700d00c0400c00b40d5007806407101441040e50001401d10704082014501100b04480c000f9031461960131b00070540b03010030302e1142042039080200d807 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 369519460 1250 369518210 369518243
    0xe01020a50070516170732030a0b010f080601050603040b180f0c2803030c020111030a0503040b0717071d060309010e1608070501080a0605120106090615020307 70
    0x805100b1100000c0030390046101c5844a0643e4203002410341c1c01c0d604803c08098116080580c0d9910310307010354048520302820800c00c92401c0b00a01ca080031840d0b000690301041e94010030700c0c003000488112000c40d40c410050000e54030410302c040041a215000b09515450030b00402c1492101500c090030999a4400103900614440d41c41c102200c204011580c40c04600349900e40c41d8003201021910442104010307240015184422016424510040e4010149141d500b80c0e9070240c0d0a100324144500d0001030408000144003920b0b04000710349a095481c0780611703041042d003000402c44000e01c110008084001d8036003c040541c0401c641c209150110181c03866042c82c4042d0088480d4801c4000042048010040d0400c0014050002c201d6446d100320740c26003059540c0a0140303444aa000c590708110315032150000a4014079000320014055490341c001ca22210b2035030060b0340650391034500400000d00207105120091250542429059094420094407440b4150001e85400721040d4180b8 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 369520710 1250 369519460 369519617
    0x80301060e0f0d0312053d0e0f0a060b19080a06080102040303050903060901050105090a0f0b0a030f0b0703060501120b060c0f060702070e070f0f030e01020a 69
    0x40c0b809801807440d40c40b241585402002a485021791001c0309081c240841c0d41d0f10144c4054001c640700c41c00f107401245003000d40e50f0880900390111008110840c2600003082c290844515016071000310071082581703451034005040e43c42540c0800c00b06401044900303600e04100701000d40344121854040c03d2900c0320810000030380a550031090095100140000c00c240e040001054143d60070350503070f000b640d503001c0498200c070403d11074260062111030000700d0302440d0368440c034100c03500210001001501600400c80c0b854658100726030003280642900306011a03104c0c00e50f40040c980c58240702c020305000000b091112441040e00040307171105041941c66645009580701b40715003a048542d50705084ca6400d680d16016200480507000d4030303001086901c2c1080ca8544280490348901e1030080a8001c11204030002032441010181c0d20100400c481c002070004180519060b40c0e05660804183c082010304594480400c06038070800941103040d24440900d004080d1021420034089008188900d = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 369521960 1250 369520710 369520729
    0xe04030306050901090914060f0c0c0703380c0f070510050403081f03080a05072303040f27020903030d110a031407170612300403080301060e 62
    0x15500c0041c3c00004241c401d201d5202803085400755001c2410351a644850035203540c010f0f56044083c3d07400030002111001d103403004010f0351038100d04031041c0a50369201c60b00d4901ca4610040425808a140000c42d02c0f42070300c0c503002d182c03206203d003400c40c1014202c5103094400c40d20780180a12000c101c24040c0607050101440f00040d400040c45103140514004000300da08640341400d024280e40c4681d20102c90703000c00d00940c2c0d88003403442e28110700e101d020b440541003814100c0301c00011031003400c0c00b501160f14981840b1004401140c8a908000070b03444403102039082420140d0b640c00400408240f02c5544c0c1c01d424010000c0140e5841c2028042401c51041029844003581843c0721140e00c2e00080004020080c5650340801034800340c0c4000d00030084065403000700098031000c01401140c500f03043e5580028004240c0100d410302c180c2164248032b2080c6403030b160f02c08000142d491910f42518001004c0040c16000d030701d4282103030b80f080e1003400180104810042c82490803034050301d411002d03 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 369523210 1250 369521960 369521969
    0x7060f02010e070806100b031b0d060803120604241a0405090c0c0709090201050d0b011b0602130503060408190507060608060910180204050a0902090403090602250e04030306 76
    0x3d5610b201e4489010707560759141901c4401180a01c044001444140c24017a02c2c061406504207101c1020b00c140c48200b99045027502400c0036998040015100404000030403002c0600b8002c0e03065403030030004000880c3c504080d6030100f5041c1010b60a0020307419040340d0107a0781d002244140400800700c160b8118002d542016801c181d010f810711682413440b10182c0401c01403070303003112071403512944100300350784403036600034003142c014449100f4000164120591251062501410324040102e00020504100394182c0d00c1d039a0029030b005c0c021216101020141a0035030007030249003003079501c0e400c85110b21008901c4c0808154030840d04d05204500302c9003c260400d0040c4419a1070b040d0068890034140e0380c800c49880307810910488600580604c2c0d03481e5840000b4481004e0f0b060f02404003605008100a10341c0e941c90300d90b800140da402802c18000c901965503e407600d4102071010385802d00d00b40b4018661101e030141c540002410710a03007001c0c0c44483d18401d11a80300c0d80340c240d01030a001d0b0070 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 369524460 1250 369523210 369523213
    0x2130b03010e07181104121104110409050a0221090a020a030c0905060a0312030b0102030717131208040314030d0606030e190203030304030c020d290702030c07060f02010e 75
    0x6a0700c20b603500058001d0580b5007911416181d18103541446085a54030400c840c0d0304501440100301e45691040801e2220303000e550490403000040e40020200c80040b22182e0802001241c1030082110034480d2035440040c00c0011454180e0202c4108c0900341441d40b50340ca5070200d000084c0d00b0300b1003480a000000c0d0f0107052408295103918100c1201907560013503e0203c0d181078001286450301c00340c1c44040342d800c09550b0b40f0000903194200c002e0000440503030705501c020070016000901000030b0304642400041855221040b64000c2490070b64035500154106038480b402d0700c046080749041750201d07540309040d01188070f40100851305600410205110140c5008400126150550000da120250b48803e80e00d42d40718144940100b00c010f410081d400d41e000f400001d000a01a0100070302d070781d00050601244201c5a5115138000c0800a0348191108030300005a01c0c03640d8811145030004498006182003000021040d43d40d00791900c01c0008101400e1000645c0c00e0003075006421503102c460 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 369525710 1250 369524460 369524471
    0x3080714030c060a0b100201140c0c19060903090b0a090905040606030f0b0610020a170c0a170c010b0915210318030706090819031b03020d0e04050105010c02130b0301 73
    0x301c130784008143d400c00d59401101a0401955000e2040c4030307015600002010b03229294480b2040c0030b100390004851440c2c984510011449c2c1d45a04100119015125403004a405061072a00500742c1520394455088684140100140c0c84e82182554041ea0001032000030503640358100000035100551008c1c0440e41098900e50a1001046c1010f01c903010986004c0c3d01d046514104031b075070f50880d00c0054006c0b02d600110012503000c1600404a0300e049000b22520302000e503c6400051881d2001c400b41d00c000069100b035255170a02402840017401c880c001c200c2d1801e02680c10061100c003903032074856401c200502c848288406840c14440c0c0c549022aa00c4110b03100003006603400e460b0015100b44241e900000384030340b04200500c10791700c4031070191904034422a0348440e1810040001c07018032003900101e2065640d0b405039000b00600950050004809046018200c00582e04c1040c0c003803030421006021030b980003500c030301c0500c0c0d040d00d074411000307c001b0001000f489840065039043d403c2c44d = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 369526960 1250 369525710 369525721
    0x708090a0e0f010b04050f010e04090b0106080a050105010806010e040b130501080d1b0519110d0305030a0b0a0602030a0e0103090602120f0c040608040201051b15010801110403080714030c06 83
    0xa07004038030038000780c0070000c020398850500300024080c81c07180c213502c20103800a0144a51294501c3c404506000d04089041d4030940d4070060035031401d0300500c00041c082d004003c423010301801a05c0c0100000c0c20442c0084c1841c000080001c113001c252607014503245d16404007907880f41c2100084801040900f0025075846203031880d2140b0300c07403808100081104011252070100c82c0d45180d26554031000034080000d840008491401da81c2d20306403960740e00b5180e19050341d01c1e10701d00c20980314425035036a80e80303152900c002d10465901c4044076009403458401440417640001c103c5007008103a042880264801c0e00040780502540c0078014041c6001140c00d22194901600086c0205403405440400755110128000c4034002c1d4400c40e400610f001001c21f0155000340000c003a0f66a039400702e90280c03488001e49514140c43c04104403404c91202004001002d4288500b80d034481190752428540b40c9151a408020700500c2806007603c0b0015260400a100800c11200000030700015980280f811 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 369528210 1250 369526960 369526979
    0x117060109240f090f02040b0d0c050f0c06060a080a0c0e090309031c0e0603040f0201080a0207081b0c0a03111504120f0209060d02060703030e0115120c09050712020708090a 76
    0x4510524511303d080040110000f01c650090381c0680d0b14240d040360074000724051410250504514071818808204000180050550010003607220090010425424400c1c14800303c41010390001c1a2a00100c644c0c0d40015200c0c2e00a00031030381d41c103032a000d180d100c1008080c21445566506640b511640064600c140c043d91560000c006c02616410500c505000078000d40e44800c960060440302500401e00040d8012440103401c800041001800d20f00713580d541050960264020ba840c1a040407a000d800c0d200405c10443d0780746050b80c102030242e01e0f660f00e10b40b420010f1102e045c800c80d10300b41044240200745040e20001c0400002c085107000043c1841041030441030816030040d810840061107a0512440c10780110794041c0000f844e1410f581c6085000344070340348289031517540b03602014030700d409900481c0c2c02034922640d042d1039250740c3d8030344894032010550100c2040c505010410030b480c2d401a402c440354005102002d656208186080d01c002d2003050075444d0b1107620942c011031720511 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 369529460 1250 369528210 369528239
    0x918150b121605040522051002120405010b01110309041802030d180501030615051803103204030809030712030501091401030503040909020604090903030c0206011706010924 76
    0x12942d004045407521641844143e078011180407070010002030a40440761052209044010b010350309440c4141c20000001d0141da00a8404c047c1001054050100348603080c0b0505c0040c601c02d017004212200500126600c0b0300954a12a2096980c3d0580000c0000c00740c98482c249540241074078581c840346c0070040d0118840403140704100c5007100f8045103030350007840380078142c1d6a64804061103290b2102300321207682c0a44084414040101d4269a854038100141c034490703000340d2000310b00000c41e050b2400700210711340c084880c0201c21400d003000c4211060541c0c1c0e00700e501442c000d1116a1540b0416166114003200108000301c510085986942c0c99440141070f244062030511603e0075075450500020420301002c0c116410401040010f1b0380d080d4040803040d031019142504141e600c011038000c84100301c000f90080390325280c201190650501100703016050300c81419510200350040241c0c4e85005000b4078400603610b000c4440410112001418180803071041c69160686810201c0c0c800030 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 369530710 1250 369529460 369529483
    0x606220b0d0b1f17060f070c02040905011b030212042a030f0c050306092503020406030b0109140417070303090f15110c03071205040e0f100918150b12 66
    0x514480d000c034070031182c04540042c0031000802407a040c1c440400403c43e51b003018120340103002c20340310010010703225801007545050041d4000101d2032854200b050b07400e00160f502400b018410003424140c510a00301058200f6040600810006c6800c6041601c040030f20b101604160400035000040100e546540d240d02846140c510804c190340d0000d040d9105825520554150001140484183c603905083c1c5c02c0a081c91900204440c1e6030f801060880e0401d40007510103440c568014001c0c00e203140031300300c0101c1030059030020b140b80944032001e04401d1a41001c006c040300081410505100740c12800c103454000c1081d122403030b840e01d0300700d0030481041884075185040402c04980030b008003040d10145440c8202461400c0001d5940c10340049403541c0a4081c4a000d200c0032800700283d9a00728840d900e400c0f0090450b044c40860a29044204d44c00740380d102e4200240b6000c2000c2e94003580003880e6124040045002180a506000d803015110a0350070842a80d2050280580003c8844041c03 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 369531960 1250 369530710 369530761
    0x330509151602011812080402010e1005032a040b0304150c03020a1707090e09070314030703030e0606130e0a0b070203090a050a060f0809030f0316020606220b0d0b 71
    0x203c1c103148013184050b10780c0c84040c0c00ea0701100130118416004a08096120780b05250044e01680ba0301d00060840d140020800300041010041041c10400340c2991103120004001c440780309804400348034014411401214842c0f0008004241041001455401324054062003803120300100040100203401c07003080a400034103403450b000d000c1c0003902d0710b0702d0140d0140e64400e500c0310300740580d6081c00307030020b82554802c0c400c2080c000007217a83d83c0198000c02c2440740185903268100d09009007078982941071401a50401c0c014000b042d55030000d41c10158001c10400700315040b00005150500b403683c1000307842442c0740002c100980360b010001740011002112340440280d01c9209020303482d0034501840300440c81c8031640f054014010230081340d100c40304008072441c000c07811802c809560001c0e030b100505480e114060000854060000c0781c1d1149080c0c95442500230f0301030700482080501030813140c2c0503644400c16501500c0d180c8821100742d411034003400720744c00c14aa80a070040c802242c0701017030 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 369533210 1250 369531960 369531971
    0x1e2808011e05060406030c150c050715090b0307120f0b0306040b011e030206180613060e0103050c0a02100b0a0506040f0806090d120510030f0c0333050915160201 71
    0xe844d1a01c18817090340c0c1c101c16642c900030b05081462600c81c1c3da450380703c0103001c0c09010000000b0001c01111000e0002c101c14005841051070003d000c20300136801c9640c4220701482000886540402803400e14250035030042207540c404401e22008103101040710b071301070066030100400c1c0040b40201a0403a0403000e400d03600d0176200844510030202c01d02000b50322490411018800180070f40f41c2002804006015515041c0c1041d00130710b026407540d02803404680240c0503400c4568151064135404201407110500d802a5000001d45441254401280351942c0e01150a00c3e5100e5011100c042c040140070741d03079a00d0f210f00e003aa11400d1280b0400707145104002c0051401da01c003107072404c141409070301c480202c0040b00781e22002414004010380c83c0d8140c1400300001103020f8031801c0c02c105025508101d41141075061034049840d01c01c43d000611540100300c51590205050008849404000c0001c0c45da01c4011070b80b400c2043c0200548003080c1204207000c0001403a0340c80c0d070762100c05600208107 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 369534460 1250 369533210 369533221
    0xf2e091b0602070602061302060f03010e0402030c060a21111206130b0a0303050c0c060403030f0915140d06170d170c0d0c1101020c0a021e2808011e05 66
    0xe44503c0d9004040c0103812241c0401c42c140010760051040354402080c2c0e60500ba02e1001e20031068100f640920440c0324200180410750400340034074110b0660603500c440c07401c2240303013024100b02c1840f00301261110f88440182c4003140c160b4060b00c11072401c910b0075076a600003941c021a10004c16503001d4402d086100e4800751b0503e052094080e15840030301446201451130303c017602d00d0703000320340f0145c4030303018244900d00d50741c1e1000010300107184240c861103417241c5015002810503509400030310043c28034000900d4070070f801c42034000306070400b410300300d44e500820b14011010385091340c803002c1e0300910408600d40008020a1001c9485c1a681d20740040c1400042c0450007403070b05481e081c0325040d0401012113051001e402480f40120141403001010310380341c409070308903481400101596001803194100318078051048880034940c0c4e0341072140750b12040e000200c01018003d104545140d85511219170303900c8180c48074008050040c0200b110040e0303a039412802c140310090b00d0302d1461400700051f2 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 369535710 1250 369534460 369534463
    0xe030105011e09200c010b090106030515180c1b0607051b01060b0301090905030702030d05031506040312320301061101090c0b1303020a09060305010506030f2e091b0602 74
    0x28020301009185403044c07842d500300c4031588050214074a5540310242c103940c5031a0800703524020b00655a0004140c501400c07107980b0700a80a4586102e501c543e4070124040c4c408502298201d16403186a6a5400e0202141c0030744a000010041a5000b04070401c0002a0044050010031940080c22a01c240c5030465890072201603019250400000b40014820001c007035000d0008180b24a0803207290090300d40000b45400200003240c2d0004400100b00301445640c645c0304003a80800384c5440e800c5c07d00750340e51480031a1003000c2981c10040500802c1020b4140141070072b1b14510044001c0302c042c0e00b041d000c032050750700901455021172070084d02410340c098144510190399030400903010003e800e00700200078076400840c0c100e0300d180c003440f404009079584003440001004607400008140d03156181c401c0c00e480009110610a80140300c400f8011000407900b0601d940d00e0442c100c1c5000540440e084007035030319800f076419540c41c00340c1101c1005030f1440d05100001c0302c0300268071255990601207 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 369536960 1250 369535710 369535721
    0x106031d06040f02060c06150103060b040602120702030a140f0c090103030203091e060a0507020f04020f0f0f04180e010509070503030f030606040308130303140f03060906010e030105011e09 83
    0x6100d140e02400c00600402c0a22249111039440100b10900d450031403140140341a406503125584142e20111140882d0b0b010b201c1d0300c0041103c43c3c0d84504162901070003039181c030444e40300c0c5005118005112811035505102c1c0340748950b4028689010f03c1030002107241e4414580448001503c105415030f03219281c405103090490398180c0c0218942152a018041000303411007034001d002d600d04101d044e01c0d1340c4038006880b0841f60b560340d032500d484140c010032096a85c02210580503d1040017502080082c2100712001000f008400d540c1d16103101014058920895100204208114041c41080c45003500004178161000d0000c0c0710395214042d515071114502c3c400e0340d6040d4010407069440c1c0000c00c015580c0b048000701010b09080d503940341c4002030742c4410301088603105490802e004141d00801c0b64080724200110007403d1403c0580c0c410081d01c400f6003030701d201e14201c00001c2e07034582c4a185285403803240035000b0301295035030b80110034521030400d4241c82c205000b4540840c10300000e1080 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 369538210 1250 369536960 369537011
    0x415140f100f14010c06230f01050307120c1d04050615060315030a3008010f0501080411150a091403031e040b0703050d060602160b181206010603 64
    0xb10280614140004403802040f040d014140b20741900303400301080c054480c1d40c0380e00e00e5100811484030718940562400e500000d04407a0050241401804940c0b8002219002c1d50741080001c0050407035414017010103041d030303130048110f5060020385041c01d8102c02d40e2280154070640407143c00d6100c661502c000c00c0f803e2003601e90410014800900700e4a08080741c034002c80d50180a9484018054890030504d603444010301a203140440007900e039804441c10b180500c171201d07240150b01e55046c001740008403802407080d2030400038114041000d0040480006014180081154540a01e824800503040d00590302c40300119040b924000761001d4010080d00010000a000e58078100c3d2036908041d04ea82e0040c1c2c007242d1028203001c0070809011080081003090300036260aa02c2d4212900c00c07206584190700240d04540020116600f604001d1351103000fa2444044580d0b00c442c130600c003009080c0b600d010b0a0f0350020310080ea098887c500898058180c0b0466a024000c00c01e15550309241311100a40 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 369539460 1250 369538210 369538229
    0x21b040507020a061a1512060118230d030f090506090f040e030c0d0302040e220605070509030106060504030b010e0103050a06091509050114100f06080415140f10 71
    0xb00640004d03516404090107584540d40320a0130810203020401c030b41212103607034000b00c0d000281d02d68403601e8198a107901510901c0d1060b0401b28141141040c0201032040c110b9860b0010900e00d80c1c54004e4081c0300d96190040c0080d020240e040c280100003c2d804518140407401c1c040c0c0c08a0281490070450300348140160003010341c40300d00b2042c072000344950b005180c5940018491003010f00e100b400010350303089160750056150f41c02c251000002e0b0402a000720700c003000c803a6103c260610a2044042c220760030040002d000d40e21800140c60354890700119981c10751a0940204400c0e410070b01400940c1c0c05290f1030421aa00c9510103140c0f90828000034080703510048a0200195668107c0003140e40300e001b00008508907604d5040503101480f500721104c0c0d450718100c3c8001c018881c0b40c590300098842e4002d14a6240501001800100c4c0c00f40074104054980090288000304e8155190400016010011038000003044a09010140c80c110010300208021920800301850108141c0d80b0015 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 369540710 1250 369539460 369539473
    0xd05151201201e160507050f0f06070c0f1d0a05090c0d0c0b1917070f0e0a03150204060810050a0501260103030e10051201060804021906021b04050702 66
    0x340019440e8005420143c0b80050460400e00390004000240580200c0700d444905404007510342035041213056040a4000e40c1d000401210556074401c0f891442081990300580c2c0382d2040c24003071a402925042050f41031503c15001803012858050701d0748007030356000440080c0c1c0795080c40f4415900d05950320f000541c4245815051450154041398280b84546100340031140d42e4210151141c204102d0404103002d462412007100390080e050201410401451401a15010b140901085400034442c000c104000d448005140c50f03064007000a103030010144040d80148941400295005000f4100007c406402082c009406000c0d4101540d034020700042e44a0b08100044074a41003840040a9007555200d10f40c401441c015051800f950003079556081c1429110b05015072a40000c924100700401041903401e426409a0700030705440315071806074019180d50001420725040e100f0b40103d000c00d0b0000005100381c0001d002885100e1520004021404100c04c01c000c503241190040301581200c2c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 369541960 1250 369540710 369540761
    0x1b0203060615040e01080a11060909011a0d090809010905120706050d180501090203070609080303010302061e121006050a0503060f0a1d0a0e030301030302070e06060d05151201 77
    0x218811503a00c0b40310b025507410302d5541c404081d4110340c2a0b0041c600394200594a81c144002c030240742d0070142c400d0303415a241c80c1192000c1242441c0510911441050a0954020f05281c0c04211031031070b20404c005000c106281e0601c0040c540c0080d54a9020610122000545007004c2c2d940d188451a0280039000301450500c013504c1c540d0203c11000b51080d43c50803540d252044103e801c82c0418000c1000291811140c414145400a583c00205c10b014106c9130400c40204000201c034107503a0b06845494441c1d1179800c030394003c82100c0c1c00c5074100003000b14a41c0c0040401001041c4a001c08001c0d400340c1981e107010985403803160b40446c000240c02040000c900d400d101c04509a00c41015182c500402d03600c0122440081040b91009441a8504184000003080703002d8810100508000355186500d15070f00030395a40c83d98802d1190315020000011042d65466090314280001020203000c5480c0c001010b0750144208000207101d1078015240c03114031035051040343e4400d02c0071018405802d408 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 369543210 1250 369541960 369541969
    0x120a030807260403030f0b030706050c012a030b04020304023708010b011e08040308040623061c0b01120f0c062006040c05061c05040506071b02030606 66
    0x1440801480680c03010309011210140050b20642015400410305080924001301510011040c0e010700b01d05108440384c1654001c143c100841c2c040d0308001340d96100401106015020201c0c0c0d1203110010060b012840c2001c401100210360b0603940c08010071401441080304a0109443c0079402107032000d1904038004034040864130b45d03d81408015040c1d010a512010614400d40100c2c01594555004c0c040c5960010090081e0028041d240c0003d0008050010f003d10f0f8010406005c001074040400c041c081c260388004a0406540800c07114048900021480b0000650340d80b8010740d075900444031200301e07203c41100c2156116808000d980d00e01613983c11540007860301590b61203e52900c00307000078103100d01000140703280c2e12021541162811280954403044d601583c087d00f00344100400a2503004588060720001c0302e84986401c0e004200201c48001350f510502c2081ca48418131051140003c0c0c03551051170030b9683d0a904411b001c42c8404076410110000350980d00c6900840d01c0c9181c07 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 369544460 1250 369543210 369543227
    0xf070801090c1b110a1a0a050f0408031201030c12020d0221030310051c03090504020d020415120e03070b0f0a0e1501060206010605041203030e1c03020903010605120a03 74
    0xd4603e00710b81d50030803000c0b0441500d0f281c0c20044038a0380c0d840d8030f00e14183c05c04550745001000d20100c680e01e00c0040f850101038070320030710313070f241c4100400028075014110003601918043d0190008582d10f070302c1e0341411030742e004400b8002a600c4147e00000020784100c100030401c21a54054000c0f041c0d10b40a509000f41c04502c0c01103030710241d4642855600140040020358414081010400020307031412043c020b0b074496030b804423541500c4062702600800c3c1c020440a00b02c55003914016911400e12000b44000d01550700304601840b000d14407080c409911a07900c00082d0f02020080011201c200a05952413190740401010148001c3c00103180000c0070000a5201d598230302d02140307809180c54a641010728600c0c6911003a4210320042c062a9810440c1c140941283d042c2242b0301410301da480100041692001801c25460b000180303c00c05061141c0880d6540d0040740401040708030070080c0107500300340b4265000c1e40c689200045e44c4d141174000380c6140c7d800c2d180500802019910102c03000701 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 369545710 1250 369544460 369544481
    0x1207062016020310090c03060b0103142a030a0b030d180302060d060e0408040e0604090c03110a03060c030608121615110706020a1209171809041103060f07080109 71
    0x556035164444c000c8a004006085100e1000c0401e5503086182000c104d40c00c40140d20b040500e4104440325241010a0b001e400c42141e40c440c030314001c101c50f2a18610a0203894080840b1404002d1081186854006010088003201a0345007140010740803225005420300d00c400e07c464000081016060540c02040040c10385000031920a4480010309030078241903504440c0500c00203000c02201c140c5000c51900160121024844902c013031f110240e25404500002d0940b0b1010096140f084d610320306482c000715403040c07091104940c1800090010403a41c81007441e41c1c05202e4111801001440443e43e02002050300d8400c4822070342c1f50304081155501030380300d0307050f6155074070900d44441c100580040e510500d4050381c0d41075450001043d68050040106116003011280310011300a104448a4500c1039010707291070350300000b8802400c2c2101d80301950024403003030610060182d1002000c0c1480303419004c9031141e807103100c045150500201d64440004660b40300511158000703401191038103 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 369546960 1250 369545710 369545713
    0x100b100e06030c0c0c0607120207090b090103110103090c06262e0902040308031506130509061908030c0f070f1404110a0c020f0f010e040509010e12070620160203 71
    0x4508210214020303500107c01175550901101341c02c0c01241d81041000007410840805101c1040800040f400c49401030100501a80c159100c6101c580d01c66881520300981152486403841d80c0e41e50003500c4241c140d410a9080e07d030f04510841c0303030300348050b0f010b001e010942104520102d0320322102803040801103c0303043c2120141000a003001c00c600152001d14020302170b035030707032802c1c5a100c02480d4203001801340d024142c00d014000c50700c4011200801250380a1b5484210781d0744090005e104c0102e0514080540040070300d000c03031200800405810340000180490300002000e407030071940c50040d0301c1044001140644180901e03007006130441255580940041094010a406605140c204c01014400202505c0d4150154649101300d034510b50810f4918a0502ca090030008042044c40c0040d14025a204e202003603a00360254003020714550a8000c5d102c1074a40d91003200d019071b0102c8420f4403d40d003420800060102d00ea06901c00d01040e62001740e203854070030f003408000c1c4120404c1c04d9915 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 369548210 1250 369546960 369546973
    0x1140109030b0405101506050904090c050a0806011e05150a03060e070c0309060327080705030f030f0a050f010303031a06030a0c030e0111090d060b03100b100e06030c0c 74
    0x7600202c4614001c51056014021384c030601c036003603422644210781c402c0070a003035002c0800285030408112102e440c0150b80c003040484507410001407010940c2d000b15048003841c00d0004010300d020404a040c0d80440a400041502c901d0b001040e51400340070341903003c0c11054482c41c120b4141001001d104116040c0890f903a944d8030140640444100c4060000c2100016607404042d070014039100503000e20300302040381814900d005040c08804503402c08820700200c1e10f540501c070009080e90440b552041c1140c0c0e03603261107a100c0450780c20507209800031001c3d10000c0341c50b5100c00d025103449a2900440415260303e55281240a008105103500d0800e007030131000700682c4c94210055108244902010550808512000703040303c1d40b07000d0f0042541d15108990251407605070880b50307855000c076056210b1742002d0a0440c01001c2d60082c080d8544280c0310a9491b103500c035001424240021145022103850807002a80e140811280c4107034003c9080002230a46070f801006030224803140070840d01d0 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 369549460 1250 369548210 369548213
    0xb030702281a07020d030902210d1205010605030c03040206070c080c0a06091203111513150902030a1e0506090604061803140f16110a0b0901080114010903 68
    0xc9050000c0e10710048420603001800a200c0c0c0c200c00d800d1650380c10107100840c2c3c680760600940300e0071000b0482d001c040c0c840e2065001e558030014480020404801c091014014203100780d50340780c603111400800705503540d42e003c0401e507441c8102c604984e010749130545181d81d24040342840364030050040303a2211040c4640c0300420a02c804e81d81c081c20780c81c0000d02d0018a04020802c0005d6203600c8003081000418060188900e160030443d4400d9050502c2443d240f100890181045a14000300300e40f0040383c1d0030040c0c50031011074000f0625003d100c442512000661410741900c440000207505944680480c100044404d214141c429010341d00c0c0c07080d045100c1e03940a0410038141c40007802544404d0600007809124030801c016034483d050b0381d00d2080920381c1c01030315401c4020302030103460300f005c144030104080b07290488103c3c289604a1890112071494030808050b6514900b600602141760080340c0200070300f080340c00c0444161610081c6038a400040c0252846440e040c50400c03488410010 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 369550710 1250 369549460 369549493
    0x170c04050703091e03030f0e0a0f020105041a04181436010b1c0302070905100b0318060601050f0d0519020a050301030b0601051303030809010b0a080c030c09010b040b030702 76
    0x201c200c0b02413005891070a8141002001e46444d01c0380c942d07000c0d151440b000000c48000402e4054254400c0c007000360b0035050b00040e02d00780601d50111825a020011042c10901c441000300107840020414059485a26003e101202e10600c4034455a28010300030036901710b40589201094602c5a0a6289001c9600c200940781c00744441c0711b9115a4651342200d6051400920580102a00050f00c240b20081741d10300030366074541d610401080e1980d800100c0e900189943c070b0361025100588615030360b03007405030780c002c42c0000e00031000519024400201d034081d80300710210b5000310344c00d007080c034207110106001c2001014040c1a103031035103206030103142441000e4000f03800c0034005929a19160f6242d4104009002d130b008240b03504000c0d0400c8690322540301c98014006880e0503142801060780c0b031a542600400c01140e00d6a8001d50744000010b507014005181000c0e0802138058070341c0051982d091110202083c02425900070f418030080c0310300140c11014580c00003c40c4111802c2d64800b141d0302 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 369551960 1250 369550710 369550733
    0xf0c01090204020c0d03050c07030503010b031003020a030b0403031b30050a0b1c031205090f0a05030c010c03021603080619030818010206071e050405030f070f170c0405070309 77
    0x3143d9000148081c817915010710903107500c03403020303071005142072aa076400801a05c814000d034805400c001c00801c92603d00c40d42c220000c0c1d80d016121514140c1c90b41801e0446a0b400c403812030000e03080041060640c0a0480d540106400e00e03210840160302810000d40c1c0d0300151008031510f07814030102d244010001e402514001e40036040c000414225140500040e240e2808000c10324482c80d1006c0d000103a0311240d60380c0380d01e400140014450b16002000b0b07081c080c4104881100c1c0c030404c030704003050003030101c010446003250300000c0241d00340b651400d82c240e004d001c20392402c14010b0352096020070f00501c0e403558007400040c401c801c002c0254030384c800e03c64140d4005a5000c0d5000c82c0700041c450110901140c0e55809000516040c58280d0000b0b14080aa840704091a110029522a510700407003e440c0503000090680b00703008001408a990f03000c0703c0c0b080d0300790341d0780c041c800240034001d043c01c0c8644403004e20701803d54510b5140c1400050071010740b121041590781c006000c04900c01c01c050 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 369553210 1250 369551960 369551977
    0x12021303050705150f0313080d050702010513030e10051e1903020f0315580303150b0403110906011d0103050c0705030307170c0f0f0c0109020402 64
    0x54428509504009290582581205001d0754108007003d020000d100700b62030040c0a4540a02e5581c3d80b003c060340c440140c1c4503001000c1c010081842450005250480da1003000207500812840d5030740030078980040d90724000600401c442420f684440d0800010807403544d44142000781c5012840c10510b0a1021000b905504080000c5030501805d44c20a41080035038050b49419400c0248005e1410214407015084082004203000000706d143c94908c0004c0e590780e121003d140800182000071426146146e40444204148210440c40d421305d09000c5c6054410020340b065a00601d03a03030580c014031840203940d05141c0142c030001400606c42d00100040c0d4400c400080090400000344600c14030003070700c0a41808100c0750003000030360102c030001014003024030700400d003502c902e8402031080c0710711503000d8101d0000100b00300c61550445801942c5d04010300c6007540e20b41d5800b02044c21409601c0315110001800c10001a02c41c50500c0039100b112540e6000007000c00b1103900040803a80708016 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 369554460 1250 369553210 369553237
    0x20d020d1526030405190e0903180f030a0b0c0705010f0e1c0c0b18060610020d0e04060f0e01170f061305031603030e0c040b0a060c0309090c05120c0703021203071202 73
    0x106101d02c450308201c19800c6800d4200550900c80580c80208ae6141254001805001c03c000c9801890760100300c0010381da03411801e0083c0c141804220f0100c01d13409107805489940c2014489210a0040d20548007010300c0032025150106140c154020700e1383c1001c0e9050708111514203e0b8001c034016000090082d0141010f0a6140310700c000ca9034201000105a284200d12400301c10f20880d0f00465120005840da140030b001031003903000002d0040c10305811103020004403500229085207148140d0781607034400c5004101a00c054032619070342e0f25025141c2a09034100c0004108a001030400122085200b02c017507a08200c00e001000d6075099243c1c1c01030b40040d0b11003647c0c055980d400d00071340948803029181444000c1c3d01318007188000e9414410b14042045551800040c18414070001c80540758400c42844241d40c2c1c2c0400428641142403202c4900081c500880c0150344001c08039071000f9410340290003004010142005947c00c0146407c052100c1a442074220484a20051100742c28848 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 369555710 1250 369554460 369554509
    0x170709110306090f071e03020c1b09010b04121b0b0d0f0c0f05071707120302070309060302210403050c0f060405060703050f13080409020d020d1526030405 68
    0x30802031460000781c1401c42034a0b1042c18003034031076480303000701124900c00c181b0032081c0c69072540c003117001f841000c40002e410b00401070b602450780d0780c1c4080b070000b10001300d618031856601d504d88032150388128480c8943c8030100091807000924410040203500c024003805a0303030306940304900da0b000c0d8040901141469901c1c208164502818800e18110703510710300c0c150400e0036150350013a0040c0b0403040060410340003608100032076100701c03040350503565024030403801604d60640c2c00f80180d0403c2004601042d6046c0011940c079100f807003914403180220301c5012400c54240410f403941c6201603c180c0800100b0401c10030300e00c904200c001304181a13030707004000d03c0c0382a0804c0c500707220b0054801c800305401d1000f4031001c4003034800708a400800ea01208010388910b440c1041551040364088041d072030000c50b13000480e01c03055010300452811780310280840101101401c0c1014010702852030541240000e1040c1da02000c5000c50750080c10b007003104d10b400d883c0c000141d0003055080103441d00000d080b = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 369556960 1250 369555710 369555721
    0xc03020c06010b1e18030307030801030611130603150512030703080603120915041a0a08090d0831050601080d0203040305060c09010c0c08030c1b09011707091103 71
    0x100301c102d0040c807409040a05104884040940130021481080301140f00032498808031550f401300401284801000c0700e079198403914010b002d040d1700b4407050301c0d550714010050004039100c0044400c000c8449404410440c20154164000d1806e408a04444080050301080c07940b580081c0c0c101545401c00203640b912105d00d030045c8103e20043c1003500070742024030b403c802d1040c10002e4581d002d0044038040303142ca405003e0004103000d0380e8007c01c440d104440300703403203040c1c903280080c404cc4a099880c82d10507600c90b04101d980b180600c108000040c01d160006181c0306546a6100c0c1048000e8070070407060410303401e01c02500750f01d05400c1d141d9401c0000108484442003010030103214090004d503007041d00d140c0f51503440b250000c020006441002850428682c82110014109c1f40d104d03200203881d640701c400740c60741e0390081001c1e01080c0c0b10308612035070b40044c4888510444200103090024070b07803c0000c4503101c2014810145c4161049031404070f40d110031800b030540e002c1ca0018441d502e07480d20 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 369558210 1250 369556960 369556963
    0x120705040b010504030c031e05010f050a1a0109090c02010f0e10050612030f07111e0102160e130f380402030a020f0316030f0c08030a200304090c03020c 67
    0x1603020701d414807008101c1080065800504001281e8201600c0c074045110808400c21220304008020541c1d4a842e111003008245540414041d0441c150104500b00100301d0400208903c40c44030ba010840000b02001022a40e8218002c0f1036458400490a00d4a01d00303154159501c4948007282c580200519503c501c190744201540708a080343c070440e044140b012200e1f1240703c0c0750b0700c0f003101007070004902060040c0711800340c0d20000081d01c0700b01e181c0c0205018010900c01f00d45684d005002e08101c448040541e000148160344011060703695546812100390000c1c00d22290864608180c61060408243d404072100c0e8015200714844c910420100c954480c01c5401055451045e60480706010143e2400200c5415a5505460485401d0a0b410009240c415051040c6803002c02520300402000782911042000301e1084051110040d02c40a440340c99004002882000448014014186807035a541201145d40000252490030b038076900d180003907e01d0070640c04080f81d00050800d440000 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 369559460 1250 369558210 369558221
    0xf050d0201091205070c0308040b090406050909101806060b120907031a1b0a0c0209090105130b2805010501020c0405040203030d110d09110909060705032412070504 72
    0x505200801c101c1442d0f56400040d400e10041d14400c0110110704101040f07401c0324450302442d00030b203010341c50319070750415010f04e030348000c2c41a8040d40c01c1500c00901d03401c242104034090840c10028000c0d140c5181005d0f0f001700284030400520424000201c0301080721440f40f40041c001007030325150341c0c101c80203ca068840028056000ca548050310800204035a121103aa46d40c00707001c07000300c0d20b895452011880720303401e4044404030380340014410301054000c10100400ca100744c41024883c2d5524903401d00321142224080001c0000388064400502c03404800b0307600c045000c4408102900e0a8030410300c0403201e090490107280e860005106560b0100070090030038004a40c140414601980442c1e00c900034005107201c5682c51b20400b1003512103d1099031400070600c1c0e0100072010050402e0f8241000041000b4020b50140340429004480440c90f0b52041040ba1a8540b46442e4032500c0070b500d502e40300341d2004202200da00454140d84034111148044134100080241504220800080f0780 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 369560710 1250 369559460 369559483
    0x30f06020412200316090207063e03092a2211040f050d081b0a110301020a232503170403020309150d0e0a120e03190c152a1a0702190f05 60
    0x24000c201701d202e000030305502460449804c04851b851a014400100e02080d02e20580c0081c07a100e00440c0101a00030707440600101d00804c1c008fc0650032040d1010384151701540d00f151005001c02d00090410300b07038050300c6038860f2130001d1400d00c041e6804401d0030990600041103400010043c400d11001c9206040c0b40d01c0118000c61611368a81c03000382510401406403040d40741030005010407003558a040c1c4004c1106030180d41007070414000702ea07150441d9030078210003040d91a001d040c0400c03440b072140c1d803103a80e0540080d03140c4180c0340200f0481035420383c010001d0b61010010740c82800307510b0142e042c0d01c40481d0014007006400d0324049905620400c080c0d41008960469a01c41c1d0f640011406c500c03d402c0d1100c0c0c07041038903c3c00c0c01c00040b14030781c1061106050500c240040d2590203c10f41786200032000130b4204801070b003200d804c8443e2180001401e007846603d10506034031503c00900350040c91500440e28079031300c048843c4600b040800020344500162420354401d1000a100014411 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 369561960 1250 369560710 369560831
    0x405130536060703020f03040605150604030b220c03030c0f0210020609011103090a030e0a031202060901060914012606190509120301030f0602041220031609020706 72
    0x92440c145074907040c08008c201400d415110310105100980e2031080141aa03c042e120740d42d00e2703840e0300f00b0800750304068400e20340d843e40d01a03c2d040e500070070622a0701419800722007500382d2403964808541c0b106400105032078201d00140c092005070741710114001c08400c5e50300034025526089841c242120754039a41c1c10b41e030800030401c0045004e008240c00700d86943c182400d1000d82555404141800020703040100110111181c8a15464000410900c0b52152800922266032240c2000d400e94a0380c00300d00030007001c407e0040c000c552207248140750800603180d9125112101518861a0070425144462070071460402c001003881580180e42d4814030315001005014400c840105052005110140c01d2002519403c010440190121030051415401200d080ca000e400c00c00c400d03988114600c040400100d516003100c0c10302140880840b06200d007122902484c00380d03940040c4d80411012110396a4883d2204800c401313013003400b4081e04404400e4504000e5010034908160b030b2040100100c2c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 369563210 1250 369561960 369561967
    0x905010b010306080705040c0c0605130c0f03110d110d0303050105040605150a14190203040f090506010f050922020309060907030b04150e0d0c05070b040513053606070302 75
    0x113800000450720100d4000740c1d800500740e51009030885030344441c0b450082541d070a003000c1c402995084010804418002c101d003e40b0950340b103051003400d20142c03100810041282440c00e0701407400319281c20b507960059494421000f0210b0025018100c4010b00310042640d40e401409036082c5442032501030142660050b001c810388088030102c1d0b0080031208410441306025079204190a4000d48503800e6080c051308130b40f82c0e421140a522600a4090580d9134440c1003000214410180941801594103031607002e80d090707001d03004446980c4a40050f5403c000348500400c0030000510f8850b410300c203480c1c1d0068603030038045000d07401e03c1c10141070301081d984144014030100d82081c03099904268000c100300c0c0c0304040791408102402d20b544845400f4000c5142c40343d0019042480e4022003442070061743d0351142ca4583e0301a490049006054012400c07240e0007034100720951089401c540090080140180b040b090481002e01d040050407060311074a40900ea03009081001e01c2d0000c849090541c107 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 369564460 1250 369563210 369563219
    0x909060709090e121806040e06040b0108070c0308040204020c0d0822020310020706090204020304060203060a0911310303110f01051308030402010e10171305030307050d0204180905010b010306 84
    0xda900603003a907944c404100081290503040c40c0441e0510414000d403086072141e684d0004062070700130444400e4081c40c01c001d2851302940c4610700041c400c505c10380364207004c150305803000c68185038010300072a00300e50308000d484543c000410000044292954400c0200d2030030100341284809602581d126040c44000e040b40142c0d8003280e021090540c032040140c4960050803d10050445110081e4001c2d1001051106004043d00114440e283c140c500000655403808002c0031901452902003509205000480001074103c5c0f403421503d501ea029901d4481c400308103501e800c00391784c2c800c030046904140b083d0601d480038001c030f0700c00507590b070000c11041c9480d00c500e921944840c2c0c00100a4500000003404682c0a03401c01015803002400340010030038010b1003c0c06a44003484c4940700d0000c3c2d10b000802c0f00c01002c3c09161102e9000e8003850540d2074003c010398076500589829407420f602800701203140083c01101081d40008240041008405c0382045800c641000e0401d90405080203000d11 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 369565710 1250 369564460 369564463
    0x5030310260616090306090b0703150b1804090203060c040e0a060803040909020316181401080307020907090312080a06090216170d1505121609051003020909060709090e 74
    0x2540301e0815220305070380b00444082201c1c42440358000a00c01b500d01400c601c14040d4000106104000d5a101000759410246e420011140c1c3c1c0d01c90300801440030400c40e0708081102d8070141c8415000360012030760020350780c000303800c00904440f80145c020703000c1401c000c075075020307125a9004070140f05d04020650030300054070703128400c43c0550f102d00c0ba03e03001c510341192010406c0b051500f48424048540c5604c5908884c45d11190031a0528400d00b41000c200940700c039400514102c0c2d625070b008500e80302041d400d2004100004000209200c50300c0c00c0000403e4840303010041e803a09036601d04400e40303004032841086841d25040318213403170702c1400f032000423204c05a030001d05a034001c0d0f0141040342c000322161010748940740b40a00d05509008003c94281282500503003603500071186011042d41c40780d42c403992582d5581a5000d48440c80310200300344c10b203c1c2d00503038210b0741d1014206410380e103d4021540c6504240c840b080306520040030089a070358010042e1010b0716500d0414001c4030001030100f03 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 369566960 1250 369565710 369565723
    0x120f1506011707080c040b0c0a030e0612011e08030a08090d030506030316110d060e070b0a27051012060b0c0706050c10060312020d0c080706180503031026 68
    0x943c1440f071114045409004160103a4004004540c0c82c02d69407111200c01580303591090b4822804112291141d104034a410000c1d00c000181044000f60180c4ca0858103c140d1079031041072000c0344540201c003180100c024001403420b0301d40d81c0c680c5191810454080ca2070001d40511030310415141c0307414841d04e82c0d008000c6803e071800154800110050030b003808840c000d50954602c0d845a100c0300003504000302608030000306402ca00903114466550f540c1e603440761003901c0c20400052150401c0b01e0003a0340303036428013040708101c0001441d400d4880c80421124610000118040381c5000041d901000c024000c010142c0100b20282e030501101e5040035030344036800e000355802e0090220300320060032410070114a07080400041840b0041e5281441801421131016000c0103000c0e00c1e000f142c6081c062200540318683c483d4039a480d044950325840000d1082c0c2c4400d003051102c050300b035008901d0400c09035018491103902c0c030703540610304003030340c12000d1002407048088038503a40d840300c04102c04100c0303 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 369568210 1250 369566960 369566971
    0x2070515011a0307032c160806070e0607060603020402030a02070210020f1905190b1807030c05090601020c0a090221060612190c0513050d0c03020f120f15060117 71
    0x108686c452002001001b80d16228055110031281301d054078803000002c0c420505d120030055525900b40c669800545800c030840700800440c524100c201c4490070401e005105107401901c00160290302c03580028140d0b4020b0381d0018103190041140e80951501c0d505000030580c581c0010081d021075940c0c0a40c031078007074400400e001001040c4200510400707103c01140311448134248044a801483d01688106c1c042c0c0b500390900545006918000200054003020750360405c1010070f00d5880c0c4420811140d070001e120702c1c118050349000102649070700400001405d0205d20260f107940f021003200c00440141030891034402c60400612403540c84800031141c80e038a2110854010340d90351585d41e824100c0200b04c80f4021840c0041c2ca25402d070b030020280150740210008a07900c03954407410000810340c0031134081e00f481c4c2d0600041005103131560020002c1c4a0103080b905811483c8070352107003450341d05d011508041d000181020389604858203442d81c00902404c0189003408000028504800c00416 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 369569460 1250 369568210 369568217
    0x3070309050f0a210b0a0f0c08010b0405060d1d0a060c0e011b0f051507030c0509100e0a08070b130501080c0403030305150d140708010522080c0102070515011a0307 72
    0x1404e860580140b0300c072030081d089480c1c8060303401e141c52800c008103006440071010741c2c0b52080c003000003840341c85041d04030ba591000303d07414581044200080f40e84040c4010a0a0342d42d50090b040c420b050860305620800702c40042e10540a081c00c10000391280c825500c01001100c0c840480c0c00da810581d03a12682c40c44003100d02c07902440d0b250805403148035040c0500140b0410000824000008104500c00e486941d014401c6280d2584150399038010f2301c1c0e0f0a50700021086c10b0b020304070b2090b1000c1c500e2800081241d01669902c00c02e05003000c0031900410381c4010005000d00c5807049460b0303900c000308002c0c07800813154a0a60f000d958030740182d0000034101520740d004034403601404049a070505100805a074003840c500e01e8100c0c1c04445a4101540768043e10301d0029101506203c1c041c440d82007000f00e809001e5003441c0143d8404441042201d090b00140500c0541303034801d00c05000d00c503114000a00f84081d052010542382c2e401603001540caa10107040250408109600f038a0b000000b504 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 369570710 1250 369569460 369569489
    0xc0504150e0d05011d0c04051909060b09010b04090b030706020a0327120b07020109050d111608010b090a02090a050103020904090f05030316020f070b2101060203070309050f0a 77
    0x400088440000302c402030815070902c0c00d0540c541c45460800c0e0035031044401158203194004007408281c402c00c8030301d00680c40c107084060040382c0b0a6001002420301ca400d00084006603940081c0d09981c0a820480c031300e00001c901804041e166100d0107201002c110010204507140000c003d5070303141c922031f005040180400304090300c0032039040f00e139000043d0161107080391a1a1104c6110360400d42c103040d1040344180011a04450061190104280d040fa016041d1460f10032b1040d0303400c0d001042c1004082c0700c0d04041c0d000300ea07140d40e42c0d04040d207903400c004101903001104000041d0300281c0031000d510300c10003000f821340d60b94080d0b10302200e03030a08000d41c4400b004800a0001c001b40b550141c0000c800d15420f10800c02c004c4020341c8104540c401d1041e04650841c4101d070365480c2c0b0300418100740c0c040001400120803e00c0603005205460b0402c19501d07090956014140c0001c1c0d11a00c0541d2010842004040e00001400f0150000350f91140710710390070500154090400744541103e003500c00 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 369571960 1250 369570710 369570737
    0x31605030f0304080711010f200f100f0b10080103110111030a080105030d0e15030c0c030d0c080609280e03040e0a0b0306070504030813030c0605030a0c050415 70
    0x52003507420440809000c59140e1501d03050450080d4008181100c50440c001940707201c030341c000c001c520742c1000c859441250001c101120007042c694200034540c040c1c03082c01c001c08100302d41000074024000301c406000c907140c3c0710710580300e082c2c031411043d03944035020680b0a070901a90240a1310b04480c1c002c10102d408500c4400140e40080c2400701c070410701c0c000010302005e480d07040000faa0413180305174111003015400e007208840311007041d40459030081500c1112528002c4008c05107030170127078031311541e443c1c49002101c3d50703d544d1181018407070a070780740d41c020b034070182c3c108482d20f500c04416203000000e850320400158240d40e0510f0f1800c00d076441c91451000c0c00040e41e000c80c7d036074494030041320395440d103030f0344940540242100c440d000141451400001c608001c2030300c90280d01143c5070b079030500b03065945d501c51503044580052059030480000001140801ea82c1d48001d104581702d080ea282004810f460a690180f140c55003481b00c2040100406541c0320b5881d45000c100d8940440c0c3d54088 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 369573210 1250 369571960 369571963
    0x60203071b030b090a0c0e0903070b04020f0a1724180f0717190b0403051b0114060f0a03020a060509030709020c060910153005060703140108031605 65
    0x403500054200c0b48a42d00300140c94078002007401d0914043c00c0000112651800152101f5004032240402504140301c000000344000a990f0380140c03000300400e05d515100008030714000142e61000030104080c0c000200007072828444c0c6c0300d080c1c2400d0886907004030185070b8030003020740281c0300d42c0e092540070342103c2044c00c0a101100080320b802040e1850241d4861030791940c00501000c5900038020003825080010150400c0c100940e84035000b04c5c031076500c5403000d42d10354102d0384501c041018050380d4107042003028443d07040d00880851681600342445002d0007070070304c64042034074020100c0c807509102681e500d8001c80304440711458081d507284a40804a414411140d10280c0c116001040d105454200070071043e22441c4040c2c1111804101b01d80b1a4080c0c0344160f00240e242031030741c0341c14441e600c055001001c903400d45500043e00c0c40407190342e000111401c4501a00d494002d68103000040b075040c0190008902d071a081ca4006505010400341c403031203000c41800c0005401513400041050 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 369574460 1250 369573210 369573263
    0x1a040302031902060702010c020f061501090f0609140627030c090a1b0c083901060e06030d050910090e0f060a0918061d0a060608120406020307 63
    0xc02e8541490700e004160340281d0f079103000795107a40155003090501204688000380c1c60600314201c000038003223916828030551138501e0021301641041171001c0082940060407206100a0039150759200e000d0345000b80b00c060118100341c031a0700c20f10003004000744010403981228522072800303c101084901e1500064500100341e02d2060300801150104411403000d540042c09418108080c1d2002c2802d0f000101c518050041000784004070502484040c400300300100b6200c0030310b01d6101c000c1c1c81c4074120000076000905040c00c4850791582010b220807165800a55004103041d002013200c8109400064943d0055070f02c144d00407040703c4030755135100740710340e800400824025103403048a00f40301d544030282c0346c8225030071800350100c03000c00a0340c40d46500c511310242e000301e203180707440c40c0d402e0f620709024080c46811914146031811240307480141c140400681c0702e00c28000016807920f04802c207410500001d100103050001880300f003004607001710440348020360022201200e1018007054002950 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 369575710 1250 369574460 369574477
    0xf05091e040f050f16050d050103061a0f010c110406030803100603050c03071b0201020f070909020a08010b0a0627140102061f0603020f0c030c01060609121a04030203 73
    0x61444140c184401000d00a1080950a860621500351140007440950344203a90fa0484011030100203010a0064165182131000c245030091038000700c89001e10a4a81c20380080d00c42c1380ea00c420315203042c044000000225042034410040842102c0000f910400c920000030340502c000503e544802d94403075000f0000755034400c10940c0c1301c2c18112110000c4903514000c2d4800b082c0741c40081040078001e842070340e11451095031480104052501044419039440808905502c928981c2d214581d000740b0012000d4509401c0011b0550102c0c01088541e0455074003018040e40b40500f2541b0760344a00781010180c3e140c0d81001c14cc1761a464804903010404911b2200c1200e0703413480c001c034407a1050705245c07186007400d0f42100d00948900792f4980829221103440a01964441020010f04c3e00a8015140714040c42c80001e007400c0d5a500340a065900034000058965525002441840e800204400140000818140d1203660641d92102c000030700c5076000313000700b02c1234001804140c4200210760140 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 369576960 1250 369575710 369575719
    0x5030c0118091e11040518061c1b0311030d0305190203040c0305030c030403032d201203040303140705030c09040e010213090507030b0609040f0605031911060702100f0509 75
    0x543c1215401540c2e1741041c042c0d2803180c06035681c00c2c19480030782c2145c1030180c800101031075007107c1e107000a109010760a406c1140c204458690300c9400000e030181c2600218000c50b01503c034006d8900416042c200744030361140a1501c1c2000707002100d000e4501c2400701010401006036a40c50f1800e00c02c000c2c61155000400c640b10020340915940d0022002c6c0040380c2c40f9440d85032070007010751004504182c080c1c032440d150341220031160038035038400e203c5000014a240300305020b1340700d1200418280300081c0403505003041e00100740000c05a0601c29501d00c481d001504c0e240394280390b00001c10b24130010b0141c281b04000841c80c881076640d01c0c3d010506120403039000315a81c007240075400301810064801c0076040c0786003200080391640603004420001c1d5004044620300f0b000c0800b007000a00b0700092030200290b46a10104503520204521921041e0750001052a40030924104065821059440e800f58100707218480068841c0001c0d518210020b051100c594440380d0012600d5004003900560300 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 369578210 1250 369576960 369576971
    0x6040605090405060a050d06050c04080304030507030b0f0f040b04020612010e1602071a07050a0f0f050c0f010507061d01020d0b1309080418020708120105030c0118091e 74
    0x805400000034414080142c9080c0300f5903440e081000b180d51194031030396801c29400d82e0b0f500000758003076125075400020f202c5c1c481d0510303844050407851504160012a12903003d21418414030074038031200d40d4040c0040320b601003c0c0c50080903400c2c4848002d44024000c020301c4010400b10740d124400e440c0c51500a1400070920b40e520704031601810000d96142070a8043c0c002e8402401c5d101060020a46a104094111518003912140c3c4154805902901d050145020134000920244a1030b40342030f00400c00c52070908400e04000c0c3c14900d1240056100300b5000200c0c0744180d0f00712056810281d007060f0002440343e0350a401c844003848890361072049500c00101035100c104a98440c0082c0711003601c8141d03508500038008021110007001c0a40441c070305100400c9888032061500402024062016040c101c5aa82d08002d0b0307001120700800f240408001401a030808111114040f6824a09590b29090755100c1110088460007031411460302e4002040ca5409100c0e203c001203015200100071 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 369579460 1250 369578210 369578219
    0x60702100e040213031202070305061504020415020102040314160504050c130b040f0806060306010b0c0a050d080f0703140a1a19030c121e02011704050105010e0106050a021903020a020604 82
    0x7080001c4d404100d8004040240d0f802149200160340c07401d44e43d10000520103512081d01c0c0890080c540304c2c5290740950200008642c40c401a603100341140190b400158a40d4250b2038622803800000d02d0f44109984a10038216103d2000708100713080711010307070b4001003c0d120380070080260710a0400064011113180d03c0000e00d003204a005004942900a48a0459494240c07143d1180c005403559903265110100520034203801030014040c003516038007140c5e50003c00740d4a00f41821440461030300860860010000000700d2603416036442035551800300017402c0d005041500b003080180c00c0302c0c01d0f55503c550007043d04cc5011035500500c40d00501e07140714101c4202c04150071060710b00048414180c0f00f00000f882140e1006160030965100040328800d2041c0010340001c4000010300342c0c10400f0165549a00301541c0c1c500a00482c080c40000c915581400300002c1216410f900280c1044000c104001c007056001c80c000d008c50141c0d41d81141c44070942d003000c0745401801c11020390f029900190025 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 369580710 1250 369579460 369579487
    0x90b0604051e162313090902010507150e100203100e06010903240207030e01030606090b091504051503090c060f0d0203060a03051c030501050906060702100e0402 71
    0x144280800c9500340615a25005044004a24000c4084258900402290031603c804020000d0b80d0b00e18544003202101d10301d8000c02441ea1440f10240d00071000032980706940b800500d040142698400070311420034640c2c0001c24504c100e00000c0c109006060204032012142e030800b070016000142111041074140d03180500070340c07080c4c80415030481044000601d8030f80c3c0b055254071540c0141c559100c95882e40d25041000300d00311145013031001c0000c031003a030440700382d10180c01c1d80d50007030399010b18401409001504680458004409102c020041007258030000c8080314402e64050f0740e00801a414094541164080c640040b83e119544058442c60304115001071441140082c0c01c4400c00d072400b001344005442007010050f07280740208030840d8980c1082d00115009080905404001603880c3c4910b4145404031a4201101c0c03100c043c00c0440d1a03040c005c03e80074140131a0038030140c0c00c2200000b202c5110321040240100082c4201d604440e01401c480052010040d1080d5074442040b101c08 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 369581960 1250 369580710 369580733
    0x3040c09020c2e0b1008070c050a0204051008151b0a020705030304170709051510020c030a03050a0e040605030d0e0d0605040506011818060e03040308040f06111c0305040c0909 77
    0x3000e14134036042001c081481d007000860040e400386d4a60141c280c540c0c040890303512070400001d41d82c601c02c4900070030042e00c80d44034440c4a42c12449c11006000d0520b00e45078200001c0c43c50a5240711460414000c000080442a01e210801a100d0540d9554071103426420030000c1e83c01182e0602021400003450304010450604005001041c0c92209880b0140308080300d0303050f16054030104a01603d0101824a6170034030152951038011a2212004940003070f00d048450181100050004034406109903000110f01c00c100b0001c4030300f4003c1c00e0400f0042a134500c00601d00c1000c1204101e000c2469844078601d629031550480000d025925040c205036a45401c00e125200000031020000b200c00900c5200b004071056102d5014031452406403182c40241544d40c42030300050000700400170018104000800007085240c803d07245403440d004e4060029881d65086003041e82040119402a130007148035410003801030700b00050b613030721a03041624081120b40c01c0420007519105000e410700c0120203a4 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 369583210 1250 369581960 369582043
    0x903011104090f06080607020c1507080a0f0f0c050a120509130207020108060a051c0501111c231b0906040611010605302514040203040c09020c 63
    0xa104d000ea86810301543c1d1101103e40ca0016007090326101150315000386090702440c0c01d40511802c0079041c0d01da400c2070394044481000421060200c9207492034020289080001080c203012200c41102d4441d030362940000400200035692056800c080507000d40255044c80d50054140d0303850703070483c0c030618009600601069001c06e10150028516151900d410f00a48001601c07494209698000c7e464192031a14001c440035500d0f072070182c1e580c8500c1d00180a0000e15020100f0401211000c41800c03189030703404422140c0381444c044107911410005540d00300b04060780b80354082c403caa400310040c0c0502d040e0554402030010300064143e6000c1d18100a494400000700b0100daa150308102200000048221004040032946c0d4101e03001e041c481c0740380300500015144158a00310b403a1413484881b80b01903020074000c035000d0004c800320340c2c008a03808005440462030360809403118040b01c181841a02c0c41e0030b40000c0d1145440c17509210210036580400d00a109050000740500ea0000841c0704 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 369584460 1250 369583210 369583241
    0x3031201060f17060a03020d111009030b0105090f060d03030608030304030801080d030c0906050d06051215071701092d020a1d090a020a14190806040c080606090301110409 75
    0x11a000e01c00583c041203000e844010800f54601c0c0c0744d90f0074008121010403081d248010380032110140c5440e01f0140084c0e0030741c00d9940d00c1c0c40506520300b43c0c0c1c100d0010782155014202c1d1108001c8c3e8034801044164000310100d8108600c8090343c0390803009030220b600500042c0c00b02000b807008058102d110075050b180c080c01a00d00158000b103089040700c2d03281f00c5190001d041d48004000140c01900140080d0204440204490742c580c00441c222175910b4240324015801214204c5900c4405e0703641d16003044043c50103810144410070540d180305818000c180720190f55182a0400d040007140300b44840c550100340a0308400e940c80715400a40100444c40046044d41c4e250380c8680005420384003200ca4003c0000020f47c58082082000b5000714140c2c40c00e026888420900090501010340f0a941d0407980362804800c1c42c0720010180360000e060036000e5400c0000f0b0300c09a6402c038030361039031143c415110300361101d030758034002405840000118001d400000401080d0142e40350000849564041d2 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 369585710 1250 369584460 369584477
    0x1d032416080c030f2a12150f090901020f0f040305160e010e07031b02070812041a0f070c0b03060a0905040f12020c0a14030c100917030721110c030a03050903031201060f 74
    0xc0001a90111070647d151300c01469000d01401385840740f09545c01c55407c00006040000c41503803c00e280c0e00c00c003070403014010301007001c00401004000d400310346c07120f00b000042c00c80d1074540c29440200041c00b6008882032002d0024180c10300c25030115940840350b174118510b101c292040a91110000d004407200360144810305580701038010b08881c100c4020310844c0500544003513440c801c541002c0b54004000108000c0751300450a609200f40c042c3c40307001040c5541c0d003410820400855615400b07600d20a041004200c0840d410711561080f030303600603010640401009404038148200003140581c03040744500c010914060b412141d8400910076400c40d40035580c540104a4000084a0580000358061405000aa10070255590341440d14000c0f64105207081c3d444c00341e42901185840340b4920901385015480303a000791546071044000d400f4102c0041c1c040d020a89450408102130240040014002c0781501c0030801c50340c644030180f60951345961a0385008210b00001010b000c00540e035003 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 369586960 1250 369585710 369585721
    0xf030705091f0e12010e060f0f010608060d080d0b090a0603060b040902060915091e0103150308030105061c0504141b011d032416080c030f2a12 63
    0x456100b03a44060980352000c264050404121001d41d02d034000c0b0205548410320f8200408017002581d0103400c4c54040741144c2c0c5000b40c1c5034911030b030050388120100a210070920400e40c0320b0380e00710011a5000140e4550b9480100750007000751022040303a0303401210324002c01c03400003000d5010348156803180380148500c0c44d564040000f52058400080e42c4000c003044008814504041820b200e0818050080d09154116000554084110006210b02908000300f28102d6134144100c1e44c1d041c0c3c010020403999821a100d02d5618003050003181c0c0203900028900020307885021801c282c04003500c5082c4071924181c80c1024415118600f03544251060400c203072740c0340030314402a0565090603503440019041900103412041881d0110b180c150095951008011800c00e11390f05400800c08101c0a0a0905031011100e94070320b1001e560400074004c05201c1c04a100e20122030b0808100b16203a41d80c1d1303d86445100d800da417000c103601c3c080c650020769120113024442c040d002004c401c12240d051540c40 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 369588210 1250 369586960 369586999
    0x20a1a190203270901151403070305060109060813080f0c250501090e0714090d030305190603031d0f130507080f090c04050a1d0a1b080304090905030f03070509 70
    0x540e041d80c1d100c0c130203200500401407400f0f5040405402071800c400908504180b002050b48140c03032100000362100300304001542c00080150040510745000c14032072410018031300c200c0602400080484200161180014234000141e954429213581520100150107221116481e000c0b10358071010028018001869370080c0c0c039003c221080030b408903c03650741d00030302285c1c541c0f00d44020380300140c018400100280c0710380780004100c0c0c1c803a8400081c0750800947e003c98100348068108009410401d00f0300000340d000f40e401c1c00383c0e0f40b2a0003041c06940707020001403848048014250f0440c11240a508440806421050044405444644154480d04000000e010080310500b060390300c809807416480c1015400715607c407250290000c0c81c0ca12a250000c00202c40c01a2074089502418100b4140180c00442d601064110a1540700441c94454425200c0c0070350700c00c0600046d030710400003060000610880307180403108500940e81e4500110050017940110740d4060043c01c00810311500c2102 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 369589460 1250 369588210 369588277
    0x3091103030f1801090b031311151b21030a05070207030f0f0f020a0f0501180f06112119170a1104030c030302010209120703020a1a190203 61
    0x203804404600c0c01c0c41454103c0c880743d0f2244101410009000d80016209410030095030007220042c5503200f10480608141500c10010400b0301d01c03407240d01a24041090640d012a41004801c442d91a20201f01500223801d240800250788a043d040c2c200c050190358a0717030f00952003031848010070040c648800004030380e113682600006040240035100d01700412100c110b00c140c03207441400d01d480d21400581c042260129503510145000303406100900031907030000c5403404087d1010840d881c04a1501c2c61404041e090340c0315001c00d200c81419411541842400212380d80510001c0d0141c640e46003106c4400d05a100d842c4003502c4920fa0340c0505201b1f0320800e03d60143e1a091001031a55880d00c9400e0801041420880f0344140360800000000070460640d03940118040c0c1c0006840384040d5062000050b406800c000709500141000e000580d944145c0c0c600784d800e125590030002c420b210078001c1c1403003920401c00340d011000e14030280099000000344455030500402e80114055012018004807 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 369590710 1250 369589460 369589477
    0x9010f140409051801060e1014060304110303070f050a120206090706050a0201021201091410080703061104080105040f03020f0c1302090a0f030303060306050601080f0406090311030a0309110303 85
    0x1044100889681c0d5000644c0010603910490300300c1c0d001942007401c6030807541c40010f0010902d401c200c10410740324046c0e40240107074080c0455800364400061010f210040005048103440d175410411381d1030030015940c02d150300c06444640303041c0301e080040e619600c80d0b80844540400c0d062007481a0310101d0740502400300440208002418004243e5440d0464020b283c06c42d9428440d21100942008041e40205044070000074a6000f03040f402d190103600900c1c007000c1d844000b408025041340010709504803504044001210070074184191102d1055a008544540c280420702062044102e481e400c0c03d4480e800b04c590f54001c0016190321584c048101d01e503ca9044141d50300f04071440d40040c60408801400400581c0e00c4100f25003140c1803d81050740003c4d07840e1401d004000c221300c10240c1185003420714451515000d018ad1400440c010001003241c0e0325051000c0c1014011203202c031110302000162a01c4150040c001002088502c4c4281d5071440740001965803030502008a1701d914 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 369591960 1250 369590710 369590747
    0x10b0907050a230d020d020301050405010603020a020304090b0414090d080a051014060d05010803130519060302160b070f03051602071512020414180f0105130204030209040809010f 79
    0x9018001049909529103070720b01d000403104000c1112000713041c0c8024203010400100c0144c481d4182010302c01100c80580081091510410460b08020b4000003500c04440b000c00020451004890104010b003010880716184031351254141b01c3e0029010400c0345013a09a542c40400c03070368503d0069000d565041d01c134041407a0700194240144141110441204080070b0402c130310301448801400d00f10f43c4c1c241e020107400d4101043c0341004405c1a15050002c1c4411180c0c0c00d801500ba80c034030340d44e8001500c28031092540c0001e026100b112641c1c032800c4030b540c210015010a2800e120054500182c855100b00024908000a80303502e6500400300550001c030350050034000c0c201840006030540816006060040c4a04002c0743c3c611140014000761160020f040210751403842440941805820540750780f8141804020040440d004001e0448004403214407a003803000e102f0310000e1041c1d400c0a034200440408100501280e84010070b20180207036126084031500110803101c41c00040f440c136410 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 369593210 1250 369591960 369591977
    0x10b0406030c200a0209070f0e09040201121103060406170a0b06060c120d0c050a14091302070c0311030604080901030f2403030f050a0509190f08010b0907050a 70
    0x14a407282c0c0c08101218032070b0074008500003984540620b5298480e201e0011984140481c00450908100c001e800030094100301d000400c00c0100500510f40d5041d045000d10801400542175a218940c4503030126500c0388100711142c0200116805030780200c034a00e010ba070600701c000034220440d134500030701c0d00740650103003028182c2aa5101d84100b40a00f00b05d6010b041882400011401031004040440c00141e03a11f82d554149001c030026940f814000c00107203c001d11160522301d41010500120010b155281355881006000050100860801100170148003060010130000c03c03050302000e5134001c044885550741e10608055461004130b400401d4404280030b00703170065000ba0000d404188000202048460601c640c10100050041081c0440c02140c0000c006154205840c103044201c145042703881d001c0b044e00c01030007500c114650640a10070b041e0348407400c1c4c9442006031010303200350801d401056030f80300c1269010f411502c1c00c842c400c3c1100c0003c540d11500aa04858480107a034841c01d05 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 369594460 1250 369593210 369593219
    0x10b030c0a06050d0c1403190b010804031b050f150105031002041a030a0209120c040c0305100b0711220e032803060e0903041409010e0f1503010f0207060c0305010b04 73
    0x717800e08030305036818805034208a80814401d840039510805001c0844644140015010340540c0d200880880c188000c0c4814400420790261000740c01060120800300c3c8500c0c1d51405c103160905060300c411050207140507020b11440c1341c01c401030481d1000c408039800000000b011030128030552280d00020000e03150034001808005c4040d55100622440042c02c1c40d01d0003020880f60340496008661a03008800070709400e180a10414491144078542040b0314504003265001a00907070050039044003001c1240d40c10000403800d0281c42c0c0b00090400100b810081140e0040d543d10710300702e03040850401c1c201000c100c9001050f502000c0aa00d04c03001219518441c1e1100280e401da80c9604140c1c0760070020510581d01030300c5a02074681c000c011540c8920345101d100201a60b6580c1038882d0b001c040040000c00c04015040d90400d1449203007290b10340314210346441c0c252440041603015401c00c18400d035158040e030302901155025800a101111141a046048071401d014404070000284818072 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 369595710 1250 369594460 369594487
    0x60c0f04170a021c0b100e1306090c12050601170307170c060103080912070b07060506010215070525020a030b0703090c0e0610051204031809020a02010b030c0a0605 72
    0x311007945005807903501409801003860400c41007500040460382a01640400c1860740300703164042007210440c03a070b203420642d1034400c502014081c11038102c01c2400d13403014000f841c0d00c0358248680c0850b80d81212650781170b4000c00f01034500800da519004000c0009030008880c0100700d420b01903031001d1861b002c956030307800c6210b48404000b030020350402c0c07000d0341c950642008514080c5005494081d1030303038025800c001d9800450000d000d09900301186c00c0103a85100400d5807079a5912103c0800c84d0340e80c500040345090310402c10002b511581c501807041c1541c0000060205443c101005035481e10920000d402c10540810300070b412000d840020808584920718a540140551502052045031505d1b840201c82e803a4200d400100112002e1000a2901029404002c80c09080860a0180d03040309030a0184000b0401f50500c030304403c041038070b0030b00800c40c0c0b07015000212086480d5911144002c0c002c2c00010b001c240244126960425103281c0301403150103c0d0203a41c1e68600d081b58840c0800c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 369596960 1250 369595710 369595739
    0x70804050c0d06021b010e100e0601030f0212060103110a150507120909061d01050a2916080c060f0907090f0f0207031101060b04050901050103020c121b060c0f04 71
    0x41d240f040e420f20a03142c00400100d002c900725800480003140d480000400107007000c0e0070f03460b40310404e843c08951807010305000c40d481e41126040f2800d55041d41060000c20700c4001c02100041d114001c2400100400c100300c1079038680940140c480740c111507229010161040780500280d40460000d20126000482200ca41003d030340c05850140c20382c0340e44258900907250180c000700700040e035030000c01c1403040c0300c00d4107580100380c210340210103240380c00d980b104a806e903d140e040f800c01102182c40000103101040b07a15034001d04042850f2992582040b080d583c00510540c281ca0040300d02040d044010b41c007030310380901c4509002d070002c1c510340280b840040c003c4261494219480d40d286d0503d801d0300d03201a19116000f40c4078aa000038401c0406801c403813068001c1300440c0320500003400389454119207141500c100b824016646e2644c01c42d0a07142041c180b201d104940000103440014001407180b1000d04602c0c8000c0f01e18a817144100442d560051035480c5420031005e0204004803140003211 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 369598210 1250 369596960 369596963
    0x117030f040b0918090a1b0b2a03040e041406041101050c0c030703050307050715050702010f021f0c030e0c030c04200f120a0902010804030f0908010213050306070804050c0d 76
    0x120b5040b20000da0041e60100c480000680006c07680c003051240503401ca5509011b0580388450150408450301507034003802c1003070701c94994144040c41c00c00301103512821a0f03540d03c4045031340f92903803100c001040d0041124100c601284464110014803400102207028136442205104c000c80181c0045645030001030992102c1d114104451034192001d00409001d5070282d000b540e41d541d498146180b400450342c4c00301030003240e1a90800741860b40007047e02d180a5091030080815146c09000724a07102ca96002000051141d5101900d5041c503940b14001044107a03c0520030080d590003442d40341d100c8089015010342050202040b10301d05a848a0000c0c44212a4665a4024111b01030071607004400750350200c0b80c001403ca80400d0030060107550004550340705002c240e501ea40001e04ca85030181000302400340030360304550700c6400340f1340b00310290000740006c5403a1101981c064056410500c03c1d14001c1c005c110100d4015445601d42901ca10b0f00200101100300d018014030040a40b812070 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 369599460 1250 369598210 369598219
    0x14010506090c1c060801020901080f0405060a051e09012012060d020d1502030103062d380f0d0b010b0c0c0a090b03060a06061d0d0c0602060117030f040b09 68
    0x3c2d405911446100d51800b0300aa04001a150000d040000d00444030180c0031000400e075000402000600015242e5031103004c115001c2415101d001d41c0d0710360700d0904441d4490502014041000405055010b0908407007403c802181c02c0c001c2010929403807041c0d1090346e46854103400061200e05190142003a664030207801001d19100e80c2e1180000e00041000300410640c0000040043c00782d9402910001040221424001c01e1300668a21211920000c03e0708ca558a5030300d0b4103e403140020300940903948114208500303010f2406080b8800020800151180d0744d66a007620490500048100919500c03007500d0f101a400c1445004240e00183d1588445120b040c00e401c52544a000c40f040003400100008207041280008040c1050401070094840c42d180540800909034090020303034681c2040d604c0503e0501c1d09002160300898941b002629200c0a9400022000c0d40040c4c56412207001141c1d088507102e120350410b032240300d6005070a0803c11f09201c24070400450302c0062031004001007 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 369600710 1250 369599460 369599497
    0xf0a0b241e03090708070e07030b0a080d0309060f020306033007111309051b131401060f09060c03050a12090b1b0c061b0c01110714010506090c 63
    0x160605032103111540070010085011041c800c002000300034810140c1020381c05850307007908010b1054600f1000800032170405071104103861064868404c024080c04034101514280400c0490140241ca0091002c64041c0d1510340b44841400c3c1601c01d0701e000d404010081c101400c0c1d08030071000f064002c0c041d0700890b0350a0603800060b5125000040580d00d2044244054804c688810001c3d007200c007800c5128502d0a24181d0000903034080760000c6030001d16640c0710900c60210020403203005418955458580c50702080e007103c40c501035140c5040303640300da071942c03a880c00000e821202060103100b40300100d500041c5002c0000d00030005008014064038040d08005c0b0080203510903158001c0041c0d4902000304148a0242941c40302000c500401e101007514042200c3c005a0b9201001400e0340b0000c090001c1c41815000b601d421540080101c000078080c4d0210349070f1220050307003c4c120031907013841403008071580c4140c1030041307600c0380000810184807681d513540c0c00c0b250740d84042c50540c8030802d00f0 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 369601960 1250 369600710 369600727
    0x1e0408010203100608090a0209240319060c11070306050a02070501020a0f02010b180c0307030b06030928050d0309021912060f150b091f080f0a0b24 65
    0x2480514030a40075000c0f203000c00d5280c0800076180850150009a0a4000c150020056181c00c8405a0050f40c0c40c101e007070500e070669241c0801e0303420100d2a55494020040c601d801482c4040c902116180503403000c00c081a1580e0041c0c640040c1c0b503134100955040080c0820104510790301c250b0f17001c04c5001001d0310748422a980e681c00c81e44103480340c40115200c05528042e0690900c503558100e0000c0c2d85801500502c0d000366158110000c0500604090010001e5003d0384203070412100c00101409880e10307030910540307050701c1d040007528012038032441e00100026020b00d4554144226006000380c5240201108106c2c00380608150683e04001980b603058929603034000c19100400288013190500042ca06e007050694044a81e049003090a15004000144140030171004441001204035907880c5a1004139001c8604203500810031580f0b07894559000350800b00e218803540650f000ea18540da11580f001c1c01b10380c0d210342d0035a0404011300b074028095001044070302c1c0540009140c6820030b5800f = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 369603210 1250 369601960 369601963
    0x9020f09040503130506040501050706091104151503020313120e1e010e040603051f0f0c0302030f10080c01050a09030803090a030908010504051b0409060c02250302061e0408 76
    0x103660840740c0d03510000c0c54448075134050314968050b040440d0054070309850040001c1041c0114107010f0001507594140000b00810204c1512200c1d0000e0400c2c400c0d015035116000c8410654480d41510307400461341e0348802442403084030f04c2902c0071121508502d10075191100780d1845038192405010302c0801004641c1d07654581350350034280144401070100101000103046100e00425a401642041c0050000503800b03d801c14010480c403000505c10f40803010807401400c0e480d819110400d282c01c2c1c071400700355455002035119a8004031600a00e8444501340d4104207038520034442d05070481c0f000701010350320a0b401880c100c10f4030316210f50500e4598440f81d46070b500954128440c0d5020024180815411a0b0800002c011030360003003015141c1911000d03202e03900c0f411001c2c00314a02c2e819450300d80d036440d8048011580c0040e1b0810100601240c0a56291070a400105280f25140c0c082d03007544891403055829250b019252904240441c20307034204440c400760159201c040c0900c00030903000f90 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 369604316 1106 369603210 369603229
    0x210030b060d090506040b06060313030f0507230f120441010806040c0504050f030a0210181a090f01030209031614030304081009020f 59
    0xc0302000200207200d510052003030145030840c0c05080c4040000c140d0f1080e1b1103803400c01003031b8844000300017060000301c82c951440c91524000320002882b501c000341780090740e4240982003000503910083c000d6200034490b10842e980b4511340004c4038080103000c142c8688140500002100300b20340000c0792085014581c080300b00828000c1c0c0c011111a4182c084040b03012000c2e070820458030024041c0da00324041640083c8852020602c18605071140f141d05d1405070701c0d01d600e454a00002c1c818465401f200003070345800f03003482050142e00d41d04107400f65101d241da925085148929075a41806a0a81000180e802e005d540051205076003011036460300011210010001e1050f0012006440f42c222829090300440203910600d074900e007080c809940d1100d482d603e0400016050603a01d006500c261019a440b6010001500b005580150101400038100e06082184100451f84845 = true := by decide +kernel

theorem cover : BRFrame.Cov 369424460 369604316 := by
  have h0 := BRFrame.cov_init 369424460
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369424460 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369424460 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369424460 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369424460 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369424460 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369424460 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369424460 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369424460 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369424460 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369424460 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369424460 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369424460 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369424460 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369424460 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369424460 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369424460 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369424460 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369424460 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369424460 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369424460 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369424460 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369424460 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369424460 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369424460 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369424460 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369424460 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369424460 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369424460 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369424460 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369424460 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369424460 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369424460 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369424460 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369424460 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369424460 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369424460 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369424460 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369424460 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369424460 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369424460 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369424460 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369424460 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369424460 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369424460 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369424460 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369424460 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369424460 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369424460 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369424460 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369424460 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369424460 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369424460 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369424460 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369424460 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369424460 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369424460 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369424460 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369424460 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369424460 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369424460 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369424460 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369424460 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369424460 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369424460 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369424460 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369424460 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369424460 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369424460 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369424460 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369424460 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369424460 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369424460 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369424460 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369424460 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369424460 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369424460 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369424460 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369424460 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369424460 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369424460 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369424460 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369424460 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369424460 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369424460 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369424460 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369424460 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369424460 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369424460 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369424460 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369424460 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369424460 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369424460 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369424460 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369424460 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369424460 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369424460 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369424460 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369424460 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369424460 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369424460 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369424460 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369424460 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369424460 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369424460 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369424460 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369424460 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369424460 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369424460 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369424460 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369424460 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369424460 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369424460 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369424460 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369424460 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369424460 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369424460 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369424460 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369424460 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369424460 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369424460 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369424460 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369424460 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369424460 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369424460 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369424460 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369424460 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369424460 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369424460 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369424460 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369424460 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369424460 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369424460 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369424460 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369424460 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369424460 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369424460 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369424460 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369424460 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369424460 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369424460 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369424460 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369424460 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369424460 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369424460 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 369424460 ≤ n) (h2 : n < 369604316) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
