-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2750
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:37:58.748983+00:00
-- url     : https://prove2.me/submissions/47470d04-e640-43a1-ab20-f4c22bf1a54f

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 494424460 ≤ n < 494604316 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 494425710 1250 494424460 494424473
    0x409050a020a02060a05061c03090b03091e2b0507120815010e060a0f1106040606210c05120c0a030503041e120605070309120906030e0d050d09030318 66
    0x40e5032a00c560807104c081d185c4a40c8032040320420340d645034010341240642c032110790f14083c1d0018403901c030346840c4103040d66803a60441b168201752107800075500000503440342114402101d010201c003202c0900980b00400c81189a0000d10310b4003000c3d40d044011010415500030742c280e8545a030000010604401c1101000b03104e81c02c122203000926040308008031040d4880c00036602da4120140070301d4903140503401c064800b600302d15490401c20410210f40e1400d100c050003494001c501c20b03000030a5203801c0040000100300480740c40110071070079508034004908401110000ca850036102c00000c1311500014030f00b0701900714846030304082c10150010030401e000005200322030f841e40202c680c180340b095401d20760756400d120714805000c0304031440012500941c0200e40150b59070900150858160f9180c0c840f0306400300c0444007050303004400f081150782501603c03d001000801400b08000404006410f5000d030010b04801596500c84550405000758480c220640000009008800302c80c680700 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 494426960 1250 494425710 494425717
    0x6090b1b0f07061802300706090e09161701050703020703120b12250504060308040614090a080c01080907061b1401060e0a0b01030c0c030315030803010b0a02061506040510050409050a02 81
    0x4042100c46c100e5a042220004148403060714031665449425602e0664180b19518001c1c104505600441040c000c03110701642d8524001c21014500d090000c00e201c0360b1508451000b172240003454010456840041d610002c201d101035400e07000015018054030200303641c02410742c11006c8610402181e0102c002c2c11945800c0c91195590704000c2c05902c0e4800d02007a02c140d440010030049d4203001c24401d0900420400d54010441d40e00542407000e203400003149075031a540003003041d4108441060341560702c41411540071350001d0042668a140890007000c141d0a16241d40303443c40c240911908000b8285c541000380c00b1160700a10001e5280e001c480044001500c042d2459440c00d80d40c01c00c036500900680e41840411307150519142c110340c4064000d007030059980d004550b040b000100000345a9406507001c1d010310200c80c0d44130040018003034a40200980b000070100a04440d5050710b03a21038044909498040da02000c0030100f0400031b8913640641d4024184090034103007000b80144580d1f028 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 494428210 1250 494426960 494427019
    0x10b160818030c0307050904080d02091f0813050d030c0507020409060c020d03061d06030a0c0b1c0b030309010e1c1a010603051005190306090b1b0f07061802 69
    0x5440304103000c40101170740c0d03198600c02e20b0b81041d1420300082c04a070040000d00400ba1150700c0162620f0021000909030310b02182c0740b440d22078061085940300540c008076040d400b102e07841111034440e100d80c0315969a0f81019000344101a10f0707018145690b40b04105582c1c841c0c2d405401408480d00c5880c04501130b0030244000c00052080d4407c0e0b07091184039009410071540c07000019002c140d1410950102c010300200758581611501e50340d94002840c40a4440c010480f05044a403190954514003003c44041402c440c92581440e000d03550b252350210807161040390908008100800010116089440034141b02860051400c42d540c00c0c001c141c181010101d00c41800c0105680c2c0350300d400c1c0c1c1103807070a03647c686d0b1030201c1e40340620583c1441d69104030044000d406000b8416500c1c1c0c2c46805a4809890490b0004540c074184a404c403224a003460544528019250403c915101003500074007441802800b02a05c58040311807005451195100480e000360907a140048140c0c0340c51815508880c6 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 494429460 1250 494428210 494428213
    0xc0432070e090f060f01140a0206010521031903060b03181e1b01141b010b0d0302030708130e0708181606050705070b0703110706090509010b16081803 66
    0xd03020381ca001d800c0b2510840b62050b81e00da1944a80041c4016a5170040019040c09000c8081082c07144245003c0c04082c80a80e0041140d981400301380001c0d150403800c03510307281410b0221b500d000300d03000c42070b40e0903080c5e4010702110b1284100400c42c054107a0394883c5040e92030000502442d0149018481c070f882c1d03c030b501200d03107100303000c0c1900000c400a04900e0b1032030740202f10613150340c0507000010520008149084e6040040320001076070207900c909000025800c00311801228003600b07005131203604800b11a5500040801c0d103019480b03100b414001400704070000342090541c101303403003200c01034407840598000c1071070f102002810102c1c081d1140003603400000c9904041244c001a003070b043d46e0a015503628224030b081c10130364042e04230001c103c4050140001c0414003143d0a4050f1526034000d076520004c1c440000c01013070809425030070040410548980c14010340d210251400d0441d0405c00c601176880300680d505541c1c075045d4160041c5081000506000455004d43d840c0310b09200490 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 494430710 1250 494429460 494429477
    0x13061701060b130b07061104090b1302070305040e04060e0d030f05150a050d02010507060e070302120601080d0c06090b01180b030105040b04021c080d0606120507020c043207 76
    0x51181c41801121880c543d40400990103020007604030025019139413040308041807041200d145401150825002096140e9481081d4640d40c5800c01c1c0e13445400f16002c400714600111614020414403441c020444a81c0824003c40e041225940c0030103404003500013a2044540d8540340107014012070340391a0b02d4241402c0c0441c1b4910f1940c0c1c1511075020000300080c40d550b00e44411701941d00340c0c1604c10ba041c09018406040891104d0251401c040e00000250007100d086104210002e2055002803440da840040180681c0c0300005a41c903940c503260821562990039850040050010300b0401000000454000250440e03c01c0f4a07145406419030203101c20701c42c183c20705080710404c0f5006006140560046805400d10403c05d80402101c1e04402c901003510f034440440380e81c040c00030b40920550311401000b00c1e0b0382c00041c0c40f46040d80f40c00309000f14100f10360002d41c4ca80e0700e4022544507a98a010701c661104600540c00c0d000300b44182120403842901c0380865010300110341c010082400c11 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 494431960 1250 494430710 494430719
    0x50c0c1524010906080c070c03060501060201051e010605280809010605030a051207020a050d03020a060b014b03090507060c030801090506041d03030402030f0f070902091306170106 79
    0x24041c81c01c4080180c0d10b46071018500101110f22603c080c00c5040a032104100c0240031802c00403140000d18000d010104455240900003801c660005201d07428903d0f80b2480741c641c2070121450681101c0c858038249440b500384202d00b5176080a13460201c1d240c20759101d0b0190401d034201511341e100e00c004200820445599606050311000c070081c1c01059600610302028547c901440940000c81c0050480b80200c1c1e181c0d80840c21000310b9100079009a8485000681040344501811182440a20b0300c00341502c1d44400306402c2540d0149030070705808088040c40d2080f0790b0019a40e208038880700d007240c003403141004094010118554165200d0050500100302e0398020032210388200d906070b44450325a03182c41500d030300404010f0700e82580300351035441c95030f804034008081c45c0c0f501242c1001342d9608d040038810145042c10000342070103da00302e6003800029040108142003156180704001d66150342c084001f625101c400201005c00c2440c00030041890034200c4007000c0f804580400030003085866 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 494433210 1250 494431960 494432011
    0x30c0d1a0a1a043b150d030f031d010510030501050114030c06130b1b0f0f06070f020f1c09060c02060a03020705160b0a020111090a030204050c0c15 65
    0xc11541c0341900c1c1c100001c00c0075150780104181c2d248655400d0940500c1c032207214080c0d0300044e40340103504403110014031058820b00c2d038100440020481d5254210b9425507001341140500303000d02814140d80300c801101d80000a03c020401d0302d1141d00800c0945000e5150200032401030000fa9025842d04002203030600c05625106c44034540100100f8034207000c1c02c100505603200801020141c0031500c0002022444880900554401514100f081070300d00842c240c075221b915550400c0a074001e90341c0c0401000041407480c0c0000c1c00d86815090304403a000140e18251710354002042611038809907040052050720081c1c0b03000d005654042c0702945c3d48204440c1641007030b0019610003001c0080c04025800f941c00ad00e02e00c0c0c4104142c0c0c2d541440c4e95442c0203159002c2d4040c102d041070024040b84060b50a108202c80031900c82202c50400d000311011441303025542c00000d0149a41b4004290444000400d5403500c4c00306004640c074000c01b0032010780f030b950f000307680f8071a0b910602010010400c20 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 494434460 1250 494433210 494433239
    0x60e010206090c09060d061104090b1008150402070b010306020d0c08010305030405132904050a140f0a02070b0c090f0d020310050c090a0303020c03060601090305030a05030c0d1a0a 79
    0x9494000f4861480b60800b00726a110300501019840000040c0140000300d80b8080c809145040624268480f807900c0da0710015a04064a664440d5900400e01d00342c03542c203e800c10350071100c03e82803040c82002c0034001c280248100304000c0c01201104000008004481d0024800c0030482d02041c00807006655003039810a6003800014119041440140120b082100c2c9015504c2c2c0c410002252402c090b08080707040382e80f200341000300211007119001b41420a4001c0a0b0460000c00c81080407181c1d4500c0c082c44000042c3c13542458410b11030114005900d950180c40d511074100000302c2c00c50410719503084850f07000760202c2d805481d000640c40c14524010140010031358001d400341400700c1e036104581c03000b8a401044980e400206022128042c3c0b128400600950321a0f001412064500e000700352801c43c0c018007803410000070f24002d00c0002c9011058840d00b9545081c01900d94846403220200c2d4000c3c40c564000d45071074880e803000340c0c0d0b4040320032034180c8000303440d120545900c84100019418 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 494435710 1250 494434460 494434471
    0x20f2802030f090316060804140c0a0b0c120a09080609190204150f06030c03060e09070b030c160f0b070c0506150303040302090c220302090a021c05010f060e010206 72
    0x1c1060120001040026000b0300e00e40200400350740480441c0d02e203080c4905400e41000000843c2d010400040262219400850025840041003045104400034112100e80e02410f802c0001c085217400e5442000c02a409859009900c45030f1250b00e2983e00400c2d140c00741c41108a03501c40c0c1e8000c10041c0707201040c5144045a0884002e81c0c010707140d021b0102a2145000e10440c108000c0c100055000d84124002e02030a003c1d0307000300b40d0140046004040d5403154000f84000b004540c1804941d5000003002811601c22031a80d07a140d55070a80d00c625203021716640380f11103c016030f0302101000108140040010300c148000a0240c903584000c945d000700c200720041565201c0c9010851840c00d144c80c0c0c007910140107084914250f140ea000c902a85400ea038403055560001c10440c11038071011481741c42546980004044413840c41c2c00080c0300d0b80e005003403094459400104130407480340716600003180840d1500c06001c0303543d4510b4503030b0070b103031070f40c460341c4c000540c40c003049a07256101145490280 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 494436960 1250 494435710 494435713
    0x121a010e0c03040503090405010b0a0f0e0a0620030a020a0c080606131505030a080306040c0503040b15060d02130e060a0e0a180f06060e06040509100c05040504020f2802 74
    0x160741e5528418090340c0054410782d280d200a202c203020a594074010305001c2c041403e41c06032140fa9440000d040c00c8203040120f001d00ca10320708a20403d8031030b584080226100d03468180717501c107801a48000250311000ca4060340b400300241034a600d0b500002d0400980d4491a182e42680e0b07584d80c2026142d40c41900c02c654094801410130481200e1600080c44040f02d444c401c020039952100000e2034044102c8c070032108420084100b0096113418810944c01c12080c1c1001851440c1075134454141e0303c001006a1034640c6050354291642d07e480080c0e89079250310311021591042c11828102d006d00c4c20344100b0303004002c078500246c01410b0a40c00c0c2c80856450b48c1114407107464100200020b0301102c01809103510074503200300003003540c076030394442d145000302e40004001c1d05180c55281403550007010603014a0500e030a000c04a000001d80304001e284403100041c1052840c50100e420348070310b0f481650b0150001c0b801c4c1e0492117140000f01881c2e070316880b121a498014843d1200b540000c1040a4050b = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 494438210 1250 494436960 494436989
    0x1d03030a0e011809090210080106120903020a0b09060f010b0408030a03091505010f060f0c0b061009090608010b04061a07020915030d03050a0b010207032102070807121a01 75
    0xd0050004012a0300141030041c0d80b840756066201501e8032681c00b00a51340e45a003024000d42c1001d003440c1d04540410b00c1c1130300407507040050140581701d078002e10989175550340d0204000d0502c2401404c0f14070b680010701e000d6a0a007080c040fa40c444082e90350403507070280c240000a40c0c40280e400c80c0c1c211008500079501b02049c10605900600b1003c20a0710b500500c00b061002070429441014041d284240104000900b411302c01800500c141d810038060103400c28039403010806943c2c03d43d92020b01194140240c0110f984c0440743c1010641c0301d42e24460400b2000314a0800640241307000d004195020441203547d003484804003091088408040d000421001d805404d01e04505079000d008040c1c0180e00c5030072000441c0c585401142c100d00000e80d1038061003010380b840c1c05041c0181724244000c01e049411607c2c3c940080c22a001468401c0450800850340030380244031500080c143d210684090303560f2200f4940c0d04113591581143e01010b8400400c01c4444e903c140103050f1411702c51407642 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 494439460 1250 494438210 494438227
    0x210905010f050f0d0903110105060105040b1c0f270209040b0606160506060103051e010b22030609050606030a081801050403021903020f2d19080705011d0303 69
    0x20580c8480c420002041420010b103c486910350000b45140c16000354006440c1009007002040c0c04c030b03041890202c40e418281442140d80c1c0c44001d40d002e0f54021885290354021070181344008594000310700c9262410801406c1d141c1d0b11651050a0400071000396000d1400c0c0d282580c686080d036000e0081d27001205101050104100b41d4056511000c040c1c00580b030070148200b01c2d0400401c003541110540c2c070003410060746584c14050310350010416440701c035200311185450b498a001c1402000700302d0001080b00002c40c0741d01100b040000c0c040340c25080005840741081005400f0300340e019200e61183d24082006400e0004159042c5904540e07070900b04150400d815040c010007040c081e0400c9018040480960382d0401c0700e20840c0d10300340d5003042e020300d5441070044591890150341e02c600b01d544040301d40e001d0a408068a40300c01c40450114003104500017409110460080c08420b99000ca408100355500080074401d40700242c0364400c0c03c0d2403042000003606107115a40d0f40580003801200c8 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 494440710 1250 494439460 494439467
    0x501120e0a0b01030807050705010509030a020f04200403060c080c03071413060512070e0d0213020d020a020f0114060f090703061806090e03031b0c03160f21090501 72
    0xa44111006840703894025440b890140c00080e0401d80350365070009a0201007003030412041c4014182801d140d4104010203000030f80741c82c803802010f40210104003128a89903555802880301141403018104c81c03010703100f200d800c10b802c1408101e4010786484801d00d0400d02444001c1d2051035a6030706107146540d05a0101c40c1326010540c4654040b1061201d280071100c0f40c44a40040c0010703548990715001b81800c900c103074032005403619091000c4071001e5181034030362140d210151034040d01c1020198180400c914000c1c410a841c155100740b010406949407540454818a0500100e0003405070782d01c50f100e10061480e09427030490b800040c0c24141241414002c28032039000d42e2500f40042e2080d030350301040c000c5040c20000540d800743d440c801030110b41110310032055503091480c020b60461410456074041c83d13101c5200404801c002040c0c071203041c0400c00031502420101c555040ea0401c00c1e01d0440c00901d50940103c40030480ca01600c0740e10400043d10079412020343d51044905442c280054 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 494441960 1250 494440710 494440721
    0x402070c21080a052203020901060f05041701090b07090b03040311011d0718090519080f0a03051b0a0e090a3902120301030206130e070903050d0207050112 68
    0x146a03820700707116a00041645900a030400602544078140e41c0c48000f291a5802030140c01c1480c41c43c0c1c0041c1040c0050788410009a05550381410084c1404070031040550302c502907580004800d40c00d0300f5141c00b0541064100c070b0000751040e61481c195440703054003078440e043c6500981e14100c5c01400010b000c03e1152840b03c4a4a40500c000aa0641400c49011017012400c04121965115410412542c42c481d251146180e081c0c0740100001c520540d1600e441e00c907914209c01c60000d28060305d801b80b1480008480901004201c2c090b5125541c2d0405009440100c4819041030f0503401c2c003c002040c1d1004680d2681d03070b01e966060007036085400b00400100060b100d820301550303031005441108054042248241c1da2031040291184c5003038015030a51966458003802c5410403021a500c82c10f020082ea03040d00e5040714a0341d121900c03110420b5480b1210f50094104207440c10031310500c1500800901e0a482c001c0003078422081100718140e036100301da441024000f8145207100d010061696004 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 494443210 1250 494441960 494441999
    0x408010e0607141317062205060406090809030319030b1e090a020d0c030b040509031e0c03070b07030b0f030303130209042102031b06011d1e090304090b0402070c 71
    0x45513412521002c4080d07103111140c08135050340d402081170000301c62813150079010000308022206606c043c00d58070b050701c6000c00b41004003090380303e100704400c000f001c0c2c040e91502c600150403203440300003603044100751542c0f804821011a1625080f5919810304481c404880300b06215103c41140c41d11050165000005001200d9554203204099442c0b0480c060358031254a160340202d0003445500401c41251005002c4007034940c070400c0f0020103141d945a001002c400030b51a4580c4580306100c6803170442c8543c54000f400005c1e8031040001c2941c0503405610081025035004840c140c6c1c090925690348400e07200300090309030a0010100602d420884564032038403d40150725a180c0700b40c200e07204240c0c0440058003503040030030040c0100300105c0e42e840c00c07005500000c106c99498000744884c0c00c0030075480340144030001c8001031b1b000114510010344a191422004502d460260304442c1c9940190142607081d03410002c000c1c44524003402902c0780c06801c505405140743c41e10b003601000141c031054 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 494444460 1250 494443210 494443237
    0x1080c190903060e070603060b030f0f18061608060a031e020d02031023010e07050a02010e1507030c14030106111c050310120506040305090406080a080408010e060714 73
    0x402000242090165480420200c0010105c840c207044029007600c410b80c001c841d00c0c100074420080c6500ca0f1070350140e00500c100019503099226000c105c2101130708681c0e554114030030780d418401501440011002c0c070784100c1d0b0311007110352640c1d0101f140c0d21703026100c0500710007034208846080002c404030200f11544024116281c050040d8003090800e0325043c80901040c2d43c4403001e42c0b40412121007038001c3c200c006c0440784139604280d12000030301d038083d00c40010441c010840c07400c10b030b00035404085414841411151420903201c000048044212080b100180c2400e08e03800040c1e004050070501d040381070050302d0850382001c0c0126400443c10080c40e180c2c0c840c00c1e10800b040d904502e0b0319070344bd018a07654256a4540002c9190400d5415808080c944000c014500701085000c07940301e4000707501d840c1c2242e171910184001006440700d0f401905060055030301040802992100600031281c03860300a21005000844807074070385504851110124a02020f2001c2c1c8120b8a0000c2c50000603190 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 494445710 1250 494444460 494444477
    0x1050a06031e0b270106080702070602030a030b06041d011505120c0a05041a030402031b010c0201030e0c030d020c030c0a0e01090509070b030103263a0504030203031501080c19 77
    0x8442c0940319000311181c00110303c0c0c0000501800d0390000c51f1030b0380180b80740010100d086c0b4002c0000e58905c03c4124080805580303401c495090369690044030010000081d410810403001141c0d620071460030301c0ba81414020310740d0001c0c0114000c60640e2001c1c603d21030802c450b607907410f6801d0b0040d40048a8207040100c10007003c51203603080380c40c04501100c481071f0306450349003905c14035146c10b00e1070101141002e001c5a0a0186a80c040b988094042c0d080c42e011a83c50340840881e45001c8188000c40d905004520751000669800180d401820108a0449605030149000e000d001e003100e008081480d28020b0062021060581180d41c00c405204210344403513503200805080c540080c5c00403110040c0c2d0303144214000750480c65150050f9a4454182d1410840c0d0292609002c0074001d02c4113183c0c1681c0444ca86000e100040c801a40c20351759051000d4500307858004d459130700440c1e4600c140140c41c0028200707544a1404648079040c480442840d10905a419034800e0149035400e50030001d155 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 494446960 1250 494445710 494445739
    0x2103080c0d06031b0603151401020a020913030305130f2d0b01030b07030507021b0301060503010515090907180e1c050d14040c03020402250b01050a06031e0b 69
    0xc1c45190b00450042c800b8110042541c400407809201650151040504203000c3c12024111000d80c007084030001c0c81a40700102c0c4850040c3d06008800001a40c0003003101e041007005d52200c00425140c034802d640c10099942d030051100030081c50b442c40900100c1381c0d01281800140710098007a49154507400c1007003041e20700d0280d4590000460703070881d00300724824010030170041200034040d08100381d42414040c41c500a000256a0729000342c0403442141d00000040c403d032820b50080c005040060003e201e1071a00703070001c0700751681550440340180c0c594400603460400204e00078003910344141710441101841c8101c03102501e80030b00b03001014044c40703110b5202e00e1488031401c02400f490307481e650f4855078003140880841d85801c0310607051200743e4081200013204041408146c0358100c50041c0c0791030003240402d04036000324010040c0080fa40c0c1007001801901660281240c43c01c42d00600d0799500c4200803410b445058090050710b10505c890010149007940141d200f200340a09040c1030b65541d07 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 494448210 1250 494446960 494446987
    0x2c061314010603032a110f0a0315060f29030406020405030102031609050102010908070803040c1206020409050a14160e04020a0521060603070806061905090a2103080c 73
    0x2141d00403404141c2150301a030000005ca2014101e02c41020000c0b0911a200c0d100c2c5a40480d1280e900f42c80f03461580e54100c52955020044d60145401c00141d0110b18074000381280240341c1c43c000e190300e0800300e0500142c1001500c0304045054240c01c20ac86403480b1101c40810182c0000d8000c44000d9001c1c0f00c04101038a00744007071441703401300c1038011080081241d0003502003002900400c0c1164100a03517680403c41c017500f1106c1e0b07154000003695803551582400e4013984029002150002e034104908410b000c0c03e03402070420341d40c00320402c001544031103503000c007154039000d0522404c251040c002004101410224482e001c40d40c1000441051340c03100007030807a4800084040450004100004102c1c1c003008074584000000001d018281024000280c0d58003000b005071007046a0000028860b4541b103058039000c3c1c1b61218441c0203401e406001425641201044c1402a150814005640c0c0c50f00074140390301001ca943c200a6288040d1011600b81400818141c02c1c2c0908011600d8190344 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 494449460 1250 494448210 494448221
    0x120c0303060308180a230603100305060f19150302040216021012051501080613110d060e06030606060a0c0c030f1410021314120f012c06131401 63
    0x2c032004ea400106240010003802000c03d40098840d4002454030360300c1d0300314030100300d2250f541c11549a9241c0c1d070b40c502e08040032040e0b6000104a4001d800510103140e07130710315405d802814114024007050748440c2c140d4007125007524641003101c1a03418100090b00b05540100328030405140c1e07003040882382d500413544203688078880d000020f0f44090500c9400b41c041c460242c00a5900f402a51046c10881c002000604042c0030588645511904210f180c00142c0c03209030746002107185c0684800d6926041d0004000902c600f560400354600040c005181c04a00180b080800401e99428548800421261480d20000c1200d03000000d030030110215460414801030b1600c52111452508042c4013a60b007826224081c5071841401840803a41c488920880d00041d50a00700751425160071030790020386e040140c000c2e0002d07640140703d1114075074441904014000040b00e80c003c21625041c2c00d103050403154401031000a0f41211001c1485150314400c0c0d100040d0060661000c201039000c142801c589 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 494450710 1250 494449460 494449477
    0xa0e09030c060705190806130509070f140109080105090604060e031224030a0308041203020706050a05040201090807030302030403060e0f030a030606080c030610080702030d0608011e09120c0303060308 88
    0xf04d000c190710f110200c0304006409810000c1c54141c2ca5070501e5004070758a031101c0c41d01101c4154a80c0e00080b41000204000401800304445980c007055981c25520307070701c6400c3c103003580c0000c100d014041188081402621b001d1071003900107101c01c1e626500c0e90002008000381703103802c50104104500b203d050814156004060f80041001e14039900b0a1a010001031080c074135010741c201c101c4000101b03401ca10345a0f4081d810201e04514203000e440110021b00c070700320005100520303080c01e000d10074105602c514401ca2007070701e90a11a98482000c00d40d200d01c60312000303005074400c00041c0002815900036260070320302d03481226046d84584200c035007980c104031b000e200000c0d510002004016031014096400031600105103180d401c11002003042c4401010a410910170380b4000b140740c01d442003040341d45103159014100038503500c0c0d0308018060181090031980300321003c44010300101d01c0740314416001c4e522032040d108207407566806546001401e2000d40c24550740f00000008501800700414885 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 494451960 1250 494450710 494450717
    0xa120305040e01080706092115140703020c19020f0909030a021c0e062a0a021512130813150f0311030a02090d051002030103051b0a0e09030c0607 64
    0x70703418a40d56141c0088140d2080103107034007028082103032641015600701510325050b01020100d0300600f4980e60080241c030001c104092480c1d141d2100d0b94181e0000004111490301031625454440b000c80980c062040d040040d50051405000407024007102104c180d44003520038074420400400050346c1e006e0440d11261071f90800a080203c4603810710003a61400c0c9001c40f84601242441c10050031b8890079541c2c030b03015602c00900c0380d00489940c0300d582e12244d44190903131199109105650703110120038a08a000714883c128101049100400340c8103c3c0951103130741a01680c0b90280701518a40002d0286c44549080141403040b40310500080080c0140400e081d07281c000c251001046002c40c04054000c05144c01364038094a10803204072904041c4042000d0707109e400314400508030980198000749544201100e0360f08a0406401541c100c0c0d0081055440c065000124041c008002c251b125502c1800e85c08144154035140c0300541d0003000032001c8070b04040405400503c0d0000545031f41010 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 494453210 1250 494451960 494451967
    0x40306021201090c0509061b07061e020303010e0c03060a030f0605070f0f0903082209060f1a070312110c0a050c0a080c0906041503080306130501050f0f0a120305 71
    0x8151203101050b0042c08640410400c2c14400355004100d03000f190f400c00c0c4907a10000b5112070700510700500e0b001600b59030080e1000c1c0748d92840082c000d917451454003681c4624a11315000801d001000f0f4070304955004e0700000b840d5503074114280156000400d2254051843c01e400308c04141e0703c07404d0b511480d104e2080080c442c1407a0001405031182c040d0a0000c0000c490412402c0c25800100c03602165401403038980c0f10f16a41c0c01028441440c10342d8500607001c3c4810000744c3d008250014000c0701c2006281822030742c3c40722003c8001c00400f502d038046002d020402d420009214030603d01d1010121000001d2102d085401485140d1110b6007844095100d080d140c01072203024404405480070486d0320840c07480c90448425154440b11307150f50301c100f4141c000188152a1500059070b554101941000019240e152144c116002500d11901850204008504035041c9120707041c141c0318004c150000906402081104100c811425560402c4a8900020301400c440c608040d5003071083e15556207 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 494454460 1250 494453210 494453227
    0x22b051009060501022a030a05030d060503010203101403011103041101090509061305090304050603040b010603050123090406140c0c0f06040f0b0403140f0405040b0a08060112050c030304030602 85
    0x405034040d40120120034a0894104003681e0006000c6481c40f1801210388040100d081011020094400070590503000d090003a004000e0003100605041c103425400f002015111810b05080f800220f40d00c5501e1003054806001140391040342501032040240003103174132400a4801440c6130001c1d5000c0f1842c54001c14100215070b004542c42c0b01900c015036110046140c5040040c0590301c65030014100c3c00d0f690008500c40c21820700c21074020b060041e20780ea5890500780343c0030032154800d1052000003403138a400031914100601c02c0040c01c0320160788001285000340700f04440720b1800b0b402221059035800760301c94000d04000280c0c1c40f4030000c0220544401d40f4100729400c00880010b80c0c4007030b0b0001001c010004400341001e2440c0c3e46c004014400300d40e19032a00766141400c03280c82100c482c1c0041945100200007000400a640e003d540900c10380c0300e518140049200607020345440c0d81c0120005015540820a41c014243e004400311802c0304407100109081d0780c420f40040d18010303000540d860 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 494455710 1250 494454460 494454481
    0x908040302042d021305060304030203041d010e0414160602033a050402190e06010f0c05060601050d09080304050309010e0d03230d1803121a04022b05 66
    0x403e440d00d000800614004260a0948070200d1410302a0040e0b02040e1552031098261050b0090728003e88034650302d00b0a0f09001e990782d0041d105070240c04940449941d5039802c01d5a00e6030403195045000380c0d04d0744450352344008040400703854100364400c08545211102180c0b000500401d46500a9542c0d401051700d42d803452201503128095204207100311004640750740c0421528030038000d00000c4d039a20ba81c40010020a00c1c0070120040003160071010410b510420f020038018602620b6807040564011000e403120300003180081d219401c0070000410b50350240000701008503071001c0010f6a282542e071480390329001540c0c2907809620119418406581000f054480700008550122025040740d600030407a8400c030100301c00071408402ca8066403640a016a40f040000c0341050261200100110b0344c2404400c00a500184d602c2a060b84683c0c40d6100d403c010340e4443c0354803130f140f4003d0810302010358012140c48120000c104180c0c038010007102c081c3d88410622550101342400c1c00b18454 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 494456960 1250 494455710 494455721
    0x60d14161b17030a0b0604380a0305070e031e0706090e01032405040302010902100e0a03080304080d060e2505030f06130c030b0a0f0806070c0804050301090804030204 73
    0x1d00754818007000000205088068001140320352604203070360780c0e40c1c889081c030242c4000710780305410100105011822504001c81320003c0c441c2115030082d4070048102513151005a00b0710011a0354040202c408180c0c802d40006511400d2810b002c0001c0700c507800424a400f45d4081c180c00700364600d40c2d940c02c240c90140300b80c0000f848145480c5260500381000002c4000061100038800108100701070040542c45848014030708602204002602d000c1c10080c0c0a4680490700b00c0c420b400d400026a40385010707000c2c140c80b00d8400b521642440b4107507a42c0b45541c1d070000d80b0a0b580a00144403000100030071b4041c820113002c80ca0812861800d003015400e0180349025402d00001e9001080c03418119840425250b0081d05810080c0300398031042e0200e08200c0c44a503515009905000c01c0c2d0f245250140c00104020740c00703907420601c943e61a4400484c070030403802808881d4100a000ca84541d104030035820030356026588051a007036035040041e08642116808540784800031408105610f46407184 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 494458210 1250 494456960 494456987
    0xf18030604050304061d0a06090923010612110307020a05120c030901050702010e0301050106090f0e0c030c0a02070f0e0403030509150103021201060506030c070605010506040602030702060d1416 85
    0x2800d03141040e503100c2d038480c081e90044000b08040400304040c90b0f008000c003045601000340140326419140c0c04020001121f034080c2310481d60420080b02d00c2078801c40265591850080c005080907401c0c07c40465440c031a00070030084181e25590001d00d610500e1000758095050383d001802c40d18007a00d4038074100809005aa52907200074426504001c90102c02c03542140f90910f401c03a640c1040d0320050314101516400d042d0951b2816002082682d000080c078000e5801810a0485455803281d086450f00000c035000c00303c000c02800403036640361181018080312042030055460702a1900006000350300e003035000b800440c02500900041c90b07010b201d001c2e0003008610140080411310701840d1204075044c4402401200180300803588420294000701c09800e00400c102d40d00d0038403103400303102d98102000c2a240d442ca801c0000402c1d1522004035021902150050760600c5800e03001c03c400c580004541c8003041d80c4982c0c01c00f05190f0340d03260003441a03003d4880c002460340d80401c002c00c005201102d = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 494459460 1250 494458210 494458213
    0x702061609141f12110703020c090703091b05090f06031e1f1e0903091421100e011a12030c0105010b0c0c040c1202030a0902060f1803 59
    0x201810035034001d91072801ea07602d0700c4104200c8042c41020030001c807004441d140c0c0e00300381d44491000c076552009401384008400b090074404810924090072840c410044010056803140c40e0300045410000c02c0c030b0780d004840d810000f074141015201c0e500101440b4405100c2101c07404414011860151501e5421841070502c0c0200da242200200341d6480301c0c0140800001d000100010010780b04201206c0c40e40104c1d910040c50480541c580760240c48100644110604e900444002e0240310b481b41d40c00007034242e911800c0044c90f0a5015900d00c0c5110340e100d0b0080240e80c09126510584a0040d600d5103d4100030001d0b009611301c01c004032400301c1c81d04e400590421030050320010407807259103c0f901044484042d01c540a65602c0c0c074505c1660356440342d80d404c107000018014071031000f4124190301e610580d544c0c0024201000211091034265a02144d006507000d061501030740d000e036602031055400040d5800140c2c00003036007031b044080044611200013528201c1c0000504652200c0e400540 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 494460710 1250 494459460 494459491
    0x507150e070b131e090506040b0301020c010c020c181329011d04230a06090b190227060705160810090b0f060a030f0f060507050903070306051e0906070206 68
    0x2200c4c121140072038881c0c25466500c0d24007050070795650303a110b41141d0304001c000310b5031801c00000c1c4c98041c0c9084502400540502c0c40000c1e07550a01c0326800240e58544101c040f01641e40310030b41c485031221101e09030350701114151070401e855881105026142240903558a056141010350200300700c65040c00b694280005080c4400a510a03042e0350310182d1036000050b0207154400614a0110840000b0705003600b05410306084c0314102019074010b000307030240b614024000c0d0240805a201c4d01e04041d840c2d1301500d82e00c451411035001c600301d01c110001c109600e404002d445103031814040c909901c80041400c401086900810410801c58100d58030b818400f030261512a01070301100200180341c4004081c00040e620340c0e51030f03580009964000c0c60841003460904000c0d5003a80340460882d8100e2410021541d103900580944200602c002e00510708607041d0794541c0e0103040041c0207000c030915101da00e4010304514880380ea2090800800501d940e00c2c06000c000e01d0114060104a501600007 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 494461960 1250 494460710 494460749
    0x607021506041a1c0213020a080601080108060621030a0801060e011704020409020d0b0703090605010603050114100504052e0819020c0c091302010201050f070507150e070b13 76
    0x200c81c50343d50540d0454583d1039140d803d0f28280c00c82400303044002d60050f101c5468200410881c0d0141501c441c142ea180da20941d90f050055800c52400e0042c41415400301c0001511032401c01201d010f0040751070815240325400c0c00c000c52868010000000100d0203032401840700b1603201078a0200e6280900e050034189101e009201081103001c0d0001e401592600b4858055498010980765110781c44902c1701c1080c275009000800400b1078080c01c94405080200001e00380703100340a028140d03130100158900e21807080c41000242c0b00c51540076000d1081c140310000d0280d441120981a000e0b008803000407030f06001030500501810040c12805010300340c401e00451410108250744500b061040069030780c1146c0840c940703041c600b00c0105520584840c2000000070100040c40c801600c01c2c0c000f071000d031b216448800b0030103004032035280002d07006202c014003050308441180e0042d0070400b0000741c5840c403110746600f4260903070400690314030002010340c202c05513484000000c1c4841c1e108903140c11140c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 494463210 1250 494461960 494461991
    0x20903030f04410603060409080a0c140607050307080612070b07060f020f03070c080c0a0602370c03110a0602130605040308070206092107080d140a030e030c060702150604 75
    0x1000c0f0b03401001c0110005281c1d8440390320031a20b0642002003075403250308030100240a10115a422950020031140c019400c0d980024424010360080d207915041d0b9440d04401c07a00c0100003050540d00c9000d0f42c20031002e4000034049503000d000c02c5042e00e80d6486280c10702606540340c0340c0c05000c080c1c0c0704101e40c001c1c460340c2906407030b0040307018a0106c04100302801d00c0111402505e41c22034203070103010021803c00c45034ad402001142c449480c0045004054040b5500d500c01c0400c001c00e41004022450001501c5012030400003880790506022000d0a050802c0c54280303042c0c0100c0702d00307034005590801c0c1a010381c100402071803140351142c605425640d072042c0500401c40e000780a81c01c0856060b441e6507075800c00c141e04107911000c0d10181c000c00079011342da23003196104110700c50040d03c80b450349043c071407920a810426088980341c604209580c00300c00802000514030100c2c0021b0080c07400014042c4a010302540c0b60398020042455055000300da846000707001c2c140308a240c0314509000c000c2 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 494464460 1250 494463210 494463329
    0x405010e0d08090a0f150f06180e0a060b06040e151f020705061b010c12050907030209011806031212060e4303050f0a0b090109020903030f04 62
    0x50120321708200050500e040401202c2a5003a0800c2604044201e103000540d540008106c1e0100d4040b0b040c0341070851544000c442c2507c45943d2a0f4002c03812050101e001608015201d1101410040c901541d981c48240d00c802c080d190003895000c1c032141c180c010310b0542ca90310200398501868582100740c500c0003a60f03424041c42268001e10010407010001c0d00d0900c01d0040d4564058000e005404010704001e08041d1804c0110301c040749800c002c5444a1000203040056941c06480202a6424005100001c001407007606c84a552541700200000341199089030900c015902e841c2c2c003000f4020400001e07903807240c0121407290b00240801210949040b90400c42c004d80c0000c0d1600b10310102c02e4040c2681060280005c4015010301c1c030380341103515621242c41810700081250980e00c600490505843d1140007295001c0032010040c00940c1581d0b00030300e24a01c5c000c0c101c1e86815001c2107c60002d40107540700c40180901c1d4800702001040c0700a00c0f1074000d61a000340415001d0703140101c000c840 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 494465710 1250 494464460 494464463
    0x40c08010b1c06091e0c081209040b060d24050627040e070b040e06060301050a1505120a060e06030a0203071a04030b0c190504120f06140405010e0d08090a 68
    0x39140c035503000d03c0150750101c44600e8124001c2803107006500c0610503c0301c3c032040c003259008141c5000090044010890804c016038800d003072407400c0018001c1001a20f5443c140c1d6a00c0311040106a06d5046a442500c00c0b4020003909000c0f100d91484024110800c00d0f40305a016440401480550700701e0380708000042c800301026101c001086402080c020b00380c03940b20403a107105681300481c1400490000d4401ca8042071801c0415a4420043c04642d0000b0710407d80c028410347c03c14402407074000348108640c0c445140c0f460424684940c45c0c03a032141c5c152002400c40d46d886c041407001821f9202500d9104000385e00802280d00c3d07a40c00300c1c0c0d4800da248104d418000e0b00080503440018541c049a0041d81c000441c0c5a442c1440c00340005990f1140c0d0f40a80c507031103401e50b09141103001d08161707411600700721000c4da200e042544403d0500d50400008603001c554035000c04d4212203c44075024001c601910000407081d0003601d2813898903e00350450024401c42780100120610005003502486 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 494466960 1250 494465710 494465749
    0x3060103050405010b040603060f0c030605180c0c010c0c140a0b0c031803032e0e01061202040b0c01060603061e180908040e0f0a05093406020105040c08010b 69
    0xd5482d402c00a00401a5500b0260b01c80c2c1814000400c0c44a41c0c2c1011204299008041290100f0301c4410340c1154040e1103880c3e00611548031958282d015403011503840782660070918580b40e489100f8074211501440604041048540c102c4280321103a0b00c0c0b001c5034544100140612002c640300d00740d034550001c0c0140544200040040d504120140c0c044904001c04412640c41e400c04600844652035019026103a03142041081c40c110015001d91030101c40c1d9400030700c02c42d80d0911000300d5604140f884400306a603020040000c0d07108240004008103507010000003512800c240c00241918145e038482500c112a59043e03031f103440e40070b83e02d40003115410b40041508600310001e01d805440c14400181484c4401314000542c000c5c0d050700903200300700b030800076801c95aa00e5251001c591054400500c6540710410800d40805070007080c5001c0d410b16028103c083d2030040c0780001340d0080341c0000d00180d45031400d1008001d000b9001201802c0100003d001c040350f48404100c88035076044005910 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 494468210 1250 494466960 494466971
    0x2070203151006080c03012414280c03050f0c070b070b091507020705040e010b0d14060c0a0f0305060f03060117010b040924060801020d050103021815220606030c170c03060103 77
    0x30b09028016815522041185d51034039003800c1410030900ac9074058804400714142045540410300c03030703011048880e030b00d6102c1c21b0a01d9041036210000b40c10030030040039503109080d40070458100c10b50143c0300f244d100381d080a0b602d1034400d0758241094080d03014081c15541f44801c2c040e074a5008601c460a07500e050320001800704075103031094058442c1644540d08180000c070381e0414000c48000682c00358120400f180e03126207034086600c031644911043c10001803001221001c07a207201c0d0f0015500150000c1c90302030f03c0003003071001030b00b058407e80c0304518a981c580308408400c0c60a008060310300304203c40800046205884070700c9a80104c407004000da00004140e01c0d2184501d0303002ea405050980c3c0219142d011401b40480244000c8c001a440b8aa1100030160107046004080d48a015640315000d10b40c0c5120b010310191049082010305161442c1d00030b80c866003500d02c07441d40140010b075008204070249090103086002c00c040e810b48644000c0d020091088800812290024400c0c64002130 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 494469460 1250 494468210 494468279
    0x3050417030901090b0a17070e09074a2101050703111606020901020c1801031103030a020601052101090605100f0f0902070203151006080c0301 63
    0x40621680d001811052000c0415031448031000000e040848000e0301c4150010352140e82500c01809010020b0000178502500340e1040b45a805000350018401d041208184880000080494008541450020b4100341c921000038259580d03600341162545900000d040710050b1011000710b024500c501c1025401120751003540340c0d18030801c1c1c0d4038a80c0840080d001000e01d01180600015201a03000074100171800c825501d040080703a00c0044103141743d2050014541c0c40c1d2000e034010400c44c40c103600886000040584440d6004200c45c02940d07007101d12981117142c0039201c50003001c400350003070b8424050109155000030b07590b8151042103030321003521703504164000480c11804032145520350a00303289408000361034000038014400c0e44040b41d0388680f9092850006e5940c2d110b40c0f40d111024840410540050f503004120507800a425181d40701451142148034a40603150144038040c00801001895030201101c0d070050b086241d05c501d1035150440c580704480010741d02804140c103c86400e807 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 494470710 1250 494469460 494469467
    0x24060304020d12080708070905060a0809010609140906091917040b07031d152709010e0a050a021206010809070f1712160807050c060f03041101080103020102060c0703 73
    0x128503c1e8003074031003d2504841c40c0e008101060030741e0290081003141002c210654060648003007515006003003582044c9032020308599100f009842c0b103400b95a6450301259501041c040d0300071425582d079111106040c407816803850200010841d01054000e491402d6013a03030031101c4190410b800c20b071491119034034051118500d1081da40449241c0d440001c0c00020943c021140d00660080303a241c030410080041c0034010909151000302110031000c21078803040480003080d1701103059045180266014045000c0b0712a045c0c05c0c0c0246540303990314410030000b504c007030240756401000c5007804c1d414a00060000c10f2400c802030b06403418007000f070300004c4c82e11204001d0600140001400e242d00640d50f0914500210010404a00f03140901300b0084d42c502148401c803034000021004181c01c00120703480e242d040343c000722000c0b0b410b80600100c0b62002d07a102c2c4080d0005060000d034080c0d8908141c0b40007079510400d100b995050041d200300402c09030f83c01265595100380e0f100c98060f980c00e200d00d401c6 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 494471960 1250 494470710 494470729
    0x403170409020711041a1302251a0c120f09030702040603110a050d080f071a010f0504180510110909011d0108070e0c0706021614062406030402 63
    0x3040d03010b01c007203039007000d10107400341c2e089840703400f034808200910304408800c0700071161052454101d18081e04003004800d00f036009003039170403c241c1903245c1d0390f440c0d41c05c020342455420020340d500c0f4885417030b0507810250300c1807594124036070510080c80e0002410204910b20340c024911042040e400f0f0024001e1041801181d84051f1b00810420400740c40340380c180c01c03004814490030300403002c130300000c01e282c2071400c54405940d410080310303814805407560854861340154411200e0501404082d042c41c0881e0140320f01810301c052903040c0070350518041c00101d03101c00380040010602c0d004104007155001c00c848114110204010409100d060f130740d40e503180701318255a40c04c1078404000240503840e000d0307402c5117102c010901d040507907030b5609815070360140c40c01800d0313880c0c00105c041801c030204a801000c205223310f40242c1000010b040c25003220303103a102c055a0b030540d1229080d4071007005108203540040324004846d00302e6204900b00b04d4070071641078503602441c0000086000d6568641c580b = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 494473210 1250 494471960 494471969
    0x40204090b04050a060b0f130c0e03060103050f0c010e0609012007080f0606090103030f2f1609020c070902130806070507060f060303120f11160209010e010b04031704 73
    0x420740207007482e00e03080b0703600d8031000019a942443c1c442c03034414501e000010b41c58425002840312450241c44540c91006144902500d01402594521020251001c0c13250a00840c000c6010b8048940c846c0384a1342010f48185c00681000b043c51000310803a0341d2807094680101c02882c00b241d00e400499208210140c0701842c1030003910a101b00044c071000c0008081420300082000d07907005485030410300800050a000003800718507e40c0c0d581c0b68882c4503243c0c22807004504c02c0040c030041802d03003a603a0200301203080f0306665000140b89a0a441c9407114280c0140310032801149005031044042d9200ca0f010b000d01d0302da01e0340025031000c03800d51365440000504801d90a03500b840c107046134007810f0399101001c00c440003414001070101c802c01030f2107110101d07078140d00d500705201e981e1078050000b44400d080382c949076aa03030390f110040711070864089c24203401e89181c403181101743c6004011410b0b105a00025015001c0c000600c80103444c1c0c400c0d90300301c1e036102051112000c050724a00405000b01d402 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 494474460 1250 494473210 494473223
    0x30804080c071806060216030503030f15041d060702060f0a1a100201020a120b010f050d0905060411011709070902070201020f030324010c12121e0c140a0905060304020409 75
    0x16100c60007043c3c0d5200302e040310390700e8080341d05101b400c1c0c1188042c0d030b000c0d01c0060400e80041c40020390f400074043d411640402440d02690940c02c0050008080b1415211043c050310448c03850005414401c020342030704078019000070455443c6c003411003690000c009080292040c1c4866240703104251109400c1c00c55840203100d65043c40100d02c0090007900a4100c000c001215400d070420701c0c0a03a4403401c024004103079605010700d4440001681c0b00d920400949a201d5500d074420030201d0802e00005024910910001443c100c044c1d0004154400fa8600800066041400d20a00c14400a400c8080b1540c264015845060a000603800c1c00c5c2d02240541103030100008110045020300c2821204c1d40d20060b000811100a4004488000a4000042c00c0040210703e81d0171843c082c3d500344050341c00070034011941ca0340c25403201809003000d40c050840030791100d00c0e00b9440c540114101121070801c01c65103060071078410b4004c080003854442d42d07010f81000004202035484c1d94000f800320f25000325 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 494475710 1250 494474460 494474489
    0xc0d02121f0506091f1202060d0e07030302010b062d040b03070c03020d030b01050d0f020d09030e040614101107050604120201110d0e092d040c050904030804080c07 72
    0x4140c028002c211102c900c1a02c50741e0008409104040360503800325401c51420340d1550800c144156034250414090b41c0c0108107000b43c0b007580589000f00814a4080b00c00b41103c41c1c0342d4070340682501c00c5121030034440c3c807061200400f01d00d0030345442c4c19500540160310501c101e000c0d005210502c07d60300800742e420000010002c105810203241c44d003841c429800c84900d42d02c5000c044049400300110540005c9040100c00d100c1020740c0c20110350081049001481c1010b150011003c40d10040c00440100b0a40e500210440c80c282c402c0c440244080001001440421800180405607148144061000d4003401031013115081015801604001c0c2002d5600c5840740890b0503001f070100b4089000590004a441d0021004290124023010319190302d40140c2013082000302d56180140b5001042c200c00c1380c3d403902c0300c400b408581151f0b00035004040080c28107080c00000c3c1003a90304514000d01c0c030001030000090380168010f40c420340081406894011811405081101070313131182e043d00300c600 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 494476960 1250 494475710 494475763
    0x14240703090617010e010b090a05040f14090703030207031e05120d1a1c03030b0603070503040c0f05030c0105030a0e060f0703141909031206080d0e01020c0d0212 71
    0x4103400c06580c015107070108000d0750f44440d18003402003400b4104c1c08100510040000803074100c090014400001c1c203010304180c4400104048424503003001c050107807503000402c41840c200d241c841d00000f10340d0141009500b9a1006551860603200c01400e42c0404c4503d140b61079800c1c200c0700d004542c46003e542c00899140650912a004156103655107171034a180b04c1204071684070006405040600134425a840d80c03142c1e0070700300324a030300182c06144d00ca912400080e5241303c01907120380c0c416102c5940301d0401d41050030350400c3c550440e00c6008404d19040c003ea580008125205c4002460096626075401d030440020707140c3c00a452015119400034480038180016440d4880d00d26503408001c00d10b00e0101d4000c101105403952084040e40311038001c12300166030031415046010b414520084c198074460b0400303c603002d5204640030340100d2040d525495110364074070303019982480201100705a0032b002460f104d850b01e10082c858a440090310f98100000e12a0210050301403480185001c40c0 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 494478210 1250 494476960 494476967
    0x615051801141b0a030329090c1c0c0f05040e04020402030408040315050402010e030a080f07050c060f07030905010329031f0501150c0f030f021204030f060b01080114240703 76
    0x45403130403800b19082516070f1170340790741401940c113100c2010104286c80c0100801402400080035001c43c10b562001c0200f0034000c00440e034501748181c000440080e8a606d840b01c0140302a03403d012100070040100400c210860101005541082d01202c0c016038035215450400e24034850703980020024140e1024100955815a2040388264000c2c1c0350480c03464032540c201034a8110110b0000c05010b0140440101d10110300b0203000810b215100b16403000005000054040d04400300c000000f05000807900b0405601c0348080c4020902801d0500c0742c901103100303540c0c00744085d40785002052508440110301e6a0b04000007040780144d20390402c800c46d40c06041c00050a8240240c1200c14103858507000143e00c1000e4100b44131348c004136180e11740c03102c5503000c035407602100100c9021032107079560000b0b0480031000140001c600c6402e41003490a194074100b0107403852911214180071181c0010841e003403510252090481040310030401000f91100c5280703014900030740c00c00e182d003404501d0100701a00f = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 494479460 1250 494478210 494478223
    0x90a030f1817101506050a0c050c0301051815160e0127030501110a0507031b02031027051002090a120605250504030b07050c060405010615051801141b 66
    0x550340c0d01807220071030113a109103510042c3c2c800c1d02d0001c0e00c01c00200c2241ea12894180034020312907030986607817080381c10000e401d4450649040785040c1703500700c1d05040e126040107008881000000004124078000401e0b010000000804400b449003400c15410160301c01e1400c008210080c148900e01524422009042d50b111070008607080e61030725003240c0386180c0c1c2405030340180c0781a43e5528075104003940c0803140c2120940c254028990029030341700040c0e80c1480b441036403a00c2450000b50566010703120301044194020103003020b0309d0007007648001c03a20201e00e44180383c140c48405a40c55080c1d4011a100130700303580c80300b41c0e2480100c5000c0c04011540c0c10441c02030f5050703080010258814004006100340011f01000441c2f41004104009510703030f80a00c0c1e04c41d030941007140c00d2940802d038982c00c02c40304450460b05659160801d01094811240034920000d0a14245041684403921004290240700303405040c000c01560200c3c0e40c081200480d100303815610b004d11040381004400c95900c40 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 494480710 1250 494479460 494479483
    0x30d050c031b040f0302010c0221010209040f050708070809120705031806040b09040921020d0201061a040b03090a0203031309050f13060e33090a030f1817 68
    0x20805541030ba450042c0009071820b9a1880c8195260700c2d05d550300541c4c03040000e41c401c80c0c101200401e810500c41c21142c16400c40c0c5261000546e540c07e8240810017112221841100c01c03c0c030704410301c20b140d41e00c442d40680c84901810082c5040d1944000e0614110111a0080109400150b904101b000110140900c8400645504400d00b0b2541c1042042d002c0d6010340d01d0301803024030082c622480c0c160070040401d809070b100429440c400201c0300800712040401003000d6441681c0d442c5003598240303d21402410b00d20070791301c840440c03e8442004c81c403881c8105c444c4888040040b460401e070600121031100e038000c040302e07a16403100303800c2aa241100c0c4500310f01145404002180040040c124a21a03d143c0c0e80050404c4400e644d00401803c58045801c518851811601c50340c2c4c2096101101060701c3c0d4031909204204407003100d03c02d0100070144200c0382c000b0346075500003e40000f10100034030f8050510042c061405851442d407000554040302c4c00c0007121441d00c103040c2c00440c3c08640a07 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 494481960 1250 494480710 494480731
    0x90e09031b0f0a21020616030c0309020a03060212090601181d0708060406060f061403070c150204080c06070803010314100c080a0506030a0203100b0d050d0806010f030606021e030d050c03 82
    0x755689034003686c8170b1078204d600500d440c514255007a0018440d5121441d1a1558100041d00070b031540c001c0341c220006a00210f400540c0010703442600c82022141540c4560070070000d01c8190b052403031560003285000c40d0110303200d44031022080744410960424441d0350002d0121806642e694400d669030b040140d4007aa0014645000800c98900060b1400c00342c800ca622103c41851000184800542c80244404104204050224009401110404078200c0c060030096110340c1010000c500700712180344c41a01c118801c122400008a518064034112900301d0540c1c0c2d10140100465800c081c43c00c0c0e108600343e0306e40aa0508160303002010240116030b81c410401c6550f03548000d155848004510295041c1d225080611800d40700da007111440d8000504032000c81c1c105995144c1c50440c0b500d8250004c100000d0420807030b035a10050100c0c25081c0c0c0e00d0180071003442e0010280d180c4080c040c81102c0705080340c50946d2070703400c20021540391004100e010042e620348051200c8880d007040d545c9011341c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 494483210 1250 494481960 494482013
    0x40504180308090c0607080a030f06090606020f1b10090e040f140c1e01030b041a0117010f03030c02120f0a030e0103022703161203090e09031b0f0a 65
    0x805400242e044c48000c0d015120030318002d155201c030f07400e980280c09060201911611590042c031483d0040b28000e00003041c01061040c01e040c0c02a0034000c5109445e803003079000002e001909141c030441d080e07181e80c0a0702e000c071010006c041c0071a10b240300380d00003e80c100300c1c0205000c10488190840c1900c6401650b10b901070314507440c100380e1190035070090709030711941010b5411110388010101c0703079405005050000b804040b00e40800d064424400c50054480c1110402c0100f5513001240c1c003006110060911480e5030400079100c0c0014040d000160400010144490031500e6070150700502588003000c07a403071580c1c0c07040c0d41c55032070f42d500314101c001403a50700b5400c800754041c1c000c1e5011441e000d1041e804515405804100b034042d041009545440fa03012218105040c03900351102904001d2280c201c01074550401920010903503000e51a8070030301c1e404200411201000361455030340b1040d00f6501c10384e07010540d01e181400300e0410503000c1c05540d002804010a9400304940035400c1402d040c407 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 494484460 1250 494483210 494483221
    0x2c07050108060d0212010b1305100e04021c0302150103050d031a0d0b15060f03150102190f1103100b031009020a0b1e0307050a030b090613090503040504180308 70
    0x10310744070540e0030b150000401d0f500c410051401c4500e04103424201800000c1900704400068108591259a40a225944d82c10b0212480900d0700c2600500300482061009082640c0800c000406164100580c001d200440302c0826209120348492071201517030518255860707003000d6403950134030200000401c0c6071080300890111440f410710b00056004146555810f403d1325001c2d01c0b0031000f8440080302c1c03615507070040c942e901c44001d00b40c03605000c40000e440b0b150810204000f21740700002e25056500141c0381a00c800b02d0030419000c41a401028041c01d16000d250901083c01e0305082c0340d81c50b00034440030300301a101e1644600311618044044900315010007001c1c008440b4805806074000c041c01c002400f070250008014603400e00524141c007002c4881e80582540364105440340b50001d00300044121210b681401001e1403481c00310340504050074110009000c205940c019041580d4440030548188030040c4290b40c012f20016200b4808501000e92035101966013000440108041e240400e1 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 494485710 1250 494484460 494484467
    0x81b030c0904153510090c14130f02160503130f0b09060307110f011e020a0e0415170c1516110d0f0302210f04182c070501 54
    0x381122044034180c42014450195030706070000101d07000709403074645240d64410030420446145c0c24080e0920025004400c1d1601001e4185140d0000c49110042e001c40401d80e512138110420204803524001541d40c02c100c01003010303010311000007502c4080d55004006120020005080d4003440d03d08042466840340100c0c05450000e0081e0802c02d942800344a140342400001142c11501506106c1ca03d0380440d40b1051400c5a0701c002c5801d00c4e5120011840a510303000b81c40400c00d180301070154142040d502c40141400400256280310342c0e02d4070b800c400e04642078000c01000d416416403068042c104401030607600c902c000c0d00c40b40191449604501d07802003960543d4402c0c1d505070309141504455860f80e001050240345019840101c1d00b00010004148000c005a0346100b900501a40d640000001ca03030b8000c83d421505405004203c14540001e03c40f0484082c2e4034140305011042502d18055401401d0201d041e401b488084504441680e0f01d260000401100400c12a02c0c802c1d103420045 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 494486960 1250 494485710 494485751
    0x50c030a15053d0f061b02010512012403110910090807171b09010306050a0f0f1b020f0a081308011d010c020129150301120c120201050a081b030c0904 66
    0x81d0016500940c4081d030010000031b8003482c94014580381d0b05090740ca011200f51a0b4080e8801d0400950801ca5098800824440307038600e440305080800082d42803050321a06441340b4030106100e6804101075080c540d0140507a040034002190440700c0c0d654541c00b0241e42c041c0300e626160301d540700e225429041c107400ca13501d40701d0420b8043d00d004110303442c69440348007500c4054054640340c0d482e6160800e03041658858902c90640262001c90b103060800d40b008034844a440d1207900b1504101c12a01207a140000d0311821235901850030350791040c000020000c1034405e500141260350820080a41c4032001c020740b4000000d10720000c0088150140060342282d12011000c040d400c0c0b00d80084030040d8068a80b9260001c000d0200c1705907001c01404410346034801d8010303129030812000080d041c40105024100600060103d0401c1d4050035000030b80b140c01602503100800020300300050b044070280c1c004401b440261103440f0b80f642041481c0c80c0b02508030000301f5010354549048002d1076244203e05 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 494488210 1250 494486960 494486969
    0x60b0a06082a1b161a0f040306090c0509130803220212061b0a02070905060f09041b0b03010b0301031212050f0a14060d060c03180609050c030a15053d0f 67
    0x50505105c072900351151507000414001c0682d08207200000218449015034400f0300c1c0324611a58881d0300b80010007070140b1000d494202d0100e1941409800502c0303080449420605060f1041450600752240e10317201401c00c50025000321130040d42c090321903400501d25001d8521044080b1140500c4a8600300c01d000304810203005a0040c0c9080191120b15030242d0341007a405000c01000346211008254104415903084803109035241c442203e06902d1a89030000e44904206640f96502d050710030015400180009014034103410f40007804140032703210010a2111580e81030210b40380542002040032002c40310742d03a09600f0010320320901464082002d20400e17004200b5598001c9503140c08000740b0070903840d0001e040e55000c41c1012106100d908480c418800c880100e010702845c80c0040c2403d40f82c2d0300e0103000c1d074400108140010a01000520441400280004c0558a1640c100e4510f900d1100d500b400d82880c4854121520a248180603000b440c400802e402a54072282a10349000a104 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 494489460 1250 494488210 494488229
    0x1c21080402040b06040302060a080a0c0f02070e10080d0504030b0f070f120e031206040f1e020702030a0f0302010903020607020708150c0408060c07060b0a06082a1b16 73
    0xd80107160580c000302c8440c001429a43c1043d880303030b003c82c845030700070908034001c00c1ea10802c20a07075502034080d0520300001ca10302018040d089031300c007940d02c100500450407190318044c000b52280c40800c00c0d09008017081d200f1203d282c06014400307002a800360000750390140c0300c400012190050398501c03034001c0c03984d699401c0d900c0c60141003ca800034101340b6010143c54071040e4419621804001030404d80000d0b20512046081000c200001c48030311244a0b1003c0e4104500b82c03480781e011040750070a4030003c0c1340c056510b41591000909081620100601c28881c00191109040d0305501161040f4865001c585c1d8585030703076200b40e07542c21452080b40c0c100d6024904484070344002140f000e0308000054901c5003481c0e180d250032810050300b00d8803c21004804101d0106100250060710b4075024190343c1ca100755414000c2c02031640e18024082d00c80101c5002e080b009501808104403101c07a00c2c0c1e44100c1d1602403201e0b002c2e090100001c03000d2200e201d03035840c0043c110b2083c0c25400c100d4030202c1c03 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 494490710 1250 494489460 494489477
    0x280e060a030203040f0210020c013203040f05030706060e061206070507020f10021f0b1011250f050105030603030d0e070e04030309060c1e110a021c21 66
    0x1031084002c3d50009000b19040750b20560041d0050312000500e210b18103480e009010126103400004141c0ba07804103404002e040e071204808103004c20480003051059034241e05507620360300c40c1400140502d180d0001481440b001410000340110303540034800f42d032070032040b4000035100d82007003055021541a1807216508000d01183c4034030b00840090060f40e2000c0c20a01413590760703000007118161080d208001503000b69424501d06602e410540b0446005030700d041141c01c40040c04503000100c00594481481a0103d0440c8085002c0040d660320105802080ba0618044454925000424400d04c1046514440d010034158020300c1928859980a00207600b000400d41528001d0602c1510140443c080c040c0302140c0840c2c200c2646100d68020344020903090010300d010011603c5e184850410000460b0080c00d8403d082e02804110040c40e10b0207600d03032542c80c0350301414100d41c504000d501802861030030780781303501240d8a40044d034081e10441a22200d81c810107090200c0d100d9a01e000100400e = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 494491960 1250 494490710 494490727
    0x6101a0c060606250b0f0705042403290118030f060911030a050c0a120201020604140c1306090c0503041a0403031107050f0105010803040602030403060f020d02280e06 73
    0x100c01030301c0f481c42c1c1c50041d080184544090200311302c2565000380c6000110008004100c0d007820b04082d0000c14600e40740307240516020701d840f032042042c003030002c400c600c010f00c41c00414440e8004e80480d591003818151414910030391031003050741a440490103d03224131440f005101c0c694454000716500704429008040e180d40d0b80310024a65010212240340503032a0707850030340c0c40400410058512a000501032009103804100e00b0010701e0f4002c80002c5c0c030219501005036404110250480d0780300c00114280d810856410f4142560402c1180c1c102c409180408041310b81d43d000b0340c0484000c5c8a04110000000c1d0085a40b44405c40d40644001c0d03003041c90306e0001c080303001e00c0c80d4418001d1500086403200715000340d51960107048140c0340f6911603035255080e880e082c0b14040c01071000100235440d06113040d50103034407401507102c09403c3c5565610001020307460b0380c044500d52042c00c20115954100d0a40f503035080c0405045a0b128002c940c0c1c0000160341c0100c5035480d0b5003100170401030078004070 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 494493210 1250 494491960 494491969
    0x20406020d110109120c0c0b070305040501030c030e011a1504120f0503160c03141b0409030e1018080c180601021e03090f1504151106101a0c0606 64
    0x6624804640f0b650300e00e031481c00b260000500c5c64022407103584a140e0810b40d1304181d03030124282d401c43c1c003071088204100c41c00203400c01c0807601142c50a080200b059000c40c43c056009203139549400c0072550914031204c40301034003d01c20340c540541c200c3d02d00c51600c010503514402c038051402580b655030901409003000c41c030010781d00080c0502c180201c4c1c3c9803007140700e015004c96030500e00441e05941100c0007482001900d00d070301a0860b020b040206107048003100b584030150701d6110300703602070365690558006040c40703100c242110300b0014107851040159000000d001e1070315854100b120140702d007004210743d1004242964a206c004002000748611007801c00c42c120030203080f06040d4405c07a541c2d4080c1d02203000c0c628618007541d07001340d81c9418040302400240404103004a104034015001c064403807140c0f40a03101070300c150801e14210880048403e883c8000080c9100302030b44516001c001e40b00b0604807681e41500e41c5400b60b22050b4038500d0f02d00202e03008085901003c1c0c1c10602c001381c29402c0 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 494494460 1250 494493210 494493227
    0x1050f011419140a080102090901050103150306020c0d08062e1b11040f1416051e0406020106050d05030a08060301200d060f15050f070204020a030b090703020406020d 73
    0x80201001d080b99511100d540c080d500c5a0300c6070b400003840091004051500020340c90080091030000c0d40380070b08640000324070000500540c1d044c50382c3c130900040c07000c1006e0807020203558171080c11941c54902c2000960f4440c2521094000070703910308000b40b05801d18405088003d107090050100b4204c0940c0a045e05d1303140002d802e02007080100f0300b04551289104800715580c064800c4580b5000403d0a02c02590350149c1075500301410f001d101e48140f04503a196903070062019404200811010804440d00e01c40d1104d48115000e1105032070b4200d0015200a00803904560001c1000340e64910610600700608200030300103410500088106502826440e0b600501c010000201240103010041d02a8685900d000c0d070241d0228050072802182d1090201a01e9400003007801d0344e00e44014401d510f000140101d080010200703400c1d040c1c81c10482a1058071b680144190f40f103000c1500000d0091000600300352051842201242c0f20030b00910883d01039030413903800350642040001e81500d0541 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 494495710 1250 494494460 494494499
    0x30f041e05220b01180b0307080f090709110708120f0a0902150a170106030911030c0a03201309150b030309120304080102030a050105091510081e010b0a1101050f01 72
    0x85c1382215820381101907041c0d90162004013016030710f81c02e1100b8014010070009014000c01c1c1014400d01c090000c3c00510710041714442c40020808802d0004402d50b01d02030810010403544020581c4202040f60740b81c482d108a1003c0d94819690703440e18050001d40701c8044001e50445080500503801100d0480100850600e60032301500341c0c2050328901c8442c541c01d9001d440000e903212440010003041d90f45040003041c0450060910800000000301c83c00070511000b0000c40300401c5404030002085501d1041c46401020103041c2c510075440c400241800300c900b10703001c5a409000c0160844244902c50551802034011800d10410750180081348100e106003150f5444280000104500c1c00d000030f5110b0003603460f0100d1254501400c0c400e0010380074004074079500000e240d41700c050f1217165402c1210000c1e1300e011f0b405a00c0d100b189010800344140c022401071915030000c80d0342100480180b03844405030342c1d01d00000b001100482d0803140306456246142643e500104105c4c000c2465400c0400c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 494496960 1250 494495710 494495717
    0x2090310090c09230108013207030c3e06070e090601020304030f060903110303090a030807030b1309030e010e18040615060801030308010b0406081602030f041e05220b01 74
    0xe07240b411321a501040c242d000c2c01d09691500172030310f0208039940141d0841154814910114140c2c1c40c40b4200d500d84c01402c80d4105a610b8070803a5405100c0c3c40446181070380c2e28214886419034284c012407d520008a41081c500c040c401c107404c1050000380a480794615554440c00250400100303c0070701e0028104d24110701c0227110203c0840c0045c0c245200300d61040000041d0100c1c0351501610b0040e6408204c400c1d03400038020801c0c0750700701150f40c00e5400e80c10f25040c80140d44002044d0028448aa00c03075410111a9980310512462179001c0040c9501079120541c12401007001186d00f580030500090300024203460300c41c1e03420003410342240c206201d10401f25a40a2281d040f45811300207920803000100048010000c0c141c002502c0c60141100810182c60700781800b202070090f8802818080f0800c1888100d0085c06101b0301c1518140750007901032955850fa5100003540b131040e002e00c40c8640c42404080050300d841c100d1000050b03070070020300451001c06c05a800c1001080f81c3c4aa66062 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 494498210 1250 494496960 494497001
    0x415020c090c030c180a0b0f0d062c06010311270405070e0d0c1e03030e091510020f030c0c01031506141602041e0c0306060e19030803070302090310090c09 68
    0x1802c0382d07c4041c181c0c81046003512903c440300e410080d41600c04d554092801000403848034604140b0a01c00e62881d4030b9034840118070f80d159080100d0041080f1002c030f0403003281c00705950280704081040391041550711000d410305001c1c3c0000b000304503003040c1c0d000c0000c80c100a03120000360030308644130301c6a48d01034800038044a980e04003410080004000860800000d0304080c420117801c80400d4490040030740790000546090303110000204461100c40b845001514601542d482c800c102e5007020401c40400e40ba00c400700c1144036035036000c1c101c281601081c00e0400c040c040c0b03000c0c5401c01040344c1990741c6000300702c1c02400503080d05501c48000040c00803204114640561240e018035001d43d0a499601040720303400345201011500e5001000d0109414404108003d40d40540c024451140072680b0f405410001c6500c04410100c5e0f46c801024004d000c810400c40c0ba170183d000c1e06554005400342c945001400318540c003101d00c0d00702d000701145c4800c84207000740c1000f03a1292141500e18081c1120 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 494499460 1250 494498210 494498219
    0x601051912060602011d010606200f0a0503091e180c13081f021602220e06010807080a0309060807030b0405131b0b04090f020415020c090c030c180a 65
    0x19902d45800c007a0160391600f45290b04480751102d509546140c10008022540c01d103680100304084004241141c0108130700901121001840b60361860200d0500b1960340f1031262801c5a101d4002002c5144540350140394202c3d4031081d240d9200450707c0041441010b0304507002d80304082400a00480c003011424002e00340f40c40d00c280a4900500b42910041c00b0b540d980781a4285903013451510400200d00501c5641001c6401c02c0c00c2c03801c40b903812621405010340c800c40d210a0301c42c4546c1c40c19613882c06d0200040d444040405c1032030585440e20191110b43d62035100301c1c0c4d03031000c07620340c028000358654604002e0140300d4050180c210060b0710740454041409000907054031303000c0e01c45020040f80107900b0350400c401140d0403040c0340f20b01c1018618451400823002007074060380c4103c0c61040c0c0c035a03c040c1018600c03541101d01602e120402c0071200700307403c40d000756101c80d041c1c8240d0258a0000c04500e420000c84280c034422001110301c00d20700a2055958640100c2048141d03420a0080c031002c203 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 494500710 1250 494499460 494499497
    0x90305030309010609060f150c081c0906060e06090109051b0325031104030618081902010b060301140613090e0309040b060301050312031b0415110606010519 69
    0x50281d5030b04400840c0080c20000d4004c1211140e9100c2c00f00c010350458200b000c10740c03003820580f900d441ea08107181c6412081c10f02424034030034450500359046800701c88002c041103070b90180507420300440082105a4499030604d048003000d80302107034010040001088621001d4021030b6000e96401107115681c104800c425456800c00d03a1000c0348140300080c0300a1044c1389101710802e90a1510b0240000d11103210001210b02c2a8080a070115481d40188180f0b034000c9802d10780078613030040388269282c1038200010710051440500100650a003a0880b00758900307403081c0c2c1d040e034a410541d0b20701c0d0040b8500300802a0310080040506c8102c070400064007144921940d00c04891030406143d032400c2d100104001c45040d20390051184800340014001c0c0e07100090481c8840d0302e9018a00d9403601d0b0320340540d0828035034603602a0042000640843c1682113510581103400c40c0b921640303414281d0034a5182c44410840d026800104144076070800e800400d155120541c3c000d0906603c0081c0390121710 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 494501960 1250 494500710 494500717
    0x150e030307052203021011070803040803030f01060305040203070504090219060305090d080108060c0c15070903020414070215060a0801181b080a30031d0109080d090309030503 77
    0x1020500118682c0e00444a80ca20500b000401d0903050f441d0a0656000a500d08900c1c8240c80401813102800103185e0410030407800544244d80440c0d8440f547c820601d0f503250700460301c02400028a500010304140a80504c50007503500402805106040809110050505d41c8040c0c0c1d024289d006550580044c0c4448200501079665020079107280c981d16252600c01109200313402c01c90f510f00100062427012174660303045222a80c0300c940d070707000c1306803000c0c0341a0108415030304045021090004050700403440a080f248240d07014011107096003041c11001000304c4104000d03800c50014094141c80c1041780c154807180052950f0b0b40152140202801c55146502c141d030700358820450312080c409030300d4072811401005003501408500742818551a1002008004d181000b2035400c03240246d4662007000100701141684422008026802800b40480c21010f0010b251441c10154080506006100c8050b0300300c090580742c0100c6440d0740c00240071064080e41013000c4144003000292050004 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 494503210 1250 494501960 494501971
    0x1703040605090c0d080315011112030108100905061b2115060403030914041b02010504060c02070b07020f0604090603030f09090923070f0825030f150e0303 68
    0x1d110300c2e1101400b86840070b1110103e01c1035010300c04420004040e14216548060107041c03000c000002600140d03000403c5640703070011707801b502c200b135200480e2903c0030318100d9191104940a202d2140403541c21604001b5018245800c10800a440341c6c4d4101d803040740c0302c82441051880d040d82c1c080c1111030ad40785202c003800c4d0302e000f030310501c0000608540f49910500c1d0841d64030b440e00b861a40c010b4140c440912540134422111310714104a0355481d071080032004601d11158800a04600009000300012681112082d282c0f038500d1850610000704841920500840c040c5000c4c125000c0020107604044240d0340300c00100f1010030040114001c3d500118420b848908040032100c80140c40343e001904504905031504804602060240075102c90020f0317148000411300d00e0000d00d490804115800028140840f40c00001c1c0740b6900142c464181c10780d00e0f1141d204038060003e80e8495a51340c1c400039024030070362420342001c40c1000e9104040005c80d06000507c8080504190f03085070401c840 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 494504460 1250 494503210 494503223
    0xf030d0c020115050f09090c130e060711060a0b0a030804080304050a0902160b09010b0a080609010c020105240316030c03060b030102030601020a030f090e01090231060c170304 77
    0x385040c0e5a90240180003248110f240c01c0e42c9990f0904010440004480d154584140c61100118045080a010003406040d0142c030900410707040a603207602900c209840d0088921540b03000030000b07845100000000a070b00c034040e05043d200e41c00c282c0040c000801c0c0041e40301800d00b40010000343c030803000700000d002090156850b945490100443d9207040c0e0f0204d886075004008920800c903034229003c8881d03620851110f903a0300d605a1240c0148180c0c0c206035000003080703902040350a00000e86e28490142c01c40240b002000b000d00403406e035001980c01840e070b82500001014002c80302e246105284101408075039440b52400741c0c036034144110fa4010f40304d21644900038130500040b405401000d48090b07000398514180390000079510b4105200c09400c000c034039070300e100c0b8140c40340740c0c40c0000b0b00a0307282c0703e178565031683ca0001c000d41c00340d4010246a4548032403c0c503200c091602c2d254080b044064141591480e0603800d403403900102c002252906021441d00720110703052000366005030b0042c0d4 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 494505710 1250 494504460 494504471
    0x5180303010e1005060c0307060515030d082203020604020d0204140f0403140a05120402121209030d0c0305270d0f150506061602030f01090503030403081b0304080a020f030d 76
    0x1000f03024002c00a80007079002e11010000c000100400208a03103907139500010000d004c2c5d40f00540c5600520020b050315074103000b030b0050003817207990050003607002d1b07200f41584103140201c81010f030009200300362008001d600200001000342c903010201c03000150014102182e403000364111070003000011940c0d10000c09644050106160380504c0c945404244424442e1400380304401c09403042c0200e1540503441c8800c800090215140d00c0010b8000c900081d080b50240e4170004172545503074000c00e820710302920600c0c00060b0754038411510504480d070142c0b42c80380707020400786a1002041c1070301141c1c0c5800801c0c4511000b01e44460719030b40d1440707004084101c0c00d84441e2408101c1c0040408d007040381207086c03605210341603a8000844034180540c4285281036121840030134140552244103032559461701c400401480000320040d84600e10aa03542c2d00541c2d40d0a241d00400801d0364000034200405000141c00141c0b01d80003003020b241d4500480b850381d2206601c01c0e2555008400341b004254564 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 494506960 1250 494505710 494505721
    0x3020c0d030b0f1c050f062203180f05150403110909030408120a0305100b0301170f0106060534150b131a03010b0f01030b0112180c05010c03020c0405180303010e 71
    0x2441440c1c1181a85809840d00d1704082c2c0040503508d5142000070080200d0f48a80400c25002c1d41c504d04a03520140e807903240545c0d031900240018040c03841214082d9081c10b1010291140500444091301c2e402580b80c031000801c4820f2065405008049400b00c4c4000c0101041c0c5980802800c004082203c1445940702c40c0390200030150ba0001d020f003001c40d4510441400100032004c20f07281560b481d000041d00d071600c0d03e46200c5c40d241c072041c40380040d03518042010502940c00401030041e0544800007244650f080c19001b2802d1070380c401003040d8640002d04113000a000c05504011a441c0468042200c60400740014080c1240041d102c02950f901c001140021403013030307019260800200c0c001c0116090a0380829000000e1503145d0f410141d03200c464484684c09001c0401c10003c6405040020700144a40414006c00400d01540e141415500024681d8070658401e1980c61307041e8003502c100807260040c40060400980b507600507070b40c801c070068000704040014600811040c0c031501c1550524 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 494508210 1250 494506960 494506963
    0x80304020f100e0118170a050c030a0302030d090204020f0a110607020f06010302061b070b0c0705040507120c1b060506150307140c100204090e06060103020c0d030b0f1c05 75
    0x2031076607590280301100c142c90201c940180c1400c28503c820700744444407519000c0502d8502005800c842d8407a102d404508905031800241c1d07141c1c007441803080301d1242094008140d5940075a040040041c0d000300007405040d1400d40054003147e1001d032016041a00000c001c0b05103800c000c20075400150070812100303161000304800ea41203200307800030380741c1d840320000c4551311038a050002070300079600002c0c020484c90300240000c194050301c2042e9240580c482800b6403280d48410000d014910034503c011500d45050710503940641c040340c0b9460b03544007440d00b40e00c0c082c1030182a0f100074020700031a0302c002442d002d1011b031101ca100c0e80000a01c0d01c2d104041049004101c2c035203250114050040182843c3c100c800c0f0006469102c10680e114486076001600d41040060100d07500c5001080018070a815034000340c0750304110000351801541c1c2d15004604900a010140c104d036480307400e5100d0803502070b5202c2116040064414aa0801c1c86030100304003c0303905800e059007418078555441400720 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 494509460 1250 494508210 494508229
    0x120a14060901080c06090a0509070909051b04150315090204080105010f0803120a060b07061e0e0705131103010e070906020a0b0115021005070504090f0b0d06050711030708030402 78
    0x800c80340314100b0350402070402d80c0c5907094044680640f4002544602c1030303031201001703c01448010f001c844c13035240030b04c80240118054820826840d041001040c440004030300800e10004510341080e06240c904960217402c10224140ca2090654560010a901040d0074900001c1c081089001d80d07030701d2601202c542182d10580c005010420002030902040c927000c030444030f000750307039644040280c0c035017400d5240100641c0d800b80000420002e075070f00c1040265000310b1a04102c07012810444490740310000280c686242c40428503400011007071219203000c82141102c604040740018031044d51103a0355803950701c01e07004401012908010022503660003510000544140c0c40170384508803c03552249000207040c06404c200703041d0884d0300e40d5420320030860f1114005e28000c043c442d60a240780003818942c060700800c4201070800d040344c06100600c1c06080700700030004e000c0039810003054941c04010b242c041c005208020460072040f0010300100050000c241c09900c1030b075600c1c201441005403840 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 494510710 1250 494509460 494509471
    0x402061c061e050609010c020a1203020d0e0108061f0215130506011208031515131724090c1005250b0f04080f0a020703110a081b06120a14 61
    0x1004040c40580c5694054030340b0205e081c00c00e00400d109520008003c84200c0c0c104040c06280051307081d0906900181e0b120650503551110803200a0700001100c0040040392840e4100080601086401d00a41d900d4458080d50b44150b80c01c207001c02100c0d80f00c00c40281e800c2c015440c002c14001090003002d1142c5401031a0656500e030500000d55240d000b1400000c12242c00040c3d2411f10320400e40f10900104003605508000664912440b240e481e0b0250542c02840100390a61400b5030f415500080c45040c40706541d03400c031001c10403000b00e05800300c400038002812400350342c840300ba41e0303100d035550f441c100b041d140c0382c443d1202112241d100e0f07031440f80c0354a29403c1c1003000d010008600e810030901e80002003c4004182c82d90396060601c00c901c99500315180c44100041e80081065004c54031005684c0304140c0318082da05488104104000caa005012143c0c02c107556032501000340c002c1200c0c01a01c080d00c5c207400c7c5a882d6004200e0403c044445030380403038032400908080658180d42c240d204 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 494511960 1250 494510710 494510759
    0x50d090803042d120302040506071a09063306030f090c03070323070302090c0703080a0b030c10090b0d02090f03010c050a050a09180b09070c0203150402061c06 70
    0x50003580031449010f0a0a0f0160401048140303145140b40710303804403400360901030840c40c0c0c1c501c0d003481e04015078500c0754050600c407a040400b05c2c90702003003c522107015405d8a01001c211421103220b1520076841065611816241188107840944410000d58490303204101151090714000c0f020500700300411584134441d80100d082480003407040e012000c0c0a140c4000c5d0314035220b103103c05880c0307011100c0e000694840900f0003005510140d450080100c01d00c290f0722909c190b2102c041c03030420354584200941d41908001c0c40c00b1260304264135030a080d60502c1c684080520b40e18282c0940c0d40d8060554009966000901d420700742c207020040d03001040042d00200021040302e00002e015010320120b105c104140000c074081610b114891134400b40100a0707080e107040781030f0700205005003610001c45e40101d0301079000403007490250000d02240f94025018205806c0019407004401000500c206e034440000d001002e02c10343e40407405403402d280b00400042040c00c1c04050102e1980000150180 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 494513210 1250 494511960 494512013
    0x40e1009061b03090c0b0d0231060309020604050f0a030b04051506120a060e03090a0f0e07180e06130c0305041416050f0103090503070606091d1903050d09080304 71
    0x404d4845c0403012107504501454445003140350150180c800c2c3c8403421990900d082c0c1140d56103600071500040c00c21166400e80d0f1160360381740180c00b511000c0202941c08001072008204a044c81d013550444110000d0040001e00d807a60745201e00080103544c00e0754182e00040061128100ca229004d401c40821240300007031300c00f0302c880960395a04079140104215103842e000c080c114800c0082d0390381950003c000c008541d0726060440c40c1145144200c13aa52100c09000c101480e0248100d140000c0b12450000451030429021040c02400604015000890036010092035400340c81010b175a20580c0d600442c01381407909055230403041e44002e0248070f0300b1022005918000c0c40da0450201d4405882803400c10b030b41e08006800415850070017502e18000040c8403020000c403075100c00e05a4402d0b00040210401c0700c4d0b0199a40c1e503046000450507401041d044400e620300030426100a4030030b1400d9850102c81405180a460051500300c03000540841400100200640d18005110220140150303 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 494514460 1250 494513210 494513213
    0x5030408032406040314070506030106050f0f090a08010902120309030d030506030a06140f09070b040501082e06020c0315061203040e07050a120501060806040e1009061b0309 76
    0xd03244009004010307592090b40c46040c041007061851609001d005001079151656818098003c4e10a4040785120b4050100301158611f002000d880c1610039070340d26035060062610040c4602c1d07001800202d00480141310020f0250348040c682c00107029040c2c000f0407000c919105200003a20004001c4c4075640050001d03580b180c8000030017850103074041c40d020525403648404603042c886101d00181025003805205218a9111502d02d030044820303114510301a9034281c113943c0c8902150280d12494207017040104401d600c14840d1310382201e4480e944104201c510307013000e40e1000c5040c0428260b50b84440c810800550180141202c2441c2a0040d02040c88040352000c5501801403500e84241c402c900c00c42040da004005540143ca0030250800b04c5051401000c0d0171500301ca1280c01c00a14207c2000760350182900410b8101c81c000d840c0e0080c0340d25807204100261011802000991040600e5081124041d00801c14154010a0009554000c1c080d10007000d03604501c5c0d800615003048203840 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 494515710 1250 494514460 494514473
    0x60e0307030213090c0801050403080906010b0901140a111f150308070609082101140102032701120f020405181003020d1424070201060f1703071a04060c050304 70
    0x2c1411501c3d00000e01c95158074000c0100c0b105078200340e004d586040b00704410950040d040f40c0c001d20b540c100300c0340170303070307652901140a4811510b8090000300c80c40c68a001800b40311001e41503000e003d05001581000340e420403441c10840a04202e00050401680c180c280400d202e8860740304c0d44010608036450843e150302c00d00d80b003184402800340742c0d2a0490000e01c08100e0564218070540000c811410070454031710942c4900030b0241e81c014488002e404861580000121031a40c1b01382404448a014400b80c0e80c42d0781103140840c0c5050003240c003082020641b240c8210038080c04400b000585a9007043c0c10f000350001c202140d00f6441000c1c3c0300307201d0340c581010040070449030304441020042c0e80314070b0001405852441004210b00c03805c1020b600140d210000041c0c1c3c41d140200880507644d0b1030108a09a0f10303980318034400902099002d01901c2c00e8414040507550007001128030300708090b920b603a04003000140c2c000c0203c0c0c000f024841086a50b0040100e03056152600d1400c5042988528 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 494516960 1250 494515710 494515729
    0x1e07030203070308030a110301080a0308070f02100c020f07080102120610080a0b0d060203010905090d09120209040204060312120c0f080f101a070308010503070b03240d0309060e03070302 82
    0x24000c01c4d40400042c410346901c2d08445240c0300e045003020345a5a444101a5a8031200301c1c086002c40c00320f900180001e4031448001050012540c018540e0b0001c0d0022280207183d50395400045020781075002801400400a9a00414030303140010fa0722161510558400e01014004610038114608001a07865101c1c0740980c12441600000581c004da17500014458011000e0081c0564000310000410031820b0340720303d204035190400d0341c5030394600c4031003111a000030380a030000c1e0a6221000c42c0140c200720a00c1a80144058000076003030392203440341c010880d000603490b00014203080d00340601040f240a0400e01b121141000700203d0b08080014014400041c80350011703024110010b440300c103903510900020070000505080d8100c1941040c0801e070300003002503001c03c10307440000540b42000108501210200240242143c440c045600d040300c151070151000a0701502911100e13a45180e2524500c42c032179141c840903d841c003800946101423150a0710700c2500703d410100050380300c1c00310341e = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 494518210 1250 494516960 494516963
    0xe0a17130b041d0c09030d0e1804150f15030c030c0602120d0f14070302041a04031110051908040b0108060f0402010320070c03021801230109171e070302030703 70
    0x54100940c0c031000c140c034180c09800d01d042da05100d949481c3c2c03c0190000c2450903002c50550340c2e0541100d510a142705ca102041e9001040149a4101d007021610035030300c1105940d94038400803803051000800220111816007040e00c00d003414550070001c10241242c07400003811741d4000751503d101c80d00300e89803080c0079001d00400f10365150078401401c903000f035001c441032040c001b100510904145800030025042405440b20740c8020711031002c0d140940106440440c1d500c0041401075120701703403d1111104001c0307186014030800b400000c00e5184460071041004441740d6492060349060300b010142d503c3c041e40900179540111080c0b000100d8541d030004d601c1354081c2008284a9101c2e00605001e00d110036a0864003080410800104070380c0807002000c5034001c60b000c1030703008211250f8081d92102841242c0d942c1b00800d07080e10418420032503c001c5000c05040103020155a6800404010f828801c802c056400141ca0480c401c664000844003821995008180860a550202e5501d04407400f0 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 494519460 1250 494518210 494518259
    0x41209150207230402030709051e060409020a09050907050a030b100e010c141005100f050303032e090504050d0e06390d030605031605040e0a17130b04 66
    0x20080e40c03880f004043c1910034800074204544e41d1504940003001c0c0c1d134543c0119407082030086038a000455580e81001910040140380e00e16291603c000200250f202d2601c81082c0400400001200c0c1d8525410501c146070035102c0c26926441d0010090480e00380e140001d01ca0000d40b04030046403036104250011010080c2456552607426040156080b1000e546000030703442400088411034503160441070050b0f0b180ca1420200e25103680d03803c004541180503d9406500910010780b00601c0f580000e1908030a91500a6007000c0900d41c0300d9401c40300d0303000b05090310303200c4080c001044010008034986450a15120410a0030b003000614a80b298010807074070491b42e1407404448a15000880c0d01000b03202015101034294031800701d448520b80c40040c0f021a01d0154000381ca0b040200743c91080551181045551608100821001b0000e014030b103902441916070090011317040c40713900c1510781011042c20f03844150418960a250005070498502040c0c180020041082ca0b407105220000e02c142 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 494520710 1250 494519460 494519489
    0x80a0303050c03160f0e09091b120607050d15030f02130e06280c2706080402040207030201090f080301050f010309020d0b0421030507080708091b1503041209150207 72
    0x5c104a40c1c2e00c40741450030742c0c8081d00400f03101460000066204d8800403400d0300080035002502003000300b942c581803a40c4250841d00c0081e0600e07100d000105240303003c0c02d4000510904000c840c00303007c13001c1d40084515a039814a19419442e00000000700b00000c00701c1400561440d9840ca070f254070002d0400c0792501c00410181c90b910164030410521450010030403c6024040440101041c440382010340e03511051240c0d8226400503042c20b10180d0b00340b91186d41d899265542070200079402190142c0841d56122403000004400240150000380a4a60383d0789a504003070800070b02601810003035040c5480c01000400503120031040316000b40d00b000c020074807595141844d40410f04c0c04040e00200c0c000508030b1000c403a8041c2e001901517042580c2c1c4000e540c0d6419020790b8002070940d0725101591000c1c0a641d81e12514500700d1141020103020b0007101c5105500e002d0241e00141c070101d6090031190042c03004154044035140050a00d00a2000c98403030004002c0d4958544c0d0003600401d11085 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 494521960 1250 494520710 494520737
    0x801080f15181b01080c31080d030903030e03090a14060403020a0603020c160302010c061a0406030c050f100c0f02040207080c01020306040e03210916080a0303050c0316 74
    0x900c41c503448010041c2c1036980388540181c1c50058801c00c644203d010403001008141100010030036207140b042103095000c0722040c600512a01c500f082014006860310007a40819401e1040c0900c8022401545000c119141503240c0602507800709030f41a11183e1044c851081c0c103640b8007004030112a0080c03209a9550604404203510380701d180c0029410080580b03000480a60550050110707031490000c0d10b10600c8588001705414a01d440041d0002d0104040080410480d5101e101107214038a031030240e680085c0c000c00d050700c0071170348151782c3e440301c0e004200410304101e98080300707150084a015028008803000584101040c941c041c00f00190b81c0130460864480740d0440702e1705504003100d180c49120341c2410394040d610865200e4000d6080500c0002840000003e99801115410410700504000b150401c440d810003000309840c0c1c0704440114003d003200035050310251000e00b001d001c68000c64203003e0291600a005d12680007800c108202c1f1484034401500f8100d0141c0c98841510281b5 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 494523210 1250 494521960 494521981
    0x1509050f040608030408060a1a0901180b09010f030606140108010b070501150b0301090e0d05030c0c1e03030f07140d0b0103140a051602030c0d031d0d0905010801080f15 74
    0x1e8202da8810b10001030041101038000401f68407805c8009001e115180007405160003000681034400c1d0050310660040c8107070003000132003110100040000141d440003210021700300c00b8080c0c0c414042003d01100600501c00c0380c0c040d65010b494503600041e034810040780000c015480511456520060101d032030010440e0a4020108481c201080c1d030303480b00d8440391941090b9000384502c0045900e000d81e810071201e0b0104000002c0049030f01c0342c034210703910f2801c81803da41c019612080c0034001c00c80811034240c0e03448640703400360703120308001d41e05c17490614004e82d200580607000000f400f04c4d15055a11000e11642228075010307160802140e05c01d11000141c003d030584c1c50396400c0d111050030400036070f01c1041e848a0300c507076450a2100d4809601d1007099803217119070024100250012203500001c1c03802500300901a00c42400d031650030f21003030340d030142c20640420f010038005290b80c00200600d40e03004404602400d8100003420000c040e01e151140d07540101141c03001c0803054100090700c0c0055 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 494524460 1250 494523210 494523221
    0x30f1b0705030406030f0c02160b13050d080702180c03010302040f020d090302100605060403030804060e030f07140c0f090414240a0c0e090420281509050f04 69
    0x24441c00312030703e55807662805800303861010340321341c5001e00d0300c4508003016100041c1d03070200035040d041c8501c80c6801c156804185501100e1744500314840501d0000340c6407900554000003034000c500c00394980c1c20600c1008583c070001c00720b89407600c101c4014004400240c03800c5030b0440313904680014041002d2240000680540c003020550f481c5090303100c0317041c5600031031a180354500c030080c03c01c801c1d9164010800680542e00010380010390072000500014020350060810910304000c032400c00d4000c10005007143e00124040719003442c00380c8021012081045608500401150242540400d0340041900480005c0c0003030000340000021000311311050100c440d0782900c91070780d00c0441140c02440c043c024400d580041e90f03e4a000c0b2100700c050700c5120445462030004100c82695100c0b43c580c50002c000c85000052110750000319a202560b42242c4415455000640c6400c42c072014958000c048c211544007a000d26400081403803110f83c032180040584a0441e8078800b04400d080101d4014072 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 494525710 1250 494524460 494524463
    0x110306040201090e072a020102010e190212010b030106240311070b040204060e010f08061317130e0f0a0b0306070f1d06030103030314090318060f0909040c080111030f1b07 75
    0x4100b5030400e960240010611b25078001c0c2c0007880300c50300502106640386501103070002140e40035900c0600520b403040e190700203c8000d4001161403040f0800103821651268000000c0260306501d41d5841c00900740100b581030745500b010016510002c0300c401281c4a203101c002d01d600c0c1c2e05000207003150740c1c81d402603000d04142c03c0c00030359a40e160380c10301c1c05a408030f00500e0410721410f000107041c0a00d0750b00b903142c102d80c8500c4000c03071700c8445d501310076181d04107401039488140c1c4100c02184a01c91142e105120340d583c03460903a0507003002c1d1850f42c01c03030f500c0000ca41e0181d0454010000c8450b0450381e4801803000a03c2c01140d41c503100e94040b502c000c41001401c1d40400b00000020038181c0c560800c207000c00c02c4640704950f035258a4101c035030702c0c854084495030540c02135021071002e241c074401814140d02484a0a0301e002e02c66000034120406c11941200c0d03000e640354003800000030910a11000e0740143e0130f19807540c280070000600c91070009083d0960940c0c43c0c030f0b04285501440d03040d1381415 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 494526960 1250 494525710 494525747
    0x403050d09060c1812080a080415050c070b090109240207060f051005030d080106120f140906070c050604060b0d0c0312080a2f1c0603110306040201090e07 68
    0xb49402c600142505100150b94502102d010008101009031101c17030b41e036181d0b005102c5490540c4112040da10400004c01c00e4a040381c0107000c62111a481c1e0050901c01c402104405a8910351480d0903c2501005069076000740c0c5495040d50000707890100d000b0103148000b02100c0c404001c500b801000c1d00c95408000d110500f45001036821340e5454000303030b0041e0641c1c030040800ca0b8541d400d06030b5400d070b00344005001515002c0104400340c06046002c2e007410000c800882c1c110440c040c0785090b5240040c05404842c00c400400010034410b1080542000d024a0000909009503d0b0141d0798040904058030859448a01c45150755a6640c0540520340c46813005200540c0c1e401c11001058043c8084004a904a000510183c0e000d104810b9001d988101714505019544009a5100700025844000d08010004803000c03080740c03210043d405c0154080421200c2c2140b4028409140300004140264030000038000142c1c2c014100d501503400701e0141f004144d0f0b400904482d81e400184005400 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 494528210 1250 494526960 494526971
    0x604020f03120d0e0c0405060d0f1b06051308030f090609061308030a080906070c0b06180117010b060408280b010f05011107080606240307032003040203060403050d0906 74
    0x40940c142c1203040c1080030b1206649801856900b441b0a4403000c4030142d61100e03035449040d0029030044c042e0354900c1d004294000a8a82600c801c2c0b400613030320303001103021800c0460300804102000c4000d801a1185d000918200000800030048034000e094015100d403101003000000764440006a80c01d00c41c1d400c51214010f545d40c0710560b03e0382e010322a00400507100c1c0c80090f151440018900b805030380c190752a18496005d036220b18a505102606c1d940c0e10000001c110500c1054826209005e411552044802c03690900502802c6a08020020f8050107003403004000000d80407a80d14462880d5101200384400c4040032120488116140100f80351501000400c041c007840b418407040c0c4e1000e80340c050b2005410304145a41d5111441400c13180e611010000d540c9041540382000d44410403840741400082442c601e400342d4004681d0140080c0d5111034100c441c0c40d001f415218042c00c8401a10701e981040c1d00801d40311940100094240b00c0002119480e100c2c1d607074000c140da581c010404014 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 494529460 1250 494528210 494528227
    0x8120a09030f090b07060b031009141e06070807020712051f0b0d030f0c050a0b090d2d0908011506080c040b22051002060402100f020604020f0312 64
    0x100326040007900000c042210721429a40981a5881611482c1c600b25052840640d1407002a04845103034580501840c2d014039019609400f40c20109441404540ca00d0a46004410714011880b8070f507444080b60b8603020030424101144064000316a854964026500c84e1016440c00e0070030741c040c04901c0c0c0d18076030780d4040c4007011500542c0103a4503400c00c0f81c5101e10072099000e60b802d0028071a405420303884041e0000b405900c900c10350112a00701442c0a540b00e40f2030341c0c10003012543c1941c1580c400403c00201420601401c1c18110850802981c00b0041c19680301c100c0c0d56080f0217001d440c1c5880c090246050091107800010030342c1e2070007404010a828004498118144200c1000c2480d000101f00500303130301e40540d01516050b031b40c001c1c01c050041103081e200b002022401095103401190105450315148050540754080c1d400500e000d003014810711014000b1001510f04220188040740303403042c1e020030890f4000340c040391600e88141c000c400081c04d05054001d690b801c064000344030003 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 494530710 1250 494529460 494529481
    0x1404030507031101030c050a0c0c0f08010e0601120b01030f0302070302060406020c0f01050c0c06070206190504061d010806120115270c0f12020903070e040b06010306030203190812 79
    0x90580740300303a0208040003c807a0045d82621416560760340402c3c0144101e85143e44030310109501140522501c0d901a0b039508215a10088241c0028200d40d4503802482e403007600820541d4010704500c0007040542299843d020510803040c08002c10f6540240b0603082814800c07c2030b0809181c006024a50320ba0340c4480195440c2c6442102728040d201403000301e0b0031580908147d805249004015181c400f0300207080040700d80c80b03481f04a902071410301681d6080c06590301c0d042c54195003074542d59030321400c00f0005004100d02d0034840412200300000c1024a9900020f61604900e040d9518841003081c400541d024020782d031b28008a01c0c0b605040012844d04000c41003141d0780510030582d590a80390391024040c0c0d0400000305000c581c80d41b0940410b00e1060b20b820700082c4050500508000092000a0901d0350b01e40c00b8185550000f000d00041c00783c50041c0380d41041c42400d04101252640d40800d460301400314040091035051300d00f91080c40103900442d00014544800c41800e45805950710 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 494531960 1250 494530710 494530723
    0x918030f0702040b010f09180e1506190f060c02060d140610050c070e07050c0615090a0e0a03121d15220206090409050303100531050714040305 63
    0x341c1c40b4508020064103554000c81c2000c00741042c540e56030410500300300235000b181d050b050100c416256200010786622130700384242480540380c229010118240f440810502c190f21110041c014001d22104104280d0401d003418221880c6080260780ea107643e0000940390b00902800b10081c500701800f00d180903242c6480c05d48940000c50b028803a1008034075044956020300340301141d1a90081c2000d20002284102043d07100041d8584145486001904503041002c20f0f2040c2c01c6500c008580007403140340c0700940c1c0307030300c030090103002c00c00e0107a191442e90f03549042030005070510502e6030401035001c2e09608080802c21010b500d4030b801100003a551a521200f0094107075055400c01c0110741d89483c9980c1030482814416000401e85025808108096200c8011164055524075561001860500207180301d01d40b00e00c18400601c0c604028003c03100c1c3c04500c910781c8108881c103401412200e0711600082401c901c04001091b694101c41510301007841694081c0d00e0310701240c000104400007866 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 494533210 1250 494531960 494531963
    0x506180a1d0102070b01170a021201060f0b1611130207050a0b0c130b0f0415020f0706050307050a0e0d0b01031407050f090609040c090c111207030c020918030f07 71
    0x5622001c5000314030360b8200d000d8980000c242803084c000401120551010f420032410000c4181d505541c42d9a002506241721010209081c0e51240300404c02d80e040150100002c240c21521207240c2840c0c250b0000030320f201400000c1820108a420040c5e031303160713075031500c1c01c100d000801195a0307000c0e414090b55460400f10201e492080c8040010001c106013025200b0030107510f49a6050705040c078000c118160021400c072080d09006000008154041c1408002070401d5900a807918042a103425410880550041424032004009120580b544107040b2401c4042d10314200400c18813080000308031420b2511f0150040b0b080308004021f01030a080c1440001900804031014540d607603080c0b00c840141780c030115500c02c040400180203401c002d00490740c4203110b4030011003000d440740c0b01042210b454844500014180201c162010381040005182c140c0840c2c00044c140465a68018421480082c0003030290304c04d88007080c030001040e02000d00c2c4400fa036041e030ba100c458541c100d504c5900034040 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 494534460 1250 494533210 494533241
    0x1810060e010f170a29091b070b04141b030c010f050a03180f050c01120606050a08091603030f14091c210302091e101b0206040b03010f05010f0c060506180a 68
    0x415801c2d441120020301c2c0c40f41d0004280c8c2800440d44900141da04000d00665030b001a50180404502e41404011030441c1c02e00c0c2d90b1691030922405161500d0b10070b04155061003011000841c100d40c000d07054440c950041d140200e540044190340420120010354000c0841280f00d0758607041040104030807080300001e0341c424484041c0032501200742c418038030469010403070411007010f0407440340c0d4810354800015001c8903512880d1454845030391080381d00590001d68045101145250701000c0e01035501c1501d030b4040d0410141d00c000881030b9490381c2d40301a6041c40d5000381402c000005056030380e1040c0e24001c1032114900c83c2d5016020b9444841c0075442104041c0b10803081003002c6c2d44082d1844c00c044c1c070400265900c0e00c03081e00d0002c040c48002c80c80390074a204000050b42d40c0320042001e0325142c035100e92a549020408440741c0c8103078000714140f00e41c88211030901075008041d5004e064010f540400c2584070320010890440019559000492405081120b01c0144da0480d600400c05881d = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 494535710 1250 494534460 494534479
    0xf0109060f0c09031e170a23130b070212070b04031a0c0d0b0402040f0b0d05090a050d0305101a1207020304180207021810060e010f170a29 61
    0x410407540f200b02c900000385002648030701c19031001803803080e0301c980d540709131800751040030561304d07001544d0004c0780380c0303000101e00ca1050318003060081c0300c84120740d070f10f07807000c03410906941e010000b45400c0e405101840312000c82c0b00415135485140c162a410000c005864103a5160000000d842d806400103580c0760034a0499407040f6195840d9241c03007210012845424510b0380307143c0310050a91640011f134415020301003c5022556802d01380d00418901d200d6a5890340c0d081c2c442c8040d10700c003c1040119404c00081c072404188040b603000c1e03404400e807900187d40e90b2804509035460342da41d007100724400156190000801310000050440b141c00c005201c2c00c030340c0d40c02e20403a640d00c190300901d5586641c4c1c2c91600e03500350646d0080c198051004142c0c0500c00c0c1e9119103440c1006084403148030141080c1c500300401d0b03410894404a984082c80d048003100f4030b445010303001e00c2c40441e240c0c29441514000a2070314071176a05c280d07201c64400295607800e5000041304004284034a40082c443c2d42c0310f0 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 494536960 1250 494535710 494535731
    0x2100c05060906011412011104180b03030304021011030d140a1407091509050303030c03040210030b0d030813050607020115060315090e2401090612050606040e0f0109060f 75
    0x3034407138100c1d42c1c1e041c1c030380007018815028443d0082c1122003200c1c856488d041d098600c00000005040540142d01c42d079a03040d240c2207404001e5030f86848034680203030810001d0202580b500030000c034498a95041491165101a4040e4079510541a244000c0e138900b0110200200e060711102d030090050a405116250809101c4c143c1c1e0301d007e40310000481c009401c2000781550305030100402d003556013012112650f1b6800031a085074821102440c3da0700c0300004000c1103192105500055001601e0308000c0d440340007022985803607002801500340595100010240420444e083c681c040e404070a464140c10030110282c0a4000c20b00c1e00540c51310714060106095120b0f01c90402c00080454004106a04c0d0141f808000c220000000c541303070040042c42c1c1100115190309901c24484050701c18040c1d03140c1000300c01214115004110200c0d2158001004590700090032900414116000240c2200110842d03103031203414100800e1650800c003100707040c80503036800034540c100164001d11051052 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 494538210 1250 494536960 494536963
    0x507030f060b0703230a2f06040209060d050303130212060408071e150f1a06040506030714211b1b100c05090406080604020303030a02130f15090e010f0e1302100c050609 74
    0x200000410960182300064050319094030401d80040014082e0030300d03800580c8945085034411644504520414001c4008504181e00e02411544520f030103407009040c00e6541c88214868820068140300159250200c00c0000c030a4000c13000390300059090180c00941108006040700e607812504e024a450318010883c5241d81c0c4111002c0c500030802072400d4103000400946e03420252424041100c4045144c10082c1d01d031004100d505503003007072010700342c0784a00e50700070490008194001610b00d41000042e50300101c0c0c261111170500702400103d9a0700c3c40601031514a00f0580606d5040c10003c28043c402d0300500100002c6500b030307400b808900c1d00d804a10703554001c2910001e405600070000110b00d2205580034200c4510b41101a400d04c95465004c19126080794000d40301214401445016035504403240307030014441e03502101c405624003904184550180d10582400120520010724040b44907051520f102d0386c010308071000c401102100811022220b9400c503a184521400309004100 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 494539460 1250 494538210 494538287
    0x5090621061f0309050c03012f2505012405180906191806020d15030c06030e07091d0607030e0c041116060507030f060b0703230a 57
    0x1c20700c441c15030002c00b10034110010504800c0981e80e501446030b07082d0165a0a0040305560382450660b0494014a500003280480290034285103640b4200980352190700c00b444c10504061503024900c2c0c400302c21303080250142c1402c4051854001c07000c081620140000440c400541d403007035030781e01c0300d4441c3c208010019000070303544000140d0240b00090403030710203454200e01c43c4010100100d07688003101c501c2d050556021500b11980da401040c2e45141c00b6041c401c844800c8840e40144007402d00d16110b0156500d0f141c00b80a080544034405540c1c40d5004016410040400000401072000506c280d8100c42c941d510226003103010360341c0415800e6100b8040c0314044c041c0b0070041d004107064007003007000501844600104500040c801894102c0d40706006024542c010000801c062811104c002c045070349001c4600340071480c1c64800c0c81104a044181c4c0c6280d035150401d03a07035010200c0d2900042c80c2240300741c441404030008401d6004bd0b0311481d00c81c6050103030846a11107408140a5004580 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 494540710 1250 494539460 494539489
    0x110105160f11071e0807080604110d0b1f0b040807030303110414060d0b040e0a030201060f06020304090f0603120507120507020f040518030d061e23010509062106 71
    0x107000340c0042c80004c2020010a80300e295046a09121341e0b42c4441040c01d18000c0c2d4400c512130b030400c02c00c01040c00130216103201c0e001d500f01c9141244000d19500c04105c424040e05a0020340c103152640c01c0740d099030198881c0540011078409407160b982d20783c441d070340300c40394001200024249165082d9180390305040e102903071403201808280788000c4080c4402608156840104070b610303103241c6034150b1100c0c8200a1040d4080010388905103c5090180c00d540c840d07401070b000711008403000c111259021042e1000d8400c5a00c0228070785440c480d80300e01a0219400c050a403844441c0d241d5410758200000301105031007000d83e2026000351480907a864054010080d4004940d06981401072520398400c80c2c5c88010584084070481c007a01900d8a10341103000100001540d4950030f008040213000540c207050315440010f41c000d03050001032400b0f61a51000804e04241030b203664181c0d680a0819039a003500040e00b0740d83c840312510032101784880d81040340a40705464001041c1c00e03040c020641403490 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 494541960 1250 494540710 494540713
    0x151103010b031801090c09020d06050f0639070305060708040f02040f0609050c0c0105010e1501110c06030c1b01090506070c060f06081e1b060307110105160f11 70
    0x1681d805501901d585820f0651140039541c40d01c2200009207210b103c0c82c007030300c2c41540c0103840b2144040100202c0300d141d00840e1244500e46010310f000d0341d0f01400c80d007800d0341e42c44640403031400b04425410300480207005941401c40100800b8040c0d40005180401c41740501e003198030a80302d5041c01c0d03c8041d815540078184440303a007031000150030142c02c005a25444101e001990596401c2d103001119030a848011255070002591855010240a25405080001c409110504000004111840c041d0344110b050020346034140801c01024010704041c00c00142409640e460880740391680c5900180803460b44819000c0d040c814050140b088031140340d8800010702c074507228040181c880d0101404211540c2d501c031031075004100300c039014040082400d20001c246c1c0c1c11928003010000d007591401c40306144d10181d00030349894160b0680c001221001c4d80e82903541d44441d44110744a03c5648004900c540c24103040c00b00c8030b007003070305e81d00d40e0201d280c2d441c109030381e0305004102d070034500d81e91100c03809 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 494543210 1250 494541960 494541967
    0xc011e1509022b0b030d0311040e040c0803070b0711030304020d1403090a14151c020702040f05041101090504111c15090507090e0f0f060a12151103010b 67
    0x4038501c42e030040010124070085031101c941060030041c24002c0d124285508140c480d410340615003001c0000302810030841c28103102100400900719002e000798800e9950340056030000c41e0a20211802100c05010120103a81e84c071350040c00c007054840c00540708400094000e00ca15102000040b05413400380780d0003404545001c140d9244d200076a00c8042c50b88032103001c104001102a681c501540b001020030f41740340700d1040384181c20000d0b4110350034480e040d04982000340100045410a6410300c24844220040e100c0501d030010900400c0c0408840140d1480c29040c4400e2016031059020030500c02d0f80c801e6036440d21181808256035101d001e05c407a00c0403d05c50029000343c802c00841c4001c040c400d001642d01d5162013a0241c0300c6495100c0b045441d0743d601841801e80e0301014000241504881000ba942012821004540c1c0c004114080212108000c98a00d60310035501000621541d940f405007080341e0b052102050204001d925030f121b241c442214203022048090303904913004203002a04 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 494544460 1250 494543210 494543219
    0xe010c020f01110a050714060301050102030d05040f17070213231902130e010807060e1315090f0515010e0114120f22020618060f0c011e15 61
    0x121020707040d90354107100c14610001d080d860100a00908180110018030000746448640c01400341390101d041d010f5002040107000a0340c0000440f101030f2080980040c05139180e040c0000c074610364540051807290500d28500c03064035440090b0520074021184400700e01801d408841c11950f089126900e2500c840070401005c0c507034401c2e40b5a020002250700c54611660321100002c0b603010500c10b0804919039281401a2610b15a605000d4041c85005152840c10410081c00e9014401d030f240d4800d044030100b2800307c07034244d000060348444580041c0040768136807110074090a40352040754802031426000524504d00072a0000074000180c66011a6074001e000440f80d403041c0c809402c035800010807840751580c440070702d070a10910b401200e40c3c0c01418800c4404044050100c410040400078503c000007690750041160f542441c5400d5203464078480c4404610a4024801d00111411000c959031807070000640000402c3c20700301c0f58460581c000701424404035280e40e01e0650840c1002e140071711 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 494545710 1250 494544460 494544469
    0x70b0f010e0a2703030c02150402030a0803062706040b0a03020d02010f050f03010906050909160b030627040620040b0f0c011505041109010c1e020a0b0304120e010c02 73
    0x1080c040748010b908050005038460340d8104030f0450710450009036258143e06020b6410701c54013000c5040092a08100d0074203400113030340e40090800180108100001207101a52110040301c182c06080f0b5007610611610300901086040031a4140c0c0281c0c04d00e114031380d1524149884000303490340103007100400307492138004413902d07020545581c05001c010045032450240982c00f86000300302c1d0100c0071504900744014424a0f21b03000c0c2a000003580455884c41c402a0031090000036650030b42d4103181c580d501c031000942600c0a00c00d11014203820450040380c3d01d81031a2466110314012402400841914000c074040e44000d060301c3c001000c41030005018004054000300196801e011540303041144003039009003117a200e00da48205580402508010b5414103001e02244600c0c41041d00c2c1c02c00b141000060007003060300d88000c299125091100d05996904050f064506130050301803001c0c962150307a404e20940c07041d5401e4881c0325580540f18216803007030385104072040c810303541c850304907000b1350074403 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 494546960 1250 494545710 494545721
    0x804110a081903090501110a260c0321060d0303091e06051005101209080d050a0c020f011a01081e010b0a170411121f0209090a05040f030f051608070b0f010e0a 70
    0x20400c0c60708007000d541a0100c030032702030f180000305400170b50fa0700e6404018203485480040b1605003900c04c482c0404c05141e81d1005001d400c81c1d014240070a204000f4038080c0741810b130a03c40a500304910180903c207011190341f100b4420703041b458420880944400800c401c01c80f581500100060b1403e60010ba02001500060b2905100f01080b60404c10601c0d8180d09a95040b13461040895440300e0305040c481c1d040020304091040d0304003c00031040100c0d0003c030449882c0d14440c2c18000c0c2d0101140c515070b8007203031030418070740404805080344d41c4a41c422156903104d02000c200042d421039099000c041036030120f50003140c4c44940b031801000d5000038089515008003074146203004e41d503131080f1040d2800074120031414100d240184d495080004220340030304080c1207200b180b85000100b0000800c1241080302198040c1040e0b510f00350400800c47d29841100700300c0d988a41604c1c010004c0000840191040740d210b511211500d6450707106503211460b00b4400c00c01d4101400c2c02041d040711165012 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 494548210 1250 494546960 494546993
    0x30f030c0d0605030a110306130b061c050307140d030c0503010e040302010f060b040501090801093212030a050702010527030f0418060f03030804110a081903090501110a 74
    0x8a102c9984000190804481140c181c0b4a03420003d8400c0039840c00b8040c2560010161441018403226510b580e402413000504007409100031051f030f00300450800301007966003036211088a0340c0d40c00c0c500e4965141c0e1500b03500c14000d441406442c1010b035010740100c40c41107100b5074550f0705680c43c0074110007007a41c0c081c0c4180c0965503564a030110090b0076003e40341c06000c9400d03080e5034451910b400101003903880e5014021a0b450152580300060442d9000b900342043e805440c5501c00080550202404100c5001e100d40d218040c450501d0010b1500a9071091140c51003c10407999944026801da640880e4003103400c0040041d0700101d201c0102c1c2007820344030814110ba0501040070030380a070a40c081d0b0407a1498000070070a440c81189280100000b0f40141c00148101c11700d90360700544500c1c80504000d01c0400c44207041f84e0715403128001d610041940300700b203920844420b9582603c1604030350f02a4002038501e6004501d550084810326402503107030340140101441c03500d40c64036504040c0d40 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 494549460 1250 494548210 494548237
    0x703030507050903101d21030411090403020c030105070c051e030f0d06090606020109050d030e01020d06090b090702010608120304110a060203040e1003020603160c0b16030608030f030c 81
    0x25100c4d44041100c061200b0f2444000103000840903840240d81c03a4103006c16000d903026550348261500000c4150700004007e821054a82c2c840e4a0880780481000707002e10b810009400c00c0006050303000400741c1b981e441c141c00030005512007043c201d90149460358080c0c01039003d12424014000d030381800106016640094038100021040700783c80b1940990790710701e030941e242d02c01407007a664103209100040c40c00f40001c10145d0b0300c50f07032500c0e00c030b00881d503061051550751b0801c80060790081d0116891031649480c1045080c0c2c42d000720000400d11100110b0044600d0000200600c0c01489103006a8582c640100b0152601c403101c0b180c15400280201da42240301440070855454103400c0030302504107600a191250304088403a00300e040b0003840100d041505035010005a12001c1c112504095490440c44004485980544503480840802051108908104101106840085d44e100f95042c0c0e000c0c44041c1d41c2d0088141c3e00e01a42d403c250100701c0400202c0c80e13401b4544020448182c1c0082d = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 494550710 1250 494549460 494549467
    0xf011d0403030b03011a120f1c0903060606052808011505090a060e010809030901091a0c0601060e210c0103050414070e0406141009020307020111030c040603050f0408070303050705 79
    0x300400c5c20340b242c00314a078101d19403200e001e046915101403078101c02003201d0020403030038600d01e2031143d4443c40b000402c051540c1e60441c2c000594800c08800e4040c1d5040b02083c0601c0350b030b4500c010b1040d4400310303009400042039001043e2081007000151901403440d641d5030516400d0624041c4002500d0001e2f4042c044d00700401845a01c50b100084000e01d0b694985c04c0303c079010a4005454160001c0410803250402c00001c60680e811600c040709560864019001d00b0381324041052441c4a0010b01002e280b244d8000010702c01e501c8104040b0703aa00a0310034134954500c150302240b4100306500c0c420511740000301141c01e20751083e885030368880e00803402c00b21000d007005c42c0c05080c88000e401565041d80c421007000144a0a8003032104914280c4820203440d18000c030101c0c01d2441d140c003480020715000001310322814800d41100c0050b0740412202c03556421308091214050340603124100200f400c10000a62219100341050b10a42d00804254905900b90354120018140245001c05108051 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 494551960 1250 494550710 494550731
    0x90314060f0c0a090b0304030309061b03060503010c0210050a111b070501080115180b16020406080c0d08090411070812010e2a0408030a050a080f011d040303 69
    0xa090045004260001828250030000111080c40400034004121684200908012164020404000c03160f079101c016031241c0b141d1804030084d081e8076070084e20f0716040001101010b0550f40c417841106803140c40422410350b83c2d00a150030b0760090840382c000743e04200703144e090089071500a0b6074030211038600010700000c00082e040303650704894003801d00c040c19481003007541b080400411002c0e05090070403029541c5800072039064004085580360801249500070011200318011450280881030002d644410951491031090303000c0d030364107a200d0341c10120b00213492403021807210740041f00070b4044202e0b01c84a4a07000a1548015202c581003562a401401020a1000a803e680f4414080c1c40c0e40c5155104514508100c1a00320400b807899a00030b0105545103240c8500c0c03032041d00899050340c840c40041201c40ca004507070000100e0701001070003224199000005001003510f54517550640e03112040e42540c031020134040e0380340104400703406100c800c01100010b9031040c400e20300801e01c0c5061 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 494553210 1250 494551960 494551973
    0xe0c0324190207080a12060f0302130906060b0903070f06050f0a0909060609090c02121804090206030702061b07020609090a150f140916110a06050405031c0c17070903 73
    0x40c40203813085080407501c0981c066202c0058910141110030504c10395007000c07001560180144030080c410a400700f42e00400032035a03000224590341104003081180c0d941c040b019031550005007074501c83d001c3c101340030070180c0c4103e141c60156480e582d1f90605018450074107801550040503001c0074090500740000e11080d25029040c060522607a90a80c02d13450441228141ca1164540c202903402c65908400038462507015200c5244c0c034015507001207002d48000c98000c01c0d900383c000c0c2d00801d0000802501c04d40008846000340160101c14800c0d0001c03038040e40d0300317001d54180254070541c01c22000c0110700d4403941c203c3d0011210140000c500640711485405880c4540c0a13050003000d0500400401215100c007200b4040161010016403600051184500e884040484280500c083c03903c0c5c9010030800658100d00c1d4404003c00041c182820a950f6070340203115000c05660081c2e82d030b102c0406843c0120b0700711000513201c2c103c0140f4040c0007040c11a000030a0002000780d941e4000012420 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 494554460 1250 494553210 494553217
    0x7050d0311061614090f150705010509010209010e090c120c0c010e0106060206090d050415020c1921210e06040b090a06111005040602120a0e0c03241902 67
    0x501d03405080d00f44022072000d44046402d019502010740e042c01016660748905800000c1c4000481e100d00810101d02c04842c064080c444000c0c0040d86084100700d241c0704154000d1001e601d00b62541c8141401903c104500d4450846023208000801e100c00ea0410507400d0a15801542040341c041c107007450507002da42180d484200400c10340c0c0d11003030104032a40c0c0600140d42c100c030307004019040307202004001800c2031190b4400d071011385080c05040140740e4424405d009400701c3c018000e400d038211a00c40c0f00d002040d540502e45020710030031404600c0c280500c1280b008250710004010b100c0900070210654060000701100274048409036035003071661285c1c0184042c0104984070341c0c544030002c0502c822000300f60024401c1c0154080d036103d00400c00202c0d440409802a03010800f99135030300e0100040e000e443c0b03510003000101d409101c2414015013105824a034100d084821341c0e4030302403c0580da400c00c41041050440808003441070320b14a140b02076070050303002c0c2114210054042d034917000c0b6407 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 494555710 1250 494554460 494554471
    0xb04020105161505010f0510050f0403050607081006020106030b0f090703050601060f020c0607210e060f0a0f0201090b010603091416080d0f080609040f050a0809041d07050d031106 79
    0xa0b4980b21202d4043e9841214058081a8442c03181681014080780900e40030003280818000c000c950039545040712411200079541c4601580d1003800c2195014001001c2907966410001503484045410751052050404480e00728616101d19100d0400800c41114040d01d01c2040d80501c00d07002c404524108040d0b0300078030380c81d545c007615070441d8280203040400707401079544941c808004880c080f840120703840e84400320f22000f098000441004c20380703c0e1030300c07655030070b07007040020544115400110010308450920b5440d0314042246e00c0d00c04a080300c03d400c50003841054142c00502c4030900c240d0000e00030314440c54a400420300c100d01d0b11840d0044d060004105507400f001c090202503070503c01c4665501c03d6080440021464075009081e103d801400140203001c0c5c80001428825280143c0241c07a40200984844c101282810002035000a40082c01581044889416024000440b406015845010b001494240720401c81c003103a4242007902005007903010780c3c0320f4400a00456001c0d1 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 494556960 1250 494555710 494555723
    0xa02121801060602190605190f09022701090e01090501020d0e0d02060f010e070e04141b090315060d1a090c1806010f050408010603050303010e130305070b0402010516 73
    0x562661090301c0c00c0da4000c0e000b000c1150041c0c4d145010424074036141e4034140764805404103290356840c0003109200140e9140544517400d02c403200e80b44225503488840054001e0300d030980b401e80092448014107150384c5541c091b80200f80b004010340456130307100000c480b43d85000421501d44503151142641c003d0700d4012040707540c500315200e61010801420342c0c62152400506104d160008801058031814441d44a103004203400140b206845400c0100311400003e00401480c40b48041184507803c044a003500020303407440064126407844001c0e103a800382c000b0000c00c8085038010710400e05183c00740c4a1504013448900c3c000c00203104800c928616001c00c3d00a03001762030050301c40f82c6444100040b00303014040742c00210702079070b144800441e03100100b130a2001d840881030380110703000c1c4201d51004006500c0c0c900c02108010700440158122500e4421a80d07154451800d50301460354030b00780c01802305000704400f5001840020545520500506009042c440014482060036031103c2003110311 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 494558210 1250 494556960 494556991
    0x12051c06050a0608040209041e1e051528091a0f0105010e0a060c03090302030d051b030c19060912030b121c05090402070c060f090801020f120a0212 65
    0x21400c16030b40702002000d061401c10719509150300418900040904081c0c4418a1840c1c01c842d4041100040d552060384190690341260381148402e021712070480c81140d5030702691111040c0c941c00114024041d800c000b40064409509a501401500c0d900d1030400b500b030340700c40180010800700340a03840003c011071001d003a98540301a00c1a0b003148140c12640c14000d0103c0b5000c2c003603d0f2606150140d031460304207145642214103054406200f0b69000075494812165900d0442e94041c000c2c201c0940c0301c131803400c44120050343d4941c6074020205030001c0c40c3e2041c22505403981301e118010178124004e4800040d0b808103900c40404580b02d806420740403d40303441030004039080903451481740c0b91503078000d000d000d20740c600c080720210040d50854003001400f042072440c907503a07541201c4185074402d50071040d540e503500004d130503034240a070f0010114281000014188106000301d4041842c0e41803002e00e007a2100701640302c1c10740050205040340d03a080c0012280713801c40b4140c4e00c1c010368185104104 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 494559460 1250 494558210 494558219
    0x14040c1706010609091802130f0b0609030a121209081e090904080a0e030703060b090c0307020c190b1303110a03020a0b030a020702091801151212051c06 67
    0x5001010121100e441e911030300c010040729500c00000c400b510440702c0003180107890840080d01c10a1700c503c010303600c103010300c001c2c0c603000c1100c1d4050409400203032414803446007021304201250003510f0100390507820261250000845130281142400c4403810200d41e64410b01c440c074411204190422070715400c2c001400e58848101210f040c1000124900182c903100038140802d03005034018000034170000780464048284c0e4050703405101429000380441c2c2040b076890070b1200242812180b070134010305003040400c10700c070301100841e4032541d050780040000310340ca0018070155580009160034008654000462544540c20042842c884842c2c00b075404030f8214241039482600b80500c0500c5090f241a0400050b112003000c0d00c00c9580842c869501c940c0c40c04500006840342c03c5001358081d940400704070903520303130034200300710b910500f8020080251702400740303040404d00780140003e21100c20f01000001d00d50031600414131140c3c2c601103040818120344103282900c401070760151107456040600 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 494560710 1250 494559460 494559479
    0x6031221020307050d0902010306120b0412020309100806030312040b060a090b010e091b1204060b0402030f180a061b0e030105010b0906071e080307020613121214040c 73
    0x2a40341090310340c110b01d1414070741d0010b0310a2151502c03501095490303400d440c09581c040c0e40003500410724081c00c200b0000c842d1030f00350301040045504446500102e03200b50107040c0700000b5034807810f90207070140c030024030009030030f4a00e810028502a454442000350f01e4407540c034403080b54025440340c0c0002e005820110204600314025420132a0f94501c0c100490aa50307a1100344150400020342e40c40f1425211800c0c4096240d600c079004518070880003802c02c1d04983c2e00c0038075500c0b650003910100700c400d107151b0400060384800c0c0e4000c1d0407000300a000c58001d045941642500c50840800c4400800c10356031240142e403800410000c0b2080907607200080390341c00190480200c54100e000b00055810503101541d54000c49083c80c1c050a4082074010412081000c280b2850038184001040c020403840c00d801c150303004540345c000501401020411000b04c0e251130074103603944100f0f245118105100c0449508101400040b416a11062444442456102454044c030300414000c1e004600301142d40 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 494561960 1250 494560710 494560757
    0x6020c0a11040b1f0f02030f16020a0603050f010501030e0a050708011a01030e0607030e031c0b010e0d02090705090f0405090a170a0516020d05240903090f090a060312 73
    0x41d070045010161120786090341c1811800120014244031004201c42c1c58104d00d18015012308040139000001c0100303840c100c0d0000417520501c00c9030031011694a0300b5045081d06c1044d281100302521010062210350301075004038900c041c490044400c440066181c903440c01d201940040d081b0f07503481071802c00890140c00281d0502d5400e080a0021200c44c9842c240d40f040000c0101c001c050750745040c0b00070700301c00380b08817261814070402ca032845403411031044000703201810845001c00d0700400e24000d00e080800031a410542c004215864590350b02d01c06032860f6014080743c076032000d00074140035201c2d921445118040e1100400404400c1c42516000741000b40144e642540ca07001805501c40f241da012040310748801d01c0d500460800b50492010944002003504000e00901944a02c449021980c040d02c1c14828007985d030300c1465032039070400c5d1a20b03840750010842d0010f800300001c0700181882241160403100a8500003211030b0349466440e0020301c1010700d04005804454401c6c031103d00351480 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 494563210 1250 494561960 494561981
    0x5070f0f0b04060605120f030d0e031605010b09130305070201030507030209061216090305070b0703021501080607021006210f020a0b03041103060c0304150621170a08060d06020c0a1104 81
    0x400d07c0040d0b01c07414030340c0ca008440900d036030076480e03001e02000c060041c0f0a0b01c1640d0407112048111003202c1c07400c0c90203003c0900009020f183e082001984211040d05081d01041d01525442d1404040c0c1c0c0044018100c0103020b1000e25808100301041c2c0c0d241c036030003420081000101c00200b410050b009680042e00c1a48600402c5810b490920104801050300011a07240c142e405954102074502a410488092602203110042100008150b08080b403007502c40e070880c1c1e0907100c4510700007401c00300b10356031030140c1003003401800380100782c4030000c5014410b003a009030b024a202d1541a80010064034803034000c1400c0480100c184020040c016038184683c40c0b01b03e003d841e0902d00350345480c0440c040204050282e1144095a203007548140c0d1003100500011709054040070060f02c04010a03140300e01c422504807200d40707500700c12744410b00140c0e0131000301940c4179522030719460200b0030480595401550300903400c22403074041c00c004100b5901800c4c03154040b210359080b1507040208031040c0108 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 494564460 1250 494563210 494563213
    0x150506030603030a05031906030f050d09080d050703030608010c05130b0c0a17120c031008012a020319030b10020f060402061803100f0c0f05070f0f0b0406060512 71
    0x284001c030764000c825900d0003006841e0181d01d0303603200521004000b008441e00041c1d10326100c004001d000c144038008031503074000c908941c0100c01c1741208541c01002c2e4820901d0301e40040403043d040f40c0c0b0960003403460a000f840c000c10b01c20317111442079084074109004400414400501903603040c004003210402001d0b00142c5d0ba080016121140751a948a0b0500825545c99420240072009400081d182044051159040d1910381521103000e503510564601444e2000321400040a40050056284d1402881210101c0644160002c0e003804000001c04017540424004804c0400a01d10070008900060744d020a404c0d0b400c4c030500100c54200d046c2c1c2e42c215088140d0700030500100040068000758152500741e51001c0956081c2c40300c0b6000c0c1c004d00c0c1d140c040c141820301d0745000c641003607841c108501010019004482000c1d00c205a4084c0d28101044082c820319003c9190192160402ca0145007210715106441d85da940c07401d0412a4101c40c07055980c0d20902503810500d070000000c110110 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 494565710 1250 494564460 494564467
    0x4050103060f030c1a040b19030e0727111c150303020604020d05070b0a0c060c0801150c061b05070b01060201151e05060a090e0609100902090d0510150506 68
    0x201c5500c40010540160817008001c0754080e105180900c00303c800410704000d81c0340c1c40300400044100c12807030301c28030700c80041e00f0f200d030b400314888020401000710b651010303006141490315000d00301c503a968242e00d0082503a80b03511301c880c40041180184055240e060044002c000815001c10031031355050794284ca0034070450f00610010f500000c01d10781068048071070b5906810700b46081d9113440e9079034014002c0c0000c0420301d5542550402c0725181000c0c4690300030310101d0008101122000f500344104441030541c50702900e8264001d244070503085000f108085620a011002c00c2158000544440f00246001820009003c801d01c066405407181d4402440700340001c0d280c2d070304186060300440c0341c4c3d800c06400441c000700e16030005031300070940a403000d0b441d070ba40f070580509003000903c102900d5260340c0700001c6143c43c0058030301d4404d1215040080e909030405c0d805500941000f0006504034580c82c4900d00403a504121141d00280e085a000c039500004c2c00002901e40301030b500c92405400140b = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 494566960 1250 494565710 494565713
    0x302070303081303121a060c0a06200306060a1106010308041502120f0c071d06030d03020a050f0307020a020307090c1d030c010c0222090c060206040f02040b0f1504050103060f03 78
    0x1d01190321700442e00c4800f0640e061411780752003401941440c3d00d58071010002c0d000c01d180c180812807000c05401510200103142d500c80c0d031503285001c2e044401d080c01c50100009000c615000010742140c1015103000c800369103070b42180c80d142100a03002075403400001326007000b070a01c42d8610860002000e202500c002400034407000c2490103a030700c8041c0000000b00da09150802c040050100914103030f1032a24090525001e0007015281c00d0b100c081c00f90149951403039480b0b01030b00840349a03014036510903192201d0403c5e00981a08058600c3c2c0845c02850021409039800f00107034005000802c00000c0e80f032000d40400b400e50114045019031000790704955400a65011448101000d0203007400103113904a48005a500300f1071295108064400720a40324013070301640d00c503004043c410a0800e240c59203a00060b40e490801f01c5004003400b07401641345005081035040b0240807034025005090000d02d00c00040c0348100b4840c0313002c08141c0042400c0100b5a814007d0030010441005003443c4c40d03040d03 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 494568210 1250 494566960 494566967
    0xf0103020a021c03091e1e1a06060403050a0b0a0e0706140309030c0a060b01030b0d020d14030d02160c0f0b030a0506061e0a09090e030a0e0f0405040302070303081303 73
    0x2100019200c0484803a183c0e404501913084080301d15030000001c1c42c0510301c445010002081900265482100380c010610061242101469500d402a07040b0a452101c1c44000c41c500000800e00c4e078024409010010020310100503003113280f4400d009401d0249040d109810840c0d012000152442e84840010000035070840900d410000311410780503602d80ea0028036510b1485420942829846031903914000e11100b540032510990302641c05021882c080c03010010a1a541078002e94002a59054503000684000b83c464440c4e05000a480c00e180b24101b0358012604002070000b910441c20003007601b0044541714030f001500d0302200d01250542000100c0c0c025000050145411640d10070100e902a0b072507030180d62011015418503100c03400302c80808040341c1c102461400104548507000310300340f445806034074207401103003008608040e0060760031607000d07019030040c0390043c217a1600f0360151749031802003a10440c00b90b002001d40c07074a1481c000f0310f0143c0043c5110300c1070185881c0302000035030 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 494569460 1250 494568210 494568223
    0xb06030c070f060b12070815010b2205040617060f0405061602070302060301180f2906130f06110a03090608090c130f0b06040302060d09080d0c020a020f0103020a02 72
    0xc10502c07800340c0b0492850030100400303070003c181e83e01603072200040300400ba0020781101952541070948140c00824801418040c00c02c3c010002003040511100502020201c94150170030000510814126910710100d02102d0079a00844144801941115034200b410005107030440d004002e01c401511b403d0301c4240d218107014243c0810480c0b11079814040c140308002e440041d45d001018150b0300c0d41d561741e0348800d00e0301000700f20411500b044102a0245140d1040c4100707011035609419441d844498614240d2403c007880581c030410510100240300102000c4a014001c00e018021a036411f10b0b030068012003403c11341e1060b540c09000e544000030b600c2244182200d1031814901041d0b01c3c9d10070790303e04010b15444801d81010404403ca20161210f8000d1f100d2007420702020064400c5903420300c0058803503030001075003051040048098011b801e03070100c40c3c1c160041c10168107002c00755000d40301ba0380d5003203001801a4401c240e6803040d407400101030f860280090808518100c86140003030740b142c8 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 494570710 1250 494569460 494569463
    0x605130303080c07052a0f01170c1303110406080304060c12110a030c0209010f080a08030a060b0a030204050a12050624060d051602010228020705220b06030c07 70
    0x1c24440032070703c1010540191001294840281c031249420f809040b00c0821404c0c9201301205031032400c214840c108940200540c0780181d6441041c140c4001403196581800741c4441c2120908108620003129546200c00145128400d2544500c10160400060f203c0b10b8010305078513001004100102074019095001c45030b440803e1049031040301106032268210740f80e01174a14003d1140d680201544030700300c0c1c0c071218403c48028a507a621200d10064585850103005040e5010720f545101007517444001c2c640c000160200812415110010840d90390410106d01e00443c5d00800e09111030b14141d05820003402401c87d0740007484216031a000e550f22009003206e0482485032070b200b444266982185010003a0240c4080e0765004041d0b401c070010a03041720034071502c004001514003001d1049c000c0782c0c068080d08030aa42090082c103091f0350017400c2509201c0c15407040400010760303a2240c0289a41d014801144128040c8640d05401c090302d04111019200f450100704004140008605861016 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 494571960 1250 494570710 494570717
    0x50307050d032a02151e0c0f12040c081f050a0504110607030e0411071109040c0e10150921020307060c0611070f1707030e060313120908070605130303 66
    0x509501a42003034185e120180004190350b0070030111034410011004000384c5006d900940303a40c3c90014018034007540012460081c0100300c4454800148860700380c00a0150100001c420707916480240352103c3c04980101c0131400e000e000c204c109507813003480c1d4070400f031000a1200d8a0310741d440280c44021503070400c0c40340b00003040340700902d4880c01c0e042e00c007210040d00c10086004115600701064001603021903141d05d0314100e8074814205031516034040d59010280c0c400781400c0c0440742a842c0d03801400311061034401d290005038044285c2c612600940c4c20349030507401d00d040a440704507102c107203609034005004401080c0010b03140001c1d4041101c10030319006054100c1442c0c0380000d40706008881c88041030105803c018005901c040000c610310501510070b0100c60307850402071078090719902802044503401010034130304080008541c0080b15026400705060301d980c81c844801c2c420114a40000c40c0134005201e41c031402c128500141c1940d0400d00c1c20948544100e041a40341408002c040 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 494573210 1250 494571960 494572031
    0x80a08070807150c1808070e0c090112020f131707210c0e0915010e0a02090f060309061503030c1c030b030319030605040b030c01031512050307050d03 66
    0x280181c5410086090243c1c000a109140c01c00c030b4000c000c0702500700d003104003480c030340e0300010403810014503802100c075103528001d00c942c2d03250745410541d080143c2a40c1844140111080e9490311440240020014803e606499030007001c64202c0a09554100002e070544590b602ca1780b09a002807158201ca92500b0001e1401c24844010102d10307861240080400402c40d030007165146c12068018400e21341d901c100c81c001c1805144c8400390130000e11442c680074003602d000c540142801d40091046010180468038050300010100c0e440303610031100142290040001d001001a410125200092003100254100011020059107482891090b02108206049c0828480d40250032949014100405882c1c448460b480200320215441070701c0c000207071900d01c01003400c1ca05846605142c40010f0000d12922070040019030040c11180c074411045141d0b00303400202c102c140d0350500c010a20a201954070f0780324500e0851300d414404414001410705107003900103080d80b482d203264036a46a40405490 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 494574460 1250 494573210 494573213
    0x1030501050a021c0b031603030305040b0c040605040608060102070f030b090c03030901050a0c0c03020406081b0102010c0c06051b04140f03150c1e0f03150d17070809060a020c030601080a08070807 86
    0x103056900034407030005a00c01f08000052541603440240b0039800307100705015a0b59180d4480c0603078030980c00b035140403650a00c028045140704034201584000180100c4440036182d803d04108410141d0048a02c1d00b148420010044001d225035440ca4405800540c145007010001901070700981a0300820002c8240c0510144128401f42c00011034014008014140d00e8058603519010152642180424901040c441d59481441415240c00300d6607107591166040d40d030386a001d0f10001d000950107140400004003441031000040008009500c20f109041410000b4401441001844144260000c9480d108080b42c0c1400040e404101c4a43e0300356910450801c542502c1074260403241262800b181240c01e40001e00002c50003103001181812605c1c09800410050a86400c0001c041402125000b0807032035500000d441454801d60340d4608007030528000c10031075085413410704010b91000c03428103054101030002030702500620f000b40403450503540f0354103594072030300c90001d243d100b00046100 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 494575710 1250 494574460 494574463
    0x50c0f01151806030c150e04092102150c030916090c0e041e02031b0c1501090e0d0e01110a0b040b16090e150d0c030507060f0801050d1a01030b01030501050a021c0b03 73
    0x441c1d40d1f0010420045400d20742407102540000598200030402103422580c01140000341984803da03200128180d0740e6164200904030383c101030000740ca60320500d0a078441c90104000c04501810407900009090300c00c0f10700003040010030040803030007039151118000900075584000380200400d80d00169aa440b005d928042d1016245915140340c000850051558600070820703d595104a8400b80355598a07500204122091384032201c146503c44007030809110b01504044a2802c0141014421346840401740343c144415003004641100d0303800100010002040205900440701401200340e100321122b010f402c0e540c25001f00c5680303051f50000541900a01161035005c1607002d042040034003041c0c41c0442c2d07440614002103409008000000c6852072003401402564400399461900607445d11060083d40072400b0410384503030b800100100c03a00b80f0101b0540c1c0c000d5200f204401d030310350f16500305603084480c054040405240100f0480011f9143d01201046038040b0f80c40c00600d0310144c3c6c0c00079 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 494576960 1250 494575710 494575727
    0x910030c0b090a090209030d0e011206060e030d0207030507030b06040902040e010e12031b130905010f061d01080f090a05060a0b1e010906050c0f01151806030c15 71
    0x40c1444294000818800e91103805484100e00c26250352030fa540e100c0760103100ba0f0041300c190a815500c1900846d000314890107030b1b00c02e810f1060618a1003040c14084460684020380c01407400318041c4003005029003007c100440c001d003038902c080c14202d07040d9515039032034220512001c0c10522501c40883c1e8503580e079030702a02c5200d41c020410404401e481941d01d02a00301208023486500600b4111810340f1380341c0c0c0c12280709507503140c0034480541ca810307050845a0010071048004044500d808184280342d8815140a01403659080c45490f14000f0001d0035544440e88155100403103081940042c2d0700902d0603508000940806901ca0341e5840e030035483e011400101400c81c0c0f00e00d005205c3e5801d0680c0c841e14400f5030549800c3e4004000c0c0364110303d0200307240b6885000810358071080001901c150007078030303a8a0042040e101540071254100f03083d03c1e51700c4500740340c018400030301b04608644a4402c1d204100117600900c030003491900da49003203003031070301c1032860301e140346242d044025100b000729 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 494578210 1250 494576960 494576963
    0x30b04031d0406030b010e0609060901050d080f07050a140703030801121a071224031704030f12030501090e071e0f090b0f2e03090f05060f010f0311091003 68
    0x20054944c0da81000030505900b8400d0a40049042c0007045550400314883c9208581c00303000100f80da4030b88000d0140321240c60303006580d0090148494210441c2982c01080ea881c0100000c282998560500396204401852a00307151b9101600800c0042d8011003003c2c110341030380030405004842d5080c0b00158040300c40f102048000c811080181e095042890303040d03c2880c690701045480640c801f10761840b2039012102d1805240030000b000015280105030b0001c02111081e182070994941d2400c4d000042c406044034602d0301c0c41c00354413010b903141c410b0714010171540000b44030021007403021903211400350003400c14194501d5103160140304140d189000401c05200c040c4001079586030742c44018410700803480d10030384207007000c08418a010f03401d6616200c0c18100c6000f000721011400068002440612000d06480d0b4082101040c02407644004182c01400984924540a0780c2d440c0c0310541600522601c01c1d0303508050004c6401240c3d40d429400301914528990388072200002c00b5004107910 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 494579460 1250 494578210 494578219
    0x60a150302040f0e06070f08011505160606031514060f0102161202030d031e050411060c010c0324090e070506030c040801060b0f090607060f05070203070219030b04031d 74
    0x103072814a03d91a512001040350050259845078461980c12107268545200700300004042d071005010a0b00001c01602d900d800e035042140c07030200c40c0d00b00c11140000304602034601c20380d56a820428464504a00f03022080c042002308580c0443c03850a000c41d180c0039102c64040c141044210486034004c00065400501c02c0000c120034540d51100a0070001561348101e0103030145c1403c4a8445029000384040e180901407103058001107407120500800c4010401e40310b030901340e010581c81352100d800a0a4000814001052000c0c4403070b0098151904c0009000010082410384003009141c00b05200c25298854400718a080200c60024030f04202600803940c400800018400c0310384280c4020700032503104400a20900c0d517141031507610350040120021101d40c082051701e0130341c075120307004000d4988078590000307080000a0030b0744200c0e5012180000940d100284407415464086034500a100b0702003000350301b9a044d5546c5224080000d000282840350103840803200c0300c0014071000c04c0103009071 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 494580710 1250 494579460 494579471
    0xd060506030f1e120c030319140a0c03150501200f0d0c03110f030706020703110d030506041802150a0207080a0309060e0102010513020f04020412060203100b0c060a15030204 76
    0x1003030641c0b8600b0f24101d524a1140b00120708104103158150780342c003490f00300554115994a2035040a00c40a41e0780e2030610ba40e1000600241605021010300440364000000b81400240c0300160403164005c00c00144151a603208002d160f83c00350490024004032036950340d111040d100c0280c40d20a149105c0602ca000e03802078500c80136405800340301c0c103c0c00b0350f072044d054510350740f8499110b6031110307400c0740c040d00100110170210b00135400800078a40b191030011482043c1e240000c0c01e00780c0c2c0c1070344000040e40f01c07030610419207414003c03064058000c01c5040348450307050b400a050704540e00e003582c680c08004103000c0c2c8a94002c0c0110301c0204490400c1e078900c0310b190b1400038884042c6000d050003080c486035804009520520500341b1407031040403000c10000c010380030803801001d4521441d82c0305800b008041840c0500c80700031040c00e03205403005030301c81c2462803d0b40da003a941604000071a42e03007803142c42c0c1e16000000320b954021680040024000302405511603800e031a60304003070b4203d410035 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 494581960 1250 494580710 494580733
    0x204120f05010c09030c03030c0201051b060403090b0a0801120f080c010e060a0603050a02010309080423030c0904021318060c080906070230190503011d0103020d060506030f 76
    0xc8911040d034a10450007001099070401c42a039030440f1134000600001da2421003400001c0c00742001c3c04100e401410400e09010407107019010300074107070802410031b07084038043c0000c254201d0b008401402408040500f800c1281c40000e000c60414403801150303040ca0310303000041c4181c0180082046400c0400580c3d1255401c09641c0a8a14800104100e1080000040144006101d110242d030307401409414142000c0d0011400340c80700407411b44180c4400c200018030184096a183d44100340c11003c0d150502e025010542001000004079004800f01000c0100507544c40000751035000d06170700b001440d07080580811901d202d9074100100700c1c0b403030002c8a001003600810304911423140c04044400680e290402240c86114211803005262400000303050954821040301660074040001c003800e04540d019404004802044448040703440000184141c0e2400e20b00e80390004501d400c908015450340d40829182c901600c0c02504081e900c00100b0341700e0f5014000f407600010818201d8007500e07440c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 494583210 1250 494581960 494581973
    0x708030420040207150f150f0602060a0e06040f1a0c0415022b271a131505130305010506040b150301060c0f060c030507080601021f020d020412 63
    0x11140112185900401e1140d034a400c1c02142e1003143d0002907041310508070740c00c80029001d08145001c0a64880c840404504041e0324103800901400360000c0c0d180b4900351000c0d040001c09414901d080c0e0808251804840000130491f07041644039a030f81154240038100250018240244201400b04000034800749018260240003a075090710150540400040e005a9a8000189917400d2001165900c009200f0100307481c40c0001003107040c0813550310700c5007c055802042c00c61130304015000d503000c103000b11060201140c0d180d140d400041860414101c24021051f805445107200e084411340d6402e80705032080098542e98400f1803100043c564891500074040e00c001c0b81d01c1c900803441c0520a5900c0d02d051310316101202d03d04515540703540d00f40345003104e82c006094400c0e0384c20b220508000780082c89601c10300e00c41d041191b03000038030f5050041c401008640c0180040741103600c07030381000d400f64000304681c0c030054600140041c1e40701c02405548000e40600d901108502c0400c040c40d1080c010b4 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 494584460 1250 494583210 494583233
    0x50409020a020703110306070c17071e0c05090f010b031801091104051609050f04060b0a120507050c060a150b130f060513060f0c02041a010e090903160807080304 71
    0x2c5184185d0a006501c8189a5143c20450fa1b101c00507555000320004101004800c814502c00c810320107291940d81c1d200c40e80400c1c204104143c841100003d0f010501c440e41d40564098402150441440e00b0002d095401a13101030050032203060340000031403c0c210096100340c80f003544810003072050071114141004050b20402e12540513500700030000b45185000301155101c030480d52650303444d450a040c04d00141e052900c0300c50307811a68402c0e020030940801000f40c440d1100d1652180850028074060f401071701c20241950050010a1060148010700490002e034450030208000982601100100000c2d0b12540d1110030001800030310040c442e03160000c0702007611130001c80000c1c0c141e0388410840c0c0c2442805030031041c000740302e402403105506c249500c21201c8034900d0111240d4140c0d8001074104c0da400b490341844620b2604100e4003a58001c0d90111030014201c8401141d4075101c01016182d21812400424030100b01d509402040104000d480361180c024090607140d00d46850940c80560 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 494585710 1250 494584460 494584463
    0xa0311151e0c03010510050c07121b0e1303050702010201150f030b01080604021f0302360d080a0e01170f1f0317030c1b011a040e0604020f01050409020a020703 70
    0x4041c200040c55101e81c03481124100d80e406401005600c40e981c00c01c40f81508a0384158880740208000002d00000344420168210300440c01d020703040041000250910b5207951003806500c44113410014070f9041000701007085074160403d2039039078150707200403401011081154501c41005200209200c11142210002d4911445007040b851362a04a441e07614842110000e62120b84d0610a030135a1a501c0701c8030075507440b1418058146410000c29024810809900b1a1051980000626000034038805176071100c0e03040e11403241801d0b46803180001352044000c41400c0c4200000051005d91140c94a03c940c036018a940d9040d03400c05caa60b06110400544002c96509006200d4010032512403882008903503128426a070060110304c29516547c10040528059140c1481803440400c0e40d582260300d0032490702c0002500e403032030f02d000460030308501068034062894841c00014209001039655001601196904046200080100ca081c0302c0c0b90010109c0c10700224800441540005420003940d = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 494586960 1250 494585710 494585761
    0x106271e0602011404081b06010b070b150d061d06190507090e07081909060b040c090b040302060705010b100905011e02060a0b06090604270209030a031115 68
    0x300d0381c03100100d080c0c854510400c3c80b0361010b000402e00042c181c1d8014a130300701d18104c0c48000e81c40d03180300607420718600764440c15107c64000b80900c10002007a140c0b83e405075040302220358600d00c202c00300e441c0088540d00107201554801c824036070b89540c0702c1c58980c86190b600446800b841d14030781d02000a2407041c01c105440d401c00c0041105075001f001e1201c250b80400c000d401c1c0940e80c0480032610a800501a0070b86c2c0701c100c1107030f4201c2c1ea406001d296259402444082801001071017800100c40342c40c683e034008c21240700011301c4543c1c04002282c040380c1d012030b13105844107246c2c24000d0040c03284c00d032450351260551131040d0416400c03450b0401201e600343c070350a4034800d0713a91001050b0071117240c100006821060008040000640c412101c5840242c038407401c112141003c1000b40c2d001e03070404038941c040150102d82c480680703075125003220704d40319056040c1141e030b0b0003107992040068001000d011041c19019510701042040d0080341d22a00320300c0300d03d42040a02d50465589001c5e070140c04 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 494588210 1250 494586960 494587019
    0xb1c060510050405191505030709030b0703020a180503030403030507060f020310030b0c0909160e0a090f0f0b091314060c0c06060f0a0b16050f01050709080a0308010627 74
    0x7a4035291528404030364003201b055480c000301744000c6580b540024009c0d01800903504010020461201c2007034031a5005440050b40c40d602080301610b12840c141896003200b18140e001c0c400b548001c02602c040360f9050402ca6203444052814401134042007150741003d52020040100040d003504118007224003c82512350305031035041500105200c1c0c840e0003508000c2150100c6d522001160001225409503d071004204100d1000280109206d034406100c00707032295100190310480d4480d00d200b80400d20410006040008045055103000402c510110150400390b04180300003907015007040c5051005882c420720303201094100940050301188150722403c00020b90909003140c098051000c010460a6018503041c090341036540301075103c0203051414003055001580070000c0c01e108000c0040089000d140000000b07128101960060355182c0c0b02c001c0200104c0d070099074090540343e181c54246500b4500001341c0c1804040088454042d20f403440f00000d015010110001e4041441c0d890403d1 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 494589460 1250 494588210 494588239
    0x2010f0203131a120f010518012301090b040806071704051218032a0d030f030b01050c0d092103080f040c030f0b0a11040b1c060510050405 61
    0x2680d014000b00b50854400700b110a0143c81c0920142c10791401018031254039101803200c881000720820f8074074141040400005101c64504030403040c03240071103030354008010743c50180c07603010328070120750800900c220000f40040d00d07900c200144d070301410310014000d40d690340c0c4d4204655a010102d900070001034146103846e0745407a0701000c4500070380e04407006166030800300f01c5002855106003c0f54024025550201099440c24002403401c2402005d12603e1070b840444030540c02086801818410309500d50814002604034681c1980d42c00c42e45000241d59002c100142e03800d202d91024189240705030203580701102e512401c86000d4810003801150b00d444160054180d0803101e07600203000c00c0d0403400050390305082040c1107600c14096200180019078945a409400d10810000e440780304080301000520081801240c0d1703d6000c2c14280340c9050f140000c8024240101d600c95400155604020140c09035540c101c0405840000c001070880345800720003514503480b40c031410f80121800d21480070b = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 494590710 1250 494589460 494589463
    0x1090b13090c030c170c1b06090d02010e03030f0705040e09031c11070206131d0702160509040311010f0c0302070c05060903070e040807121d0f060a03020d0e030309070302010f02 78
    0x1044c0c45001d4541a141e401d00564843c002200100080d1991009001084804803000102e0700d001e00345501910399030425100081c102004814a0015a070520b044503462000000440b9130003806828000f03182e07110b007042100d1038880c0f9813003007280b038101e07406012050300301000420702880b259070541c500038105840501070b1240d01c070410303080c003805000d0360300907040100040901d505941070701500540c40d507066102403034192001c504020480760410200607010000e65035542c008504800400749004006034071454020700003400c00450b48040459a00300750031100c0074815440040c400c404904030010000d400041040e14940c016180003d100d0070218101c442c0544040c4c054030460b8140901d40c4030a9001820803038101e0b030f04200d84c00102d041d803125410100036640c1c4042060020480d02d60b1610300c600800c1e8820000b54100e0381823551781c0e81c1181d00510342400c0150312040980100740003084600d014441c9400300108204003190007240200503203200342c80700e001c0a6603403071049 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 494591960 1250 494590710 494590721
    0xc171213080a1b1205030906070504080714120d0206070927021b060a0504060f021201063605040522032a030305100503030f03040b0601090b13090c03 66
    0x1524030314080101e01c11441c850700c101c000f10898440d54100072091aa1648950320006682100145010040c000c00340c00074421107812080320302e001030a25040c001d1a61f01ca0809224030203400c0e0341000f0a28040d103942c030092000036841c00540720351002002c00030391500e0003164000001065210b0105031008091040c190840340081c0b012000c030f440c04050300081d404a2042601040e18200721001c4110030043c4510070002c94102154905103450640d054035041450f100034140140480d420b50410590554111102441c1c0f00e000d0750250300107039a18595008201c100403044130a1078040600705961071044071803c0e6410080340e602c1d08000100b48611607c2160500c01010b03070340c00881d220314200035003032082500007051040e450404a60994555000301d02098507801000310001c4010003d0303000b88801c1d0051490300c2446e01c85a40288002400103140c3c450700c01c00b05d1341c140d202b03142c01e0001d0114174601c250781d032030614a40d908081346485103500e080c2c141000f482e415403090081 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 494593210 1250 494591960 494591963
    0xb090f070611060417120405010b09070c1e03050c01060e010312110703141005010602010b030d050a020a06050a020f03090f0c030c0a0312030b1003020a170f160c171213 74
    0x1a103c1611995107282e0000b0302c26441040008081c000c0403d46298405640e014902c00d800004000c1495014050071305002030514007413181d0202d103a00402c0c9202d41c1d41c80d00d14001b85e000c640c0843c0c54942680c15000303241d440071040d840c228001c1810000c0e210801d069174043c41400c10030206400702121021303441105003c1a41001c802000003604410910006001c084280c1d01030859411178031044400c00d174450030050f91284040801400c003403000c5071000c0024035009180c054841800b07580d801c544d0400070300540d901c800151004040e941502d0304d031050300a00300c2d075a080c0302003955034500e580d41c03640300c4900440c000403a4a1400040c200108070000d80505001c42c610744851010f02c0301781c40140c041c1a120400f800c02e41d550808101124451074600585078445160000d002a08410141300c2041d042c0c000e01080c42c07420004c19502c080540d54483e03100b03032225411250100e020303c008012180580f8901080c1c00b03003401401030107240d0300001c07000d03903034501e400325003081010700 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 494594460 1250 494593210 494593213
    0x40605040207021c291906060e12030904022a0a170313020306041b060e030703020d03120507090e0f1501032d14060303030408040b090a030b090f070611 67
    0x1016503c010040301115900e014040240300c440c18a400c5e6289100000240200003520004000c40d003a10501d61020b030200100c0c0c03c01020341003000c040c240c01c0d85482120710078040e400100004040400850b141000043d00c00d43d11212a180e074200c100003d182050003c103c40400109500d00000d0a00700030390308070001d24080c2000004e1390842d6440074007585c40700001201e1020140c0c03000c20542d80600e00c00c0c0e8107100080750b20101c0061400b5142c10034010028103203501d5072140d8001a084d0240d0341c0441e44404840301c00d00e401d440142d20020201c440318106403c03c07050b2a040b1220b007003140c82440030407003181c0c0d4400aa0852140403030b48181c4200c9100c0c034404655102e07501503014030809100da00840c1346000545002250807404001e110781d2509400481e0343c002c6008150000800e400440c00c50a050b0364440c2c0300d00071405103590242000c2050912552680c440800850b0810f100d5a007a0034000e55050704c0b9001d000403908a8401c0c0a000907500c0d10444400100003003860 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 494595710 1250 494594460 494594479
    0x51002070b07030c06140a0506030d08010b030604060f0b0d18080703030509030c070b21010b04030312020909010b0705060f070e040504020604260111070308010e060a210204060504020702 82
    0x1014403002d40109009804015202c000c2d400000e00e5441100b402c05000c0d00220071614040201c10265000101554041c2c1c010600b1410002d0300900b0070f40c151224103442a4603980ca20020800400d45584122554240c5040c0050044400300c018111a08507540500c00c1508944004405010b1800c0003418581300700301e0000400c1c803e82c400c642004c2d0304000c0d00e240c4014000024940b0700190003003401c100700003a25138001100150403100c42c07001003440580c0c9600d001c01241d1540114400941400a410b0004035500381d6581190b802d02001449020656105c00000307001d608458800c80340d510030300780070880c03600c21840f0701c9120f07108954402c40d0684001052001410000d48203d0700002c081c00b02150125089428003007190000030341300c071304009000e902030944802c9004d800170004200102c1d0040380d4400b00141c1542c1080280c207095031a0740c2c2c0856810354190388410712041c190014288074a0409503000400e90013100c080c00459242e03002c000492080441c0290f1186020 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 494596960 1250 494595710 494595719
    0x60e030318100c4115070c02100e10020609070909080705010c03091a13020108040203161502070b18121e060714030f0406180c08061005100207 63
    0xa09280450b241601c1c0030000100c09075036180c00c00101d1001c540c1d920400d00310000990029040d02e4100c4c0044524040c1d10540702e01113142c07110480002e6801d01ca011000281c00c03103002e1400908201d5011b0b0505402c0108460028441d5034084003e0380f00da070302d4105062000e880064081d0240d000035000e030a030309241002c06801480c1c280c4007282e85031014404078012070320030301c210440602c164a011a0b0840e01d49850300012100325112124203000605000441825900004156074203082c06240341d15140002413900c4088140c00714201031000c80420395000204071018022026000c4071f4005446a060440f28000c0e901407140c0300c015a0b144020a19000682c0c214101401096410034030a002040e002e010388003041c400190320503814054140c0d070101424401c0c1001c0b03034000741903041c480c0e00400c0d0440b0141000e07240741c2e101c1961031070b1842c03420b00d10740c0060b40c001e4400211550f070313406a03500d40c00c04807a00c141202080b100083c0609080c240740c4060f141d190702070513a05040 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 494598210 1250 494596960 494596969
    0x1b080a1e080c0a09080f010209010f1103030103020d020a0905071206060c03171b03070c0b01050607112116030209060a0e010306020a0201020d0216061d0309040e120a0801060e030318 80
    0x211040303104200d044c402c00190154280151440f032040c41c800980c2c1c9100c45000074220b15103038802c1c4810403940000307817242e20b58044107030703811749504503504c2080101500008903200d02c1a00f041000501d00420700944580045608542480034503051020366aa4102558080c4a03100040c0108104809142590702c01041c1e16600018440d20412914041c103904041500708440103808a000c0301c0e00d050601c0700c001d00060041108480103841c02c056541c1c0c41c2951103001401078002c7c80303e8000f608000c00a40c2642e1610b4019404480d6849100404e010000c405880248c5c0035003c40d50204001f424600300d100c06480c00c510082486902e1a0f850320300943c4901103180440d5800d008030035818140740010402041d42215840c034119003804c01404984102c0904007248508400d00c0c1c603207d8010040c2c3d691007104a40000309022400344040c00c0800c155050a0b0940300025600749994010b50468161082355039400e1641620405046d583e10640e000d03001900890548010146807 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 494599460 1250 494598210 494598217
    0x109140a05040e330a0c05180109030210120b060304030e121203040f0b07390b040c06170603030909070512040803061c020a050d02011b080a1e080c 65
    0x8050048030025040710407008138400c0070000948100402401c10752854090402440c1c00c84c45c03003e01003080c428840c002070207601c61009114841c404241403000d1982c060164540196009417186003808003400c4014500e49011240e034000510f006a0070300700d820401c0c2a241318552584519001300d2101c010008101a62004000c0c10300c070341030640091400a03409075001e54880d06045955600300d103800c2c000d1003401424101040240f200480329080300652040c0d0600c01b02488004861006020b402c1201c070380100906841042001e0104011884408504558040e5103168a0002d91048500d00c0c1e241174802691551091010b011140340641200d900b003146802c0c000e1074103030030ba00609884102107406903102c9101104001d0a414040300c20120030803803d50301c42e604501c540c00991121140d0160600841078030180c8011a409210b20b20030744d202580a528400c401d504d80910b0542c4a1a89080014080307506410b45050001c0c2c1060907001c1602d032401e2590350701c419400d9540 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 494600710 1250 494599460 494599481
    0x5150c0c01020c060a0f050412260c04060e06040e0a050604020705060f070f020c03100b0a180506010e06071e030201020f211806010e04030e10020c0109140a0504 71
    0x20800800c000caa03000d2008204807a481405403416103400c00c42c400455010305084400103040000300b100003100a9403049102e6100e080441d8070b1204941c5c41c1254525400d81c0b00341c050721702810300c45214004400b510403184a42d0311060702c051036405200490003244144080400440040f4440e01c0a42c0c008560000f40a407005060800b01d40381d1500d07002c3d064410300345481c000010310240070b41c4000b010310000311900041c60384d4410390002c03030350b04e00c0708110f40740820740e58290b0f03004555076034407000c002001015101c2d01d040e981c091207500280015124a0301207280407002650a061141c207480c0296044540744803690a071a20300203000c0d54000c0d00b2011550308100740101002e12401074145000e401364420801018155001e040400c0034000f039410805c6500c00f0708041000080b258191a20b685010341140c546e840c1c151400d0410044080d0b1103e003c804c843c070140c3d030010706600c6a5009a0310034480b03d0ba5000c03d070001c4400300021a400c43c00400d414040d50a10703420406280 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 494601960 1250 494600710 494600731
    0xc02060103150f09061d0d020c010e0301090c060f090806010609090911060309030d0b12032703060c030a1a0108421201270311010608010e011103040515 67
    0x31200010300030100d551041c01110f40c15510b11400e02c00350180d46c880e40880d030341c00000300541c401440c0c02170f40d1005840304c0035040080710400d060054800f0b4001e00c00b640d0780040004070540d00c8000c041e19006820a42c0000540c1008000500190019215049a180392a51459079040884200c042c05842d2426034003031600d001005100d44501006511985284c0055500e9030558550380003950011084a8030070800d110361828200030100440308045286d080c1042c40085d10905444017080810a440c0d05001d000104161901060000d42c400d034100c441c2000130300801d0a144800002c1c411900e400120348500203008100c034107603c0b0050a50280c034290310442004e10072112107400c2c40702040e4001c0c40444001c45403c11041c481c840c411170301c0c021b000080101502d94040131108070080ca00c00e81103170b0200281341c05425510007a0088000902210340c89a4101b4040e21007610640d0040d0711300107541d41c00b400c2c24000d4030b000e80d0780000034007a482c8200c500075584020181500510 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 494603210 1250 494601960 494601971
    0x604030e2b080a110a03020709060b0405130b0102120d0203220515070e04090c0e07112e0f0905060915061306080a110a120201051605030417060108060a0c0206010315 73
    0x40813402c20560103454400d600521300907040911501c1611100d078020b1009180901043c0710070f56034042030110000d10745000052a44180c00100d18000030420a40710b00d80000512004070f201940085124070b4080200f808501000e000242e0700781a40d030030103019504003503030203c0c40e46030303025540303802c01903a140812490001c10002000c8070400c25080b41c0f09051050100100c0c0903031441c40358000007509140b00e002992025981c0c43d4000010b0f90451b40e030310700c280c003000040d40000380e2010f0424840108580c152242040008200e01c1071b041d14113104260018070010400074180e440000a142203117059110241802880c04007103110790a80e0b0b4940c100030942c00c1d030800181d03500d94002e89020a04c5220942403280c501c02039003101d000e0154800702500581d8002c02141c100d40a88d507040d02c580802814840e0460145805c890449a010500c46110400015209050f1084441502d42c0b90703e0740a108022103480254580c05604081c0040001c07410800180d50740000402c5c0200f507 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 494604316 1106 494603210 494603237
    0xd03020304090902030106030f050a02040b040e07120213020f04060807090f0b0307110d02150916150201060306020a0f17060307170106080604030e2b080a 68
    0xd080b07850f0040d0004644007580b1042c011500040c0401c00043c4a19049403126200d50b03042e4030a5080620324400e40c5018810310b410545618002e000041c94004800c001c06003501c01079a008605606a4138103811500040c60020b000c2c08045995034180a40604100b2000c3d1000c0c0070403170800403d010349039001c4156000d42d021805a9502d03030381d0b10702c4121158407802003581d5a80c007030180070200c141c2e000a00f0311301c0301c00301801080d040d03901d45041030307903a443d003840d00c058001c0096410007039450b02c480440380c0e58a0910000c10280d49279241d10003640d100d404030b00c002560b81110883d543d64080284113692000c00d04018440c201440000d944001c3c0d80150540720180b0040400454000d501c080001e1082900340c864a1400d030a01500080c4102c1c440e03030259500c0541030719000380e140c91104004940e404000e08140c007549a144094010020801c00c1c0100001a4003 = true := by decide +kernel

theorem cover : BRFrame.Cov 494424460 494604316 := by
  have h0 := BRFrame.cov_init 494424460
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494424460 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494424460 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494424460 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494424460 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494424460 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494424460 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494424460 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494424460 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494424460 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494424460 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494424460 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494424460 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494424460 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494424460 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494424460 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494424460 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494424460 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494424460 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494424460 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494424460 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494424460 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494424460 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494424460 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494424460 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494424460 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494424460 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494424460 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494424460 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494424460 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494424460 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494424460 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494424460 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494424460 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494424460 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494424460 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494424460 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494424460 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494424460 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494424460 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494424460 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494424460 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494424460 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494424460 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494424460 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494424460 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494424460 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494424460 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494424460 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494424460 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494424460 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494424460 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494424460 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494424460 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494424460 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494424460 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494424460 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494424460 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494424460 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494424460 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494424460 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494424460 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494424460 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494424460 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494424460 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494424460 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494424460 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494424460 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494424460 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494424460 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494424460 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494424460 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494424460 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494424460 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494424460 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494424460 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494424460 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494424460 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494424460 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494424460 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494424460 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494424460 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494424460 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494424460 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494424460 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494424460 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494424460 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494424460 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494424460 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494424460 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494424460 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494424460 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494424460 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494424460 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494424460 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494424460 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494424460 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494424460 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494424460 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494424460 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494424460 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494424460 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494424460 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494424460 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494424460 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494424460 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494424460 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494424460 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494424460 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494424460 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494424460 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494424460 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494424460 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494424460 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494424460 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494424460 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494424460 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494424460 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494424460 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494424460 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494424460 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494424460 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494424460 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494424460 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494424460 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494424460 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494424460 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494424460 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494424460 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494424460 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494424460 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494424460 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494424460 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494424460 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494424460 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494424460 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494424460 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494424460 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494424460 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494424460 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494424460 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494424460 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494424460 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494424460 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494424460 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 494424460 ≤ n) (h2 : n < 494604316) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
