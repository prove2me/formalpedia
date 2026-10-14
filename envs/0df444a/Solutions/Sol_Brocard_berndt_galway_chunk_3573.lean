-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3573
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:03:19.650605+00:00
-- url     : https://prove2.me/submissions/5c54d07d-35ca-4440-a76f-066c02f39034

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 642446043 ≤ n < 642625899 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 642447293 1250 642446043 642446071
    0x110108061008010e0606071a070f051602040216020612040b0703141824010f0501020c09040b0c090409030203131a0a0c06060905091614010c0b07120f0b09 68
    0x310302d03400403085046442c0c403608900e068907400d020680301c0c4100407000d0510324403040c41c03241b0350000d030015501401280c0d551004901d1038010480700c60040854084240a42084010241c5019000380280d074400c1e0900491440c1d0650004030168442c2024404103e8880c0410051140c8441d4031a40034031725060500191413005c00700c8800701c0c0010b2050b010005401d44c02c041c841000c0100103a0442e4a00c2c041001701d985414504452109204640603920740b20b0000c074165101040e241000c8d03802400780540c6855598038000385040050500c085c6070300600038107403640c3d12400780c0210103019801031640c0b0540c0d9150b080542425822100380465420381161a03190100110b5001c4101c0d031412486441c283e00d000c50203481140d0291001b603007032006100c0d542c40b010074001d410011243c003181407141d0310311807550544401c540140c04100030000c10004201c85500c1c959115100b89071a0012982c810060000c031041c0300c260010441d41d030048400d050170401656508980f12180280c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 642448543 1250 642447293 642447319
    0x1903080a05060f061b01140109090c091407080403030b220e0a0818030a17131e050103020702060c060106110c18072304030803150919050c041211010806 67
    0xc04d2807156000c61500329586003001c0c00d855100f9841541034140310450b03410f0a503541c00c60f140c064a8403040503582e801c0300d03000004040c2e18a1003417402c60040014000322690b2078000075140e2300c030018819000e144e19003170074070b000c0d039240f00308400850a00213140a01e0841c003225942143e024403442d09182d8040000072020854010a90b4551000d40c0e200180075080720000c28202142c0440c0200301e5604403981c5148982c440d00900f0592010428034020aa59880044000141c001518850001c00002030010303510a4004201d00ba001511092521034021252440c0c80026804500007940c050302400b4030040c144248009807608607040e11451b5000131000b00c80303200241c40413090110080e141e00090041400c0015450301113070130b003a00d5940d03c0c2020000b607402140c3da4201c8003441e201950280c03400200050040040c1045c01c1d452003074500540008180140444c50543c1081c0000982c07072100d2410580d1461154443c0003032030940c2d400142a545016040301d200e207803500164 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 642449793 1250 642448543 642448549
    0x19050705060411130e06072a0b040c08030307020f0d1d120a0f05030a08010e130204090804180204050a052b060219031b020d020a0308091903080a05060f 67
    0x81d03000b9070004005112208200005084c200401586252060400600f5480d0100101e000d84c814a0709846102c003095140140040106151428101a0711201c40180108040040455205124044c0101055203804c00e9900d142c0040301d03c800184c0c42441603041015090014041c00c043c41c0c01d00850001c6414401c048007844210210b01651851241c0d1115903c10000d022030345821441c100c041d0411070811a4480c1e000e000b481d40410b0781e2034000501a45102c0395284030b103068120503440b10310740341d0800c00500149082136130300c001b0502002c03c0c1241040405440f0082841f801a51a4130704401d1001c0658680c1c0101d2054222001900c0504100041507005a001d00b8180200e9200e44c85c0100080c000c8178040c40c1b00c2901441094407042d00f40e4449680210031071100c04400711554000c0340c2d01c810f81051040182c00c48104140080e0003000741076048a00e41d415a8003880c2d00038200e404058004c074007a03000a180406026141e4068031459400010070346d01148200150b0004c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 642451043 1250 642449793 642449803
    0xd032a05010c093026031e1005100903060c3c230a05040e180d201203010e0711070e0702010b09040b01140904050601150207030503030a0219050705 65
    0x3100205025403034101007045140d060b030707080c02c245e06441164600391101c0c0170f19040e04203d038074030402551400803206454000001602c50103107900c80724595402e2005008891000394184014482044000701c0000d515000703003940c0300107607540c58440d01d079080540e003246000c030100245034055903540e80c43c151803100310500041c40b0a0410050070030b2550382444601440500b05810740d08045a4032124aa112008100f02c03501c0e028036800588030f013800c1710310341c220300d00c1e000285500003804210247d0192945182085240001c00000c0d0000c101490034100c40c071007140c0c40024008018042a40503921700f0340c00c513585107040f50344c24244801c00d99880c0b03032600805195065040c00954014800d4201c141102c1e000b0300403104906084c504120080350a000d209007000e4032010f040c01c01c2c140300198501c500c0c0c11000070f0410380d10b0040b019925011610440046000c1d4240103c0461800c02c0158003d1030007443c010b80c0c2d0030742240d10540c42d00003600c6400070410304001c5d0b00041400094 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 642452293 1250 642451043 642451109
    0x60c300f0e06010537060f050909041e0c090902030105090d0504091d0d0e0a090b0612060a08030703050304021807200309030d03020403061503020d032a05010c09 71
    0x2020846145e0210f5100c0405107600c011107040030074402082030b929803010041c01114050748428200442034030060342e25004141000f40c00001c0031000401080742c42d59460052000241e182e8002c01c41515078070880c10712a00040d501c00e80320082d08046040900c9030310380c4042c1800c094843c80c1804400103246208500c5841c000d20740b10b040e410b4003040e00d502c001e00c02c4110b541c1100c241c0701c00404044d001c8202c1210180c46220300344130000381d05ca10b42c050030100000041c10035181458040c14900203440c00741c2201c2e003021000e1004110f03900700300000c00d5402c1c040d8449544030f04c0c0900c10040a0016500f01030303510900720081c402981c0d0410086c01c990300010a0300207a80707400b50001c43c41c47c05101961a41407064a20400080e90141d0040095038050b500c1031180e448004000010181c02d8403000350001d2600d031000021031b2082d00442000c105440000c0c29042042010765010444000c090780e031031759641c2015800c180c202c00304200038108a4041103103000c20404600035404110 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 642453543 1250 642452293 642452299
    0x20405130b090f06030c040912030515030c061e0f190504180b010e0a09060807050915090c04090501031a071119050703060e0c01140702060304060c300f0e060105 71
    0x98003013061650284280700845001034404c00c0b0398071950801852040c45204d405001c00d02d07000c081250031001140141c200c0c0c0340540106012004502800182d42c0032020400e01d0b2800c001080d00740000e514000c1060540d1540c68649a0409040c8000d100a01e1440f00701131040401c01003081603e814020420541508000140c80e065000103035040041004480d911411500004c103e14105034041001c1d1507944003261034440d10380b005e2000d2100c0c280c406a03442d151002070b417100f0f072400d041da040c1e11190100b04035080039030740e00f404000d40340c00382c05c11180120a460014615000d0420b4a07500c1411407a0003c2000d00c1407400d1604c8020524082c5e901e1480305e500c8500340407007001030100465202c1420810340c10540300799901c034180c000410340090b0810725601e9120000310240c1d841260000c1041c1d1440d165559048014101c0441d501c0c14000c5c0308400f2483d28022880112007082a44040c55840f2201b050035822142c0d0201c003007100e5490030840d200d880600061241c1510419 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 642454793 1250 642453543 642453571
    0x302031005180607110708060f162309090601030c08010b1602090a1a1215221101140c0a060209030a0b0103062715050a180303020405130b09 62
    0x20712440b42d404150350007461074a201e42001d210486501c60603580a07506200d083e9007030340f91070781005510f40d0805d81d80a02d8071020000856101d44202d040020380303680c90300305802082901542540074100c00c28005000500115100210341040c0c00e15a521a100346400c1001e203028041c064043d442c1800fa080c0074040116880101c1c01c0528101080c3d80c3c2c004009103000d141c81c01440780038040004418003202e0013240207005c98280b18090015052441000e08060303c65503c83c001d0071040285450025407c111184c00354a1021180d00e032018048c40e038003442c209912001621111030040c0320443c0038410000481024004500400a180c0c00203000d60340c0c11003000002d243c00b090881c00b030044044000000f0812003d5441854020305903040043d11840c00c002c903581d50a84c01102070b111100b000640480250785074040c2e60b002814501c00a41d003143d07403800341900e8002140440c04641c2c001010b108615010b03250200903d0b200c00c003441050080703408901d0202d40500754240c05448 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 642456043 1250 642454793 642454801
    0x10060306090b0d0611040b0d020d0e010e15060117160806060f0403030e04020d0524010e0604060c0c0e10081002070206090d080d020d1406030a2307170303010303180302031005 77
    0x1020111401481e020300480d0329423090540040c000c0d48a00788030080c5900d031104030341809070b040c010f052a40c00040060184201764000341503250700010b08103810000c240c0c019043c680c0030001880e00403001012468080c0d6410300c005007603450050714007480342c0d00500c1000c15119806080b5000d4a6241c40c0045500030600f01040c0a07014055002e040141060104641600038086543c4503c240b5201284d120295000648034444d480051541240c4100130610440740600c2c1d03204c0500707215844034600c032556800d080840c100d06403800034840700342050803c0b001d841042040071010b502c4004519103009a80054128490200e08078058043c000c2c00c541404145020b5842404028900707542d129008400781c0000c1c0044000c00001c1c1c2c00f84c2005c0b54441c00c0c00124046480d502c5000507800b00440000d02d0b00350f0394140f00581d1503101b0014080780780c1c4416020881d054125000441d2254110328010f07082a0600314461003078400c1c044104096500041d8180400707003401d4000609441d = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 642457293 1250 642456043 642456071
    0x10501110106210c06051305061602120601090c0809060f06010908030a03020a082206110903164704210303060909052a030610060306090b0d06 63
    0x207140d806190000100d022007140180c07001190f00d20580702d04016200d19840748400c0e66207001d0706650b00010364211109002030b0070484001c0c0344401d000e14482c90078515550008a41100c20120000680c204800402002010340100c0308584014208890342e0b16007000320943d601c00007440411096140401b02e0050b90140602102412106064960761084480003402035031012070010005035a09001510f0600184400c0b2541c0ca0000407071159160030b0b8481c0d81c080e005003220713120302801c01c009805569400b0030280c50254206c400c950307001d52401d4001c2c0c89107080503035a03042054160b10307000302c0403500009015000d43c3c094400c12a034000e5885007180c901880c2c001c0c1c0380d401c9240c5045500d0038444607003c060184290360900019843e400301c20150b81c15000c2c002c100768001d0755552184264820381c81144050a1541c00ea00c080d8071002a240c500c003926200550582d076002400415030501845c0060029600148103900440f00892190146e1040103449581d5804400301107803 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 642458543 1250 642457293 642457301
    0x30d05070b250215010b0c2e091a01050405040c23040207060e0d02210f0d110406110309010f05090d061b030f06050d1e050312240303030105011101 65
    0x25020010040c2c40002402019555894211003640740f0814100001024241c800840d421200b0b210040c01402c28062314224114801c0c040103510001c0340011010044110b101d600d000394080c80940c100000700048160922106030446c50040d41480200008507914590744022204a10700b00403c01103c2c541000304400030004959000340001002d2042c0680ea41003601601c030f84106070b030341c9800380120076a9254070301c1e030800420502c40000480d80195010241140d0111582040d05c1c06e8220300310103085903070070031520030a01c01c040703000d20100354000500342401071000d000f545410050030001e44400b005404030820404002469150398a5441340d000340340381d000c0c20070702844402001030b45440b0141c4103844006483c040804601300028000ccd4400c4131009029410141c16940707030740c40c4080009000071602e400031541c1c4400500100003c1460241d40365610500341030006014240d170000b40c00300c042c00c0b544410241026a000f004a038110f800034280340354000141036085001d0 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 642459793 1250 642458543 642458581
    0xc0509060a05070506150108090a33020c01060e010f030803060d0609051c0e06270319051605030303101e1e0302090702030f03010504020a09180609050105030d05070b 73
    0x1809170005004041c00d50101c1d485a03c4826225007c40745d41e404503180d40c0f5060490302810781c1c0822500070b0b0790383c02130b021038020031011500100c6084c84400071910503a80410145076843c0c0d9212403c1249004048105024014883e112900180f03103071110306540c080506110300c615041d007010030070005598806950641d002c801d4400400400407036251b01401a500e04011411800301256940351420031110081000021800325008110311741818240040c40603401d0b104181554881c8000040b10070070b5984540c0050100c055034140011107241d0541c4810f000741c0c0f0600610030700080f00301020040d85c0141955900c07410f6941d4201c202c5111a6010711204403000809028200d80061030394180d13030086d90002a540c0303595408a0340e9200300301d940040c4000500040c0b0080c64550018040c0f001280391500c00e1680f41c404031f600460340740e44032486142e0340e4041003200f29140d00455004041c00c6000d0003c08800041c060301074420380c00002c001403a05400101c144030109030030300c81c3c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 642461043 1250 642459793 642459803
    0x706050f1309090506191e1d06040b090c0609060d05040309050409050304382113020f190e1906080a140703030f050310170709050603010c0509060a0507 67
    0xc02801420180d03100c82003a0761401501b11040c0e6980c8801c1c000e07025501c0c483d030012002d01c038807601180d01c2c003004010405241d0022400c451342c04040b024100906030249006079480d28a90805007604c030319080b008403105000d01420310820300142e4070241540c18001140c100891300f9601c510b4116240b0103a600041c1d442860050904240800040580203550349000b10f02100c0380d490200c444400144000c2c0c0088080c0c1040744600118030038080e0130202c0b090f0b0942c1542d5100600b00d10900308044078103030740c020001c04040c01540b808007115060050240d45207403031443c5030041e02208504500940810035514008280010401c24134010b0349031464200700021070700c0700180c3d038071b418201805480540c000307214480003003000b25040040f6603154541950030f03130403404152040d0304000e00040c0303420b481410001c1c800c0000e01569050402d2800a03007410342c2480500c10850300043d0010307000c2e80c5421038a0003181d800800302e86002c802254059150424030004036400d104100000b01 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 642462293 1250 642461043 642461051
    0x180f01060e1f18050406092004050a06050f13060c12090303080606070206070b270d05031303020a020307080303061311030a0e0703051902130e1f15030c170706050f1309 74
    0x18040000350700013200c0c00302e10740004046048c0500b041116008038010281c0c0080c1c01c08040285900600061140d00f500c80c0040d8200200d0302c1c4107170002c5800383e010001103080754032200d003040200c05a0512a60407810305040d040d0a40e10300920f88031004240310b028500000d414010341d41c03a1415201c8103039010b03100300301c503140c0180d698140c20200a10400e00b50802c01419090100114100707191034035960b680d5040d0360361030300445c00640103090140c0640c00340c4d040c0c41001d40c4040c00301001416032030000303654a007003000c02d1020310f0745161003d44804d8541050304070104129000c41c3e4200c155a5004a10014034240950074122a1b9000400c03a2049000c1701544020050444140d135008945440d01c581a0b231034040c1c01d0310880c4070201001c0d04170b10044407844507846416401e8030700c01d50b800110388101d00c103510102920758000707458981c4500707410400c4003800031440c4076410509000c0d00a40d442c2680160507401084040418410081010f92030002005050002040c07082000c0c0 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 642463543 1250 642462293 642462299
    0x905030f030901021903050702130605121b010207030308060d05011d070614040501050904050a180f0c0909022110020d0b0a05030d120506180f01060e1f18050406 71
    0x240d40d9620030b80320640540603d800110201403075803150203040390982c886078900903880c1e0801c500c00e0380d4103940c800860354800300412161660017441550807442c40c001d0103144070a8041403031035210b0303030f01c4281158004a414000281d00c0361019401480986078412007000b02e20b00140035000301901070003000911455407031090703000035651048400c01d0b1a450b4449402110755429480b41b37008203400304004101c210002d041036404a50b0000307080e10002030307071403140e586110038050486003075400003591100b940034084410103140003051250010016000a0743c0823900b8410b00054000c50785c803642e02030520301101800604c21908460780c0855a8861500881d8010903071260841d000e44100c07180800d503810001004049a12582c0302c056041d400010008044c107801025a60488401d1160b03044102c2010781c15030040c0e048043c000c1c0e20b50704040c401000826201d0545100b001611085481800c03000140b44500d0070a240015001030a204002c070091015404242c001d46010400 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 642464793 1250 642463543 642463573
    0x3061a042706091e0c1e26030406021612030903080a03020c15040b0f060303030105150702040c1e0804030c140a050f03030a06090204050a050402070f152003040c060807090503 77
    0x1955600d204402078002c042d19110000501c0030b207045803891003c1c4940703080c03003c0c5051801f40e1182e4030190340c01d460b0016480d9501c2c1e0541e00980d11110141e8850391074004a00540201d040c090108524503803486510398030001c0060140b44005084060300050120035180b0a804031407000c01c0c1201202c00755540140101184070086400f51003152071380000c50b100e01d1456000038086c1400400450460f400c11f4100001c9050030404c4400740441040b017140140c5a50055241124403074132440c807508134050b00c2c2c0c61100c25100f460002c21a2101c100000650069401440c2d10381140e08503510290801d0f49030700d403030400c16008d0403e00c203078424012040070010042d8814202040b003440442d40d1001d000c02680158040c00c0c0e131210003103500340300710b0409502400c000e900406001180b84040d803200d011034040741d05074000d9a9150340391162103e0340a50714171841941d8019561641c6800c2d203c0c00800c68442c09040c080041d003801241c1c9140c070850302c08025000040c01d6804000321480c2d1 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 642466043 1250 642464793 642464843
    0x2d04150c030e030f0a080d0921170108030a050304110d150606020c0f060711150a020c09062809020c160f0f17031303061a04270609 58
    0x2200080c09820080315942000700b5100e80600508000342841c00043d034400751b086c3c201c1c2110546d416620304240c4042443c50090140e080c03800c610462100d1907a400040c00003070600d160f01120380c0410010003032000f00100716018205a80b4100741c60f900c5a151291244242141942d0310502030300c1400b05100c0030b80d55229480300c00700c901b0400740780d0f142c270140c0c2c43c0d015081c60582c0c0b107888204007803400d003807540041036018071030304505c4040e14030036000a24040c100001c0003d18440801d82d002820340400614110950403920702c6850b103400d40c00100b2030002d00345041d00d4041d200700c03134805404284812038081e040143c1c0a41d254140e1850310f6984130384442800ba001c1808240000e0703048404201d0b44161802401c0c1070b4581030400034075801045000d403003805184800c0100d0302074006480b190070040d52103100f0220b1010241240801c0c0c0c90f1900b000c842c881c1d071a0000c0c005402071902103140d000c001840f0340e610804514280034008110594010380720700c2101540c95640c02c5141340e = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 642467293 1250 642466043 642466067
    0xa0b04030503360111030706090f06060803032206060305071d060916180317070b06031c0320031003021002011107020f1f09080705062d0415 62
    0x103000034410701030000080720b045541c00c3c40b01400102d0710320030803035118031017501841c00310b401140d261041b0365440400716004054140c8040c56084162002c1051a020700401850703200021400c4d400d142004a20b0134181144c0b015488846000d00340801645070082c0005503000020745613823603a22903980a28402030341e01940e61180b503074002019490164007060240c09034101c000104516850207442042981c0d42010f404222084004000340c40810b40c07101c05d800160f039194544a0754903201c001c980e00541464441c3d0004030032000d0b0510030f2650807030100542c0c603020642400c6082c9007001104803030140551001d00004009107038070003450a0044034400c0c5e945c030080903024074040782211110440b40403080c0303007008402c0140c607066a44040e0b50f04002c1440040070241c00017084200700c9001c001d8041802120200040c140900500c4010642a2112441e00030b240d1181d006800341711104d8900e1110600c03001940d0149442910301600d0011010343c840144540e01800b0031803082 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 642468543 1250 642467293 642467317
    0x1b050105010609060e0a080c010c021c120807210c1101050109090210080708061917010b10180905070c020a0e09070f150c02150d051f03080f090a0b04030503 69
    0x18003242c3c940c00c0003103000d1b04858a640103070030708070800001100d2450328450140c0e4850224004200100e01c0b0034419098984a2000340c16000100d907005030a03000002d10181c207104016010410030007042550f1000c80f00b444500040c103180d040400d6a46079a514002c0f2500d600c1c15001084407800c69200002241c022960f1072002844058201c1e03041c1811504400041c076101d02151050038406115010002d15150780011030343c0b035a88901105c4003070114868160b448401400032420412001180d04105140c2004070885801384000801070718480c8101450b0b4440011b07510340e00ca810390300142039008118020450b03a44816070103048003030b02c00c0d8996024280000030144419911001142c96003501e04d01c480a40040617070f08044d42d90400da0b00400131f0300a42141440040040a0850604900060b11b00704808120421080401d09003001810b0450a10100c0c02980549420898820b501c5694039000c802144d4070b542d07150b1061300360040118012003003050200160004803020 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 642469793 1250 642468543 642468557
    0x3071203090e090d021c02190b040c080105090c090604090b040b0703050f130f02151306110a021f0e0d0311010b041e1d03160506130c061b05010501060906 68
    0x8208903131201d902c0001300002d6030000341c21141e25100c45500c01d8000070130b40156081c1c85010200101682c190b06422a0f8030740700c0a081008100e086481d01000d031459200800080c54800f00d2fa6a65100050b0b499125034100c20001d105a034480c0c1180e0f122036401b44c0d1040b030034140392800d000801d4058980070040fa082c81d000410031400004480d02c03075540b40c031048500041e651150050422102000d030b0304000c500050b20101c21111000340b55109000107140141d80c5445001013411490303080c00e45840c2c002c10360303090144e552210140c041d95658140001c0c1d480010788240ca400c520201e1903038001700d101c06e9400034580c0007108110114cc4050090220036108000c02c0b04590704c1d850025040a0807480d030070340e10806640011100040280310320034012812860341c3c6190403603007034403080e0154034002d00f04120327082c480c5640102d00245006806422980e801070100c0640c012081003018603001c0305c03805480c00126440441c1c021008100e1961110f10023044a000f5000d048046162 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 642471043 1250 642469793 642469801
    0x30601110a02030a0f061401080f0d030204050a090c1e080601030501140102100c050405060d0504020a05121c17101a0a05041806081606080a0209060a0e03071203090e 73
    0x3010030071640281e030060203801d00740180d82c0c40404c3c0740c1d915082a030b1256900c44040032105c464900e00c502070010640180b00340301344661480c1c542004405420704240c01480104155180c408449050703e02c8a0404102c6581103003003214804c40e06200020f42600c004010150340d9000800c0c0d074001c1e002039070203110382d81e01c6552031490342d4a06060640180d000721620b40c101001a4010803001c4d00d64944a0b01c0d103540c0b4400900980c100000180c0c90503900c80034082103161880c00300d0002c1c0402e40b0703200352072034203020307aa034a03240380d01c250180e002c040c01d1000100354400c2403107440401c003482d00301445041034104101550342d940030310030700c04041190100c503a021580c150b661010207580d94038505030074032000010482c0c4683c2e804001075103030f12000c0380a04061003c0a9181d540c2c10341444090b00e8400300030041d0030058450712200c2e02c1000042d160761220411201030301c47c1400e004a0071109040424680540343d80f220040403801ea106a08150b4018920000ca0745a0380343e070181511 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 642472293 1250 642471043 642471077
    0x200304030206070c0201110a050102030109050f1608041a04050c0f04021c0e03130308030f060a031208070c06020a021b060901020705210714040e0c030304060c0f02040e0102030601 79
    0x100654015001d603100e000083c0465103c0c049040040303206140034120f180032181e50928100c031000c822604c5035004401407004108601c0343c16031100b08454560424201106100c800c0e0102125510401000c8000a0180040740503907a00c110418509082c0f00d01d00f0b41082c584404006520318818a01c0d55860422844c05d8001d4828007005c0d0a000841e42c40c10f01420700c014100c40745050324502060009d1a40c650810003030310011401444903a40c6c030f20307000f015011030801c0101114407601d15072400380003140c0782104403803481006d8181200c6a484000080d202c204803801c004040c1c0b0f00000348415000d9020400043c0141407608500e2483c1c8803000b08440d5004030034405006030310850301017103c0e00c0e291064081002c00581110308204054403051704100c0170b500054500c80d21510b03009401d080c54071034200c1c980c001501805402d0a0200003a40fa48621302c208400c1240c9030b03844405120030108a01d035481d034020401c100c02c5c0c05d9160682d004c0d41040321520301245040c0d0001240c26 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 642473543 1250 642472293 642472297
    0x212012007050f210d060806100e0f090601061416110102070b070b06040203071101020a0f0906570b13050a060507170f0a06090212130204150920 64
    0x3134500d400401d0306801401d801c01d07070402c1030040051521518001840001485458002e0381d05441604005042c1020586580307006400b04800219440401850300350204149041d640989050005020b10700350f0202140076039019422001540802007040200b004200b44410b5000e03000e543d0364540d2403410303187c103018400f005001e40340110001b50080c035050b801154081010704004105100100302340c0c2c00c9030002c21894000c2a0300c0d58a4181407034104031b00303400501140c41d00b0302250001008004101e58918080301310384100546a005040c01c9a80100d980032043d09a0760440d00b8801e003800c0d003c4072513036054075005c590f00080782c10240e000d003001c05815080702c001c142e42c414681d948001440000c01013000c008c045034041b03151020800f00c842c01120070600d8001c16003400d02106013141c1c1325a102c0c044441c81004407813024505041802d5201340b100c180080c0080603030000c14040d00400c0d1300542070943ca90004901d12000e43d012400e4042500304407429584144060702d218 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 642474793 1250 642473543 642473563
    0x20703020a0e0702070e4011060d020d050a0c05042702040b0f0702040c02010b011709070918030e042c0c060a0323010b070212012007050f 61
    0x1e03401070a11000341c0442d8590303004400380c4121034180342d680c90701c11282e03141030f05c0001c59100c070084032030b410300c04110000b80c41c460000000c0b64241c0803e202c04403944116880181a00286180502e0b29030714501a07614143c9074900075135071802d0a0a4180007881b0403a401d0740102e192141c8400003c3c032803001d8a0542d54014000f6000c11784040c0c40c4403c030f48034042180c20450b02000045018814540a0a850b2907074001203600e4141a10400040d00d071072820901c11689070007010000303a03034081c002c40d801022040071030b40d881d294a03402c6400c0c82800d800c000c643c1400c00001c01001c4030090010b0b00810f009684050801400c402080242e4801000d403201e400c81c40c1d00001e81c880d40340000511109529001c548450030030a01140c4c1a03000305084802180c0d40302c1c0240c803140059030350142c0c100c8ca038815502d507940c14000c0d102c030740780a480d101038000d0080f80302541500400351b000c0348800035149803060318042c000341c51081e95070240204032064050250600c40c20000000c2c04040 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 642476043 1250 642474793 642474799
    0x906010f03150204051903020f120d0e030a29100b030c03091c05130504061a0f0409060b0703260105040b0d060f060e1e07051612030c02060702070302 66
    0x201516580b51280741c1020707881d024162503420040000c4542e6848040c5110b4102d01da051021a483d40c010401131304015820f007030250103401d020000c001c8000c0782c4005e81160900340010804401000b1030300d0f015480e0030003002038204001850084031091078000400c00400c20b0820217030350f10724100050500c5071181e110b2501d0140003080409400740042c0d648149a9411281414299010005002c0e0f07055082c0e0081480001c1c4880200d842070b090707101400d4299414000d261a160450320500e031150070266260318041078148010b91701070200e500a2100c441c084c402184c0301c24482c0d425900008045000c110105582464003c00381909410040c80c1c0200c0301a0707a10708000e02000d028040081781d0b004500c1482440054005d02ca540c20840c801030380015030354100ba0b05100050340107007400f0200d81c210340c3c000c010b03c81e40401140d03220800e45480c3c0e45030b10460000c050301c1060111f00521a81c0c49511002c0c0e9030f6499481401c01403101d034200c958549614500f81d807603604500010790 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 642477293 1250 642476043 642476069
    0xb060c0703170d09030f0207090605060f130b040b041e1508090106150804020406050301150b0c0705060a050a081006230c120d14070c0f030c080d060509090601 70
    0x400301d040200044028031480046510301903c1021240c1241d0141e041103005c01d48081864132182da0411100018080b020300400c85141010005000c41c06103490440519078001080862640c50290302c4000304120070700c075515141c4403a00030301960028026150184246041d18800d1040c150002044600700c01800b5a9814242002c9914110040004100350740311a00010300b80d100316102145580c040da03d50150b07050a20400050f900d0302d42c4010712a070b04040342d18208403030b0125444229000040c1599450003141c2c0346509000703e80d0b202035808640400d150400a40040061a901d0b00542e92500b50f69200702422403000041d000e180c0c0004c01555000303140180460482c858000000410381c10f16803025080c41c6003110025940f0701484c03000c40c02c008088118060307014400e80ea111400001c0c40c11000082c01c0070079400c405041c0160119090707052501917030401034040c1e040710705644e9a40070b0114040243c100d522642e8000c030400320008080280105045040c0c0742030034080e02c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 642478543 1250 642477293 642477299
    0x804180f1b030513020a060207050306010e0702150709032f04092001050705010e0c12060603101a0a0e011a0315010c0201110f010504060e0d2a02060c100b060c07 71
    0x1401880002c10212107104c28050101c05641c40c0710022004042c6030703004104003810704060505100043c1e002c0d40740440030030144850990003081ca8459501c072901407200a40e180300c8100e4003400e455201038094182e5018103000303641d40c01400b401c00b00303017080c00c01c006110346010320048448100c0f0103003108040fa910090f9100701c401e1209100201490450300300041c0c1d49841c0c0c2161410b0413807900f5640040eaa28116081010940205e0b171403800c00703804035241c4400442e8884001d070508403100f40d62266410f0350140c501000800004005d003610309150f480b40070449400c2405e0141403040d0384009134601e410594182224407650a096040b0412011070006442c0e0240d0310781d049050040e01c0303105051030b010030005441d02002e40400400c3d103040c181802c03c00c0b5501440403080c40d4004820780003006070402c05909a500d4014100010000310340c014a40402081e84001c3d07001400058503290b4803000500e41d50303550b150541c02c0200e0400c48040118074400c211440c462508109020 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 642479793 1250 642478543 642478547
    0xd0e06090607151409030a080402101101020c010c0207081f02070c05030f03120a050106020607080a110a03140606040303080a050a1d011505120a0b0903070804180f1b 73
    0x140031400800790846050601a55400e0a0201c0c0c006942d0816680c03a0380a039000d000032440181c100492801451401207000e900501e0480000c2020b40a18a00c0f0164104280326808517003104407040004c645500001000c0da010307040c00303001800148100c070008180850007040c2d5540900c0b2501c002844c42010801d010040d401102050701c1d03180d414040040c1548003844ae0a514900c2c42002d5940e41c0d441c0f80d01515212000344c00a188585000010b0190383d8001400b6604150f417814071903502d66a108244028180903031000900c0140440e04002c1c06070541c01030444400210035130009940e038001845070303034010b910003d070008460b0004111000300c00c0c0d000581089081c5004606140c43d1b060015240b01802443c1a15070755031091040c2d040190704003040a44000c9801c3d034040b043c040c0d45590394000d02d00c40034080034250030107e00109020400c66807240c9d8424011911142d48030034a5804150b104580041c0701c0c1042242c00b00740030f4621420409209812044907010005101 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 642481043 1250 642479793 642479797
    0x61107050d08190503011a0301060f081005030d090608011409180a02060f04030506060a0b0a260906071b050a0611091306170f0307060c05120a02030106110d0e06 71
    0x1d50360b80408000340d11542400c03100d014090407858503001d07601e5141c2554226006a03806100b043c07118103100500c4555400036a02c00c00f040b1514159440c1c0d00c0e000c481070100d803900d0348026418403540102e0013a043e00060321000301d401c1b036100c070344441ea0303202803901607019100c0074654881268000601c11503502e500040058032000100d50b511081035002c01c000f030348801c5a0038070814003c60304104001c4108081a4440010f4452500031071410500325118010300050748140000c4031a007189038945c0c0b044180702030b0461040c2200c0c0e030400e50302558075850207892850001c0c800d0030403104407540d04249901801e5000c0000c088140103600c2e020010b180310b0409580320002041141f000d641c03020080200b20114a10016a6601d0854110080c0480d00300d070709840e030000c00001c2ca08043c0801a1001e0941200c00410200300c3c00908988a03c658401c03603010341c0e20794081c000e161450794003442c180d4440b40c484944107083d40c01070075520740007005400005002540c000c0414107107500 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 642482293 1250 642481043 642481069
    0x20040e1e1203070903062d020309030d051602010513050c0d060f050703330312030e1005011d0603030d0f200702030c060702030d0309051e0a0c06110705 67
    0xc1941d1a40c2040800152180c1c0309581810005843c0c00c010301c280001445460900140b03814400d2440c58000c16007060036131002d42018a00e0717030220009032102024004c1700ca0020303c2c0b24007045689000d4408032503840910781c51100641c600b400284908110710600503005403c6030040076003020400800406600354101165020f840701070756804070344280a0680070340b40b140c802159400081100d00034000c4030442c664040b0f1102ca40c078644600040400c0c1050b69008210a81d02015440003500941344511424a1070310070300f001109000150391046050301c2c040403000040701404603442d44482010398499a0542007003181c8602c6480f5a401580c0340c81000a01158a40903010300700d0010b407003014210721030000003450740110300c0d05001e2041c01210445440d4241851038002c02d54132023482e8000720500d55500c1004e418807008016081c0380c14a0001402040d02c19003103800d4a0b004a20300407244d800180c00e0201c1e000d80a1030100c0d42c8440003100400107940341c0f000300542c01013940 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 642483543 1250 642482293 642482353
    0x91202041b02060f091908070204090c12110307051f030e1009060506060406090b0c19060b1011060a110d11030f010f03020d062720040e 60
    0x82041100080c0d01500307054021440e00a00140d103409000d038407443c0c000800c64251600300100e6082d0352840111540031484e00021142d446030240c3c408a0018003080c54040c0600000800002c3c901005020301d00d8414480d40c40146910040014141d49110030f000d04d80d4058051000612103030f40449114142c00e45c240f8000c1007544111001e41d041c004101401601d031503ca01c816030500c4014020a0b801c50010380700c0ba45024a840c9005048001e18021101080c4000034100d065843c02c00a51750351211a900c0b40502d01c00703500c2e244006013082044640241c0c50240035880c654003a10491000c4114800500403d60f100d652040007041034039821070300d80109100b507090105861045403290104114145e60303034181284051580001644034601602d6403143c24401170300c806109056080d4001d602041000d90300c0c64510183c01d60405043d440380d024101c00060080c0210701d00707902150100310480f088014414802035551040c1240071950000c840c4803101c541e003416a0700a40018 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 642484793 1250 642483543 642483551
    0x5030d050c06190b2d0102070302090c220b210f04060b01050c0a0506010f0b2106040e0109030909061e0308180904050607020d03020712110f0d0503180102090109120204 74
    0x1141c0094000c200c1c01e05d03403602c04041160814162843d01601c0320100d0070900080822034950380c00107551000041001103420f5020910f80e52103010f94072050b10035503408401d2085030780c54400307042003500901e4902844007070703000490111085210704035000b100e8541500c0841d41d142e48609003d4407031042c2540c1009010400e50780d0303e140034450101424172910207441154580742c80c0192070381907a0000442c8003030801158900c0780a2032207404126131075268900c1203964a200190041803900c00070440780d400e2114000405034400e10081c141c4100a0f0100311301d54880d21895003006054145140c0c040c20800d061000ca1020300140800d842d01c4190744601185035800304d9609041514120754952010091046150b0140401e6081d05c103180350441c00e11410381ca5100200014050305410300581100703c114141e020301103224003a8041040724480e00395100014000da104855140b550a0091324220807520180211405020169070b0000707505e04050060f0390501321818100d91140e80c0b = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 642486043 1250 642484793 642484811
    0xe0f01020708030a0c05060615070f0c05120a1a010b0405011202041a0c0d1e180306020a18050a03080702091f03080901020f060105010801170f01060f05030d050c0619 73
    0x820090115501e980c1e0761648034041da14000c7e25080d009071009206030b00342038800d950000c0d15801d9452413900442d01c7c02440c101800c1201251401d03801c00b0341c00c443c540c01001904c0d900001d00c10b000030721803140d650010dc1082d005011540c001c6c010848140010807007001150710844001000d2100403030018541651000342040c2e0301d06240482480320008103080020034014070503003a0140990034181008030034003482e046540c584410020a00c81441c4251008107103000760100619030109003155680003410001d40810240000d031400c070b902c0480c000c261418051000021250b0100030907062000b140d003002185640100702e1025880c03002014045c40c0c000060003002075010f809840c0d0b035020718000090411003c01c0381c044480c0c0c04940100074a0b60f100c90344d1411141501d00510403450342444150410b000c800c4a40c03215030070a00c0c0400c004504005603003c5400480481d0701d041c0b0784510540c1c00740602203000c0c0c10742e0030007000944400144103000c1030707000c605000001d240032 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 642487293 1250 642486043 642486059
    0xc030301031208010905250e09040303150501020f120a11030a05030a0f02031e07030902040f060807051f0f20010506150f070809041b0c02130209010e0f010207 70
    0x241c0c0152800d1482240006840380c200b203005000d414103400c01e011510b400c0000240380e44003000761480005001101c40c80042c400ca4411644d09030040100f00300c0d051a007002005006402a0008030316481d910000d0300d0360001649003108040a40036046000b01ca2110b030b912600f107981c54500f0f001d00d00710034404e07000081c001040c01c0d18540d2600c0361203040c44801003044900100d044c245d0703940b042040c885045020310754031003d0700304c4003084802c07035072424002c802406c00014001e401c9400c0c88125082c2055a420031401c2da040d100450b41d42c10364800411801d80341038280e03150344150000203428100d115035040c4603500300c6800c01011001c0201c02c030402c044ac0002070401140d5645040c84000d207841c01c440112a2211040141009520b004050892003480e00040070745200159055141c1c0f955007222140300ba9010b400c0e040790340740032406401c00c0d1410000320f126403020034a00c480481d44e44280e4810000c103954402d40f040640062140440c051000305040d07118613840081e040b2 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 642488543 1250 642487293 642487297
    0x914030310030510020f0d0b03010213080319080f0a0b01180b0a020f0c0a062109050604030e01020a120e19080115080606060f0f070515070e010201050c0418020c03 72
    0x84620050165107a286007401c0f81841c82d510300c0c0b441c0c12801000400d0030300c42000142c503e5440c080c0700001e4408d4407080000c0c02480390901c01c0c0306a0304410300004400c10044090482c03041850341061800072240c801303c1d000c0600716802c0090100d4080402d09020803540301c01003600701030419002460702c00440d00b13444001640310056105000400e44003895061100c445c5050001c001401ea9a03090b50000344003120b20b00406d400c0146800c2844070105860030b068001c070100c01810403c80e451420503c0e140c520840c3d05401245001c00e501015502c0010141c1400342c1084411901c40004a411295480c1d04915242c1c020741000300d0168100446900c0b10080031400000a11000c403080720080b081440c0d8042c0c1d980e0307000740b810448140c8a40c401c83d144410503100b81d9540f10303813000307c501850140e400701074224403c0080300030030b01c85501e030000d0240140c0d480f20301201c0000401282680c0c0c0c1201c2171012003000384020848110000c0d2002c01c4d02510300005400c03d000e00d94923910f15 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 642489793 1250 642488543 642488551
    0x2106030819030c0c0c0b0c0a0813030219150804050a060c08100b0c070501030507050403060509030307091202030c0f1c1505070f02070519050303070c0311012109140303 74
    0x402540100200264052199090f4560182441c0d00c42c4e0381e5a481d60700584031030b48201c14510b0710000710b91400c040240310112010790f0081115031980504115403007a0805400124015400170761400081003d202001084a01040e901c010410060b842114a080058030441d0365119041007000018480e02680c1c078480030780e544200d024034140481c40140d0600c0d42c0201c0f1001d8040012603544075010500109560003804e0102d800e44801a0882e0f0071f00c0345034405400d542c43e10092000301500400210300526540e0f4a107039600751500c00d00c0e82c0d00508020004c2d0b066005903084c00084c20202107071481d402c0c00405c4200b2820030a82458500885038904488910b07000d03081e00a40c4140c0d210765074002c111131a01c40d041244d02c060107582da14660107001e2240503200d15140b1404035101508029040c007900380d0307413a07038002d29007040c056009000454280d480c502030381d44294411080300030b010112090440d1030003440c9140200414481c442911068030036402240c0c602c03002c00041d801 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 642491043 1250 642489793 642489817
    0x30f0303092405011512050c040302060301230609030c21030a0e0405070c030c080313150b0a0b0313030818010903080901060819140c0307260604020121060308 70
    0x94020b00c503036100b2100141c03c11810080040c0c40803048a07400034040c0c0f480780c4660000a02600c0300343c0d5030300340d030700032a030000303600c80c100000202c0c4140b07078806042c400c18401d203e10f8944503401d004214090150800880e05030307212400c0d40e10185003115003003082c54409c0074072403140038810340d0507421540074420490210f40104608a005c3c249407080660001403407524050088159800500760024600003500005004c400b02e141030702280d0703d01c0700595020700e06482039501e82d40f414024116441d010f030b01c2004401d40002e0550000e100f100c2c80340d401280840318000442c3d030180d800481c090301044406c00d16207070240e2003000034410800e00c14045d4540945074600030004034207484158108081d00d410101c02000040b20340c040e0033448981c07040b40c0342c2092443d02681481c02d01c01144080d031504c14802e00240c0c03c0351a007410101510b00210141021965801c0d49a0f00e100a41c0c00a000800003042e42c0d55084d00040c076101d46403509800440d09035a0707034441441ca90050108104 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 642492293 1250 642491043 642491093
    0x30a020106050a172a0307120203160e070302070f0f05010504151109100e03121338070602130f050d0203060a1814072607030f030309 59
    0x610300d03009900e41c000b0113021940480702c241c250041038a58044039203400b1200c120b15000c50106642e400014451031011b001c50301d9040d13a41008298a044102e000d074001e00642c80070b1581c98499a0068069460000c803107481500d400780118001e5001403010f403140f6004c500c40c480011004146403a60314003c0e4000308150829041c500401c030b449442d205c1c5050305e8050f08401000c0c0c040188c81401e00110348882e129088004180c4203d616900d440303500d4041c05401032004183d0f9400344c4000e1f01e48031801000c2545602c00c240d0380f8034038200a0206121300c464000c41003139449542110390f00000b4441820304030982da42034140d81080244c01c07020402c9500901901d0b07450300c50000100801c071000d0080c0e1450b44c010980324440039000c1e50038a41c82d20b10444048901291041200394400c4003540d4442680840f107071103400c0740c0039001040c1d4030610141d20344044240d16000141409016240b558615502c030008801070020440901d034469540c04046103800040504440c19909052 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 642493543 1250 642492293 642492299
    0x1201b01020d0914010509150c010f0f0b01200a1407031109010e0609060303040b040b0d06090903090b0703090b031f060f090e15100203070c051816030e030a020106 72
    0x2a0401c6034107040c5004002c1c02c1c3c0c00411034802111280d502c40c40382030801c142c1ea680f0f441c000c17421010b070b00364103058500c60015081c000e09005501070010f0940c10704041001c9107282d050703401a95101c900241c00505404940030403017692000000a0303540e03220880303201000b41c3c2e544070100040400749102681144504009100010740303211441c2008460b5041d41c1e41c10710908003180301018114a00443ca4000081e0302034030300b002168007404109000640300d0340e0300d0080724100d50041070300d05200307810401c0000d03604220f40141011075a0584980001600302a0381c855142c01844080c4d040001500e400540300d43c50718020340c01024001c1c8082405000c41e0740340c40c0203d01d260700840400100400c00b50301c040c1d0041c5030b14295064111042a9a25968000c070742d0a10002007096000d40c150b40c860400c1a000002080028420410850219544c13010445050010740075003401c080000002a500403124080c0341900046040000c0c2d1440c80045640c0385030404882000076070354402c3c0c18 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 642494793 1250 642493543 642493547
    0x10902090112050f011416020703080d15080a020603061933020f0705010f020c06030109020c1513030e01020a150608010b090103120f021f0219080f010501201b01 71
    0x103a13108082000078084040c2004110060640052040d04184000f040c80e4070b095209010640003540c1020380c040e19a110707100c07540001c2c1390180c241241c48428000000c0c00450208100d070b1142d400030804c1d402e6640c0d200c14020b100180207802a1025108900800d9402e10100400301e0394911004003c6810144480403440c100c07041100015944070086c00c81960b9400100041900d60a20306040c140882260582c94142e1500041ba44588040000303d40721075564003420400d0824011224208208881500f15510a0310250088107101040e0030100340502c46a81d04d02c1c0c1c044c8111070007031351103888030f2048952070014031082c42d4450400b00300c2c0410034010600e041604988620f140d502d56601c01c040103c65201d084c0a200e00090340b407003190300034008540c001a040740c1698080c4030091003000254408c50110800c1c0e5404800c190210340314003d844d218507581c4c0361110b05079080038010f40c0d00081e52a40e2044c0c515502d0304a0002d8542803040119114444403003c0e1036107510740c00 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 642496043 1250 642494793 642494803
    0x9142701060e16110601050f04060b1b010b0607051005271c0311090d0c17030a0801060525050c060c03071e0c03110d02060c0604060b060c1e01090209011205 69
    0x35410400c904c1800510480c1c0300420081d046401c102c03130080d1440700610205001e0040e0354828150300c00c000c290b070050b050480418a040c000900000c03c500c49840302040030074015488054039581c8000c00d122104806540071039001000200d1001004004404046004c5124041043c554011240b82c0b07041503800600f85940114604050084d0603000c43e450455004c0c0044840c804d90041724200c2c02e0100340c44034039000d08002905200b540c98040c030360640e00d6020b21665800a0f00e50400064a0f0b031081003500c29059011071001031014403c05500f041e041d0410080d6841d0154822903c456550040100700754801c0d003010311703114105800c0a038000c0110003620704585020138074441c00030341c1511119050300e03403120100c8680c0726182e01003101c00d28407031002500000001405c5540c60030005141d441548150030074040c000242c0d043c06400e0241001e200c1c003d500122101444210301c210f400c0ea4206010000500d080e01ea070005604505d0a070b00200400301c9070520081030002c2400 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 642497293 1250 642496043 642496081
    0xf08070f0317130204050402190305060115031107060e160f14060403020906240a053c180406030602031b0a02071a0c0a11030709142701060e 62
    0x15902d0303240604103600c02504120b4020b100700d43e54800501196101c04080403041610a114800c0a40364900703e90b54080038007441042e101e1021085094511a004100480c2c0003c411f4a040501941d42c107000750149070854a194016503071100b2a03038890202c9000105810410900020b10300400302d51801c040f580d803180030f00000c1000748056114640749640214058070b24146404c4040040d116804805000034241d810000e080c3c44403a074884094414484005001c00c145081c0e0203039202d900130604c1c00c40c00c10016100454000856001c041c01682c200f00410b6a0f169040400040803076a082d002241e0050b40402070140e12100c80755030180d40c45500614504c1c00b00c0d04000039540d07600e00d101c0d241d80d030b2182d0120042c3c500c910000703541007244100121000d0b1402860407a06a282c09a075181c000d02c11050002501c0045000702c1020044101e8520020340300c9010a0440040381503806420140f488050901060309100b000c00a0481c0c07200d035015810041070719079071984118 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 642498543 1250 642497293 642497327
    0x10806120d030b0a0611060c0913020406020102090f010f080f070207080f010e0601060503070512100e10090509120409020a030b10090905070c050c040b221a030d17040f08070f03 78
    0x1400e207500c1c0b186d0000340250042d10240380940c43c0c0c0b0071040003c0381c5c0a048403d0301c2c0c00070b001190000c0c0054054001c3d0090610441d0a101c09085001c01180c02240c0d144400d800503036488003280f21240010f81c0c19400442600c11303034070340580305c031007041c504408440d062041d42e540d400c01e401325040c1032080703034003503c1645455891410007072401001c0b801041040c40708201020301040c5615111500d01c802410401d42005039031910100580040b4814880c2c59421401c08002518040300440c0690103400d441401e64141030510241c00000e400c0b9000b11024182d07100c400381c00e150303507054014076001255903c18580360300301141103086d550003030001401d0240450110b000240045410880450203880010359198240c000075026401402600480b00161041c807020820715001102019000c0c1220700d541c4c0505420701d03513601c1d80845005d0009542202c6200349158040105802c1405503003003e0309641c003901c0c2c1071507613400190110342d8025032400c5041007540210380004c0408036a = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 642499793 1250 642498543 642498557
    0x1090606020c06300403050d050702072714040f1401020f160c170d08060603070c031b080301270903080105010f031b0807120614010806120d030b0a06 66
    0x1c1c01042c0103002c0e64042620070300c120786a6101d0040000c4502981070134074540e036070850504d401c0182c00c691210f00c49982140c10200010000d600001d80c080c12200400340d20101d462803c00c0709110500112401240280c0703c070300b01101c6503400e01c50140514000c0d480641640084d15001110782481c0c00358500380d90050103222013198210050768200c040e150312050141d0403e250118080203143c001c440122031580c4482402200041c451000302e82c3c0b42c44000640e110503081241d6030004480b102c0010340c0020304580020312130801c0b0b001001d80d45108030324034030700c5503142d003e260400d801426501541000341d140340f420002201d41f107403800c84001c12240c2d4581c0c900030700400e01409214103004032510001d014174429484009920090400800d9000c070300341000385550020b4036a40c0000b26601a0030a030240c251240c48111140d58050708120100e150064600f80c030000d11056010300f030075660341c502c0c22051000070210400c0350340004664034a0020805100b182c3d4100d48104012 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 642501043 1250 642499793 642499813
    0x20f07050906040c03022b0b032d1507050d0b01050702031b13020f07020103050c040e01031101050c06040c060f020a0309210503040905101202090a05101d0109060602 73
    0x2400c0150b5080301c025680818030818500003038001e44103440701d907691054488995004041c00e1903000144d0109040c0a0054400e0301c0f0801d552100707003481c058050303002148096051a09a00007040c2c20000b40107850048400d01c024121004080700d8140200b400064500c91088051142001c440000d081490920113650080384d6140341f40d900c1c1120382c00401081c42c2c465944c40b48001180345101e10b0540d51402d11540718031071900b241e0b004902190419002c21480b00308175003944d040d00c4061244450680c61500c841c007a0000d2520f240b81449000c000c1c448402d03509000385881280038591402c00140f41a5008140fa10018020411904148401d000003580160010201d9505030b9014400207458103810040300c03550140100036100c001000200d00b019604440d21a070b004200c9103611070b036914071304041d1450510300250b12903220301c0001e485454a9001580000c8030040c403c44494844034031404050092101d02c500185100040012901d14007604001d08414405808a421 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 642502293 1250 642501043 642501049
    0x8060f0c0703081005030a08040e0a2003060409020d05011a030d1b05030f040303090603050c090108070503190c050403060f200c010f0f06060f09050307090905030708040303050a020f0705 82
    0x20716a00500300b10300f040204030f6000040d00e42c01e01600c1c0080a13680d042241d4540035405a0140c884d0402c0001d6200c00141440442e02c5400011656030203c81c595007050000c41c407855000402c42c65200303a840c84040c015031034003030003040814425000050050030070b1715040717a03028028100c1d61003917002031480d683d4281c0c0040035694035044481038034003000c01d03807526138154000e0180072245588041030000c18540d01c042d8540c2258465201000a511000c4401c003481c881c0d0a0340d9804110300c0e2010803000c5100380d0085a00c803045903c501c1c02c0f0600042c1031400c0e540fa0317050b12000104081002c0c02400f50b0791142043d1424608420813144039000210805218192518249000c0210390301c040c82000303401c1211200c0314144c1c1080750007004046c400050900c1d00419001503103912040003885d00410815044d00d070010001c0020b01d1500d8141c1020b031054140468440c04144076440014620300090800383d44a80c46543c2c440c004008003d10b070401c1c2c1c0b004107105511219041185407 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 642503543 1250 642502293 642502297
    0x15092601050a0c1b1103030f04150e010f08090c0d05010b03010c03020412060513060516111f0f09020a15170c0901050a0302040816031209320a090608060f0c 69
    0x4066440104070600c0c0c2c5c10a6006118140c010039094000020090610410ba100410540f01039046107400c1844600c0c00b1501010101ca0b4a03003c18801c0030b03000000381c0a00c201d290310010b20800c5074043c0c01d201c404905200703141102103815a44a00741952149020b0080c0b024080c100c0c030381142445d00d444071603c0c0070314003140041c1401d551035010a2151070070500700e05807030750000c07014412400c02e8100140700d0092814907d000841c0551850503112011034001400c0c0e00034001c10b4039400074250f000c1c00034904d0010f050301c0c15569006000040e190840c003000109544080c8403031a14442c240034000d2601c4c1f019054003955554204500780f80484142c6076000028a0503d8072084001d006500a20907a001004180b02c0c40d015010031008580680060724031988214248400304c1900392075001c42c500501490204c1d40e025054041440b403102036071001c102c02042d503101c0080c00441c49660041d00480396035a20351406005900301000803c0d0440f1920034540690301d81704c0403000c218 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 642504793 1250 642503543 642503567
    0x9030c0907020c0d080405130b092e03060605091308030103030c23010e0c01030216020d020d0b0c04170304060c06021c0513020901090e030415092601050a0c 69
    0x380036050302080301e03a8420040a2403842000d08483d44035102c50800406a42151080c1b03846401d02c913220142601440c080c01810b6240585648100c1d1102c0650807501d038503541004400d142594a290810031001c103001b401180502d10005110782070409120300408000d05401c0b4054600c003001000401712011241102e8062400c0d0900b054039182c080080307041c1420000d0384c0380398070248012030903041d4010162072005c2c80460711403c20620055050b401409042041001c694804401500f01f0180301100c42c1c1c40180072141c94440380c0e68021080784c00780d0b01e8002c0d402000c90b00784107036500b501c510009103000b10021070400b8038200000340100c8180000030580358003c51b02048000c407610041030083e161810512051509482201c10088a418280d1044d6004000040c1c0890350f4030036110a01066070181d454142010312468101d040c0e03414503001c20010f100005201c8646803041880f0801c004500d507071142914031402d0945501511010307055292a030361041c86900100d00b550700c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 642506043 1250 642504793 642504799
    0x12060108030733050f0f0906060d080d0504050d02120309070512010f0504050c180c04090207050f0d0c0314030601090603110c070b0918010308070620071b05010509030c 74
    0x4140e414615140c2c3c4503c545040d060503200c695110440100e0fa03030061407040700c140007090b901e1360360000f5501090704103681d00205038008201081c2c190600284441500380141035840c41c5c0196118400215541100c09440580285030b08202595050011852200280e40402d0460500c030141c1521006644542882420000c203880300031102900500718202c1001c004010510302828601c0e107031504082154130035004c2c3c00007000510788240920340241c6000042a044c1402d015008009501410040d281c40c0b0a0300134171a40d0580401502d18041e217141e54040c11a5440e250103000150401d081e0303440c1d201c0c240108105668081c040002700c0380f4520b030101d2440e1041068400e04c0c45a14501c554901485001103051b42c1d0403401485041416a5503170801900054049801b81c1c0a0000800020081082c1d60100d4000d421511041034501c0000d0030108a80c1c3c454419a80300711012540f40e0451020503038041e800340d01d510b00400f42820305d649007a40100009445000000c40544 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 642507293 1250 642506043 642506063
    0x1c0902011b1121060910061e03120e1003202107091a07050c18010308030c0d050108060703060e060f04050406021e071401021809060d0602030c09120601080307 70
    0x241482c8100c45020352000f000151a000d040003041d09840e0300000312000b40c814100203000502c540f66107031540f0342152910344064440e045170b5a51401c5030807020320600700070f8400c049010542d502c0020f4030701d4100e41d03200000c0380c4403001400084142e4507110b010800006000c0380010701040301403c50b5486125102d0328255444d10400e90700401207412240710482d0381900c012160703130498010013050307000700111200300d0300705020040c10011802c081440903020030010000145100301039600012403401c19410f01c02e00003080344c210b0b00c00b640b120940364405402d0100f06074061207104040d002100d010885450002c0114003000400c042060160f0303903c900080c180281c0c2d0b41502c2000031080f2400861a079030310382d0b00590342c200e2001903515040c1c09003400c0300000140f00700c5401e0380c000803046114050354400c0201818000b1302d001e400c042d91504420000e47c0c94802540b01d1500345100340e031a2001a820b0284260740c000b010031441e072240340144424100002a503c059510a132485 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 642508543 1250 642507293 642507319
    0x1b03170d0c0c0f230d020a020f090907150332250c06020405030a0803180609100b0d050109060615090e0f090a0b0c0d05090307020a0b0a051c0902011b11 67
    0x44400d010a640c0510b107405039840d6100d80c10390200b01c42e01c0701f40c02181c5020300190075904000480c13100b40c0340d91800790702004003040209a10350b48520080081c1c01c0019440c204035458140307000ea06540a0b407203000041042d1560401d203451180c00505282c461701c104100c00300c008015085001c10070051007076440c0c003c4108400c1d0f4044070041c0c0000b50030b036100064513240403075080d002552038198000d00f150009074401d5001503a5403003904440010903440e5103803041034000309010003070780350440303440c404031004913109008000d0302500c50000012040e20b800c0c04844d2903503a84200c1c0e403c002d040c4404000707004a62403030a130060180c210088260702c0b4420442d183c00820b80000701252a00030800c41c1c3c5013000380182001e00000c1005000310341c1d82d020700c0c0380c41e4801d00030020341c000700200040c88151644000303040354003254242946020101101c2000d0060099450300d1019112050340c0e0442d6407082d4502c0c828901001c0c20980c1c14010781d240307200c01e103d0700c07007043c068510b0305260 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 642509793 1250 642508543 642508583
    0x20d0806060d060308120705070c05060a1e0906030b19050f040603151a0a030b0f191503050d080f0408030a0b2101050c090a031b03170d0c0c0f 63
    0x10b600e081d811110802580390760303180c500801e070804402c150010b2403030000203c9880c0140d01f16901c4a500071101c1171014201010030201d5004410030764200030080301c408442500d07003001c400c0b000807280c40d145005450294010151690000d250b4004c0e41500011080508400003c4007641e0048610362011100c50001c103005040f08c4d40090400d10300e1001c080400d64840e8049070002500ca125401044181c07030a1102c0503a040c440180380b4540c010015402003070180510b60002000130b101417901c00c503070360200705550500c02102c00b2001031030302c00c008004042090b0058440d00742030600303691400850111340032000600140a00c0e80002c0003400350030381c42d406003190000c01080c81802c059500f040740c1014204207a034075500e602e088081055561440290303208880d00034800a40315007142d94441d100c01c2e078055070740c40107008004007000251515800071100c01080d10380c161203c0042080c03400747d5004000480901c0102406400410225002140502c4d0030190641c070052200800d = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 642511043 1250 642509793 642509797
    0xf040c120b1504060f0e0306040308041506081e0601090506060f1e040b04090507030608062d0c071b0b04052b06050a14090c1513080d0f050703020d080606 68
    0x40240511000100858101d421030041140d1741195a10b4001c81002038051550f40c40d0150b4001c0d020850503000100002d003a40444d44042d00004008a0003950b00c104c0c140c5401405019801540381d003c0b0850900c6108200310f60050540d000c00780400e040c107502041551080b0032054100100009441c9480a400c5a0705002d4900d00b0314655610b0355500c00d9825250020300401011078142804945c9040c400d026040c10b50b8516000f030b280c0b41d203960b1203c00031840404500b4000d68022500c18000c00c0d640c5040611450305450403e50314a01740c64101001000101d1010103030032090405d10141842c00240c60a841083d170346012502c00558452100b030b00162015191401040c3c04442045055041203000e101c4040c070901000050490a50748102d048844000c07a50044200e02603502e490524200340b01108055039142c0f40420494a00710304050300b1401095016000840f1480c0e80800504000025894003c0c2401c40ca40d40c02515031142c9140c500400410002003030b10782da81e500c1 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 642512293 1250 642511043 642511069
    0x11011b111f0506120f07060810081504030306060903110103091502070f06060803040b0313020a080a030503040b061807031d07060206041a04020a17010b0406140f040c120b 75
    0x12010038000e401d001c5020103800b0403030344580603286800151649a00006118039120070001c0034000c950300700321b412151240000c2074512180e100b2480080d00480c107014511801100c410001c00303034a01030034041e05490442e4050700810014840c1000400d5840d01d071205c84003424a4003181e5120113081c1100c0984260b5401c86c40103100103581401c115400719010000d9214a106108581e51407034415243d004512412808010406c00100b4061848169612040c030040c150a80b0a8035100c00034680955101c013100410400001d2100f0312078072444503940203200b250800c43d8140c280c408620060006040101410b40f00c85902da4500f0080f88001c2c2c26a001d103041300c60346613646100941c0d940040d90103030340310103512851011000b000b9801a10440d00541080c064514048816000524043d940021956102c1d5040780954550150900410b080c50b50f524072401c42500704140f00c1265110b580c4503500d420300450328150804640301402c04038140c0000d0490580e0041808841c03009 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 642513543 1250 642512293 642512323
    0xa0503120a06051c0303110406021902030f0109080310150c11010c0512040f090c02071a0702060f0904140609060f01020a05120c060901230c09030a05060711011b11 72
    0x8001c5580c000b0304c4030001c0301180070baa030034400410040703134800c6213114034010000180c0003659022811004041c000301d03850720250403035148803654044503003164101c3d0070403030b00b000d07000040c072601c1e90013181c00b000035008404000d500e840b0400006401c08404541c010038444000154481c268022999404070039040800c0ea04890307000000340707015a001e40902c040480326204041101e102c2440381165240d4550002c5c0b402078180601ca850150103090416542e10041140b9001a1a0034018000c50b5400341803098958810380100000d5030314564281c0c05d0700200c0c8040000070b555045160360818016542100840142d80c0100c2c1024541d942c09481d40c400c503000041100e02500003400303a40b0800f019242103843d2942c10500781e860142d4114941a0311801003107040c0c030304002554014071605000e0303282000d80c2c2d003c0b0f0f040805084082d603594008508100b10146c000740c400d9030941c4100003c0125880242c0d40c1c1c0541c81c24208101c0400500b2494902880001c0204008000c807003 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 642514793 1250 642513543 642513559
    0xe0703141c110115050609190b04060903020109090b18090102040e091020030c1b0a0b10060c020a0b03150307090b03240f0402060f0a020109140a0503120a0605 70
    0x80c10090060565004050120f610307040c016140f110b0100d1140c030030f50754000c15940c900302405d401c100c4590a05c070b012901e82d064000c00004c003104801d0040000f002551075403103807a480d500001d000c1c140075510402140307003000080101652103000d00e08402e060b01030704039580d0b100d528041e4020b01580e040b00d480311034010184025003400195080c10001004003c2c015109450880c1040e100703108108040d0080c00d1000c00c40800760003003e841d060310450700050b0200c1c0310b07889840ca00b840d0b00300190351400780b20b000c0c84180011006414064209414083c80c1c0169550100300741c07110300e208580d074964003c004600e04205500812140c04030040454001c5a103070070111000700448014a4400d105e00c0d100e80b1001a0700300d5901c10646100485101281d44036100303045c0c00c0400801c2268020000c125541c02200450040d1094484684c00010480402e28110715514203290b0520380e568004010394001940c0041140c0c4083c5140310040040c0c1c40740903d1001408542d0410340c2c3c081700c1 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 642516043 1250 642514793 642514843
    0x4080703060f0e01020f0d05042d060b0406060e010305060f0a0b0a02010507020a02010c0308092a09060301110f070f05030414010e0d230a0b0112150e070314 69
    0x5607401507403601121480401c800c10145860f5800c031310603502e12013804017080c0540c0302000d181e680074aa100e40207021802d514081e5400d00c0f0035500c4032403800015109d10207140e10070310005104d002342440040d5030400c089401c00401500002d10b03040c01c90304040e20743e40041c4040d00c5000540003401005050b001c449511464102c542c1d410894182c80198a4140020340040c030004003e6030458060b1140f040b500700a4404031905030000b00710f00e856100e42c0030707507010308020f044440c0079604445103030454000740d80c030401c2a11000601440e00c00c0c0e0600321a030b40144103c1046030004030f0444e500d0b5940e0f002a14000f40e10107902c10b0050094000480c0018583c1600049528280b41c240d88100c10002e01404000400140307010240c0010300100c107824998000316001000000200c1c112409001c0603600c6001c0003200b40c00c92005000041460810082160200d00d002501000248a000381414002d603a0b03a00d28400a02034240126024500b00e40511540c900c110380345165803100e040b = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 642517293 1250 642516043 642516053
    0xa180b031903140a050d05070314040308160c080d020318031912021612030915060602070806090d140d020304030806090c04050d02040209012708010615081b04080703 73
    0x891900540c0401c0c6018076000d00000903e00b1504a180709441d400c0c2404d01c0c8440c110004d01c0b006000c41c0030f060b0f582c0c6000240302c02000105114502c039645030412071401d0008452207902512280742400311981c1c00d500054004002d482c91100c40180050700d82d540c030b005880c0201e08a40b450308581c00700090004141a03020704880011140e0b44405070380e4002c84002030100d2242154940850000140075000500034000060700b20900e460049030134203013138403030840c42c1c0340b0317000060190f943e207007000c101c040c0d01806504000c040b104003502462500305042034662020420100030090542444070441c0d080c0b40c140c0c1c032000f10144085441e45001c0c40c000d0010a410340c0c01030b200340c62440c0001c5c894101402164243d410141190713a01d00c2c150741c2404082c0d0000000107041c40034801e80c1d0708403540008032140382c80c4070010f621049c4038074101a450840c1c4094000031781403040750b440c00843e95000103441c1d412014210745002ca400128044e00d01c1c13030003203801c02d1110340900000001408 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 642518543 1250 642517293 642517333
    0x405040309030b070f021509030a030b0a090f02090a0815040b0c13060206150a060c031d09040302060f0708040c1707030b0903040812090a060c0614041415060a180b03 73
    0x6031740e000c490716502a858010500714040310300b94240d0b0310030000c0700703583d921070f0300046488907015281101440d104d400b100d050b195045030342502d0070740c0400c01c001d003843c0604000c0c0041c09050003406080d141041030108030b40c801480501030743c0440010810b0005440111103010400301e1040098546852000b911604140c0d070784200704011544030001032401e14609011035406444034050150a99425507509030300741c004200343c0810403040c03207042c0c0381d400205203e18460f9000c1c0010345401c042d1002000e0010700b1031402c0203105010480000c80801da0601a03503c020000300c1c907130f030000301050300d003d04d41d810040803081c00754240081140d0000190040d2894039040e80c140c1010b0b0b000401c1c15010384000164800c084050800049004243d464103881c00750740c0100d2a0000701d40090525402030310f084418070030340503103034290307180520807075450301d0001b02d82d03185904000700002da0480300e5000e2950b0700003c0b207485084510b07607540085a04880501552440810240481144 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 642519793 1250 642518543 642518567
    0x120c060207060b040c170a0e030403050715081509010909060915150503010e25090e070608090d02070911160b01030c0e0708010911071b030c0906140405040309030b07 73
    0x21030800200c5c00c1d440740103038039440c59200300d80e08401c042e030703100c05080b4058103084800c1c80c05800204008404034000348007100c054040d0030a01d1580c0140084024590032008041e025100c404021000c0b4a41c0c6200c13900e81100c4020070702099240b0503042120060801d102c00034404490b0303001801d2032541d2500b2110404c7c149540c201060707070742c46c4240b50999a031038006041540022452200e2506031550320040584419a40d0340816250400300342110502040380240d82d00c112000c02c140c960280308580e03c81022400750041c800f80d1140a580c5400c00d0051104407515000108040305500b401e6804000340d5450342c84045860341080c00c81404203010a807403038550110b0218004680c0c3c014070b8000c0405581c0c0c01c10b142e1900b100751000308290f281c00d143c0c000d0108440e00104105418901000c98040000701c489403451038809040002c0d540604034045c10b00c10100607424081854a49042007a903001c41c981e034840ca41125008416000101044034940504c1070041c1e1040b000c00d80 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 642521043 1250 642519793 642519799
    0x21318050c0f0612040f02030d03050a0f0911040507030b030a08040e09060103260409060e0a1a01050904020f0904021603020106050306040c1e05060a0c0b10030c03120c060207060b 79
    0x80740190400c1c01445030003210000d80100042042c95420308000c440f0301d078824018190b4140f0001540e0000b406d00f0440120300c00003079210f0041c008500031034420701e0380a042000c800c008440061391100d0b10001c05142c0e07603105950f1040040ea010707000b0303042030007040c4008042e01c010340c4203403511070029045401048080400b040001e6480341c80042c480d03060720741004150380b04042020454002e01c0d548120041144400c0c000010b03224085d0091202508101c04c2d00c180d5860044028130880d1010818101146803c1c044135203140d803c5801c40e42c0b219400d5401507503c06140030104107e02c951803d40740c003c4d100080491800083d000005001d0388039900074041c3d0342d40d80d020143d4401d000d6902404c44034611008006c060b5044124500c8200200d541444403550750340000c210750000024000891860703103a40041000440b90300307078054848460308580310300315100c54541c04103602005101940210a10005500400c009054941d0004003550742d480f01740b5003c4003810100b191980 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 642522293 1250 642521043 642521053
    0xb130f060e01030b06060f0c0724020111091903020a091d0a12082a04080d0206010e040602092404380315030f060907060f091202131805 60
    0x14201c41002806412203402030007161041d11442d08002c0c0c00e40c01030200d00f00e1041d04210021400038188510001000300300c100c042a41c0c040391800b08454400c0a01400b1a498030a02010981c01c1c1425031f544d007241591424813180d000b0b40c1c1c1c0102f480380f981020303512000c0703c180011800705a401414004503940d05002c068206028456603402203004000d203504113190410003004d200f038444540c41184050612800c10003d0381d0781c0741203100034a006142c04030004061004440401100c0d883c4490f91004090300d41c5804860920054041c00081c8541d800055910300c940e1009055103c0040301d0002c12400c5a408885101651180c451400107954440271213039424421145100c8140c0d81000003c1914a2140d942c0f503181d200900300101c0b840860140300480d14104480091700140c14010180350074035134202407070a0410761081e4200080f10740002131003a07120300d01a00300d0740410b48c00c2c01c4141842c8001070070441a4609800d0840c60a100d404189850488224a080c050005e4071 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 642523543 1250 642522293 642522299
    0x406020d06060c0f020108191a19120b0402060f04091506050f0d0e030f04030f11040c020a080309030405090a02070303060602070f030f050c03120403030e030703030c14010b130f06 79
    0x80c4800b503003050050100b0401110313110140d4010700020340c0c01440d5150f8001a0b0100c461410201c881d100f5601c101116040d415904c94100f2250000c0348655843c9090503c61800c07992090b0800070000c024500015540481d003191916015128102180c040e11510785841d144030308020150300d12011681c2e003022500048103809003003103401403000d50a00724680940c1c00220b1024010410003240b1b42e200410a80384500c2511000d00080c41c40b034450340009641504081594a1b00803904a1107107181001e43d0302850b400284801026902490341a16586c170046110b066014a5004a4005604500300402c10b04154000c2001c43d20030748040191a4444d44201c1c0d030380159000e001c5030040200001d20208205121000c00e203072282d03040301d18400b8058082400c00100710740602c008840490140201071704443d0105c200d40090b0000c04003e482d50320b0081160401c1e05000c0c0081018000c151000c543c00c1d0403240c440300028180c000100114030320b1100500c9581154003001e482d214000c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 642524793 1250 642523543 642523547
    0xf081e100c18090225020f0604260304081504150504080301050102100b06041707152d0804020f0d052b050309120c070e0c04090c020a05280b0406020d0606 68
    0x25400940303545500e130301c9003414007000d0340c40d00381c40d4a81039034041d40011f42e075405555518000c0c009000042c41d00d42202000d2074001c610030140c0921180150024001400741080c0003802c0d0b07106070307410743c4050030944450900800801041c6540c0703144c182000700304414001040000e604945003070342164000603c05a04a0485a90503851507001000700303c201320710000c0b4800c1100c8034035100241c03440e1b1a07540c40c1c101c120204041c0e180c80820019a030072140801d6102d0481c0c0c619120381e400e4100700070b003104020581c04008100038800d42c140e0340062025124100781d541c20561140844542d08000b400b82c2001c9030760381c034412807002696801081c4540c4204181c80c0600c13190001412848506c9503031315031035002007440e03403802d00c6030b00c00004101c03e00090741c9002e0883c00010755550b60030403c4c00c1040d0380c809246c0609540c80502644001500011611550391880051446100e01c3d003203645080c00b102003001e4803000c0400c1c01e104c18003551781d0040010742c0d404e00303040010079558201 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 642526043 1250 642524793 642524797
    0x70605091b04090c030201140f0d1a01090308030a05130203060403031a0a0e04150b130b0102100209061209071a0408061006020d051e1606060f081e100c180902 70
    0x8000c0c01360704100c03010401940100250b05940201130011030604801080741d4040c0d03045411003543c020303101d000c10a654030401c8400044c2090a1800d0b120081c11500c800080384800b605441019a540002a0f0701d442d8142880a000ea030050642c0c0c0d071400c103800c0c020081c00e00d0b21408002400304100031241342c584000e84c01c00b00c40d16210038100a54640c2c4901440b0304c001507032203000a88491496000e035030350050350700340d141940c500010f10107100e4000a01e01a03159000644091040204174180e82d0703540241e8100d98801c59040310075641b070750074050070114264881080703d142c20480c0603d04a40101810548621508465240e40c50200030010303e5403611808026803c0f0405c02c0c2d8610348201c000381195180c04020806100c0e0030010000329030300c41594000031104080003881000028000c8400600c13510306c03170164003400d00c1d600903110a01d01e242d000172611507480c207040d5140b040c0140b050a1002801c20400354031071540117813280c0303400b002c00400e4040808004c20700d0601442 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 642527293 1250 642526043 642526061
    0x130902180613030b0a140c0c060f010b04050f030f1f050901050714030a1812020c0301050408040902090103060b0f0a0f1103070303090203030d11090102370206070605091b04 76
    0x1a003070082d62030340e120301d4403021001d05184519519041106103504080c0005e03801a111105055035510700110750070300340100039190080d01e0b0100c6004126030b500000a94080c1c540c1110030804140c1c1c10b20019140079030101180300680a0364080000510404c0d40d521005207000301d0500036035503456100c600f21203040b1a141e01140304450031080c110141c00143d030b40800b440b44001035024460003c000e01c0040e9034822102980b0f4408104c00746a41400803285c8024141c0c0240035506003a51803503014000d601501d002300d6070218a0303007542c0e0b01c81c5d04030b00d0080c81061001603030350412030031045a59005134214000702c0c000d2002c100602c0e20890100e00c084035910042c40c203041d000d513421009006a10026a4944400d00102c48000c0543c4118401c0c2071662410a503070307807124070000e810304401403186100301980304031004400001041006039804d4211286010705503520000704503000300e220241c051440d180400000440001d0480c10300c0040c41826440c00007100c0c1000300b6030354402 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 642528543 1250 642527293 642527317
    0x150e330c0304081b061f08060f0402060a090b030c1b03030f010909020409051603061b0909050a0603080c0606040b0f06160221010b150a20031309021806 67
    0x200160214032043c02515095403138011402203031440c0411245000c000b96015400b15010007002a107a050a08064008141c0324019141515101c7e11403103e80c5d8004002a003d00f5001030032110062040703100802074040d45a41680b2030601d0f0b203196500790001490956a00d0007d2102e04002c500001564880c00c0c0340000071126078201031240e009400c407283c0c00c98000751111441400140c09015650750f4150b03e882e1403100614500340641a2100c41c041c1d0000e8040c01c034010904039611290303004c1650843d100108058a46515082c01005d0300da0028100c0c8070701080d4580c1d4100085011401080215018481c1c011030400300100300420320f170b000c1d52001c0100300a6880801313400c10010301e035000400c0e1108101d04462003000144202400720034a0355900c214008074504007501c4100e04d0a031401c42d03410710780c40c3c5001421041607103000201c02c0e90320f5214400241810400c4581590028000b0313600590360752800c0700030f50018104d001d60703400403101070090780c14900240d480c9000c0c40 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 642529793 1250 642528543 642528547
    0x50d0b09011d0613110907080f0c190503060d0c080f01200d050702071e030501110306090105190f031101030c0f051e040902070b01050907020606030703150e330c 71
    0x24251213001d41002400c200c4030f80f601060b694521355641105640300d14050703280c0800c146490480803c2011008044c000d51382d1301031160750920b54612006403000141c40c1040d580c1e0b03407512000950710b14103408000341011072b2610041620380000c80e08000780c0650302c0083c80009264807003011501c03850040c034292100188034404840f040781e000990407160b0350060720001c1e500c541c016204240151141d0300f401103190780802c1084424441c510340300310043d01c00760a50404c17100003040b240d010f1007030a02c180350700c40c00c000107800c28840c81002040309540e201001e81d52498601c2070500351200c00c1d40460310300a80e08170110700451036072540340c10a41d0ce541c0f4045604c1e0011103000008500c00b08a5001444080b840ca07202d40300810310b2034001e0051a00940c9000b04005045100600f0301003190081c10030300c030180e03c000883c0300540c2d5101400c5280b0f00c2c0c20680d580001e040d0407642c0316070340c030401d100c03034681c50003040b400d500750b450440e214030480741c40c0004007122000c15500d8450030081 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 642531043 1250 642529793 642529801
    0x50f161a0108010c3006060906090509010b0301151403040f030305060306160809031b0c0901051c0308280605010e3f0d0503011805040305180a050d0b09011d06 70
    0x11170070840100d40021a000e42078807049481500f1076903241c104501180380701005102c65a00182060010581214451507960405101c800b40d408184242e25041d80303024540c10000b80a207400c64500607010b5802c0e9182e141c035046c0b409070404204400c0e000300349000c001c25018240810004c0c031440e8480c051a1305410805011140050000c1c8100c1c03041c0800e0203146d81c06c0300c18803c2c040c0080031079001070a02030710040411031102010f900c134a2043c11100d8150340c070010220b1001d100980c040c182200c0d40c6d40c514422904440408100802ca41c184000010b100404c41e030241d420360783c081c0d80b0000c055a0130030600220050340202d6940090105400a40b00e800d104d90b007940007a10100084200307000059418581009400e500c03000c02c0c0d020006000c150b0030b5266040030001c900c0410f002c00d0919031405041442903c2c2240c21840440000c2c0721103171500d420460003004088c245a51603409802c256100d00b6003941d40007140e5081541d588020700307501049410110b4070307401400060b16 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 642532293 1250 642531043 642531077
    0xe0f1c0210090b041e0603020a020a11010e0d081c0203090a0b040c03020d050d0e03150f100e070201020705100c09060c0302100513050c0d050c01050f161a0108010c 72
    0x54950051810002c1064000c5000e0f805580513100038503401710840105c1a210350400c050f024990046020540305100d00601b1581c001024400030b60040d04040000c0c074110012101d45040741081034009804030103000400c540c90005240382d56912402c0100c0300c9003080700e117050b444162161041d5502c10a410400314280a10031500144569180c002c2e055a980c0030503404001840c0c1516103410104194840b1070f0412002e6600c1c04086001e003135076122100d0f04041400d0041c082884d000c15240010f419100703150703d030708007034100d0280000c40d900e0040c1c0d00a01130b60000704200c80d80e020f15070032a24010000d0003007000d1b612240d180d241565040100813205c014882d00d00780c086100f062100080034203944944c40c06025941c0038000000c402d82400703881c1c415002031503809121100030250110700081480c0360254000d1034403641c5c4280317401c2890100e0242c9070300700602880602c1e10004000080c000940081000085002541c0e030300c0070418203c446882c9a03c022868040c95091508 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 642533543 1250 642532293 642532309
    0x607260c0418060e1602070b0301180b121b13020403170901021c02070e0603061b09012303010512031303080306060d05071701170304090209010203040b0a0e0f1c02 72
    0x700441c0006409991355a100c0e9400c5002e80e968400010030f40c10701e81c401c90f030500c0942c000d03000d0081500d146501d4030b00844070340e00c0c0a03c440d5070300c550394180d005d4640d034400000440e402c450390101d9100700a202c89080b5060700c12000141301e03c690201d40720401d00b082c001e583c1217030740041d00b625505840d05030084003507000c10501ca0440c0500c0361920210101e0151040360a20154000c1c81c41a0600c001c0e2102c801c00540001d100380c0c008400c0018102d9008641c4040c40c00590007240c50b50b0500e80140c88403179100f0340d0b800314180781c802a207020440384000341d4103c400490300c000000b005003801c0c0780c603031151807141c220f4414100c2c0d090020072011002950080405001d051410445440c00022500305541c0300c1c00052801c0c1201d040c1c40340302c041d890b000d010003020101010b0281e0103555560b204d9032280e0303120b141e00414584201da0080c400e81e03004100d080712075540c4400c40d00d4001d06480b1540ea590348204410007814542d0b080569090480f2000070ba50030301104096000c10040c0 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 642534793 1250 642533543 642533579
    0x608060a1d10030b01080a0209010b0315190824070306060f03050601090509090604061d0c12120a0207080106060801050112391b0503030112030504080607260c04 71
    0x10021010000f0002c0d0095520b18020004030025001001c194410040d00c80010b0703100c141d40071014800d10502d549a808480307040c00003294004111a400c1401c107419020903409000e41d0b000b00c8040310403030180712013200c11091200e990f00b1156a11064150b00705e030b40a0003104001400b841104002c5030081d401705030803e0050400035040c03562500003d20359a801c0b10a200305802c40f00c240010011240691400c0419004041d09102813502071542d42d1010084410b129992580300340e100360405000d1401c0400b800490265602d62004020750b54540318402e0400644c80c1c403000003500ba100d040d2003416220140c2d40c0c04040112005103d02601c001c0902203041f610b4195000881e07420350100502d0469551380e140250031060300054810300e440440503100c4514a25400c00041e40401102e05443c40700d020368144c12113904007103585015503081a04180f288038188110150400380c00c0101640040c5180c841aa85030558000e940d030a54120038403c0707080c4000d100c46800c0e80070603012 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 642536043 1250 642534793 642534811
    0x2041410090506330c0a08071e02030d0e01120f05040210050403030206010b0c0f06041127040209180a03021c0f0c06020d0f0207080403020f03030f0306240a02070608060a1d 76
    0x240822507885c1e50814840c10760407181d0714000143c850030007a01d4002064141d02d00800540d0304040c90f000310b1348607084036064004101030449404140c0e8003418407604003203040d080400c0703440c0019544000030032068034141d11800007003c090341c8052094040700c1c20385e54558082c0540d81d1800b01c064440e82c02084d0f0f600210b004c0d2906040e070702401005803074800c0f80a1a10181d490010301c080c401c460b203424001c9004e042c0044041d15084001240d4036402c2a0f0588181416a0b6004c528001c203072a9803003581040d000b4016000249640069000030000c03055444506c0c444c0c80c0c2c103094940d030007034620006c0411101160100440c425501130000c600e0441d6004c80d152400c00b14400482c0d029800888a4410107d400e0081d400d00e040184040e000070b8008515120361a1410111804003e1410780702c0c04449121104c000d042d90802c0c00740317896001c0502c3c2c40c1c814246029486910034026680014111800200d01e460201200000c4565181c0c41c90100c1d1101100101600c0b4001c0000403 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 642537293 1250 642536043 642536047
    0x9100305031201050a06051602090618010803120c090f090402040e0706021b03010b180603160b071b06092d0303090905090c0f0d0204141009050633 65
    0x80450000d00090078600c20104141c1859030401c0c04100040346160440383c100300050020f00800c0b607900d2404d5029540481d41d0a1655841c4c00004800d03400b803000c90b030002404040000786004000001d480d010001d011340d8142c5075140c54416209003d10829554000b010340460b0700b0f5810b1100025420500241000c1845954000094500105940040010703805540d850b00d10503000d0103440e00400045000703100c903a03441c00001e040c00d22440b103a030501c502403901013a01940c0c20084c50381d051281c90001c2e00c80035555003c40445410640d001c1e940300c00c42814403815030b403448000c1419a481611014a06400c1054039020300c49841001442004031805221040004d42c140ea00118420359506070744600340701c00300094038800340503204e15900000c0415400d80d50104102e000400c147d80c008080359070360002502600880303000c4000e500c00361061010101401e101d1600366440e00b801849203071620010b00c01c240c1c81c16071808009070800100000d446d140e42d9800c950f80322000418138 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 642538543 1250 642537293 642537299
    0x50409140f0a020102070f0317030a06120b01031103060103031e0207170304150206090309040f0b1801080c0306040b150109171b03031303030e0a030804031104061e03020910 76
    0x80e01d001c4040303141e019141d1003006944215a41001901e02400520141c0120107103540e0f1100300025180d40a4203038601c002c00010f0030381100b070748040020441c416414480011038280313200107400a0006a036840103000344c425090800144c8941201d1f41079590301c2c0300c002000d00080b40741001240c02011030080c014000b60000450b80305000021005020715915407900d44e4020f5100700b50380b04142590483c1d010044408004825214000d4013664007050384551103102400400d50140b449903c00f001111b0003c885c0103080015040ea100130040320700c0a415030040554803442120014801a400c800240010b40e549005201d12501814442c3c0001d4980d0b000150b00b0080b1459218036a0050801c2c08103070751200040340d600c680a40c044d41c40c10b180581c0c02da0604110b0302000d000d020824000024944940b01c103d0b000b544c1209086440d45d44a150400a001802803171602c514103011012401c240d2644500071541c1254903000c011515503420700040c00d200400031f01c80f181c0008000 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 642539793 1250 642538543 642538583
    0xc090c1e03150d0308152d0109050114031b0702120a0c060804080d05090304090c0905030f06060109030b072a020111030309101805030a050a1202090a050409 69
    0x44404101190609460745400c0040805200040790118410003d421407440405d4009400e10b03002282941544404076070000410107048410481c80141445100d0214580c2c41e96076140c0315140c8242d1b501824695900c0c01151102880c0d0780034078100408201150058400302c2d071111640211561007414500c0c50380010307116480c0c500541009422000c078600401c50260519005015a400c040b40d06040c1030704ca01800d0b02a20b1fa031170b0f00307640d80c41c00070074040c240800a41d4010303e14020107000c00b451489008221848a1241900038131801501315240b21010941e1403240c40b040e95040ca0851450701d5541082c00094040c00601200c080d600344401e41ca03002c4481036413844035070042550352500c00181250740c280048502c6030001e10034007100d2140030410041408598402090181c410030707840f201c000b84a10007c11078031002030180551390304038004e400204496265440d6540c0a1a48101640b194000e40e0303038071034a2031500384410716041c2e0001c020240141100e40300c4a942c0c0e0a9 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 642541043 1250 642539793 642539827
    0x3280b031501081906061d010303110a0f02280f05091623091e0319121d09010306090302060a05221b0306050610140301050d1b0b0307110a02030c090c 66
    0x805103080c603070f5200610a068122184154400b002e000503d890350040d1940b0711437050340a4024030486200c1511034002da0320f60a00002030703042c4519080705550f00e0450f45070b100242c0c425180140440e0000a4415240520102c01c0044949481c04010340221501c1c7d40080c108440b80d0f0a074000313101c83c0c14140c68083e0f5800c54084040c1088840841c010b040526012010a50131034544003070a00705c0c0051506114011051075074142031110f100341d0b00d00c074040c03d000c050404d03420100d590b0000082c02203e40003600018042e4090350100d1b1235103440d0000340c0348110b90000c03030381d4007000900c200d0280c004010311889004194041d183c5400c6400c01d003a1458039841600c03015160310502a280c5000c5206409d042180d0410892503500d4410000450105100301882007940082a07400e200e90003418000361680072040a45294036005400c2d240e03041500d80400250a00385004409100052102c14160700113005041c0110f4101c2040a4240000c00d583c02c14031080c07004001c1e440103500d0b = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 642542293 1250 642541043 642541079
    0x60409020d02030612010905071a0c0f0c040507080c0703050a03110712140403030e040b0d080c06010303021204050d0b0a0f0e01050108011505100503280b03150108190606 75
    0x3000b503035038101101045490303030948140b115240d260480e004001980025500b003100c17100503407103069058144c451540c5002c1d103101c5241034010341031800c0c8801c1c40441c001c4c0740c82d90210360411048d01d440b04201c410040499001c4d0200d1010850000401d01030009880c3d0280180740204500c0105103c14007070303030884035045400240040703540c68210b40000c800003480b9448008582042e14607200100802402005203000c0e558130841151180c1b542d1000c526450307080511140c1d91084c4088469407100244020b50040c010400301190800044040350200c1c0d1004007501c0e150030b49038443c9044400040d01501d9003d9640541200c80c11603402000031540c100000001d80390700d00341080742550781d818201070402c51003100034083c0342d503065088102611503145c040d4580e55210100f003480c550f0a84000400388000d540c0d180b40c0d0800b5003141950380c0065042e01d000040c40a20903103151000c0c040c440154008500c0641000301111011000c14000c03000410a19a075030754072180086210 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 642543543 1250 642542293 642542317
    0x216060c050a020f010203061507050a0b0f0412020703081b010608060703141008031215060f0d0b1009120c1502070e09070803040e07031d0303070e040501050312030606040902 77
    0x400d00070660390f014042d0b0300c102c6018400940c074620b0a100051a03455465401e1300c8201c00200b0aa014084200440c01a00c0e91141031383d041c030304040e0b96000b1544000c650440705034944140c450482d51001ca80306040f01d60040c070603030410303801d1151203c1070f5000c203d42440b550b40e44e00001174034a408220301c1d400381e00300e6240040c880101418405400c00e004282590584184008024000c0700104031602c00084d0340c414070b40358440e103240311602c55a02c070b540c0e030340140003081c00101c041c0714900500c0d0021107204208568005501403010428081308031502080d61103008000c1c404140d120030740014410003400381060788402030b02090b8404140510010303070284409100d22050038000301e4005131201c006200f00e5280c05103d42e9a4461030107019501804140070072030030f0b030094100240d094072031231ba80c2d610544124042a6644c104850b00340c0040d104120300b00030760030548525810b8031005005803041000c1d550001010f940060000d540140c0100000201c01150380b0180001800074 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 642544793 1250 642543543 642543547
    0x60b030f092a18010806040305210a060f05010201050f16110109110f060f0406050f0d09140705180426070c0e01092a090503100207062d0216060c05 65
    0x40003481a855101410503d01c1a031100c01030101d0400000d165030702960504d00140c0d00d040701c00c01d49040e041e000c80a400516017050500140f1841ca403c00c10649003a480c0c02c011451ba58170049003607500503945040040e0075600822440c1d41256102c81294101e03040c0710f0351600325100745508580c0200c81c140c03980c03441482001d082d4544046400c1500310122005410b11103045a0401c440c0f095110b400b050000000b10401220021815112003a5020404000074000350410003038031140d80340c2da104240611800842d0929000c0041c0c1145c0c00c3e440110740040d581d55940c41c2105425070403914100c601c0d04c0c10040f000c0d501000418950740f0031031541c0a1a8642418001a6501078103c030343c0c000c1c1050032210400035640300b10221b0402c404403088252404400c02e948003c400c1e04695098021465203031445580c5400403c4818400d41003003258215842c2d041c0c08031100901c031405006007200e551100f03807a0f1034007d8101c0d0682405c443c0e078585066907400c0d08880740842003101203180 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 642546043 1250 642544793 642544873
    0xc03070e04060b0a0513231314010203160c1a10080c0d02010806040513020402190e03030a021c030e010c0c051005060f15040305121c060b030f09 64
    0x145026102c416401650f0084c0050f041074005100c003545a13580303401499554214403c199102d5542c00303104561454142d0f050305100010024005085605580713a4904040155000105200300c03440781c100124825000419607a0032146030285690998400d020035248114143c012000c060140340d440201da05054509045181456003d1900030300c20703100380500e100983d800c50300711035000c1d600300d400265980d14003450050340900040069003003880403682103284a0b01081c01260042e2a49a0482a40c03009003010356a04c10b0544d1400140c20a2142c101e80d240c0002003254040400e0801061284001d001c103403c6455400f030002c006070314041c450050090a015502c1e6202c1000e0040c000703031a0540100d0b034221440100e4a020b4034070802010071109a04040d5405554000c00351207001e000c801510a042c0c1002c82c0444040c031030710005028030609481030703800301c03001112407508664600d0580040d0380401454950340f4016000720300d440c5403040c18048034580d0300c1c8085200ea011 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 642547293 1250 642546043 642546053
    0x309010f0903031d06191112030115030509031c1a0f0a210818010807020622020a150306030b060d08030a0f02070f030203030702010c05040b07140c03070e04 69
    0x5018100c503003840000401800840c0d4042080110160100d030407022036101480810313401d2003000c400324240a1034000d2483d51580c4940d480390050708450885514a00103003594001e40b0003032044810800c00c000c18904141d0198200c19405a074075000e4a0800300191907034032426448002d455565607841642c14002c0d082c4204506034010305545100f5181c1c0c0800100c3d481c113219010342111501d07a4406207000d0310350302906221550b400042d2540312001c810141504074004c04103503003c10400b82c0007c66082c4000b8807180306090136141c3c8442c840c82421480c01c01c0404071030590b080700c0c86440105402105400f91310b41c016595130002481451428245007003407000d07004e503104195140e01f20001c9410242600e401c11403810000400e400460001c0009100c2e0f920000c02c5103440c2240c94040c0354010026505c51a4160000e0007000d008070002c5400e40f0450090190a06040c8001c4000c52081c000706014443c0c20000c80b89800301a00c0000d16010459011402036802c82080004100c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 642548543 1250 642547293 642547307
    0x1f0609051008030d09020a09181109070207140f0a0611060c09010c060b0607020910150806010c0305070303290103110c06010512010b09070309060b0901060f050c010f020408030901 79
    0x4940704200384506400c0c1a001a124030820700e261040d941c50311402402e40d07403031042d54401030600d030400b0002e0003078403000b42c03a90703800081c01038420602400c60541c00342016800c441c403c0f00a5806071030300320705200d42c20060704040d503052600304d0310308080b2200a44860031310b080a02141e40328901c00c000c075030120703510b0801c0081010f030109505100d001902c2c1d80054803911003652103000800c1e501c5440c0d0100d1142d008410000c1d500c14040340c1808142403964000d1000c5d1680030f00c0c0c00e07200c0c101d200000c0d103409206591003400281c240f28004042480740010b425114403030314021a082c11816500e8505407030308011041030b0000e81c1260082581c2510501c0300c8055100140d40c00c000d10021080c0d120395052007280d01070b080c00c1499041c215002e41c42081ea06900070711208260030440300040060140034012144140391211441c80c0c0d10f003580c0e0440c1264880e80d903541ca401c8140b01e007103900d9001ba802e611081e64998101c0d6000c41d18500140014100000095071903880708400140786c5 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 642549793 1250 642548543 642548551
    0x150a18150b0907030e0d0c0803180a06020703030e0d1403042405040c0501090501140d0e10050408030106032702130f0509210a020a0809060c011517010c0e0904051f060905 75
    0x2010031f12944200064050060380c1e8084644410002081c44c03c1c80d41e5030802007504001031955200040c010105a01a4800c1e01c0503c0310000700d030300403103c145003600d45440d00e52850050360018800100015140c80040600010f00c0810a1050840c1c8140a00369101030b1012200780401200502c2156405074801300108001d29081d40c0c8002800f0945006120710348080c21702c075440b00f06071210800f040000c8000031601e008200000d20701801d02501c00e420030f000740c100107420000f1054038924000000b1814050040e0388100c2019180d08110b91015440b81d107001c03598580070804003000c01845034911400114014140740d801c080100d07002900358004511104d0030070700c0801c080d217600080e410400765005580c55a24031a0728001500c901034030803660402c0d0700b40110900b03082131003a088804c684599a0b4145024a00c08100d401c3c0c9249130300300000505803c0c1c0c00c1100b842d000c070195411901410544850032201007180940b261189480544030740c0b204800c01c0842400d101b85680 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 642551043 1250 642549793 642549797
    0x9100b060702061605030c030712091703031f08150402030f07291c0c181508220503070c051804020603070201140702150a18150b0907030e0d 62
    0x90328105600040e11401624013481c0c0000c40d8281d980208801001103c504003007560842c2c0d00c3c2c02a901e058200c800404107003070005507030074000207800d03007843d0b2003020004c11a1019508560760b031200d04492100c251102c40401810f01e000280480c800d12064040b41e200780c80d42501ca24080c01894a0904024081b150580c0130800030044034040d811803c100d0050040c80701c0c00e0314560441c04165010761340f40d20700880392600044d01e0341719030f55020502c02d00040e12401e44030103c401d44c8c94503084183c859440e116440c9191056114411f46130740d54000014111030810351149024052a8016a03800b1209540001104030511240303921001c001d01c000c648007070301d07450b919020011140b009003009001e910040041007c05000303420841c507503101c3e031490405900e000d007402991980910a080d07104191600414031981307450041c0e00700d90010311014003001400348d40794500031210b42d5801528940da60440052540c030504028001c4c285940c1c04910300c841c0022107800d24030610a0502 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 642552293 1250 642551043 642551047
    0x11070206030105010c14030d0c08070c0b0606070303060801050403090314010c0f0509120f07050a0602010e07060e060c0a0807060b040b010e0103020a1704080a080903030433020309100b06 82
    0x1a0385100c11039042d24003e10708615103103034601d00f500b0325210f580305188050001145801e144005603125044110309a03858500c1c0e034030f5004c4195072031410b1350405010303207241c2400039800e81030050040c011503100740b4000034810b40c1d4003503903400c607003050346d08400040540d4410010b101c0c1c0800d80d04200500200204601803020324094130f0400c8001c0c100c4144000400c140e8401d43c0d40100c0070a1100504081d160320902c0584010f894440500489104904200020400600c1440f030440140f180d00c00030b0009a0038006c0c1a9000c1050351440c50380b1150030840d45d050300c4c40910045070214400c00c40b0b592a500d40745815001d4519607115140154640000180c6a030783c0f00140640340310081c2401a903070403900b0000c9074000d0b210802c2e0078034106610103220410031074100034a400b03e21655107040d0385d125040483e88a1000380c9000d06443d4142510381442040303424201a501d0350070104039405640c0008941c241d8008484240494014072140a506007081c010b0140201d002c41c0d900b4 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 642553543 1250 642552293 642552307
    0x605060111030f2a150709030219090c030204051e03071a210f0402041e06030305071104110d0507120905031309061802030a0608121b07030b0103061802040c050d11 72
    0x30340e50380c8000c4008269440045c001ca820300f030107008040b024540140100c0400080000c0a441a09081c0308880d0701e9854021040f1074284a1320135a0140d4000400d458114518038900d540a60510140f455160194070b000243c60020300034400b2030100c0c82d01708581c0b1780f091580c114400b802041c000c44c039081d8441b000c01450b800d030036680c180c2c40350741140c001440b86900780080e005140c42d900380485207403034401c0c00710500d40c0020107040c0862003102d1010b80500c07620700b8130042d241103001440043c1c1040c06203c0551003c2e8010b2680401c0c03c1c94031135043c203001c030385507000d6402c85ca60548194000041c5840e400c0c2d050a43d85018201c09402802081d00c1c0c800004103e45d04040030280a5038040086100180142c0183c0000c184c0d00e021218591183c0701203150582c001502600c1d2200c9482262540110108148003101e40103080320b109d5070302c0d648565010700031155141d5214100c080c15100103a55074822054200c9d095501d25443c4c520101406085918a050340074824500f8040c2d4 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 642554793 1250 642553543 642553627
    0x9041b080a3005071b080c0f0301060f210210050406020609010614010507050a2003190809010c060b0d0605011502010b030a030e010c06140412030b010c0605060111030f 74
    0x4182c1c501e40c601d0070580e1666641400305503152041c0c041001000c240c2d000040070b120004a01400410444020740220180320815080310301078801c0503041c004d9003100b0442c400b40520783c1d0003101c2c6089a0a04541c11640c000342c0841401600351002c900b02040900546504001031940008880000c020140c184038198480a840310354080c10408002a80300411009215484540d40c0c0700315154400c0c0c00c0c541141e040070030083c0e07410717000e40301e409158901403c4041101e04038981050318940740002a01c011641510742400035a900340d1115228012500e41400680340d40380075000000b815410324050141400602240b281168144051010f81d940e0118030340039202c0e0300d0704225216600d40345c01640d00c540d24442c0075042c285005008110404035510451140c0e01c540d00c00b2280e080405030541c101e94512682600141141c54a80005542c81e40219040329050400c2140c0c00981c48500d0b03d1580054141c0d50001c0d408500d50015040c450030440c400121003100e00c03a81103a02540b = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 642556043 1250 642554793 642554873
    0x32d062c06190b120912041401030504020604031a0f01090e1504030e131a0604180510080a0f17030705030406051302060d09021509060909041b080a 65
    0xc06032107107405550001001c2da600034400020004842d04984460500c50001e001c21030850300700406025100040c0320154103803007200c040d940040d1000319001d00e030b1001100244030041007240c200303104100c007001141152801d07075547c282c401007103400c1d4903000601901e4100182d200c14002818020058030100e8041a10809101c3c0109000c5143c0e9540c10222481d10305060b6464219a451880c407180c40241c0d0846802512150000318107294004140270f000d1081d0b2250085a241666545c103095880390807140d04810303260724500080361a60a01f90802c2011801190803416000c1c3c007004101100f540498401c180c909030508503d80080080d24510004000624240d907520000359050905083c1c61041074019159503100d5040c5140f4900410b40342e41c059101d841218081144ad039402d008882804030054109420710100100b481081c1c04080c000301c2d481c86c80c0c44411202c6d0080c056403000103110403001010348010500300340c8103419240c0034003000084c1c241c00b0517544a01c9401 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 642557293 1250 642556043 642556051
    0x30706050a120f050906010305070e0f01031b230310020a05122a0d1401050a0b0d0605040203100512010509030a1b021e1201060e0403032d062c 63
    0x203100c0059402c01c07858100500f80501c26411051030481408281c0e080002c40c0e0b07068920641c0ac507182d042d210301d062165820b00704e805000c505144001440020311509031102c0d403450440c1640d00c19074403549920981800c000082e9a5142d5a06400009107001c1040701c0c40040d41441c00c43c680720882200400c00c0c880d01580350001a0050040340b003515001004a4400c03d403034441e066500c20001101b451355100000c1c40f60305030b04200c0d000650807843c40c0464100d80e0000c0440c000d036448c080d0076109680000a10002d030a40e5414005000d80f218001584a00d0a1035402a006420b00c02004851440340380012590782c986010480141e900008035544a400ea0034010221000800030b403e0075051860000d410504407540400c602d0840c45040c10041c004a0b024000300b1000c202560880b4410310401c0d40302141c01d80420f001c24026031080c18011154a001c0e420414a0918451800c030441070001441e0313540d403810481c0740302205295915030002d131200c5c0c0803902003403080f40c001000030f8 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 642558543 1250 642557293 642557297
    0x1110a020607080c0d0503100819021e04020d060509091618020d0f0506040608031c020c0319020a1a060f0f03011e0e0601060c0507090b0a090e031305030706050a 71
    0x46031000e00c004401541c540350264000c80f405c201440c0b600604642041d10401600c40210740003260b40500454800409401d900542e003440f500c5400f000307004082d82c0e000c0308484941140c40941c2d51181c0c0000c000918840c2008100b0b545044280800d02600614201054001d6050816002154001d42045800c11140003503070110040d0064001c0c030892943c0a01c10740307410f90850b100070b0190003a40c0b041c01c0842e03040206596034042c5540380c0c482c103100210348201e03141c58103000100d940d0140c086105400c1c112820300009250307000c0b02000c2c40d1280d00160f884201c002080080011a00e80c40c00e0b01c10714500036a050080c08503c00d41111071a20b807045d0011048105981c900358484814902e581a40d840d020f044684101c00610651031900f5503400340c00004503c00d806007400d00c2e012544074004207c4140380c480c0160081860300c68a9078003a0380c50704000f4480189015000c2e8512041d0007075507541c00903074040001880c003a40414001d0308141c4040041035000b00a850321540343d4 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 642559793 1250 642558543 642558547
    0x3030a050c01060b03191d030d0228120c0201020913090611032701090b070804050a020603070504080c0f01050301090c0315030501050f09010218151c0506040b01110a0206 75
    0x1072060a03014000d81e401040d0300210100c00c02c035140510000c2c0041240500f0303c208040a8400d402c292468424540c0035a00e500810040064840e0f55000f840e500e82c000800c0c1e04080c041ea89000c500342164981e150000300c100c0c0551351001540e110780101c90f0060700086152402d450007244c03c10001824042800d82e43c1e00001050140f0750b0400382072181c4840c8410b40e40e203071030007807584410f007610050340d810b0358507803498601030a0520030901c1d02074101c0700b00852381d82e82c080101c3d80c220300108200d4040c0a0300c909600180c54100146009407104e46031540c0b1603040007030461400010400d081d02c221180004041c0d0359821000b00da05444019601090a000500c2c095029140144644419003088040002841310642c02940100d00c0c0400343d00582d01c0c1c1c098543c0c00c0c1e00403031344083c0c071007807907000600303401e10b0916079101c154241d021015080c158001c0b0f07056030384102c0d68808040c00380c40d1804c02201d03282500c125180d5903024200911002000000a6542c64901c00c1c002c0c021100 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 642561043 1250 642559793 642559807
    0xc1b0c05220905070f05010e090103120c080c03030f071b030e03030405060d0605360402150a0e0f03010e030d0c1707030b1c030f12021902210903030a05 67
    0x8081d28480c080350380000d05020301441071030619690380c201d1107031480c2e0309040500440c0640c4105186413641100a2094580780d09586828881d81d1118802105101003c3c603600c001409100190480d404d0180282d51285004140c90401e0798000340b107130f03003040751000229101403094454845090b80504e465129041808007003840d5128503003002e5403100e40810350f02c0300200590000002e548080c0c40125141c07c41103072100c0f03e815418119003c241c12100314081c1110301c80c034132541c4680003c08400c640c00d0b2070324070f01120f544400030840010300352003a904040c0c10561020207240703001750001c115411661021985074041c021540309c0340c546400c2c404c404c40344100c07201d0701c603042c4a8100248906044401800801564404600484015a821481e4081e20010002a0303415071030300c90a182401c0704c2140c8280806082078034036a424414494080407403040f0094440842d00204550524609803e01d0160f51140c2900700300410080f180e09078502000369641710f1001c2c1040c94490706 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 642562293 1250 642561043 642561079
    0x10506150706360501060603020a0912080f0c010f05010803090a050103050603100c02070602010e1b0d02010c0804090c140403050a0f050703050d12140105010f0c0203120c010c1b0c05 80
    0x72a410f038402c90003501440c01041800c0701a21500358500c103030002c211269940c07906509034081c0110600100d038129004214510440908091071380c811b0641c5031030708003001030507402900300f5030422105a540c3c6130000500d46041c82081e0252400c540203505040c451720025901c00c50502801e41010b407030300c0c0400d00b40e407410807501202a0a4800030b1010071112100290703a0403140c40762400560034070083c09480b0030080ba0307520240f8080d030034007070400c900d400c10710055800715801241004181c000d0800400d60100c00350002d800c03100004503030b0004d43d54005102e003400808030340003000200810000284002034041ca0682e0000e03c9542c0c41340e0a08140e403c11110303520143c510300800c0b1000044591241d0094075408403494100502e80a88404900f403107000d004860100b200d00c0014014940a102907128103440142220040c42042c6070342c0e5079a820a400541c9269160721b03900f13040b41d400c445c2e4000d03416030f2a617170700c480f14500e9100d1034065071541c401c25000f11220060055529 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 642563543 1250 642562293 642562331
    0xc020a0804091e0e0a1a07050a05090d0219061403060603040303110f040f15021b010e040e010e01021305060f0d02160f0f0b070201060807140d1209030203010506150706 74
    0x184600703104200f0300f0103449649840317950001c0c0c116168a40400014002c4094074103c500030241c640d900d5081104c8440c00f5512544520402c0390b02080f030300074040041c0d84104503480040320a03055801c50601d0503d0207002e0f0482010411030910f401c0c400c209580e00c500e42901d60041e014640816040001c7d0481c000d035100f00101e40c904803400090108007501d100d0ba4407000c9400700c00440c1500284450201d84418501000c1000022001081072040d88500b09d40702040c180200f0000304114840c40c0c1c0780c00c44045584802259402048440700903c1c1d000f1100020081519954072b803084100c4000514480c1c1c140d0401a06e07400b0030040030000000845100c00341d4400e01c1c0041c40c005a0602c1441000c2c409000c82d08412a000014803081c4103001d801d00700c43c0e000008120705410000040498442007803802c4d00054259921404943c0c072800c100403d201d65140c20041d982107006040c203540c1e004007032900030b00e283d4008980d4440e242044503c801d4000c80c0002e81510859803614181c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 642564793 1250 642563543 642563591
    0xa0503090411092706010f0c0201030507111510050d0506012d03030e0312040f0302010c0203011407050d0e0105040804031113020c0309120f060127050a0606030c020a080409 76
    0x807038001840e05605107010904c00703244a401e014442200e070b4440004403611200750f000c0f000040c00da0f201300d0700154003c0e042550000710030700f0321300e500b507640002c05460f0032008440040808180c3e41400041540300442101803e404e54900c040c52406494080c0e580006100c0c500c0000702d4550740b81c0ea81c42a115181c0004000480c0c030480b0240da84c1401030529080e0b409152080c0182c420380481e042d94030341200c003104e84094000100724035603001900d40f010343d00da0aa0f019500c0310803e420b41c3c2a12640300d417160700c03144c83e00c0f034a424030118100c003102d80800d0480181d07071400c0184400b041406040e10100d9502070b8005841208c00d401184028031402c015055041c000300d018a482c42010000d848565829110b4150150412011650b01c1c010120301209640210780140710090f64102840380201810f0700540f040141c5003e402c0c1141d004030781080560b40d903990188203e641c54021071901c0111803000702a90700944d00c5c0c5400c24800ca200c1c8240d940c2c0c2d1090020000b03426520350f9506 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 642566043 1250 642564793 642564799
    0x5060a021e07052d0d120e040f14190614060306011101050106051b030717030601200309181026120310060801031509031b050f0f0a050309041109 64
    0x20700d03c0c2e5050001c800303c400c0958100e610040c4081c0880320705010743c080c0c9416030800300c100106e204060041d42ca2145c400d00654200d0b4484907401c1000b440740c0103840341c2d0310002c2481005071401c03011120030410804c0c00d5000315070030264100030380c0c06800740c4401440c800b111200c0d82d13911010b005030780c0b0003d2500d03451419400c1000000d4102d8000c030240c60080c0c003076042c4909426114040ea9100d20031182c005000400e84007030391031205c6010000e140e100d50181414402c1d1041340d080c1503132544103450f29251944c0005200c00541c01c080c803074081849501852095641440c2d11107100c20301c0307240110502184958009588010000c0c8000481901d02003564050043d00000700e50700d600c00c503807802c280304c031411002451610600e0300c181280d030441d2446400054040500c00604541030090f0100410b1070100720402030b14500c2151020b110310010b003500380c4141d17116420040b440c0f072241c845420084680780454408011034016800440f40003038180e207003040048150286a90440e0 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 642567293 1250 642566043 642566059
    0x2120306190e10051002070305070b0d0b0a081f0507020607111204180b1503130501020906030f0a0f0b18100b0a050c0c0d02060706020c10020a090302010905060a021e0705 75
    0x110101c0d181c1007201922805d4420703151303050801c101603a070b604951200070301d50703030040600300b10042850b005054101c9840310701107002c401480000301070000e07d4110400360741084020507400c0f4080b407070b500c481c5685040148024540454065115400281030300240001c03000c042005030814040e540d50354802425041e20f50391184030110304401c002000f400114901110101c85d443d0003203081089a03010240c0915644d545c1c0d07060b00c3c2c101c280ba40304656540d000c2c4040000356440001030351040034069060300252400014003c1924418120507000303500c0c180815883e91900102c846011071054140c040c2600d640d04100c2e42500c0e69404880c888002140c0255800e42c401c0041940750200000c4403840444041040681078800c600294002c2c2c0c10031001c000910780ea0041c00303045005800383c0d00703004084540300b01030b68418122000007070000d020038821583c001c848100581000e50307203141460801900a55108140044441018094002d040308284200600c1000d441c02601d011 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 642568543 1250 642567293 642567301
    0x605031302090117100509072102041e050a0e072c04031701150503060f18010e06030d03050f070c02030a0507030c0e0c070c051201151401020106050102120306190e 72
    0x100504002406032215401902400c000d0340c40175001e05409202039801401001d403810142030030540070340000481408203035804002681d51031081c5242c58104924800e9102a0b04010030b044441c02000c01c25805d14040c03c0d10680c07840043c60500340c51089401c01c102030164043d100d145d2408c9c00c90304070780100507420041090760045030b00a86c056450a48130999072a080f08911412040c0c208034001001400001c541d45400c03203544038920030140014400311030210540e000350009030010042001d2040500105041c00c01140e034100d440c52804002600704280320300c0c665900640641c00300440d03502010190741c0c0600c002d881050303001c41110003d5580b0300d051210300005104a80d042c085881c0003c1c004c82021085840a03540140030509085c10181000195984025403158666039440210340400c8142c50110241460074112101c0e844440d000900799489504401d0454000e441c7c0b84c445d03560030740284da8000b04100c2e02c01d000340ea03c001440440e642c055102070740b08000b42c4148 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 642569793 1250 642568543 642568559
    0x50f07060501181b0804081b060a0c020705010507200a15030903120b030a0f03020f01090c05031902090103060c0c06020307080402040e060601090306050c0904020a020d09091506050313020901 84
    0x1c641101e1240c08188940d094000019000c02134821034003021800d40030000e0002181040200440c0040c080c54444403c0b298000525100d02111a180407035900c000c0c1028054040011000810003403804600c0c00b1000c0e034a080a248986041c0c54009144c40d0540000344e68002511029000b0401c002d02100188400103000e0034040100303070302140010000c030700d01402c14020700500050240050402402d00c0c0c1d00d0030184c00580b07c040d011400381101e000704010b003c0c00f440d00741d207015407101c205c0e00b420b04c0201405e0030300300802c65400105005c40c0d01d0040c1c54004185044903004440000d003842c0d1442d09840340380d00c0c818010900c51002040050b1607412884440c09580255400c100032045190440e54443e01503d4140c007040c0364042c2040054000c0c2c0000390309c06041c455003428031001c080841d0a90b000b40e44001c000da002440c05507007040d408100c0310018031041d0010b001c08034001d6006011410705000d40c4c0c6c104480040004c040412002a09044650151000040c1d6a4030101 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 642571043 1250 642569793 642569819
    0x1d0d0f051509010b06162604061d0f100e03030f1c050411040c2001020a110a02060f0c0309090a0204080c0d0c05210f011406120c01050f07060501 64
    0x4075510103410110744140014410742d141600c2c0a8825440c00710080c0ba007000f801a0701a08484a40c01d0100c0d0702c00c135020780342c24072071060ba0002000b0380f59418618040c00702e01c43d9100d0114055110140ca0005545802e0401e00c0d212056494418590080f20101c5440814102c8250180f00014080703440340c100600500110015590482d60300480f00c51803c00c0c0c2e8402d5502900010442c41d00b5541450181e0040c0076003e003034240507500301103c00103a0741d904e040220702c0d03a4503580820600c0c212070300300342c5090682d140d0b00098070034160703503a0000c1c5c0240201c5a0005540784040303007031031310060304100306c440741c0310000c06049840c0b419509003406944540101405401381414580c040c2c18401d08905105038407e0905c41c125052605001030f0065007080203004000320000d04802103018003051043ca4101400440c91000404445d809228083c024500600350303d041c0740080728001c1a6205114424a42240d0311003101c1e9040d00207000d0150050030007807429000241241080d01 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 642572293 1250 642571043 642571063
    0x51e0f030a0615080114060904110304030215091f020f070c090e160b0a021e0303010302190503100c200a1b0b070b04050a08070b1806071d0d0f05 64
    0x814454191107070500005000d8070b101c503c02044807000140030b000640c40c0c0c2001c00b10005014142040794060018095521800b0720030f0307d04400006102c14540c0c180902c170b224100e01c410308801820640201ca98420706c11000108403030305100c1c08031075543e10750110350440041407505600e03001d41e41011108580d9611400e58075a25040c2d200309514800314022410200d101c0c40c0c604034610306103018880c4ea000001180460098409440311000881c10062303858007140001d580380c2d0b042d841403104400401080560701d28044104020950b03000400b0001ca88280314040b5800300c94640a80f04900280201008484000000e40c80c0751000030349101c405000c1c07c43c0006001590303142e004031117524003490006440402104001c1520340640030b80091281c1c045071a69a8140c464180740e03049010b0840b0340f07071403000c1803000d600383c0c1548000d000182040580801d042c03d49025014040c055501c0300d880c0d05d402980004d070b58a01910502c403541160030300419940900c2c0a036200c1501c01 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 642573543 1250 642572293 642572311
    0x80712031404120305071b06020c03040504110c0d1b0f050f06090f01050105120706180b1207030b031209042706060e0108030c10050a02070f03030b030c0904020a06051e0f03 76
    0x3200003508070f03107c0c1c0c500d0305240351004046250703650a074a800000c0d5001d000e02d480c0c584010040002c0d141c03180d00c42c1c1c40404400180303031501d40900c4052a8180800703418001d041140002d07640700d280c0100140440c00c181c2c030040d103000c0c51569180c0f2a080002102c040340480c0035100812100c00808141071950701a528001c210980e210000c212071342003945550000c41d485000c0504c4100e02a00100106800704a41008401d958039210403c0343e004185540c0c8055004003840201034040c0500303001c0076400c501a005070300040c41c0303103021401907112940c07080351240c558614403044409800c82c200340701d1940166088050814001403e8907100301c4880e05400d8000064050021007980e00c541c41b1074000d09401c01c840070101000d0030019101a807025401c10510f00011144940108450310035200402c2c011540d100309801c207803103a42071031701407840303a820030006a80740b1603198203846041c14815120b0b2006511014004030303076000090b90f01e20002d40c801101c0f0420002d0f6100b0b501c84 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 642574793 1250 642573543 642573551
    0x608060612011b0f170103050312100f150f05032802040801050f010510020d171b0705060417040803070b090c060c010506150a230c150a0f06030807120314041203 71
    0x140f45c881e80000400d210240c1290418001e2501da90200301d80c15400c40d80c200d202a41d03064481c10f070742d114110650300c408215507143c41824103503030700105c1058002c0b120b4180796095190200e030109420b0440d078400c543d50044040d0248000005505507005040144001c10541ca443c0c212402e0701502030281d41d10480110802d003008903c00a50554072503455559262003c4604462002800d40a0f20340448000c0900c12402681c14200c05413603468000c02c0107041c1420141000000003200902c004e64a280800c0280282c403c000121151300e03500c00348000040d0f94412406042c00b04510b0f9840c1d015500007006040c21b070054000328029102111040300119181c5c52034055407003031200131000701d0300d9102c03140e0500d4984e4041000c040041140107140003400302c0072904000f5106c02803402205c100c0240f10030420240310390840c110f5001c1d01005881e0031510f40300c0142c000d0710401441882661030242d0f481c1c0c401d420058084a403904018068101442c1c14009940308151000002e0b01e0 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 642576043 1250 642574793 642574817
    0x110f0f0c0c040507050703050313171323011412181b0109091505040c0f02010e0d090e070309080d0204060e030a110d020303120702010204030c090608060612011b0f 72
    0x26100c3d01c0d001c0c480c1c07500d400d89002c8060381d041e182508018840303251548040d4a04002c24903860b1112160510240d241d950340d0401c030320940340d0711450340141030004c031000600c140110740a0b00395103080c2c001342060046603040100701c00540c481c00028802c2110f0398000d011101d0f40815031003030202e0302d007025102d91101648138200c480780c1400104d0300180c0091030811031940503034011549403821491000c040c1e07440728042815a903078200e030701000a6100f0306000c0349a41c28459aa841008031000c0c1011b000b000b400140b4000705805001001ca9401c4c011a0620b0300a5000d0070210340d0042c08a610f4040341d05190000350058400e034000310b018545281068500070699980342940a0300c90b131845619081071001d4910f40342d108982610003000b031100a2090742a24520a96090b8009603650b800d44c585003003e81925400f008070f90307003002424413540301e000c02c3c032030352012041d10900f6030300c44501c03140b0f03004d00a40010481002c0071440c80c0843d265000418100e05131040d02c40d1390090764 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 642577293 1250 642576043 642576049
    0xc02010e0d03050c18040e010911150f180102100e030a030605040e070e2d01080706080405060105190b03130204060f0b0403080703050405090c0d060f060206040303110f0f0c0c 77
    0x2404407a6040600c02c104440d102d0101c100c1244017691002400010304a941030030b2080c00c440c0982820b60380456859184c10940c41c255214641c848481c0302910704001c00c81070170581c40d01500ca0b81600443d00e2901c0c00c1c242e644204070005044850701d8050060100c0104040c0d01ca6000c0300d8030742e0010f41010408107042c14640110304000e08030700000e03d43c031498048030f500400b6001d0004240319035150440e001d0740d28400d04601840b0320b030000312045545482407440c03620f60320b43e10030003c0c0031150301044086980070414504603001500c042e202c0c541d050380744000c2d0700d01c103420044450102000740300da41e014000f031200c0400c0c0700b40c60030442c075911400b2101c040783d00c038071030003042500800c41400000c0e0000064802c161280c1081ea043c15103803000140e20301d0044811010761000070a4102d5848554000e40e0010300c280c40e61201c500d400c140000b034841d00003c0c4013070300381603e8501c81111222a602200c03140007150700d40c0c54a41c1c0030382408124550103107010045601c140741d80c84a80b45 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 642578543 1250 642577293 642577301
    0x5041101030e1903021f0b030f15040f03090306140f18030418110a050d0f231b03070c060b060307050a11030c0601030f0b250c150c02010e0d03 63
    0x201e41c20004118450002c142000018061502241107006d000010455011400501c00c8110410f850102e4060f030b6100c1032629194020300300c140117600000001c007a0581c40a00075030805c1c2c000d40c00010a07a05410103685510840e4030040549160400003080c000d950100c0d00c2c0a504000c1142d411501c600700e14803a0780c220204a036490b60806c01c03040004009008103400060320408002c00c00034181e54020311a03420400c40103010031400112682007444502c20043d444001c154100407802803c015403108500241300b14a80904050205200b07811135040300c111000c44a0030300340da13894402402085040e81c0701007161401d041065444d810300d010ba00781c82c0701d0092995018100301e60030b1011a0054004114912036010807c24100d2185091110f207000c2c42c042d03170860000b5005807400c200c2c215002400042522200341d610600c540a0f54a5400040420311f011a0b21202c04e042910500c449044004841c92030850010813250301034102d0992001039a0586410039051711054080e1 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 642579793 1250 642578543 642578561
    0xb01080f16210c03060506091b0f0702030f07061116031109070903060606030204061b050d27031a01060f02030403031211031f091a100e060d0504110103 67
    0x140220901440641c0481d1030711030881990925508100d020743c0c591042405641e0410b60380d1684403020171950341410302c0005c0e080043c3c0741c0c56114960700c20851007050f000c1c00e000c88414040004014041d59010080640c500b0f101d18281c5100c907903038284c05014105401c1410541d40541c1d048503004e83c5070100200116508980c52040441b5004100086010020615003c0c0680d203407000c801310b6560310501c009040302e900c1c0140e807941045005041901c0703400e032101e01800625854030005401044800d0007101a04295804900f0103000c00b0b054030800d0040503003051341c2940042030200081c403142c14002d502d8812001e90362584011543c9460381c02d40b4902580c0200400c1000a104055203145500c00c008000ba0410a00c000603a5a80c001c3c1c07802d40400800010b040701800c07842e401c810080c103680008010555a05480120080e5116a5140310305001c00c11000c00303a00034107450484080007010107a45404140104000f0319040d40c0503103410296035081c031260b500071b00c206000 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 642581043 1250 642579793 642579823
    0x10050a080a09030c2109051e0d0618060204050f04020c0607050c0102040b0f0d0c05360307180f090308010b0711031b04050c07030e060a1403040b01080f 67
    0x5103503036120342003000c0c106400049003000044c00301100441c00b0006071039850802c41c40b40105144800c10002d002d001c0980015114400103802c0b100810515842524124816181440e0051050414030024030540080c0350032544000107910801043c0d60003041035070b8040311910181c0004d1800d0004030b000d4440494000d0f40b04801080485014501a000d60080840098078041c0c651060f0303080b42d081654001c04207413010402c8640c5610600402d54401900e20b089824208111000030414421381e580604402811702c0507102e0070704104001e24084800350440710380980e2035500592040d40903090501042c13400c01c041800740054000e1101d2a605540e880c000380e400c5ca0110030040d031160740c08480700c0364414005d1441c2c1d02e003408000c04492000d200c6c0702c41007000360144400d4500c014948482600c00f008000002608401014003241003078030150b0316180b0440c811f640070304641440426004001c820002003060b240441c5050750701034402d0300d032001098005140e031a4015614015 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 642582293 1250 642581043 642581057
    0x12460603081b10060e01030b060909030a120e0607180f03050d111c0e03010c020f0a060b060d0603151b02060a150b07052103070e090604140907030210050a 68
    0x100c000c02d0400045196a2808156000e03200c10b04611021210158410500745070004010001e1287c0d0312682e55115109983c10b003d2860701c01951a22031060000e03a01c14090504508460703014203074080041007441008440d040d04100c4000380c0669422044805440c0c0050f03000700b02034405200740400c82c0d5001c00140342c10b5444010940d949050010125014420356410b11120040921a00c1c54514103840c0c20b007038144480300385802d4503041c9100c43d0942d0b0ac2031144054010780020901842c0b41c11680004903000c070800000c086114610020400c0e0f4101000031007800380310f00211070712030007035401044152110460102070a200c8035858015070800c0000648130043ca0300000020786160a04a201039240c91407148550404036054030700f98403002c60861840014422289141c95500381c142c1145030007200180780d8000c0304082ca011b001001c01080e59919941c1002d05c54448510964100f40380200445070350381c42034401a485a003c003840006824007130021540c4489855035080 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 642583543 1250 642582293 642582307
    0x60e0c0a0f050409080d0906090506100609151112131a0304020d05010e01060b1201120f030c03020c0a030302010207020915060f18151b0c061246060308 67
    0x70041200380704c156045030040024026000c1e25200b250346403442900c00040c0103c01b8108036260000040541c002c1840c5000140241ca4100305506c08036180f22445c81e8001c2015242160940c5210780142d01303610510500d01110030b000390190003040141c07202a01c803990344041c1101034001ea5000c881031020b04101103009410a1140007240c035020704000320f02a0120102d007801c4842e90f03031104e941044040303051407000180d91001c40c010640c40000040c1c01c006603e070080c12a042000060610407240c0500003018001d21015041071001020810b40e01d9503410064082c1d400000120300c0b03490204001800c00001c6515035031460b8000d08ac041c10010080000b603055406042200041207042c02d00700b88940d5a0b6428081010224003c0d030346503042c1991040c07015a20011100c1690045442201c05071900304c156007032401c5188002c401a202c2c0c208030820b41c19a404000c80411003400340d00d2102c15600d03e112242108090b00a080f070f6040d84a103011129180801007003504200450 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 642584793 1250 642583543 642583549
    0x6050f070f0f051911160501080603010509330705031602010c020607030e070e07090810060b0a030209011b0303020a020c0609060a35040c090b0d141504060e0c0a0f05 73
    0x101e40495220b042c0080503040d103c40fa141b40c0360405984140d1040c4440051100f560312001058100c50164002e1055041152046840c0c829095480e61012000751052401d0031801244020410301100c00c1c1c0140d045c60b010003445584101e4121924a096041d02144184140f1444c00c420303000340d01401c1c158071644011005420a0a514011481180340100b403929120795200c0c02211951241b5160621b0705c0b00c66802d02002039025490145080805c01c02c0600e114109c40d900c24092400507682c0445000590f414420103150003c1c01010301c01480801d600340d030041003024030070313002c9841d020f168404008035482031000719508030405200020459000c0c000004050307010f11602d1008040780260200110781c10104c0258901c00034050000380300000d400350000e440d000900340b01504a002c003107004089148002480300001440c1814600c005101d80000c1040d080c03491101c0f410141400400307044082c0704d18800340211400301d9002c0c50f04403020011203500300c0000c210a86000c0c10 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 642586043 1250 642584793 642584827
    0x2010f17061c05010f050103051e03040315060b030711010510080304030204020307020c0d0503040e10051c0c08120705150f01181112040c1403070e090a06050f070f0f05 74
    0x6501c14410202e0215001a40038010081c0054030b00e500040c0e107601d1810141e18003280b0710f1101203001320400c1c10743e00b0312001108a80507260828201c0f0100c840c50498003000f4103e03a40018210000030092242a039408000d103102c4450301e000034011a12a00c11451080380300348690482ea40c02000100010705041e00070b503074007000343d0068803000104007003c2003070103011160440b4a0381001600707004075265892066008202504d40c4030358141010046002d00b090001c09569080361540c802040106150001000d081401c040e41e03080c250f000300310012900301c0b070021a240d008031083e81e901c08010091080c450514408000180d92070b0105440071840c83d00a020740460300d40c08060110141c001c01440c0f006445000c0300783d41e150500300007000c451681c00080c003131006000400c42c10740d000910942502d90901c108080c507241e00710050320b09107650070300914050600c0b0411100c498200c03207052291889840f00910130144c400115050b41d065200310005c601d0610180f0800248038035 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 642587293 1250 642586043 642586069
    0x20f040501030f063501020301151101060b040f0e09030702030d350f0f060609060a020316050a1a100e0c0706052403011b0521010603050402010f1706 66
    0x74001000d40e2030301035005d80c030020515056401c15091072900350704494245000403182000c00214215410310400c003501d114100c0070441001224546445054000e5106100502c250b000d125a680d40e909006100385486204405a03a18140c1c0042c59410000c401c860195070300070701810303951130003c8050b40d80505141c0c810041310f51038622045524030f0085144154010007080c0001c901c2c0520920311075070801045812014021070031f0041d0742d00c0f60f030140c3d0343e0480101c4a451300c40f030342d05004030f10718082c000d50a240311010305501014800c0205105c25120302845c0041007a280006c04080411000d07200d450200103480000c12010809600c0190407100701c02c0014600443c035100e000546800f030b203400000740704c01400d00cac418035404001c080e1000c0d029130081c401c0c440c410010a0030410110300c03000520800240c00d001819185016000151841403035503403550711000006c0091104179000c030f020035410201e445040303002d20011281d203442c40b4a9059150f840000740014007100917 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 642588543 1250 642587293 642587321
    0xb0a050c04081219110604120e06030a0c030b0a0b09041a100314010501020a03080f2203020c0a0914040f08091201090c0506040b03010b07030504030c0324020f04050103 74
    0x1010120b6402000c0c030444201409418220b600c03041896691800c0c1c590440c2c40d601401364800e14500884030100e80c255025800c10049056403110500969080310070440303282d48003500200700b2038869030a5122001e10304684c0d5003040406200c0003442594440c50140084811051081d0000e92510342c2000340d072038142211200300b04900f04081290001c1d809440c40100303488125020803405401e5440c1d00501e401d01c010565190b160310040c1800d80c001d0041e6004445060005401d4070320b4480c0100c10003851000482a0b10450800139112a01c03070304068401c0f40c01c0040002d21020314007a0800602c0801d5601e0042c0e11250b0f41c60302a0b041a01003160204400e12903604260740700d03100540100b05200000c50585e0080c03a0500c800401a0011449180c0500c0140703c180002d0b0146c074107481c0d40700d01403030352114913003003d846d00d02545d44024480750100034040104598102e45103840c0708030544140b200b8201000940030f0740249402c181c1340b064140800c00c4150b12a0708074500c085011 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 642589793 1250 642588543 642588547
    0xd1d03121602031c050d0e01111225090e060a05122d07030b041103011a0102011b08060d03031b020c09070207120809120d0809011104030b0a050c 64
    0x1408160569400008100c08509521030290081d401d084c48140d40b1a1001102420100950600039246002d00002d98211a50301c0310f100000c100c00750b0100500c100c852004d02c0d180e140c0c421412106180894a449808410010494142c280c0c0010a9402c8145131070b03d500950a001c080386d81243c2c0180030740c4e80410040c000140540340d000030404500961030141400d00724100917404c09000c1112629915075240340240b120803000304d4418103403540505807400d10313210303418200303c054000e007800c0e90700d5480e1000c01a911000040c100c5d85210080e0002c2c801c811610b1a4072020180504000012501900c005001440d010745801c80ca14442d04000588201040509000c0c5066810305000b5a01c990040c802e00d1401c000d40507130154441c40205801070500440c00c003882c2401400800d12103000c074210005945181c2c0c001c00281c0c2520481c0c9442009280081c02010140c462001365485d284120800c0a9824112001d51380c1064140d00e503500c4d49840310008007001082e4030310039402 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 642591043 1250 642589793 642589813
    0x305040615080c030106060e090a110c0d030204062718020c070f0303020c09040f12030902040510060e101b17070f03030605060304050c10090503010e0a05010c020d1d03 74
    0xa080c0070903000d06140030041818031100d2050500710303940d98004078140280c0154040f0744d82d84254019600c03010f500d03004600300701000003a0030f540c080c1e103020b8040c500410b98440a00d5a160303015004488030b50390b030000c1400058403c00c0e41d0051011044001d240c1c070b6a014442c0a80e41c0c0c1ca031800d1000d10031030041c90011150101404d050142e00b003c000921a5070013001855410045040d048008072201c00341e034105607803004940b11032043c00405408410007007902d214043d40c4400700d03035a00940240700f94904814548000300c0b41e801800c003c40c01401851546003022403840c04400c85a490b49401c0043c0304006980c881c0a002c008c8507994030108950b58070241000140070454821007403820854001c6c03030f02605071f8880b41c1105000708002d00800012401c0082c4d4024800740950341c02c01030f00a1182d08441440068200d19003541c03d0468044901d0800600c003500c050050008102210f10514100d0b1150b125000120010350010440c00d02d8a0f0300700309444514400a0440300a121 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 642592293 1250 642591043 642591071
    0x50613022b14030306030d1d2106010801050702030904050c0c01091b0602122203080f1206030102040f0e09031c050712060e071115150a06020705090703050406 70
    0x252a804a81c0040c011415200c104904000392040515035000a1811440d00c1000700350b4410444c0f40200810461000001450107421001102c80f00301508180c3c0c4206014100c020411001105285030301c160700000030010418405c05004203140c0d80030714505008081000b000c1c09000d0041c40c0c0310300d4104001c0700c5508092084444103481070b00038000d400300042c40d042000f20a68040744c1950010f500700c48103400c00504a58a0844144c265500404070180c01c160307891858000030050000000c6c110000170400303010b00321200003422440131a42e0b40900341070a0740038500c80c000842e55848024400000508600c03070b4000710220481c0e007806882215160410910442c54440f90364910a22000e154420120280300451890511641d480c00e01d80300305c0d07540010100e07802c0002500021503a84e03c103000540100c6c144d068070310440d0a0100d00303d148a9424280e03e44100720400000803818004030b8158211440107282c0c08041e520040242c0c00741030300500854009a9886c0078000c81c1c0c0d = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 642593543 1250 642592293 642592339
    0x604080a0605010806130507350106050307061103040918050d0915030c0f050a02030f1c051b120406090f0b0714041a0a0c0f0303050a061205061302 65
    0x36000314004507440d450102614107149010b0500003000079461800c101042c40050308901704d51080c00c01480355000100c134901420201c1418281100d4600299025140e05411100941d14114103030f50410303a0742d24041d91003c5012914481c10341083c0810003062036540d024144040c0e01b003a4501c1690030170f9a0b12400d0144070a000e00c0440c01804003485100c1e000c0d04440076207003290408119420000a02816400c500a004010880b0005803000014070074030540d4090303c0380860403034950f503001d0b46440c080108251250141407600000507032201c0f41c0c407030400354a88000c4180f840c01c4119070014058070b100404c26500c0c15102c030f40c4140004c0f0a06859034585000304a00c1c2032034200044014039106100d094103095100c18042805924070200c287e582051140301e2541e658502d515040d140c5940300c1401905d0700c400009003109158154024600c0f0f1004442c04000054903081c50544a200c4404080c00c20351240000421110400b05440d900303d0009205040606501c200d084080d = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 642594793 1250 642593543 642593563
    0x13030b15060f040e010e09031b12070b01080c031c030b010c08030a05090105070801050f060903011d0a2108070507020d020901090b040b0907141e0a0c140d0518060408 73
    0xc2440001d0802c1003032498403c44d4058010100304003d20704008810a5603070198034940d442c614226519a1185102006004036880d01c0c0f00c0d14607203922283c102070080c52000d00c00c0c14107a00540300818080d280201d2904d003480d04000740b403c005074601604400a0540410f910305204080100802203201031010f103106441e08031001c500c4d07140c10146582524406171000060002010061000e0742c0c0b07828a6245081c001d4441079110030000c1c00003809007410100307048000c03040f1202c1041175580820a0104140034040b084017081c60040c880041c43c2508000c3c80006100754041201c035440b410003000010b0006050107140d00d0f0b40d0300054007851003070780003414050380c4051007483c80c105405482165142165000d0081ca03100c00007070540c00000074a00c5140b09c00040c4540d036489009050a052090700008548440c0c8035100904407004955055602107010203161041342c0c40080c050b140c14145980d21414108075045d5011900341d01c800040d44030300144000b188002c0c04000f50091 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 642596043 1250 642594793 642594817
    0x131a09130b0f060a14070308040507080610090c020f06010b13140906010f0c0506040515091911180c19080903070308100312090602070b13030b1506 65
    0x244129500400001803010010304000e00d0401680003a595948201e0541d10305055520580d1801400c2044480c0300440e40e884614020106000d406d16910040c214030032031081c003c891000740c03101607455441d207040392801500240755609001a0300c1a402c010407100c00790040303035104444101001d080900980043c0400c890200d40d05501e03543e1841d140000782400c0e51140700c0d8605000224070280d030024515070500940281d581d040600c11880700c7c04d803075008000c0d5406420075251840e1140c1c55004169969101040418840807003c40c401200b440d0008415090b4843c564804840d07200c80c95056610001c6845400c00c0c805448200c50b110f0351a00c3d10055075500c601407920003402d4030304001420010b049003001450400003049501d956014100705810350345840100302d440309076030001010200b010b90341c09200da030844444810b82d0701e642c00f5241e020b80c0750155910140200c0d4414080f501d60041304202042410544039005803913009010a4400442e001ca112070b4459401110 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 642597293 1250 642596043 642596047
    0x90d080408101b030c09091d0d030501050103050a02042904090e03090a1502060c090a0f170c010221071e1a060603010f091a0301050a0e070f06080408131a 68
    0x140c4116a08142c0010243c1c4c03c04019881010b88001d16401841c0269400385640303900b204010080d841002d0503001c0c189085558410003804001c014100a00c80c0a001c281004041400e044407402a07034140c1e43c0d10070401507145680b00c0c8119011000d6241c00074aa002004041208032043c0035048100a80100642e0384a182500b88440c4000690100c0c0118801003107040360285d0109400d40c00c50505e9100e40d032551019800502c614203650301006000f00c000750002913140c00710041c4030b01d508688050f039040300d051000582e04c5442441d00369500d510400009940ea06281002e000c9450007902e8048009800f0703143c025078605050810b441c01d8000c200b01358040c030229030b1920b521402c2660418215403500d1a8004114114040d205689844010000d0300c5d4442d001d2242d04000c0041c0207001c0c2c0d04200b801c81004110947d9035002070700500c88041042480311203140b049503fa03940d442025680e54550311311640060306040c070f201c4d40d1241c5c00120034025010740c4000343c1c00c4106082d = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 642598543 1250 642597293 642597311
    0x90203060720030c0303160e03010501150e040506060a0c0f0b010e19140c090d0f060b100e060906090a0e0f0a0e19030e0f0a0f091808090d08040810 65
    0x284000d29642d00e0401a03520810041000351004001c1d03030380000c1c0d951104c2107100281c1c0802c0d2201c5040020300f07501586048000501c10524003410010001d668544482c4204001c0070300045d140119002c1e03400c0a41000181040c6102d400600c50842c0110313900e154003034940d035444c0c45140080e44000c3c0070f901500240100703002e40d030071404441c8426010402c42500815015008988000d080c07004400c40481c1c44200d607102c04248451556111071480200c245d940b8021008201d0980080c0c081d50300340680b00aa03074011f44400100500061a0f58140b03290542000401d500100e241600032451410015804210041d814042e6000354001c10076841c01da200003003120b111030b901104a602c04564480c0240714580140c4c12180c04d03245c00b8015014030310220302420b09009100d504404580e60001d92209001c3c60007003522101e00c2c05010320a1a102403031614884001c001c0e107220410005450715140c00c10241d000076100c1c0d107215040c507555902440c10940719811010715141c54401c91 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 642599793 1250 642598543 642598577
    0x80703020c0609060f090334080c160504060614160203060411030c01090b030a110408071202030708010b061b07050d061409060c0723190b010b0f0a080a0902030607 72
    0x41540111584019410807641990069840d0f204120340b01c002340100c0c541420045c480030103007000c40d400030701c0c6559440464041b00d6407a80109460142660700403004901c6203018060f00d0304a84840ea65011464100782290410b540404a86c0d4040d0030594055001a1400d004103403156003c2c0018482d610b078100181420b08074500c503410b04121846609000a103200d00c2525040101f80f04005121100c40118442c1840f990308840a1489003240006c0c1200c078180c80d511405100b54141c540c2a555072a665082e0341d070402c07020303078010010301008903481400703518126003a41110890340c07066580c1c008155030010400040e038a4580f00d1540d0319031005201d611980000b14400200401d161201280041d40074000c001010b4160842540b10481c3d036403407050102025010940b80780080e45240d45040c40103141c030490f18581c101d4000944445220255a41101c003c0402442c02540141c1160701c070341c3c001c10750072005035248111005a00c003006414815411501c81d500c501101d0160 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 642601043 1250 642599793 642599821
    0x9070e09240f0f100306050613063b2404060e010e0709030314070501060f060801030302070b07050a1e0f060b01021009150c0225050906010309030f080703020c060906 73
    0x8803144000c010060105a04e4490400000c0340c0d0008800190f5407107102c005a603001006010075450350816002050180c107040c0114a000d0107a60250340e2101c0c0124500c200ca00d46040700450020683e00203240b400c0d16002001c1c11a03c3c0c00d800301803082d601c00c00541240c200c0d41006c0c52401c5c450300184102c8801c003404c01e41160040c24190011442e40d68000c001c07607280e00201c20003000120300364007002025001a03001c1c02090302188505e507115080208118424402503006118589000441907200021210a190402c02614111203551554229002940c50400700d031183d0350b259030041200b02c035009000f41c0c890600810f440031000c00081c42d2148401c01f290321f46182202d094000380004400c4032440320420008a0b104841c500140d00b4410462101d9070708256020469003401c501ca0300e100250b601c2118400580e1b2500001142110031850380200454a210b01c40c500b0240a600c00c50303841203030b914025203410b501c030150600380003054611070b000358046000e1128036008100 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 642602293 1250 642601043 642601051
    0x30c0618121e120f0f0f050711060c07030e0301020d091401180b070201090b0708160f121a0402070b0a062411030906030f100e09070e09240f 62
    0x307000c1545142441d52407600100550b521401c1c45012503100807840b020760003512080c100c8003410450352894480d01030103044004030410190340307014001625a40a040601c0680b504070000300403a0b540c0e0220001d041c1d0100005405006010344000f1140d0303001d00081070250f100c0fa5000c6000c98883c03030104c1c20400c0c07006040d41c0603418a082d5000450310050066140d90b00402012000c1d100d02d04140d00400c0180005231100c9050b00c100503029400013041d40c0601004007920920380700075038040340c84080c0e070700b107000004900040c280320f12040760304150450b40342080040d034481c8200d00080c080703a0201c601210303816000001c0160440892081c7d000900c29080950b1704448050024012000b07011010000d00407807000f030402c10359003001500c0103d0405040b20340e80b8103029070003000c403540844000100c0015084003081a0040b016003034000c06000d802400094285260380c001c0100c0109020100d100d1480d1501000100c9005207403884034084d0450014140104540c3d882d1100038 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 642603543 1250 642602293 642602297
    0x31b030903011a010516020a031a10140607080306030114070309050c0a080c06131e090e0a03020c040c0e030102070803061c0f0314070c0308030106031401031e030c061812 75
    0x1c0c0143c1d40b6600a0201e6519002e030441500e6500028400245c1c641000d41018000c00d01d501a0021024443c6400314083d85940c414001290350395603041c11a81e03640803c240e00140103108410010383c0900107140c204030300070008120b1044240d0f01d01000d44007107801d54006034581b80d000302030110500494824401c2900c05405140c1014011a036030014443c170107014180004d44410320300d20103a00b070070151420030982443c888900e0a0760303400c00103500030801c403030f032070804000044040000c030510a1949500030b4110750050b00c0800c8002c1c000d03040f2000c00e00005040e82c0c10700343d8003803000344155845100e50f90345a04150060004d0302d02e48015400114003490200004981106030215816038586081011112071002060441c010756000800703400000b03c0100402132401d000d541a41d80540e400c1041c50004160301800140a100213884c5089402815900c03110350026440071a00a081400c075092066448504440c1d840c0b140108241c1003040b2401001a103ca840d45030b01028 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 642604793 1250 642603543 642603581
    0x10050702062707260727090213110c1515010c0c0e06010c02031c0e180a09170a0207050a060512072a06090b1006020312040302031b03090301 62
    0x10039080f82c0e103d14901450382400b51115400700d801030307806845100c100f0004191184c030355072036001404442603030468088400003d500c5082d14140f030300c241140250010400c039440301c9041010402070074004150780344103104022401c981c0c0c000308001a02c020314041d0490301741c6802c00c0f0320003ca500a06031a8108070360246c04102094900747c050b4141d034200d20140720039888100c01a6002807803050003d405004050300c4180d82003221050804042986d1100f401c0c2c0d80050b070411540500c1b020408180d01811008a60307540c0c125844510010701c51580c0303c4520005101c0304840360030034000c910042e07103e03c009120078109000280010882410702c10304102101040b18a81d19005140204021075401344999003040002c50990b11620603110042800c0e040c1031290192155110603221040000003003410341021503039080031501144d0196082080110705143e202e0b102400541c110300c400d22900e80038002c0c0c0d81444140d014100010756071411203105050039240c40f0f5943d204800c0003 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 642606043 1250 642604793 642604861
    0xa1101180807060e030720040603150e0609030405180a020906070b090f030f0406032a03060801150803040e07030e030a08010603140f010510120f020301052805010305091005070206 79
    0xc40c0c16001da1441f00b01c452010b060900001040042c1400d9002034220182c101d99a0300c14050303580f101e007d0f4018981500c0c020703542c0c8510541d583c8110704c1842d42000c0a203e84c00070380e500b180c141c2c0341c01154108001d4a4181c2c041d00090103074000143c00d51b2080d4a6006008040500300082d0255000203c040c50a007020b1041d80c0030140600d00c034850a1580b1000f1109404400003410514030040c40c03d8103070087c000c650300400030420b03801503a01c198a4801c0a400c800200c005810841e60701b840154a0a4105020300014040150043d42459156500300c800b03c00c0500240c0319011003a5907289856143c200d000b420345014240251079040500c083c065140000300405056a0080d1081e40504007070b050103c6841680f4000e2852403854001201041340c042d400a5040360012501d02006001209009480b200044501030101c040e10702d007000b0a502a400c02e40e0321003940e40c151019451540c2e2a03001340c0708111303210310050f0080b0b800c2141c002c0314150b40d04250120488401c01d4299 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 642607293 1250 642606043 642606053
    0x100e031e161415010315090602070512180a0308030106030b1203040602010b1507230f3a0207091a1e040e0f03030c07050a0c2403050601050a1101180807060e0307 71
    0x86c424007a0165540f10401c0c84203200c0340380c0441c1c1169501008898a12010002d0b00348a40c000c03122a6034000d003410340307400440c0b501003020020ba03074016811900d564a440381c16401050008801074012480340300101c4858002d002820080c00160004281100300b1010051045000c10030b60300070300e2003400001c01040465425400d89aa055041d1242000d1080a6841c0c07292800c64032040c2c0c403c1420f03100880382110250003141601c22100d10051146101041250360303410340c0d04005900c0720100b00b20700030850304500c00b0440844204800c08001c0000b14a0489112070482502030845200d0303807260038548200c01d10b10301a0030280261400345044c0a84030703c4041e0180c011503002150040501006014005509500003844900c942e56554451201a040700c1e031800d030f55044058140025010b805880d100384016511146082c076007040c00e40d0551940e00c1c1301c5690b9175a5002902c81800401d014410700c900500c0040c1e268000c0c1d180c010141c030703070a61901140344c10500007000012 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 642608543 1250 642607293 642607313
    0xa080a0912030c0b1b160b070503040f0605130b011d1b0f090f0301090507060e042313060f0e12180114070b010b0903100e031e1614150103 61
    0x66000380d07280b513103803103858000c006000d80000354158042c0001d0b0f8030f901c881e21138221030341841c4030b4035241c802613482450984203800708660180c11054041c0c1c040c000078815034030899118001c06c00030b0300c7c0507141e034445080d4a40241c110346040d403072215040ba010303051020041c0c0c1c44804069843c01500e891500600701d400740c40d001d01d40d40c2001081c1c0715102e41c1d030310712005155140070740200800c414909101b540c40040340301e800c010501209280000741824051807018400034030090701d107102581610100b1a200030484905401c00702a040c0c0040c40d140100c00710b1850082d0301250384034442c07401d2401c00c1c0d40b41014003142c6030204100c100c00804d101403120210070034206041e001d003070b41e6141d0b44d06225012004000700502d20000c10b0394410600503151904080c2c048821241610152000321030000d00d00c010540e00c14000070b610328442080801241801c0340d1210700305100c0904040240820110850b0700201c41d80040c40740410401002c4284203140e600682c0c45c1d4510785810401d5 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 642609793 1250 642608543 642608567
    0x9160302060d0f0603080c0105060910080604020f0102031902011a0306041a0603030d0203070206010611030c0c040b0a05040905070326071b0e0f01080d0c03020c09090c030a080a091203 81
    0x2032525000d07001003c09450b80034030000c42d0400e0341c240d920145480b1090003094100c500501c40c10800000c9140c010581d00030600352481d08009280c65100d036020051100e5802c204181184010001075000382201c900c0c8040303608650300040348007080900f600c86541020070049000c5d034070050070030002ca164110100710840070340300388094a03210350000c28290b2092441d08000c01d400042444078083d400151107041700e6841d599100030444984980d51248280010713a1f100c1d80c4011841034045c80c1a92082d001c80c0401024520340c6c0d03650700c01107019180706600136030f40c07a006600100180030b045c0f880074020768034034142a0342c071000301a04041d081c054024041c0070400c3e4203244c00891501400c07240c0180111b494603803035503e0002c0316038006d01001d000b181558061849901c9000c2d01a2168080c61036043d0003800c000600b500034028110b0004242c0c1e28544541d180041030f07034030203002100b0700d140030740303002c0e551381c400040050501d8009501071010b26414900030000f00707510131818140 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 642611043 1250 642609793 642609817
    0x2070221070803180f0a05060304111f0c060f06051f2c03072103110a02060f0a02010c170402042d0f0b04060f0510020709090b0916030206 61
    0x1000014111107450800326800603003152100040b0506060b031341e141c5070062940c0485900c94009600400d000d91088684901a005103040c00410300045420680501008010b070455800480810213507925440050415000c60480051001070000310300696070320940000081c0f10081c40c1c0404940054407403034950b90040441d000001a0754814080082c10580205861000749204541c0c252146046612030b4440d20400700000307440c6140d003490046855407280080a514082c0d1010b03105c404124041c000c0301d00481500000694401d000703001c003085101e0745951030780d106140107421210032881d107400740038030b4426100120030080816548142d040d2004101c440c01132446c600c40c00201c00c0314040040a254030300341d07002e201d81c1c01110346401200081c407071070b02e40c03a0510085400c00d0041c01202c9901d400700740905c1c00c03c5105c410111035a4030488032881d50381d00740703242190304401c400c03a0366011a20a20120b410200804008200001540802140b555000858034440c1400d4980 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 642612293 1250 642611043 642611089
    0x9010303080c09090114090610050901030b06090a060f140c061b0904050c0334110a0f0803060a060201020a1e02070810050a050f10120c05210d0201020702 68
    0x42c20010940c243d80003940b020305410000c1d6192000c030403040400f60000d50244140000042003441d29181422405400f5214641f604d80b03031703030b0045000e041074507110343e04414108204500e6031200b400e04c2000b450715644224081c1c41c01100101148043d420090a0345018440e1001d040c0b000319045821203601c1e0517400040c0864407038a10300303010725400c1d00e52083ca01420040c01001d040011840380305089912180c2081c0c0074010440e030314140d41c402d41401c60035881c1103112401494096102c0c0640022280104181d41e20f18801c46994101181c180b0f038040184680e50070891060005056940001d5041c500710070b40091024404120303120100310407490700c0d503045009111340c0c0044c110560586011101c4111000c002e840d095400f00c0100c0e10344000a20000c401e8071134a802010543c0c40e4592607854070264220886200c9826140326103004000a4180d07280c642c2c4401800f40a540391850040140d0140c0c100020005040c080d0f9004201c803c00580d07031060108507001220030501 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 642613543 1250 642612293 642612301
    0x50303070513090c020609062413090c08010b18160e040605120102031e1e09070b031311010216050411040812040f06021501150c080d09030905040207020901030308 72
    0xb080003a4003d459551915282c00190340c0d02090580c410003080080b14402d03140c0c0d80b2014000c4840d0034040441c440590301604c542c1c9416285200e408200b0200030440e400c0c02d840b0072100380324540c0150080e0390345da9440041c90400130201107411401c2c4041c1c02003031038040c41001c0001d00a09000e02080f2141141c1d0030f550f038279644010044c25018040000c07144240802500075802590000503540150b80c0316640d07004200c0030240300300e094100607c2c00440c4481c00041404000d01054068010782d900071540381102005103200b007218510342e0171070080a04145d9840b1a51000c224110b40003640610031038642150104219002602d0008901c0000041c0c480d860280c0d070001d8005000d4040300e98a510100009441961810b415101d4419551070b000c0c2e039030320b082a1003519440c4403900108090700000c00340050310402801d00e246082040e40c1d4003144c40e4054034900060f15550a11503050541c0b1141020181400307032011840c20381c039600002c040c013005200060030011140002 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 642614793 1250 642613543 642613567
    0x90b01120f0b010803090415060e011b0b130308070206010506041505070204050f01050306070c0f0303050a0b090a0e0d0201020309070302100c0b01080102070b400c080105071103070503030705 84
    0x2914503504241c0b000001e5031101c00b4a9201c0d40120702e9140b0a03414441d803c0091902d9610f4541216140e40300e440b50214000015a11a1a11142103a8100203614074101244c130560744544240d86442c007192490744c040c0340140c90080b020b054042198451130041c04261540e20840c3c0a070358481e60740c6a440c485c105001c0b1410721503400c0c005d401500300000d1184101c0c40200c50342c181d420803003e554180c0d95401e412a80400b40301000381c4002552280c40700820f000c0e078445900100880c2c0c010841c44007607004204440c100390703651061143c2e50900f84442d15001e22411452481c02c3c40250302d14201055441e580d00aa400081d00c503100d01154441c4075401543d01608032680119809495030395003c81500039001000140e4013021fa0000050710041e0a24694041f41ca0701540d20740760805c0c194400c414500c0401551340d0ac482c20300040c0d0041190008081c0040000a00110781ca281c0300718014200880c8202c10751140d44280300010014201105913540140e045ca041c0d51105c2e10f020311 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 642616043 1250 642614793 642614813
    0x605041b140d020f0c0d0f020a030f0302130504050f06010201060609060e12030c07091a10210b030f0609070506130e061f0f09171b030312070207031203090b0112 71
    0x1100d28134070004080b8180c0700040340e02200022140c9070201002e11045083e81c45080d9102d0003400103103440703002840240a680a089980030081c9508451601c810202e811600d040d240304810013000c1d010000190f9090040c9005000e185c07800707803c0c4610304031028221a82d1980c03414454101d0803d1305580c046d00700141c03640d44100b0030480303132100d5417603c00c1c0004002c2d020031845861100c8064502c14280850040d050320300c5680e400008422421582d80584c0c800950303c000745850740383c1c00c91941e1b410403100c0c040e000100080c0c042802c0018035607107410125072005000b4901401410903035445105410300700e514240d021241c5954503400640440c030220326140d01c0f0307039988441d012810b9211441d45190700c499120041c0d09901c0343d0081b40008580c00700c40800d90302034000541a10340d03d0070300c1307005a40c015080700d0403d10601510740008804071007440040e0f0094004006118514071203594102c11801d0400000c0141c2e186c100500005005030300b940c1a07070703440800810035810b117 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 642617293 1250 642616043 642616057
    0x5010806040b0c0a0e3f15010e011503060803031810060b0a08040314040b0a08070306080c06090303070614071d010c061a09100501020c19030b0421030605041b140d02 73
    0x7418000485507420021011761001c5101e61a44a402c0c24401100b000315071f054142c80030243d000ca420703032802d030510391526101003451007007603183c03400012803c0082000e140107003a414020031030541c0a504040c80c007241050a50340160419604100c2a1804011509400c425280c06541c50b0b56605090310110700c10720f0718030781d032145c00140010520986030141030402080e41d2180850b40701d01c203044085d91030602031010381e9000713070f040c0d50000c0c54620020101c01001038280c1b810410aa04d8040032202c00d00c000740006c521000070852026800500410300700c40b034110728000305210000082a4440344000102000e5480c01b11448152540c42190804c800050801036107252040c08440c4903d03013813290501512595800307414524100c9103d00f911030301032043c400203624585800c07801c402e01500c1aa410f405505d28044880510088162112041d171000310703030189400144002c446a448058450805115186aa0300e90021428142c00c406000c01900c4e0140c20f04550000c0c490343c4 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 642618543 1250 642617293 642617359
    0x1809050c120403020307060c0c0c06360306051e06100507120c0506060d0803150109080304090e0709020405100818030a0224040b1609050405010806040b0c0a0e 70
    0x10700300400c041d400802030103954843c0c04140803840c00941c0581308011002030003000c4c5e000300c81013481602d00c03602c84c1e445045c0c08000700c01612914440ca50000c400300c480f500d0b02680c03840c807091081c40312600640d070300050030350482048000d640806001562000d003189214003580710b4a216601d224006881805412160500041c82d580310040c11340c0a030404102c503203014180004580340341c4401e1030080c09030024a654591ba0f1003024424440100402941c10301600c90301c003042a6500308041c10140c00881d9000a110110201c451300e0051306500100005004010a0106032148180d5810302c0b17440741804286500c0c0c280d0091500030700304942c00010310002c078240c01c071581e0015802c03240c5462818400040308021500c0c0c0060801224040c04440000c400b10b90310302c00e040110300f405181c9281c400c1c007980d02c8600003400c2e00c1c07003070707103c0e41d459444181030000b802044411541c1040880c440c4500e031000095001e010b5031264000b051040d180d000490400f850710f00b1340c600900040c4 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 642619793 1250 642618543 642618577
    0x70c03021e04050703020a050a030f11030f010807121502070c031e03111912021c03020c0d020c0a05010c11060f220e040f1b0f14011809050c 62
    0x440074541100c40884424420b40c14000403030070083c040d100301c8100e148070b03542c0c1c80d240429407030068014156007003060400303d81e0307054002c3c024a000d902840c040d00048560301074a5141292480c6840702580200c0341652605d14004009255801032600d0700d4002440541c445500342081110318002e58809401403e41045800051080c11803078407a19110b91102120318080c4400a41d5825098942c01c4104620742c0d0b86c2c00200710440034500194031030b031040b24030400c0e64076152514101040307804004690041005001d000040c85405000d850354402001a0070050300042c2803901c0c0c51140505121080020006011034034414940d0440045c000c2940c03404140003900d0180c0c060321282c105440c4108c4400c8480103084480e074111440410500016102c0380c4036084a109089400c0303c03080c0d10a101c201d1400d10042c2082d000700070f007210220b00540351000d220140e94a4040150400c041040c1042e41490500201c206541c0ca14038005515541c0306901c203502e01c00c001d02d0030b50036009 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 642621043 1250 642619793 642619819
    0x306010c2f03010606090302090f2a030601090e100e070c020a031506060912080d02070203060f040b090708190305091302040f0504020a4508060c030c070305070c0302 73
    0x3526011281c41e401c250020401c603665250b00b1180c0e1035030b07130200039407000c00038001c90202002411140d070000680d00652460124a21000040c030010f909140d030340c00c5010041201541e0880307a141e000700030980e8010000e10f003000d040403e101c01c9000325103044100c4008124224170403030803040303403560140070960241e84a00700020f520b00c14049080c0030724180800400c420b4828071005044580c00360802e040708002d690384190540141ca06510702e180d090011034050781d020050980140c0380b000820360182402e0411030480c100040c454540756116241c00c001000c0000713594000001e9017680d1300d10141442ca02120325114007401c00707a04c154441c041c0e8031305000b15030042c4112000001c1c81d19500e40d4400030b000030b034001d90740c0b0f04001c143c600140c07140c4c5c0c0b00c2c48131004e49100c103001c00c03003a4451040720b860700800004081e88211040d55041c18844000f0030405543c00a680e00a80c0341945881e0880d000e05210307158004080000c00314220003007084429951000c0d50b401051180d031080 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 642622293 1250 642621043 642621113
    0xb100e04080d0c020f0f0105011503180602071b09020a0f1107060804020303130b0c010b0d0c05040c11030a030b120114180708010c1e08040305030a1104090c03020913110306010c 78
    0x8c0203000358600c0000d100c2d184240140207100795044980701c00ea20141c0e000c82900c5020081d08070a8003510303c003941030f24030b1000c0e0b0061401d8001401949034010b07214911848000c258410000810051080b181441300054a00003011001c5882a103843c90540c0d45610100e42140200000d48a04d81550b80c80486c0c00e12503a0080d14080c0424002044401e49280070070172140001000030340a1042c014081c81503041c50381051a03041058146150700854220105166034084081080081c5e0f5500074500c0c00e141c101444035005018000a104200c4404030412109802800185002c0b02100307280700d03007950a10201c00103041d007600801c440b8030fa5104c0945050560540290700324011000c450070b103030141907054000c1d601a0b0300d0303500395550600f00d03000402082c1c17201640000c090100150b221250b014003031406905075005038589114905000e03060842e1801c00d2019400c24254101d8211003800742da5010001b4078000b9000716960601144030f07500c8083c0d030400d140f0640b000c2117200d6 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 642623543 1250 642622293 642622301
    0x70b03090d14070b070e040b0a080d020111030606040603090f0503040e1801050f0703050a0603020604120212120901030506040b030627030405010905040917070b100e04080d0c020f0f01 81
    0x240958481c8030b4441e403031001007840340c4903025000b4580c1c10260042420540f00b841103800c510030141c0002110466407000800c800501e03404049294000340d04046460381c20b0040481c00303c90031040d5425410000c00283e02400f0380d00500c001c065480c281700003444580740425400a4014003070b6036032183c880004480510007142e240405201d1515114010281489003521400d40380c01d83d00c0441d11002e100728068800501064907068507003001001503960580184000d200000c1c1200c1100303094030501c200c4180e01c1510350302c0380e0416000c0c0349825403038004031400d4140034600001e05907030366000500104825641c8541504c00c0c801040b4071200140601200b0040c6e200c9448602c10300c6000441d900c0c85940980c0b40007581d84201044039003130030740280d01c000f8480d00c05078020107150b1040640d550850802075524014203814440c4580101940700068601d880103c611450b01c0e85401c41c9070301ca510640f0480c581d451013814032451092000181e10003044050780c01907c08644040d01030 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 642624793 1250 642623543 642623563
    0x20d02130b030a06150219050c150c010c02070e042901180f4a0601030606290c010e030c01020a09081605241c1a010801120203070b0309 60
    0x126280400204901d0341111200c5c413622100d40c014008000c507580c8021003285040c00c121400e10070752a044100c0c0d51212030f24840c11030240b0600f6180d2940048c5c171800d440c01e2000e50019508010020300c04840c8101185900c80d40280316100302442d5805050144030b1440000c0028028150001c0799140c2d6000d02250b0850081d00284805d036540c00c0c52600329481c0090b070161034207000f4051440404500440c0520382d0300300b00020b2802401704144140b40d84070060f42c2c456a0410401801046050b00c01c00d80540b0000310f540090140c0c6007511200d54240404e01040d111700813540c2c1da10b01d00309400c43c03907100e1040019251910456210745010350130103806e02000c20301c031000c0400d1140e070005100d0b10303001c0202c0801e04818601801c1c40030115a5000403105e02001080307100400c2c40780d0300107240d42096001100740140d06082e20004440307028021013040c10203a101440b0036a031001c0c2441c10354489101454407008079100083c941a041d501c00072124001104120404002048907000 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 642625899 1106 642624793 642624811
    0x1c060e070f0c02031605120105040312110c152d040615090c09030c060509010f0f0207030605131a0f0c03060f030a050a050c04021c020d02130b03 64
    0x5018800c0d4202905e5840c140c01000702d41400150709060b210100020007081c10140e40003480c140941e04140c08a540352508174040d442d14408845100e00305004031800032408a0000d40c03085421030b1650481030302c021014940a07041c81e08c1550b40d9101c0525041503680d503544500041016034188804504405008101ca40003481a84404001902d540401c0d074690318010310141000e0304401d007000700620442c22180d801001c1025007061a051402a803030b4280400c030b14042c0a5030000c1e01513810b00080c0f04400000d80d0f181140c071400707002c2110034100343c0241404401025110b000096070314000080c800e03030141c130241d40c000708020203000e4281c0014002030700c0c10340000425240c58215115a00c10480c04101d245858201a1415420034900c1164078a102c03400c4092446401d8000450f4045c0745c1c0d442e03044078400303540001c05021450320b40c447c4840d25002114146a = true := by decide +kernel

theorem cover : BRFrame.Cov 642446043 642625899 := by
  have h0 := BRFrame.cov_init 642446043
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642446043 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642446043 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642446043 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642446043 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642446043 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642446043 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642446043 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642446043 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642446043 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642446043 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642446043 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642446043 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642446043 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642446043 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642446043 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642446043 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642446043 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642446043 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642446043 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642446043 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642446043 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642446043 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642446043 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642446043 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642446043 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642446043 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642446043 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642446043 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642446043 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642446043 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642446043 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642446043 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642446043 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642446043 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642446043 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642446043 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642446043 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642446043 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642446043 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642446043 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642446043 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642446043 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642446043 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642446043 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642446043 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642446043 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642446043 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642446043 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642446043 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642446043 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642446043 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642446043 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642446043 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642446043 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642446043 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642446043 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642446043 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642446043 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642446043 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642446043 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642446043 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642446043 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642446043 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642446043 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642446043 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642446043 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642446043 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642446043 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642446043 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642446043 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642446043 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642446043 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642446043 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642446043 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642446043 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642446043 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642446043 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642446043 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642446043 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642446043 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642446043 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642446043 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642446043 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642446043 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642446043 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642446043 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642446043 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642446043 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642446043 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642446043 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642446043 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642446043 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642446043 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642446043 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642446043 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642446043 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642446043 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642446043 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642446043 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642446043 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642446043 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642446043 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642446043 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642446043 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642446043 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642446043 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642446043 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642446043 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642446043 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642446043 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642446043 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642446043 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642446043 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642446043 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642446043 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642446043 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642446043 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642446043 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642446043 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642446043 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642446043 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642446043 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642446043 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642446043 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642446043 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642446043 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642446043 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642446043 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642446043 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642446043 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642446043 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642446043 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642446043 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642446043 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642446043 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642446043 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642446043 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642446043 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642446043 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642446043 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642446043 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642446043 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642446043 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642446043 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 642446043 ≤ n) (h2 : n < 642625899) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
