-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2878
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:00:58.344977+00:00
-- url     : https://prove2.me/submissions/4ac0a482-faa6-4f2d-833c-2d18168f9e50

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 517446043 ≤ n < 517625899 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 517447293 1250 517446043 517446067
    0xa090602190809150d0c111e12091912020a090b0a03020405250206070f09050a060e030f01140f0604020a120f0b031228020c090709050405040b0f0a02 66
    0x7046440440c4a0752582c403900200b045044290385200c942c0200400085002640c043c05200c038020281c0b07c2e5004e6808410b10304aa034412014204080c0002006141c6140400c0c02e940c5d4080c1c2051a0701c080b00398015600005098100780c003030300b0700401d0921680c04600c103201c46800540c10581e00709081249003401034450400640403250100c0d00401c0d151214201e1008410300c00c0003200a00400c090300614664000408a010301c0e166078421a000240c100110344001c103901a4540c0240c60110030001588110b440d83c0b1125802020703202c000740d01168107400c68108800f060714100c3d200702003240c403104614800754001004c0e00d040d4a8110680d600400a5141141100c1c045581d1201245001702543c065891400007404444105215070b40e4041181c003c2042812640b8559440f5207807843d00e210340a08952180d0018480b50b0300e10000c000924600400800c1080742c003260000340342d42c4a01825000e00e008208803180c07402c1c4010345245034440203246003e41c074010885200041 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 517448543 1250 517447293 517447297
    0x13020f060f28110613030309060e15060303130b0d0e03120604140c07020909010b030d030506030c03120f210103030c02040510122909030d0b0a051807140a0906021908 73
    0x92120031210b40408520702903000306a0b0342005811107181500445560400040b070104250000100bd8010b07a01c0c14101a942d12803104648402500d1101c100200300c40d500c0070308907000100c88045000180c000e1080c0c0703550400000e00d0121948041804120b0402c0d10a0040d40d032400e40f1901070502e0601c2070007840e80b041040080c06103410400183c000d110030760010b050300400809444415003080401005000c05803503d91007030103562001c000e41d2900281c030280060707010b070403142008622546400150031204100c01030108a510040c5041035202c010380c0a14840d8481c032070b0488841c0180300860748020a1001264242403081c03204480e008140d001642d80800c10001d40031a101c4c4544800c000071f040036007000d140a040c41994400400580818051290b0030448012040700300100740c40300d8410309030400b0342c240004808401c14031354141e00501c1d0b410100c1001601d60203100055000e01110400a0380f2400240300741e541c18020f001c42d40c00040f100145034030030b54644000c03034 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 517449793 1250 517448543 517448551
    0x617040b0c0a031407170f1003020603130b0f07020f16090e01020918090d02010207080a031802030708010203070306081f0b0d0b0c04030c0e13020f060f281106 70
    0x1c200469541c002c280310f40c1059010099800000185041c07441380940820084a5030303481d072100c41000140320301039200c4054842c0483d15036200c44546036400303000442d4805080d101e0082e07080243c0d05c0104020284050007100c1695400450746440e06009040094240600c1001e80120152040e4031007600e1040b829100030000000c0c01d1090041c42074028403070700c80100c2d009000b40b86081e03840c56202280c03074810080441070710625040d12208038201c2c03007030040040c000380081c003528100c0c0d4465070203070150f5080240711028080841c2c001074501820303640029041d0b900041004a034541c94000c01d0002e0103014003c01041c2d03060700c1701c5c01c814107120b11406540e41d9076008081d00c039958003096005082d0040e400388690b0810317046582c0c0c2c96005020a03504e02c0b190500002d0083d86001d011442003180c449041c110072050b608014284015581242c0d22107006d100086510341d0440c003c000040345070500c007522186600015001c207170f2910a4005204011700500407424001c5451984 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 517451043 1250 517449793 517449811
    0x7030807050906040807080609010b090c0a030216150c0e011103030406050405031207050a030b01210c05041502010204140d020a03060c0c060f02030604050f010803040b03091e06010617040b 83
    0x11900c42c0004501107004691244919108410002816642c00305d1058000d10800b802440b500c0c0e0484188203000e00151810f06103008200100c1310154465400b0740441c520440c1c5240d0b401115854110020410180b04170205507140030840c140c64011070281102c0600382080400c2c041c866100369244e000041000e405503031900002000c200043c011506080325a4143c00c5032030800a1000b0700680198010201282c0350000c011001d40c040c040360005a80d00c82602000804640c0051001c0d0500c41038148c14403c09020120340508607800641c5140c04540c00143c0310380c540740346070700b2850b580170109001c0e18054501c3e60158031484450415030f0380219000c504040903090846008080c210098911407134408103007c944403030b400560003041c00f15400e00c4180c40f1003003400c3c500034080c8200740e41540204010400c2021301030103503512080400640c3c08a01301c806080158140a02d1700000c290803a100622055403c0382a001d00d25241c15412159031925079503070a40d4400c0030700340e84a = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 517452293 1250 517451043 517451047
    0x6090603050c0c06040c080f1209040e070302061b060a050601020613050c060d050f060301051005010f03020405130902030f01020906070b091608060a111c0b15030106091a0703080705 80
    0x2140d180320702c1101c003007600c0001280d403a8609820644940c17111401042014002c030b420f61409030500081d070801a05806004e28075150305101040001c1c000048400c805d40a600c5002001daa150342c041e010101501c1c4900000f5910800c005050004c02000c1c09109d074035090604c091640d0000d8040d42c49022090301072158105810007500c1c100e001e47c1aa0303400140012010300504c015080907004282101c01082c00f5198141058240c51048402c03000d00111f01c81c00301300c20340c0306821050500751281401440d02d522000410f00c00040305003941503c3d610350113000110706040103031016982a090003103080c0b500340c0340040c4451242e110064852000c2102245590400340400101c401c0c2254102880a5640c00b2032916084103c035440b051500d803a0701d902d0a1202c04044800000e1402248101c4c05081c1e0034500003072800c5000180c0100104045c1c2d02844048002103000c0c04580c1c6030403003164030709450300036540c001101e0010750400a00c18400001e0704103410980203509410055 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 517453543 1250 517452293 517452301
    0x1d0117010b090d05030a3506010f140708070b061e0906040e0d0c02010e0a0302012a020d0c080c0109120b06030c04091a010603110313020612090d0909060609060305 72
    0x19680c3c2942c000140c032a0100051381d80807140c0214007080544a00103c402c1080448010350460154100c0c05891040c901400500998030a50810122903e14100906095019170080ca03450300004d5044920340800213910050040200a0f5540868201d54045142000300040701240700c0a50b407140c01041d0744400300381d00d503960b5045400c0001c846012a20f00814413030008000c40514042a404141c07440403207801410909540b8082c1c075010303100d000868600c4800e80d24150584203040c0c2c0149142a40d450060f03551a4600c2400341c01942096916410720301c00600348180303401c2c001d0500048000401040070142d032908a0560807980310901390f61460042400c1180c0c034024560b12a20b4501d006003004030525140204646004100602e030707032101019021642d01a8040a42c06400c0c00007900c41802041034900561001d04150304103c1c807030b2500303049128161030303c3c2c0003a04441488039003560b00800c6035006000c0702d41d06021b003d240c100c019012892a010340020162108005 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 517454793 1250 517453543 517453549
    0x30807030c0b13110a38040803070b0105010315051207031b09050609061c0c0902070303020a02010b03070605030705130305030d060e0f090613021207061d0117010b09 73
    0x9002041d070806001d4002d0720300040900d14020400d1002c5039007000d0000c080039030341895405a026070301000ba14698030009540000c03c40540010700e210000da0041401c14150710f0003002d0401402d04000039900c4d0714803460404041315050300114101440d040000401c200742d0329240049403829204060455a50320600e81444026003024082c03103580e100504041a00b03a130210101e0701c060208202a44038901040034100341076274459408040300c0c072641401207100448840e50342c031a44420092030380c1e0b003461600ba600418029008a580851011036454081c0507501c1e0010b8201e000c0d298480c2404409400c030f01028107000200080807a4403180c050740c48003524082d5400c40c1c02c4a4546006d00584c0c405020b81c2e002c1c80030441808008107181890300340402c4c0c094641c02000d0501503448030945c47d8603203504031080c0e900210030a03000000c02c03400d110b950050101030f507e00c0103040d2003500740702214501d111107604020b00c04040e40b5141060000d0719066404444c03045595510b16400 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 517456043 1250 517454793 517454807
    0x50f07031d06070f02010e0a0f020906010504030b04030c060c11060f06031011070203010b0a080a0303020d0902090f0106020c2b02030a0206040b030f010f03020d020108191a04060e1003080703 84
    0xc0320440b031041105002e0314540054034052442080c0d8028440c0c0c2148101c0705403103108000c8002c0100003036140c07140043c0352202c2c02075403100045c5040c90500f640c0740c65a030081071041e03406401042581060b4014400c0e64000e000c420496420800140394000c0c05e019aa000c0050450091020000114030f569905004a5490503001b01c0144003004150405101a50101d20220300ca90310b840410300031400c1c0203080d80101c4103a00003800698035144c0702035020758004030360020012b55030020a40107a481c5050140994000021940290304001c400b0b480e249a00701590700c10b243c82c081c22801803580c44d090031518405031200360600b042a2010034580303444c002c030081d886200032401041e4103a0000c0603511401d601c800511003a681c414080700b01d001e2a00020390090400304400300035500030081c3c5030300121420f2956490b4910391034a0002c0381c1916080d5003240078109201342c5286050300035807001e0b100c1c0404c80c61440c20802109600d41900d440018401e1344042005400d16010b502 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 517457293 1250 517456043 517456091
    0x30b010e0717150a0e0a0506042304020f1f0305091614031905030a0f030c121805010c0f121a01081e010e040312110d150b0705030a080901050f0703 65
    0x84c40940311800d00842c0305045543c008118070300800980d042c900b5020b001844035480c1e40002aa8400c119a03007410280108180e80121201481e0000c9403202500002880c2d00442003116203014843d0040650b80090841e4240354400b4284a0f100c0002d4180d120407a00c40122543d016107102002c80c1c00e00d41c82d004034a194038180c01d0442c05101003c8014a202403095950451384a6841010340486c0d100c0e00c1d0402c0020401c4440c000842066030212000b5410150411840c5506546d0f690940c0c00421400002030114076803814142e822a00031401c10003688014011441070b000c024152800949602c0d04000f88000030407910244000400240c1c1c40c1e00c0e4410606684030704510070b04030402e44089000500403540d00120580920501668040d0030381c02d1440c00e00b065924001800388006070941c9181c820384001007031912140104100d51040c000303186c941c28800e80c00f5251910042a2038843d034146000c0210114030800141d42c03089050500203100030107600d0400070110440c1d = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 517458543 1250 517457293 517457299
    0x7080a1406070203070f060c020c1f0909050610050a1206031118190203090c090901050103031107060804080d02090415091a03060402060a2106030b010e071715 70
    0x40001814886862860041459044111619500d8808040741e5a201e61200900501240100c0500140490f00900b000c00c880d44119a046100040080c81c2d1907800c00c60340880b101c550088071481c50b00003440500400840000700198a80b040114180c1040169480100301000502c200b1203405500c44105940c180f400402400d40c0b00c3c03a1034000070701a9000184190342c1312000129840707420840d540310f9030a0316001d00d1030004505080d0040d4001500715451401112140000b985170b10301a240f10709209000410254034505010b0000d00341800c0f640b41640040b070081c0720240d0800300540d00164469001580c420180540400a0003011051130f80181413151000c81ca518159280e815207480d1541004024203072100080c811600703500858051300314000040242c070b0104080c245403101800c00c0c03c14003030140303280d41c3e10011603d02c070f203901640ca14051050104400c102405045040700c8012141000c0c0c0020b8400e0f9040070124500003515000100b41d84003220500702d00c2c440107 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 517459793 1250 517458543 517458553
    0x6150f03030906071b080303010518160e120d03140106020c010f12020702090403020a02100219030806030709022214010815030a0506011203030f0b0609240d060501030507030b01051b0708 82
    0x21b62100f80d120351080c411148036411a00c0301602e080f0140d01540d0048a2040d04501c0c0e012006100b42d40054054103259800030f1400b09080300b42038188a001200e003007a030380020b9655040e5a60084c0b14006030040011544034203001d0181da6005214225020303e28103000ca108005040b00710064800c4200094200f200c19060008154001904480d850b20031150b81c0120412440120390f61044014088075403501018a1004a07000b1001d407a0441400ba00b036406144d110100902603070310210701c009121400b09081c00b000461031415102510340f01d00c0300040300c1c11036400201948000307802c00400f4820300300030000750f5904200e551141903100095a40035a074a048200712140740300004d40c046820103070000c51000e10340c071031070580c005d001b01711600300711480040c4a101c80c40d80c000e00728503030b0701d00390300c2905030340303690040c0903148400304000c100c0700e0900000409441d40039000d0341c03e15082c5055030040341c0e000800c0d60000c003511030364000b0707821441070070320301d1b01d1b038070b644041090300403 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 517461043 1250 517459793 517459799
    0x503090708011103220c0902072904020306010b0f0f0d090f0c0f080316240e0a060e011509020d02071707020a08060108030f07140f06150f03030906071b 67
    0x1039900510300c00c541860300281100c0c0c0303010310305178030140065004044203211201030143c42e420382d002d0305a00c3e000310542d440d0001709101c10903a0300018404212403280540400c01140b504110041c003500171032420900340b1b040c24012200500880c000c2140070f80f4040ba400f800385100794000e40045401109085a200150509860076520340c002c501850070700c0400440c4a820001c00c6500c500741c451200c0c2d1144030304c1e45481034130f607401da044102c030303180c029486882541036030154010240c50440900041000381c60301d101108c0b4010400e210a9050801104140c03d010740c42104a401a0030007581c2c800481420f00c00074461032070000d00c99000c180d108a03041140350060a1064800e6a0120240751541041c03580c0380e10034410407042d50710400c0015103407c8a2809000c0d602d04c01c004000000d5141010035082c000013000c811174a070b011804000c40c9091350301000c0110398040d2281e20f4680d0a200110341c40f881020f1a0601407200082c0030b404000004000801c050140710a42c6d0000f52 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 517462293 1250 517461043 517461071
    0x1202070b1602030403030210020306060c0a06060503010b0a08060f1b0c0a050f070506160222020c0705040e0a0b10050d080d0f06050109140a0306050a020c12120106050309070801 78
    0x505446100ca0758039003902000d510381c000803c03541502c3d00342d001040c5c1009004607030030207588000c1400d60052014440502908420046000f03001d200f0003000c50401d052000307040c21a040b0b444d400388929540c0800300310200020460f030303401141031545005103945160180100c0313001e4a03520b81c54a4400110f011455a0204001e101d0620031001d82d10b500c0003400702c4590b1522940101907000742c0810800c0012469900c0c101c81007440500118185081001100d500e412643c1800c0d800b6600003409040c4450140448000703000c08850402003010ba00c8a503640e00d04850301d0040400d8240c501194071801381c20701203001000010244032551080f450105501d800c00000410350398100364007403950008d1405080142ca506a407101022860b08504c0c0e440c3d00c458011140e0401010000480400c0c2e01d030242510456100c500560b0300c0c00d401500515084a00c0080d2050700400d10207295800d00da003110a0441d411490002e031660bc8d0b69200a0811041b0f80c07000006620b00301d900c0c08041 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 517463543 1250 517462293 517462313
    0x507170a031b23040602120c010609051512010c020c0105070302030d110c061005010c15021918050604081b010215130c0e16030203070c14100e1203010e07120207 71
    0x404011854028012503590603a405540070301809070300b0104282c036100c1200f1008d481c00e54480e10020505960b40d030700980c112042030391404030300c0d11403014002060802d05a40e811750b0055400810210742d24200082d00d888819152604001000440200381407080003a85e01d40408200100084484e015842c5010b6100c1140b401250140c80c00069008007401032410844070103845051401411b0b99a0f9442050140301e031f0100b280d0f003440707403041c840300d405600800368000d03884105604040b000030012450f01035200030f1246800300b00c24810284085104400c90350001a01103882c5401d42c0181d05104542e50380d00c040d01ca0400801800344500403d905019020303c0203444400d4640b62450042c500864105007a1030307550f50b0944005120307034011980021285000c1c0d45e83d9445595400900404404c403180d2a80107402c03913030004005200d07030b80071050b02c0c1004111482c800c3c903900d10180014800d54102c1d1a103800001ca409001e41072844980ca0390613021952040306240c40a956 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 517464793 1250 517463543 517463567
    0x4020309010212070f170a090b0a0b0f030106030507090e01090834030e0d030e060d020c0d0201091e020114030f07020c03070501021506040603080a0c120507170a031b 73
    0xf9070320640882d5240b401440c40200c0c1854030703a200040707084035640052801101800042c60650b40d03000260111307405c0000907004408200d4042a00007000c0c00b048a292103040c0c0712803083c0d161000800c0080c900050034011900306440100342115101d800d240100911440a0100100020b02440144c01d90301004010128841d650f201c02600035503150030780a520100030081b6550a0350040f26180c00c21071214030600c2850101d010182d050040b6400b034100b101c16008075031b00416002c005a40a000c2a1588080f510007007080f0b0710b240d107650b001850124000c00135240c6802d9a58156403055400c0c1503a0600603031804e68034140300ca0074800400c0101c80400041c0103540400da05031501081c01000c41b44140c0c010505030314000b050508aa40141000790b11a0383c4a50001c00200a800a002d66a4032500c43c40c040b000c050a20b802c003292405004d2041100801c40c0c4400182c0b100503414600341607032440c1d82c4544400100380c00a14003007140d40301503284d0080b0825020f40c040700711000 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 517466043 1250 517464793 517464817
    0x30909050901111204050f0106181128110307030801030b07020a0209060f010c020d030201092a06120f290d1e08040906030b07030506030c0d0818040203090102 70
    0x80d500c1441040c200c3c3c4080f80083c614400411075521042c0b6800d82c013681090080741901c2c1c40c1e112200310242143c43e0307588440c0d40070b0410b01c5c00030b0082580344a0385100d480a41b58851030000c00c101303105111556035031000c2c107024040050100243c0710745103407001030300707200d040343e56880d82ca09010303180b0702003484110b80c088400b5000030241c0b88041880e00c015903020b00301200644a00b001c000e40012420703c1c42d4100021524034401607512240b0240215010b070b0000160b195142c1440304030032440c80917004052100d144400496922200900c04881c2c1c289030650111034007100c0b8a0107000b95a01100d2158101810351168400c60070642d103c01e040f403030403000c500038054103000144a11400160803035941c004240740f013513802d007000c04855101d5180c0e540b8081d00c950000c1d086400c142c01c29034852440c00e08124001d9010701c00c1c1904030004074000c0461185480c001001076000a0000709902008280140315980c0b800c6d1030141420020b005640782d2604003203041c002e40000c5c10b2021 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 517467293 1250 517466043 517466051
    0x4090204082109031e0a021c0302010c09120b070912060c2a080d06031202010f1a10030e031b0f010b01030506060f070206190e030d091d0405120304030909 68
    0x14001c0d18404a0b0b00d0058082c010745809030f40d021a030801e030381c42085945400d000d03c000c86c0707006a4a40100c150310602d0f10302c02c95036000c000c0c1802821269641404000e00106078070511621403404103640c24641d2244040c610742d604e46804448001c0540c1c40036002c034058900c84020403045800c9202e04482a6540c0021341c1002902806080c0742240c01702c800c0004511072401103804200103000c0c00c28003100120301240d072651240342000109800e02c0050355030301002008110140030340ca002505a204170000c1c8500800014110b03890011904241a0755490040385000240191190020b000d000c4074881103c0780301094880010b00001c12955107095219601e540c000d1081d64013507500a0402806c10604540b40801584446010f07a403021042c4001c0540039058044210604801e595401e4200a840245440c2c9130081403140140045918140016107062520f8551414101c0c0c00850319101c3d42002e5041c11405d501204141030000108400e25030003503480340c101e03096100104 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 517468543 1250 517467293 517467343
    0xa0203100e130302060f01151407171c020f190215090703050c040501030c2102131a01080402031c0c121e090e0402400e0a050a08030c0409020408 64
    0x180001002d0240c0d03500028500c0c40230010301d1141100c080d0390400403480380d2406145441d510900c0b049001d219480d4100028581040d1840d61408520303c6500581507081c000c107614411200c0c05607800f6012a000d2104ca5485454401c10840c001c0d504c85111000d001d04010b100582c645807180400c1d1214407640c4044040c5c0d050a00c13030103049035044408010345a0134030f11281c40380790214a80010300da1440102d4005640c500082120f0b03075094240000d0840d42c040c034804000c03111503100303034140f01c8107104120160301c001c1248260300c4028940380300c0f2035550650982c0c2ca06078030000035103d020640d1100703a8803500600401d500366156440c0d03114200c480c02e4116089000390080b80d034400712030400304006007404188003011100207842c80c101018805407020000300030442042020001402403a02543e00344200b07000d1041c0715006c0c00100301291507036903440041080c01040c800000001640c0c801d054810354001c0c0403050fa05540d542d07504c103081c55648035a0040300600c400320940c03031 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 517469793 1250 517468543 517468561
    0x1f0509040b0a050303160302121c0c02030703170612060f01030204060b0712050307030b1c0c0b13051c0f06090b01090501030b06130204090603030810050907080a0203100e13030206 79
    0x4012150000e00942c41d0000f041d8040c80c0a06c0d041004a040d4031440100415801c52440640414040c40620300c0042c142c14442c4010f07905608132000c25034008020481c0803c0e840070240c0140d0460700e081403220b032250804103c00101a103581d40050082c60140b00c03e03050002c030001d040b030740226803d0044030303142c1032107114602c074410005203d410604108500c07580180003130b65000c005400c1c005800e0706060081403455650100a48100c40e041c680391003080f59030308881c0f01802e00821000d0400001840100fa1414640031f0036101e0244d03440303220344281c2e1745180000c0036940400c00071080e141e24685034014102c070300402c540c00c8041c0000890351038035510132503040701d400011150b80b03900c8480500c00d01803094001c40b81c1003030702040041160340d400e002d508000c6110340c0d1148036929203407900c010041e03110381181d4410309590b810300500d10b51001c2d6480d0440341c61280183c0e240c442d4990003039119034a030300c40302d03804c900c4204110764041c14a0100041c14025000e40395660ba0303032a20 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 517471043 1250 517469793 517469809
    0x70f1502041e171b04140108030c16061403090a0f050a03021207081828060905060f0316050913020c0d0c02030627160f060206010b0406030b1f0509040b 67
    0x20414903904c5519800d001c211600d00c0c070300c800f640c060070009040c2030f0661104001c01c0260020030f0f01d9031000030111200f0307100300b12245400c031543e20b203850304905060000740600380307501c1c41c142c0002c404400310710840300078018121544d41c001da1894120242d41352a42e2178020750301040c1c4c05406260b481444028140c2d08458070340340d00080881c40d1806c02701c001151160314126558001c0f0b803070303804c40d003a240850001c80b490090010f100f525161402400501e80b25464101c02c1c060101403014542100c0b210b419a500024094103012210940c01811596800380320205684000c1c405400600d0b140a41d00030105500c1c1a8141d034603000c2124000d031b660401281000b0340592007480010809041c81c0340c4249030040104c0080c0045000146640c0781002103030105c049406180c20130009400800c450100508a0380003a1a103580f4085180c2540c0c043e610820050580300c10403066155a40c002040d90440d0040c6946402c5950a81c010030350b8112070003117030040c0d140a5004409181000b4 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 517472293 1250 517471043 517471079
    0x140c0c0a08010c1202030903070f03020102030a0e0a0b2e0b0711040e0c060d1401030b1e040803010506091201090308192f13060206091005010506070f1502041e 70
    0x151654840746144c40b040c001e42c0010160441c60005200c0726000400100142020fa8000d44c0096104d007050b4035540c080b03645907080e074106e940c410140a00064520408907074021521151400740d4281c484890f0040f18440d50b111040c0641250082039405485c1b0142c490103003c0d840010103655450180400c5803950101400298801401780c54145000d0700188840da402c07407001308211001c00c0084488650a8100300e070040c036100200040c00040c0e0b11407107d10300303030480c815015041c0754440070210720040c0240350040314005462515501c03003074130070500c1d24400c8008000189590800400c130403401d40d8032032140f04100701900c01e0300d21039000312614050995100c20312214002508294030f01c0706003403040f000405000a40c0507041100d4848010311340350300a0000307480c12000c81c1d81010084585250401c0c0f802c001030056488901c190f480c841e030702c03042c01c04891500c1c3c1050010b0184c1c0d42e21101403e40001008034aa407500d0711042c80103507801e1039555580341c5a030030120000305141 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 517473543 1250 517472293 517472297
    0x110d020c0714062704020c0c0909010b09070e0a030b04060e01060602011a0405180106060c12080432120714030306010c021c0503040b07051606050405010c03140c0c0a08010c 76
    0x1010280803c1d1001340c8441c1030f1481c581310492100c41c810049410390300504407907001c0b0341000c0b001d00b1182c280101e1213944250940c0c000c001855044000a0a50801410b048c0800859035008021510360341d41000c051600070010003e10b28092400c0000362004001240055080800003d10140140102aa800d1100122800705a0700d48240310040400030400012500401c445606101c820711414010309030390b541c3e100d0080c4181c20458000c031989400350301000700c1d0004200104400c901c070b07a030050004001100e19103840c1c90f000c011400708000305030044d0007401d05810844080e14000c000c4039100744014000e0864244499480340400c07241c01e0f002c0340600c4400001498400071940e40107141d01c1d40404a141035860f81c03440c542050700f2180360203e0010301c0c80d090020412000300d0b00030b101c800940703025003000300040c410300a5128036030522500d0603c04040500400c845041e02c1c46803c165a102c1d203c084800d960342c001c02d1051130090500101c0411440c0041c040c02006c80303469 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 517474793 1250 517473543 517473547
    0xf0c11120a2a080a1b02030a0b1f0f05030c060f030109020a0909090b010501030f0506010e010503061305130b09060106082a13182c01110d020c071406 66
    0x214206842c0c40c20030126400b26100e0400300802540203001c03410306024000d000c4652075440741c003000b401c403501c502c1d0940c80d11030700c2d800e800c001a980010400007030707648280140c03025180e80c03d07038030345280d103008a5880800b074400021681e089074008440032504110200c0740d0b040d41600c1880a244a07900040807101004c10060140d0710f1203400514450320f01c0c1c41e080c8810b694400c100e408854801e041100c0005c0c0a0b801003107d90313454020380f082c0038008001048035040c40400640b135148240700700c07814400080300084c0c15030b550183c80031410310074080a0219140c110512503005052103802c4030320110400c0443d104100004002d41a01d44c642c6540c2308a8843d1020103150f800c00c0001c035108038268800008a0407590710143c0002c00000100d181103c0c20001d0b900b01d1082514041c0742c2103440c1545c1d40701c3d030301c0742e851020f003840d0340003030b002c2c1c9101020954581c094080b130034018008210004c0d1641c0884100e500034120801c080c0143ca07000e070b07150305550141000343c00d1615400303202 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 517476043 1250 517474793 517474807
    0x607081b040e0603030c030d0213050109081b0a12060906110a14070804030c090209240f1b0d200c1012140c1e120412030b040f0c1112 59
    0x1070100000e40181d030040c00c0724285071142c600c40f0720710780c803000c01c00c4238554001c207401000036802d07540c22010b46001d0030115000e030b0070611a41d90307480c000106184080410a000400342c0c03900300203000030300000001e6000e14101400c046004c0c0002000845401d4544241388001000c5102624200110f50780e03445241d1004400c0d00910742c20444055840d0201008004001860382d0b0603500141500a40903845081d14800c004502005410082200100803021112000318904903410007060325240d03a1101d890980244002003842c04143d610b1244800105443e60810184040d41d0f14a0202460b40b04550b55041d48481540c800c1d0340d01f150341050500952409840e0020301250f0361200043c0e410486003000c2010b50f01981c207155550000150714240d1200c05242840848208400c503251200c403551281d41008018009840e00c0c00100002d10994800e800a0b401076200030814050034400100343c200500c2340d0000700f0b002c940c5030214580d10003030100f0881030b6001302d0f540702070a08903 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 517477293 1250 517476043 517476059
    0x2030606130e1005010e100f05060f120c1c060b030a0209030c100f02121305012106060306050f090712051e090616110d050d1d0607081b04 61
    0x310400d180142a0301c415002e060740e0800c01c211500207603041e0303000c41c2c903500d000b01602d04108044c080d4405851b07211010720484080d13001c60710842c2c2c400c0d220207517140700807440c0203800d01654a040c940d601031103042c440301c00c00141c050f0400413116002141800a0603820000b154524460070103501020310000e0803048541d40506078002014003030b40e2041c10303000c000840d6031020070b0510001c100c40e120b4003021580e0410005020b80c5800d04018905640d441c0e8540c5450401e100e214100b11083c0c0d06034440055140725a1504400e400003803141c1a25844041d015082c1c034010180100d010b10110149440d010018a001c8d0149440d6041029185003c0300040c00e002405052407525071b42c03035518010704500905200b8941c0b20044d1419003001500d00003205032241c4031004101850201508072038010a04c00390550700d0381012640d0318154203101010f0240305000d04a0035409441603c4000c001050440c0b140616546a4002d59038540000000341002c9505500c101c20174882445811 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 517478543 1250 517477293 517477309
    0x9060c020d080c010504030f081e01031103070b0a0f030f0207030806132919030c0927080a0e06030705161403030c1908074506021902030606 62
    0x2a0007460328030f26114600c244a400d5410540d412400070b08241004100280d1020340341c0d800c80300c1d0300d9018101140036104105508410b000117001c802d404a0400c00a1b50104030305001803410101c0662913400180001d02003481d21504400440c0c2000140460081d15200322036281c0c1e45a1168030050701d03034a050006401c8401302d6650403503911b0092090040c55a0552120078440c032140001120f036800500218007140d8003034015040c4407540c24000200c60101100503210080700024880c84110041d4000c940180c070084080b22580c0314110073b00c20420000e01014006443d8080b13134401c014140700302440100c0300c00340001c1c0d0501440054424403040354201e140034081107502541fa50351101d0841c1d0003592611607104000030b4940c07003005d1000c6028a004982e00340302d90107240022025203200800701c04040e103000c031101034051440d0048230004407a111b22100c102888003800c05400c3c01c3c003072801f41101500c111241440c0a50440b000c0c001000c0c2d000d4007401683d01c4000501402c0 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 517479793 1250 517478543 517478569
    0x1e170f04110a080c0a05100504030305030405070f0605030f090706022e050f06090c07020306060d1e0c14060c1005060303160803010f060206070f0806010e04050406061509060c02 78
    0x10701a40100800300d940e0548114058000741014000c407418120402c010350030709502c142c0c0100d880c2c02000345003a4104003030381d04494243c02d1a40e50780c1e8561910b0383c100300a41d000645000c2060502003070083d07101d0040c510a24480e000403480303440300782c0c49039985c0006116910040c0d00c649a0720120040d40035004040c00d50708200124070480110703001050b16005c40300741010f07110b0a41005220310b8034682213600301c008103000500d0b0002c40c0e00883d80350300e00100180c2c00344158050107401c02c21040d03600010820f4201da1a40e88200b6403404400d506940d01c151651307060b2040d00c000b00d44c5020720482d07103d921958020461200c0d08426540600002844a42e050000307001c007850720541403404213841881942541e5896044c014a001d03200a507420890031035202c0003c00407065008518200100d55500307101110350b42d50001210041f440300c802c542c0181c10982848200002608927009940380000c00e00c0420300941801c6503904503d11131f800015032181c40c004c0160410400100b22 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 517481043 1250 517479793 517479803
    0xe1509011e09060b03041b060c0618020607030e01111603140c0306040615060311120406020910120b1009170102300f010503070b0c0c0405071e170f04 66
    0x1400355624002c0301121015400880c0c41000042003008101c42944013101100008150560407420307e8001824410714240c0100843e41d034007003203101c00c0d01c8010b540c4d0805038014100c030ba803401d8500d00101426000301074180884d140c1c034049a00700f4404904150b041d64a03ca44c2c2010910b15202d6001800e1032820f001028000c03801d459125460a00030b0a00c160f018981c00b068440300101c010b8500305c2650700c508109498071059050b18004001150070000d401c850601341c640b03482c10584001d21650064560100c03021000303007451a00300024400c0304003241010070000a5020520030640b12071a500c0c0300107aa44031003440280b80d02e014100e2601c0240d000142041c01c08184419a05180d009022010600e50f1307489510014084a017a4440e000704c185015551600c800f080c1c5d9614180540160315074041032281800000b003002020700e10004100b0f00c0503081c120005032001000200d40410058031420700d00d580d50152050311a6442480140c041c0f030b588005103400c04407006001114 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 517482293 1250 517481043 517481099
    0x12060613031b14100c0201021f140114030d0f09081504060b0f0f1e0d060914030307050d0c0e10020d02010f11030c160c0803040e150901 60
    0x46050440e249030806144241c0c015121070540c5900360040d40301d0369120400c494180c9041100c152a008441c106100a90822080005280c40140d084c04441d810a0b103070100030081912182030320b80c00115000c6008c40c80d04910380d80300d080c500c00114001c00115010b03801184a044c24a01c100760654440c4190f25040d0000780e200c1030340f0342c100742461640b8165011414180001e0001601c561400c502045552200c0450182c010500403202120414415800454946600b4102698041e0240c030010880c03a0011802d15206000385a2035506403910309000b84800301c1c108001080300d011b10601e8890a04180c01800c0ca84041c0c00e1203012501000001c0d0034150301e40d1100381c1c100304104035540141255025100e80242115440130101908500301803031850003100794011241c04c0164180b00540e5034003c11100d426081e010140180b40180311000010241d201201800544940303040254490700d03036682840903124013010a5038401c858500410000e821001c61007030840c00300e6a07041c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 517483543 1250 517482293 517482307
    0xc0105130e04080d1d070501140d0e0703050f0a0b16030905031201090c0c03080a021b070b03072607031e020a170a140703020a0203040306062c010506120606 69
    0x100752040280d500700e07002c58002c00d0407401a0f62034001d201c03640c070280e04034120703066200c01104ea84552511481d0b0502440588542c11000c212048912001a0801c14403010b401c0382802540d440c1c00348401e036a42e0041c500c40f65001d410120340e401605400481c143c403151201d035612031045200022005c14107541e40301200c0050010300280c030074081d02c5011400d06626010b22038040d25074442c400410484505500303800a604400c48a410040340800141c4800c0842307104501000c0c04402c03115548541c1c4400181040194001e61040040c0e40d43e064a030042000c14800c50703200225203c0213550f00c14009503102e03200f50310036680d008458015060001c01001140c040340e000c16011030001c1d07083c44400400071100c10009401c040300380ca04000c1c404030300d074400c81041c40c0600319000300b5400041840300d0920800c2a140030b550008410011950b940d40c41d41d007501040c4900000501c81d461003c0b1012401001007412207402808042c508140b07140c81c0501068000c21031079120a040c4890 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 517484793 1250 517483543 517483559
    0x70303020f0d0504060504110a05031002130305070b0714060c270619080121031103041a0c2b03020d0e030301140111060402030a0201050f0d0c030507110703050c010513 74
    0x3c940910f005d800c0009190410f8200304c0248140c0446290180d103816a0412480c0c82c0000e4030202251502d00042c0c4540c0784101504882c20709903c0074245201d0b4680109516450390010140c207032203030b5084d403040c0e03245642c9191154012144d0364440142884550f440c1c0380044428907004c03c1c442d40702e03080000514000ba11940048c204240206581480c2820303042d00142000d0250034000c001d0440300c091514103000510385440002c003013000b0301c282124214020804c0d2000741071340c000690807420150319885410b82010a8170a000c0c410a041c642580e640e04240ca4039803240c030a11080c00c04515082900a5032185600c407500c00d9503800040c50201003480a180a4404114100c02c009a402d00040541012100c0581c140d0004d40038480141c0c0c0000d03100c3c105990a0810a80300c482071f41184a0900403200071410741418600309d5002070340c1c50b91041e03100c0c10a5440c1e240c104000c00128a50301e08042c0002055644007101c806115030203880544042c021304004082ca0988032504 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 517486043 1250 517484793 517484801
    0x608180313141c023102070825050715020c030f160b0c0c010c0f0609050f070603090b0609150307140103110702010509090901020c1915050c070303020f0d 68
    0x910b44050b903107140a032032070624000c100161080d0032045480d000f980009100e903007103c44900d18044020b59011880e0b108801c54170511309002e000715240c40c0d040c18400203079400000d120520003a820750070b01840140000000b010f03608200103081c00c81c14140da8204444c0300c041048194404c0e070800b030700c0d950b504011107803800311450046d1114030001000b4011004140d044001d400109010711440a000041c001c2c0e010082442e00c0c4a92400500f44103400800c11070010b0a84d60404c1241800d110700050644018554a004c803844035a0320807045088a14120000300b0035407541021500d1840c02e05a40360b004207c0b03118251038000340c1c500103858054258400d405051048646000540c3c1511881c00076003680206213140030400c3e40000d01c2840b03488020b5200e400002c001c20320a98007541030720340c0840880212011418003e000e2000c2501011045940e6107034841c0d1640d11184a0243c80e01895080c41c4507402e0031b007160740940c043d42050070805000f403418020255500c0e60390023 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 517487293 1250 517486043 517486049
    0x9120e011b0c140405040f08030403090f03050312010b0322081603180f0e0c0a110f011a0d0c0b030c0c0d0915030911040f0f0207030806010908070608180313 69
    0x1500c002d026191107070790407540c40034520340d40c8118500410080400c81c001b082d001043c0d40400700070b50780c0d9243c0c541aa40000d0681104800d1041a06d0200c00c0010000003000c00050030910f1619030303030307072029840801c1c1700480b800003414404e4411507c40d2007952107240c91441c45216044d023420074004488102c5100715409500040403480002c0c0c0c40105001d854002e40220481021010700700300307071403035261005012248694030006800034480c4c411501c500e00802814142c450307690744c801d8103502910ad2142d21400345003010603c03030014039140d10610030301a40041941070480c548070781201580c00c02030402140c00d9041040e180300a0302031020305e02c40b03550b40e00c40380700302d509101140000c9244040b010b01803600d024640d10201c0c0c0c0c99035030750144000403540401c5108400c4c203010301070207000e941c00c0c44c542e00202d510410560231812051040200385c3e07895818039940d9101940e1100280b00f0f040c045180d240200780304101201c54061001498000c85c0d1901c0003030792201e59a070300254 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 517488543 1250 517487293 517487303
    0x3040506030408040302010f02070608040b09030c1f060501030204030b130f050706091406032401110f01050402090f1902030408121f090606020613030306080601090e1009120e011b 79
    0x40c1c00c5c0115a04500002c0e239010580c402802c180d403c100c13024041900c0903101900c140031a1000542e0103c0400444150006a10942d0490440d200d41a0012840c655070425064180480840c50754468804d40302180d0304088031902a80b5528800505004900b0068a469001c01219030115002f008280c0041c146640e400c00d180740b81c56403581c0e6468200c07507440d02c12a801c1090107030200030f031040d5a000c10b480b11030101c4011090001030f1520880700342e00d55800d014920b02d4040d45070040d403241c0c0c4554026510784e0f030180e81d905051691000b0440b5a2180091440c0c0d0000c0d0141c42c55018651252051040c249000d044641030000e0540403900c0ca9080c0b0148101c00c0c8003107144050a00041c5440c001c10300801d4101140030b5240c1000500c209020085401c40340245446a0450300090124030191040b65840302603400240444010624040c850603504c0d1101a005108041205401001440e01c000405030300701c400b42e804644142c100000041c8480c0a640d10b0811030803a40d1040c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 517489793 1250 517488543 517488547
    0xf180303130f030c090e0d0f120c050301150e03030a0f0c0c0b071208060d080309030f04080f0106060237140f0f01090803161119030e0907050d0e03040506030408 71
    0x40c58250b402c5016600071030842d5080c802d00343d00845000503005200005410a08001d230021001110900d41c3d8400320102d040c2020484480d69800000540c1603401d402d585555046500c00c060b10300104200c1d0f0340342c0581c000c00c0a490520b00c00c410001131000107140c01075400906869a51040c400c0b90003c00700501300040400402008150604880c5050b080c800007601c0c011300002c0c2c1e9002014009052404008005160903609008071507d41503405249604d41c3e403141012603603071408201c940030646c0f0300340000c0341c014000955088524070f0310a00d4401d020701a441605107c0c0350f020962810704000e089240003881c207c681e00840c00012000b0103600352074184540c0f401791280301207000d5916003106403000c00c100c4000c50790700854100300383d03600780c41007402140d0366041003007440480d01901c01e90131021000d07030a229000e41d000765903d1441a001030100003549409441d030402051082000c24407940445e001000c185468405881c01d003a036035030110344190301c1190211510240 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 517491043 1250 517489793 517489799
    0x70309120f031d030a2105040b061315062a05011a09010f06030c1b0b010501080a02120117030c12030117071406090f0d03030c0807050f180303130f 65
    0xc544204001c080e010005884191050f00c9907036142d1040b00400010001004695007044884441c070010b50a59004100318902d41414410340e0100c041d41c12074454010305c7c101017605002c174042d1004140e00d4106540905150003001c0e200700301550314601040c0c206000c601005440a0415980d40c2d00450000c40c00c00d00c820a11a8980e682c49042d0f0b00c1015003500604c10450303440480382c2a02c81d14140040c142a090400350360074501d08a082509004101c0280c0421a10543d00d0741295001c1e290021b0039142c2c681c030b4109034041da82d10110940d5189004014440c98684224881c44200c0150392500080310100350800180041d030303450468000004002003030104080d0790600d0405406044024140103000890b40b042100d454840c840100c4c2015983d551794000c0c00c2ca9010040c140c054407000c41c86d01174040c000d03c605407130100d0082d200080840b0b0090003244c11800a03c2d0307440e4030300842046c800e01c03103030f84160106400d8803041c00008a1010380030520b8000d421031841004103a49 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 517492293 1250 517491043 517491047
    0x21c030207050109063204030b04050a050d11210c0708030310171b03120307080f0a1a0d050304050405071206060309152016030e0f030303010b03070309120f 69
    0xc4d940c0032800308106c04a40501104030101c005408521240300b02013071041e51440f580043c006d030b8101600c803c903400300b8082046800078007030b004580314801707641d0000a5888180c442c0010040a0840ca80101340710720144050021100d81d4260b0020855003001116503440d894004030347c0103070030039910000512600c07032903903400d00004112018400a0f050b015440740e81d12244002d45820041e8045030390842031365801d0040b28000c0e518652180d860303280000c4010800c200030755a0521104034040031600304801e500409043c42056403800074826103a005100c0c2d00340320a041916035000034000032491b683c50303002d001e001c1c410740e90307869136002031490992007240e03016403107841490f00d4900d030755001620400c0340c5d02d46052101b00004a111200c003208002c1042d8189103c42800001180b011001c2c80c42e0039028014040d903214130a0300c5511040c4010b011002c1b0a213039055000740010400d10144000641d0301240c20310300440d02105035a02c3d191355a14464660009c10051004414119 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 517493543 1250 517492293 517492307
    0x1060c03120509030f250f0323030606091206040c060207090e0709020a050d060902210c16031103030412080705030601140d1d030d0605030d0912021c0302070501 71
    0x10042001c00c101909202200960f42d10500301c40c5403051101003030200754060f469031042d05118480d407034440390801600c2c03c4042002d1109044001c60740620007030817035848000ba03e0310f44051180d0f10500d5a1140f00400c85030350131080c030040d4407003480071800380408000d001a6001d9881000c3c4119101e00b40500a0f0a02c1202e80018807000c0c54007400c0d28070b407180000c0940455103072120041c4d841c55603400880e6588200e144d004100d608054002503103805640c0280340c000341801c0326103803298034002100380d03107802540d0002c207016091000261040d5070321032242c55944a8180b803031110980048003411500f0865081c2c0e00b4084c0a10440a207d0f0059041c1e503020500b440c0c000d10710303c0c205001034415503400b150701d03c550102091008100d2440d80c8036041d490b2015440040c25100790b900d50b9920760009183e0100c00e0305203c80052b260500040f60b030340c40711080c2c4030309000310f08201103007110140e00c2c0c2d000d0ba03000c102c5006842860b9072030340054007100d000c0e13805407103a03d04003000540f0103 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 517494793 1250 517493543 517493567
    0xe0d02060c0a11060a1b03110f1c050c061519030f060609090510050709050d0503040f0803070c090216060203130203121e0f0403060c05042108070f021801060c03 71
    0xe40c0042017503011156015200520749103001501c00e4a00c003807030908a030181000307d40c2c1040ca10032001c0f841c400300c4002426420f500092004203100901400c404c40759400345030410a95640300714041507002544030101c240d40c0300043c0000c0085403003615a021181025401075442e034803003150b15020b01509000e41c0001d44000310090000c020180e507141c1d07480284690200c0305540c1d0b540403900f118402c02101009000080822003000400c0c200541c036031384035105121003501014800150b1070808416200703100e400c000e440240c6850300590070040d41c0720080c02030545030807180e144001081c078030165004a02500700032004030130b1441494070b007661410010450078028031808040c1c410030510181c1c6001345224054682d80062500c0d07810f401660030040c485810140b00924080e8450081c00860307014444415a0943d444041c02c00642003040c042c090120030080c0a001c18038801e20344400070f2015042c2c04001c0514108141e0028082c0c202c0800999804519014581c0c0700c0500561 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 517496043 1250 517494793 517494799
    0x30a110f07152304150e03010c0f03060f0503120c15070503040b0703110a0c11060c1612030504033906030b04021804090212030309030a110c030606010e0d02060c0a11 73
    0x20f449a852801c1a081c0114402c242d0b620f9600d0f203248131101d21880d2101210340001c0c0007031081c02500362018000c0818100004006450b10a0004605410001c3d203030880748003901410361440f8609010006902040280c40e01c2e21422010481040340400031511555080da213850722803e0516241c04941d2010f003407032080505290440880280900c11691844079904000400c10594034100a580c0101e034034842c2c1c084070215005888450108041d20100040d0304104e100342d48404035a0100e10022201a000410a0000340002140c0c3c01c188049401070560002207040014010a4104601c0841c2507100311095410040b840c3c140c00351003030354070080305c056041411a8a00240140e05070a0f01d42c480da44a2282a0542d1a019414155002034409603a501d25010306007503682c0d840210300790000345551700445003917000400c40201c1070800030094280e0303803105c03001114860701151403680d200c0d25240c655001a1790b118000c25074070700c2c14809428200303600d0518a040781054015640 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 517497293 1250 517496043 517496087
    0x90f1b05070c080318041b021005090708070b0a0e030d050d050408120a0e1002210601050c0d030e0d110307030e03010204050a06020a0b130209190212040317090f030a110f0715 77
    0x7c3c0036000304000e1200c012000b0002001d607944c4070420301c4c00c1440d42c8004464099603a0215940f0481c4c0d00500140b1020707100c92107030a11400c20316598840c00c08070200000c400b0300c1200382c00b2800d80c004c543c10038021607115080144100015001c00d0060760070f111220307a12314103410204828008440580f21100007141424001c5541000c00c50519010202254100c5d001030700907801901640c2d00d11154034122108078450580140040111000d0a4914418100d07a040d000b846261110052a40700c0007075800c0400f156003e8400201c480e41c135581c90354003071101082e5038035240040d10007401c40e50300600361043c4601b006100c240e1b0141140c210b8000000400000d601c6009980d500b02c000d18409411034415400004000d00809052800c0c84d05820140302c28103a10100c08075122541000061075074807503142982c0d032950352802c4546640c2042c017200b07410a00550b242d4140b48414015a16180e0804070040c1c100551900002044002c418426000b2680b01c08210212480c80380e80031 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 517498543 1250 517497293 517497341
    0x30309100501080d0e06130f03050f01020f18030a120207090513110d03020106050418060e0604020109121704080d081602120d18050601090f1b05070c08031804 70
    0x1a00d4210118255092102c10960607071541c449600b11048801c041f000c06040546411240c0c3c1040042d20043d80c03144144407c00390801811b00c2150a80002c0b8144285440420620300c0010140080140ea060041c580ca20007c1119580081c40012296010b000200d062002314811280d014149010361784020800c100020090b41c0d20000707107070301202da280746042c03986822405000fa50704690b411074140500340100501c84054905903e118030024401010b400c1e05540e511001160084e00042000c00c1c20001d64500042d40710110b4060804840c00284101008105d136000b64800c2c040c03940310944500902341c2c040421a0040c10200c180b40360003c20180c020344c0c6111403490707400c04010000c1e4025000b040c0d940541503954285600020981d400d0500ca0f8039a0000d220b6140c5c418101109100b0034a018454031f01e0188040d0300340c401015513414200e0319a001510212020980c60a0104000804201510511200f0b500001e0140001014001a40d4102c039807520500c203902069 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 517499793 1250 517498543 517498559
    0xa051e1603052515050d0605030105040f0803150d0c051212040905100503160302091b070f17070f170a050d090c0914100f0b04090b040f0e030309100501 67
    0xc00c0030011055001202006250b000034a080300780d0340400803000c2184d031110881900b00020b410030300011a02004807641c0c410600d0309a40084800604400c154070700400000d18040203181c00040000c0700003070145040d0701182e800609141c003510b600004c19000c10491901e205c04c0e01c001c1c11b4000141c21000c102c4002d40d01c1c2070095000301603a4a49803400a42c107028032510410040000600722500801e00940c40351002c81c00e8041a40245400300c0001c9035484e010118040000b80d0b82661850801e264640403e8204680822907800c0d200001100d0303685131420161501a00400020100040900c0e04030586a140c10340311490748814800c600f43d0350b422a0688600c1d2030801c00220700920549400c101c3c1160701c0d005051710f0703881c05e12045810300b1304442c1180b05d070f00c2d00b90010000540f40c020f44900104540304c0d5450000c0100014000412140c0001410010180c000f24001c0e4808240c003058401c5114080c0c02c1e58004001c000040c40100044071081403592020030007035040c1808 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 517501043 1250 517499793 517499803
    0x109080c1605090f130213020318031c09050709050c03090d03090b150a090c02010c03110405090417071a0411040b0a260d090f0b0c0712050a051e160305 67
    0x7508041c62660760001e03820000c1c117404409407690040100d440b54000c40c46880c0250420340b07100040001c00b0345001c0350a100081101d016604020104a1040d01c9119a9010b0042d04ca011241030049000c00110040c0d00c2c000c45000f00400c1141c1ca44900d001a055450f0201100800c010103082c0a83e12003c241c83d143c81c40c0e080005080034010440313454011400026040d40640c0d41245819075140c1141ea0641c0441b0940034aaa4140041c9503c40030019032805140107007980422114003040c001003a22a000300981c88084000f814482d59840380d001c01000403055403031306007201c010001080b21078905404a903078111420040040d10001040300d001d118003690712070064082e1a819030320004020100c44160f800d0883d03001d40021711006103121a148030b213001100b10243e001c03402c0c140820030b03240e081e40c040d002000325501c0c00c44410325000040130203a48134014030203944040780041c48400418440702c40212740c01c241d0a139400c0d10f441c035609200151911895000e00010b000810 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 517502293 1250 517501043 517501051
    0x25170105070813050f100203070e01050c122803150501051e0918090f060c030c0f071104090609030908010902130c03021303050c01180e04150e0109080c160509 70
    0x140440c0c050070a02d012071800d0740c0c605c2c3c20b0203980b1039482c01982800103900194454003096803050044422280103460398082d850b580403c9401c1076121070900c090400c050440c20301c0d400302e5104000ca58819200d8041c114000805c0003e45550405290f44001c40001b00203240a02e0801c0c5003800c01c140c1841e0210240d6030106400b03a00003001c414980c1c41012003d6402034600d100e0303603a424070307020b41179413450a0084007509004002c0020801c1903c003040d248540d0140400d14509026144d0001440d032043c003048030360383d40c80359440c0c42a894500c2480c840a200b450000b50090302d03410700bc0c2c0ba01049901c034051030f82c1420848001a01d60525260f8000124500030844060450702074000e0b00a000d00340c078210303040b60310010900c800021495100390080e25111188000940c06481214260143c01c1d001182000070500103150144a0b02d440b0222960000300011098206400c0d02c0151406451203200421400740008090042c0303500e00300300c642c005841030f250074046080759000034 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 517503543 1250 517502293 517502311
    0x4061d070e16051b120d0609050a150e060d0807150e03090303040e0411101d010903020109060503040c03050d050403050106090e06040b0a0b060f120f0402130905251701050708 77
    0x1342d020140504210b0301e044032140059075910f4080c14003a031030003003409118480543d401c241c04910181e5191041d040283d244003555411380742811404140007201909807034200c0c03014001807000c01d4030032000d008a548900c0c0c002110300c80b00380c403400a80f2182c030383d101c4503070b0420404e90810307a0300041110201c6650300118011036403036090982500c1e440c3d5108a80000700c2075115000c0542c800601035440200c0f900030f01c00307010100011582c6200ca13020090210301600f0051000902640c0a9503019200d00607491007107840b0b40d9103134104008640b205001c0b035800302e01801002001e008500183c100c51608000c1c40b0711440010740d6944000c1c001410020343d400110b10380521030f400c80c040c1303103002405540e13980303681d805031749160350014281c03200e4000c1c8040403550a01c2900c007498026600145101000b80f87c0700f00d0344004204030310007210248950302d14480b0318482e0001480b00c202c0002c000204491a181b501030a0028a01c904695a4980420400e81079004403280e50410103203 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 517504793 1250 517503543 517503577
    0x9180609150301091a0709090911040b040e0f0c0a08031908060d0b0708041a0405060403050c07170a060518030403060b010909020d1e11030c0304061d070e1605 70
    0xa9000720f07005004105014180d240020340c100504940e00750300d02d00860165560340b9265503644040000c80700003d600400b42040c0f5450900b0381d03d400e41094040181c020000140c00040d02a168900007607080d9051064000c0c2820740c0c003d20b04000948024940c0e4809549003200c00c1d0010088408521244d00c00d00c074140b1f0204070f1139100c4440781d22902d54456003101c110b0400010207001400103e40807100c1d54080c6c1d8005019801030030b1140d01407a44803009141680300d81c1d80a45140d00001d0b01001203218507400001d40c070000b14841c030103802200010f000d9070301803410300c2c001b917400041008481c04c0c034a40c84d1515410000046404581d008400000c80303882c414012140d041c950751150100900200d140404140c05610204400c141800384075400c040e024002410b8643c110311030b409500050000407402c8010200440d8018451200002c1140080c0d2000556055600b400c46055001c02c40c144040682c82550f2904501f00075060058203c01660023850340c03081c0c815010309070140b = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 517506043 1250 517504793 517504831
    0x11100903020c22050c1603080c09060d060315020301050d0f02031f020c01060e07050a0507020a150c030210050c19140f1201140a1a160809180609 64
    0x100340207040c08410010b060562842075070100c02000f5018510702d60200d4a082e01050b020700e21081110050344001300d141d60780701c09540f000c1e18942001170400300d001c04d08000c850302d2a640e00e0020560701440680c0016490b0a605104126940171041503180a20400060040341d5a41c0d9460513280c0c1e0020080000b0401440400e080000e0450402c2c080440c4d0000461050f0030361b0007401e4141c115030000c0205940d140031030b075010f100c15100c0d41e012420030015540100d10640c01071203a039002a0181d010143d4484160300101d40c2d410711000000c4005003a0020140c0c180b014522038032491905000701e041140509003688a8400180d1010540d6604194200d010b0920310f070b2846840081e449e224074a144c0152119070201610040d59128017001007542c00301c4125404107840040d108070b80c10360030f0900030140344070030b016404d0700c584060041003145540a020b5207025880f440107070b5182e500c5841808145040c150341c01c00324103540d0040200a072120b042040c0c0c40401d0a0b503080d500c140c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 517507293 1250 517506043 517506047
    0xf060d090c0f0509070305010609090b040e030a02150c0a050414040e01090503030901060603050910090c0e070504141f051e12010602070609030f110f0409051c11100903 74
    0x480c5401807000d03924440000c0c80a02c504015011210103880100f00340d695144110101c4500740620004a80040028000039900d1351211100420241000900030004180e9034516001001e4401c010703070100c0420802c0c1141104050380140e014403003242041400700000c1d1140c01140500b07103440321010300d5040a80d42e29044416600d20090080180c1c26403410800d4482c1c1c0111240b40340d83d82044000140d0610901c9801d1003015048041c00c01e141c2c3c0c0c400c441001d00b001076802e43d1303210140003007c0703004980145081e001e140c20751640c0e981d0700d01d48050b5501105504c80c0d16403141c02a103521513240c59215180024014503880c1c216612410115200c030801101120403034515004100000c001a8000141d8140c5102d90219030401d40c1d035020403100d10b100c03400014020304034150b00f10009041ca070105e61201400825001e00303441c8810100e02205c0b200c20041e01c43d9800403842e08412241700e50b900c041c60445141a4400c2c00352241030036900d080328510585079030b6035800c070300d41458 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 517508543 1250 517507293 517507301
    0x507060309150507030606110c0315070201090c0905060406091802210a0510150f030b04080912030d0c1b110402121003030807090e070e1201020a052104020f060d 71
    0xe08140300030083c60a240e41d005000305051f00540022420300340b40c841c00590001503114070200c0040042c5040d07800100e201d228800c0141c500000e42d03484040c0d2900080302802c001c0b0283c000160000b1301842d0000400040e2101c0340c3c841e01d10f4074504985104824000040103421301d8040d202c01702c5501d000c0c8030040c010000f810188529000380c481c10000c014001c034849000c8000319000b03100110762944031220a000d14810300d141180300d80c00c02c1001030032452140364482d006a1f030b050f042040440c081000712140c5040e220180d0000659107038051410700c0703085040c50591405101c1d21413201900181a1401e0001038804881502c0314081c643c1c0d00d40403155449000c0404194909026007105802101b03404214013184004c4000f031012403140898408950701100c11703107100d80f07640800340d807090f502800490300310304800d043d8141d40c20240002c1068007410340d82c2c03541d603641807100111103031071020142804000c8117080c0400750399203128000c406001101c825680303414032800e82c4024 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 517509793 1250 517508543 517508573
    0xa020c15010909140102040e01120503040819060507020c010e0d060e0a060e0609010218090405160b0a020c190b34030305070e10080c120406050709050a030507060309 73
    0x10303214100010503604000d401240c8154401c02007002e401c46900c048a09070300881c01007500e030b42c2c2e14000401143c5001c070003074016640510b0036285130948512545040480800034041c050454090000030848144039140d40824030b80302600d5000b60135070008103d00141c0a805105511102d000c0080c081954004090310b5002c0c0d040360040c0120f407038203902400022013681403d0060354001210308071306000729990301c0b0300d800c0342c100c1d1000c11200f044aa49009082640c2074400c41d80035100140c082461807002d0045900c403d910f81c107000c18005d01e400e40110441f4081e0039140344c030b4124010b00d28440410b940c0c820400c1c07503c40e42440665038000581e0303c0441f41843d150356000344a0401840310400c01b901965060200f80e5903081c0603035440c50314910244c0c10084515003880c0007440350f500190072190303016a25140034150700ca070b04110581644c0a03104035070b56509010840d074000c0340314002008143ca880310b5540c910b441c1c3c15240c401621a21040c56101c0054008100c0355540c034041e0 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 517511043 1250 517509793 517509823
    0xc1e0a0210050f012d0621020a0804110a0506091002010b19081903080f07030f0908030609070207120b0705091816080105031e1c0f0f0302070b0a020c 66
    0x681d01e4401d43c80420081c2c00e20417600201307202c094146070383c00380d026107400b0302d440c031303030b1040c0f0b4152038240f00b101d4031440005900c83c80030301040b0b03003c82001e450000700300c400095511401a03003002c1c14000e000c4503000c10410310404c0f010764200310341d440d000c0544100d658101c0e5281c414004143c400e80c0506010750307286600410001d54020f404503c4401c001c107a8220400b01c44401c4000810317040c540d0541c10000d0007103802c441c005000b042e07407171104c00c0c2e00004903c0c0c0419025400c01d0920306640c4a80c0c01190402350100811000341000e80c90950701540f1407006101032803810703407801da12401c030034400b90880c29110005890b05014600701c5100100c042c040b404040054010401c1a50042d5045030300818003040180c0c00c1881081041d0503510018050050186c5400e048a44540c0c6103102d040103001c3c030140c0b0319510300d00e207004090349102a207800d0341d0300302759502c02460409020003280a040c03040c4045000304a0070b074922a030011100100603075440502e50120701e40b0ba00c1560b0240 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 517512293 1250 517511043 517511051
    0xc0212010b04090804090e2803140d060e0603060115080a09020a0e01090f1a01030e160902070b13030f080405030705060108070812070203030901080c0f0409050f0c1e0a0210 76
    0xf0801e4440c02031007240d02c8240c0420404001110383c41e120b41c286c00d03840c0b00c00c0184940101007038800312100344238184a400c0c0890b0051a0100c025040d40216800102c083d40c0c503441008442d49852203254081c078214007414085d81004420350451201956090401140d94005a2041c0b4140c0c402020150002c0900c064103907150024200d442d000d00440c40f44c54140345c081c899041140c01860104407102202c60b0b4806450320044008180d15000100c9074415540e201d40003001c491020320180c0484c040140ea1441d043c02e11a02164010308003048040c0010b0074840480d50001000b4500603192520300c0160710b49060051940c041c00360054000d018610001800c100c0004010080b100c9410648501c1034000300301c0c0792103018011029406810070814040150304c103480c89944030002480160904810806260503900a504040c203c00d0341c80c0144600d60340941e03a11070b8044503440340a480c01c0c042e8140d2050761440c400034040c0140e00407a0401c80706009106041620b00d400790100 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 517513543 1250 517512293 517512311
    0x6040b1b0703080d06080a03020a1205040513090c0f0b07060c03061e03120203120a0f0914060a47190311030303091b040b06070302010b120606010c0212010b04 70
    0x206680d02c80c4213008600c40c94000c00140003140800c1e2040806d4040d00902110a107c2c2c0b20345020100c1250310400300b2100304004100c940d40c0300c10013182020314100020315052a4900391800c0e010903000500f07403070300b000010801845c0340d504440303009520200c0031842040c800d0f020340240c8a550480902c901142c1501c076182d6106844117000c40f80a030f15640307000d00780d01d8030036610703032140805031100251401c00180584010360000f11038448404800107401c2d049440758003000c100e401103416241c10410910100340c09a006072090908005504400c1c2610340d082400e0626800300420b1098090b80c00c420440c80b2191200f0240800c0a484118080c1c550500074074028124007003203520424500307046030642000000d0364482c1d10a00d00403ca442c0d005c4003505485440405400d03403241d01c4443d61b40c102e858100151014511a07000400c5e038000381000c0040340c007801420f00c041c552218040003110b80e480880003d40a8044c0c130202402c0c660a203120b030140c0810b0f0030068005003400212 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 517514793 1250 517513543 517513553
    0x5060403060b2d130b06460206010f060e010c05100e0705041109030303042004060e06040507172707030f20180c0d060b0c0c0a0506040b1b0703 63
    0x4402810f040b00c0581c04040e0051940046130100040305401c0708050000301c90200b400c183c580c00c130711648012804503110740800c000f10720700c1440f034051a01e0240c00032500050b8041140390301411169100c04c1d00c40742451401407031011b0002803641000320828a440500c00d003802202c088a0075110309002e00d182e859101a66910b007032003810300413440d2010a000b1800c504c0191000405c6c000d0145246464540318900402c0000050510a240142e1988030680d954403480c0002c00305000c0b40003e42c6030400c00c0008492009010344107003c0300251000d2007000c01c2c10626405083e500c04c1070a60001062541507100084e407200150b889409008810300000c9200c240600340320f07450620800d82c80e019034042040b40f41c040b403504801c0602c00c030302404180c1c10b01c060344039201c00c2c505800c09184118180545159900c994000c0800141d82c024000c404d1103031207a81641a2003082c0302a152902080719072003688601c1d4201d50021078040198420700b0301c00604142460100d450b41512130410b = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 517516043 1250 517514793 517514869
    0x3040b0a1e0e070b0f0306060c150a0522021809070506040f0f060507110919090c0e0c040609050402030601020c0a030302060f0f040503090d03051b03070501050f0105060403060b 78
    0x614034207201c1c505001810488a200312004061781e02400303403d603120003092002a800081f149240c9002d020604280d1001d01c3d51450310034402e00402150608000344a040e859403141d01240d6000380d003030401005a154481a07a40d115800c42c40105107654409803103003448126000264814800200000c0e40c0002c0610071040d030310396a038000a13090740c0317820688052260344402880300107180c1c20446d4529040c95865030008000d1a100524800010150105e845000084524113040790701400101200021254000300120340395103441d04024020300100074902c100340c0b03d142c0000004809910038801e502180c440507242c0d6068a40702d250107501c030a03044480208604007180001d00c44a2070b0300c00d460085800002139131800e401802030003500303440711009600f404070822200050884603040d0242c0789103802e0142d81c40e013107985042801d54030050310854508523200c00601840da11002207408981e807001e000284d4294020200b0141d04082c140c0408034814200110704204841e00 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 517517293 1250 517516043 517516061
    0x1f0e0f0a0c0b03060120010207210f02011e0504020f040509031b0c1f140c010e0606031b09130b1503010b010309110d15020a0201151a03040b0a1e 64
    0x190000303003180c82d6000460a804100c88107030005411942c0f0b51003040903805002403401c200c10000d4038018454071500340d007101015041210101182c4e504941641c032518042000c0310301d20080c4295950052620540d0324482040d401e01940d0711701080c1150380c0e40d100d0041c5c40b8030184c410301251810b44062501d0741c200c01c01040015003103490026480f2008650114080c5004013041c0c071b5045110b8010040850084180040c4041008410a43c0301c115029100c1c1d40c036000004a421100b00190900300030001e041d10303000e540411031320110240840d1643c500300009030303800304542d0344121410f80c40844040d805804616500c003442000e18410612400d0010203030001c0c031501c0b540390011000c441410b200500f14071500b04040d0a2807406800180c0032500a540b0302d1241c3d000d0500380c0341241e11100410000d42e64401444034109204000400100705000840070032004880405900b844000c00080200c0e400b10001084803001340c0c00880f072100c83d91182a10030003004011002080310352 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 517518543 1250 517517293 517517303
    0xd050f0a0b07050a050a0305220809010212040305060402100507120201150e1005010f0320090f0a03050a030f050c160509090106080a0f03020c13050f060409051f0e0f0a 74
    0x101c0010100c0e400390085420150300390340c0d0b003480c2403d0035004078002e1002803c00c684c0d0101c1e503010107502c0030001805c1822a4000d40c00241e07198103400000e840d18007213050400804405010030000700d4004580264442e80641c2c6409000e2101c40302290b2503c65000b00612040b5100100c05c4481c0e03055000e440c00021840d0380080350b44e2188402c0418000c101c507400c4c84190100014030032548666000c6401d1040d6050111b202c0e44202404035088091030254000c08078007140c42c0315540b8100c019010720840c00d59100c168241103403150b43c2c490615100207000d00540c9154a801b552080c01281c40e00180342c001c0e41c0740450449100b082c043d0251080c148900700d100d02140603c1d5040c840e083c110f400032401051201e68560303982e405070381041810740a5008490004d101600d80c105a449000c9a050000941c0e2601c0e84c40450034500c040e000398061450f004c1c0b4080016400242426501010020384040303c182c003500b87d020700420002101c1c54001c020184070040b80009800d00024824 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 517519793 1250 517518543 517518563
    0x31c0f0605090f0a0c0513030302011a15071b050604090b03010510051e12010c112806020c0a05070803070b2a0a020319090303030c030c050306040b0d050f0a 69
    0xd01c04118089000303485503d5602030382c0700490012110b0784c0c425140c00116050003424240068601001c101d401d13030064000d80d465104146c0100202d02d090511040e045414655262000418001c14040c17040010002401c2008444164010300d40010061000070441642c944d158040d00f0060800d00e4803076030082d800c24011032041503d035055501582c0e409486940d840304038480740c2c000c2c02c924108483d003103015088540c5100b0001e000700f586150050311441041c100d065003462400605034140341c0d240c1e01f4400792001106815400f80085900a807001d6121201524060304114001400070400d11444000040c559404800362074983d002c0c031520029951070010b80040100c13415405000b0018086005284032000005042400c09902c1240d051940d40380b1221303210715100c214040440da001004004065050003481c80240c8070345014025040087c070080c0c0a40005813609208503113a0720042ca1070b440340c50b5405816070300841103030504000ca20b84103031161520700040e6050307280 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 517521043 1250 517519793 517519799
    0x50d0f03081b0306060a03020903060a051602062205160f26060c03091015090e0102120403120906050c0310080307030c120915080f0112050309060c031c0f06 69
    0x5044500d0b6a1500c1d03405286544e403004100095a0320030800e04041c50350074401584207031402c120041c4142d005645c0094141030200b40b0034202201c4100e2101150b004008000c01035200618901003003400c43c1800d404c0c91410701d81a428050502035006012010580000741212a041c1250846a1201c40706007404211f4803100380340355001800306a00d90141c1701042030b0b0741c002c1008641c0400401c2c1920106039140b03844006413100d052258500f041000d10501c0350200c03038403442d40390640c442d00852501140c503c454080036002000a400d200d144c1d6440380d02c00415401080c0305661240b130801c034034985480241c56941042e1a0f12242200f1070002243c036480000c102d80351a038164032070f2040f00c1a240e0b01c4000848030740d5014010054030020010310047c1020a0481c00e00107034a444107103240c0761038003550800303050340404141580350b9051030109070003100f00c5254200696010365103160004200c2e11f580300319040c40c51450310300b9100240080040c0c0c040c0c203444032601400d003c040d039 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 517522293 1250 517521043 517521061
    0x5010203040e041b03050703110915010f0c0c09060608011502030a0c060b0d23060f15060c070b0307360b090f120c090c04030327050d0f0308 62
    0x1880c01260818060074011902007680941030180d040240f00c1c541084170b03102da442e00d050a0841d80219500b44203c0741c22907052a0442603184c0c800350141400e140d100403000000c1249424040322410f002c6840200c0c000d00c0b480c0042d00000c1c4c80c030440c042c0426543d400008003c5d080074400c1b21b408500d11828555440c1c0701100b146d100d420540d13241080740c8000d440311703001845250b4240d5803041440e00b140c0002040d000000340c1c81010444185601c3c0c3d90030007030342c3c00c1460080862036107111540401c0752100c0c10030607110300000c0a031451502d603000440701c0c0f4642100c1e43c1003140c00070804010003520700e0b400056181100c040f41d0144610203603110200c03101c00c0c2062081048030401050522280d4070f00307000742105110003410040d0300201d9070301103011102e802d25020710ba83c110329204005800c0090b0176603049011407083c24070b040d1075514028290125001e500c2d81401d44d095410488105018080002e400c00915030500740c134080c0303001c440c200403202c0308070040b0b9000310000720000 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 517523543 1250 517522293 517522297
    0x3021e070e0603030708030c0d0b040504080d0b040c21060f080c2d040b1c061a03031602040b01171f05031b060c01180c060e191217071a0105010203 65
    0x1079000b83c846003161901c000c408e00c0740d0804070307100110680c0d9035425462a682c1c1d0180e140500e005a0742d00e030307643e40910ba410082d201c0b00c100c803602882c105003151351140c0c0e0000d481440c2a25117021080a600100702d820044c0c540c0d075018041504901d68045074a00011031814a41c040888102d2103130303001d51903204400c8101c0d01e0010140300c24250800b526042940125136007100040403148100318030814a080b90b84c000009036485c5507188064072060000400411180004030002d42c100510b031a44610980300c040002400b80b130301c5210700a4aa4010840002003813000844a091890406406200b0548a50b0421201c00000000003840d003000308074080c0e8a10b00c0303614400550b02c1c00d001d100300c603800a55541010b640c0da1340c003c00c01b410640e2244082034030443e910041c0c1c91070002e00030b0494404520940c840c5035144a260408040b00300d00724102c07200824400a6446542003170b041c6c121030411404600ea00010300c07a001c2180103050110b58520780204814140d80312001240d0b00c0c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 517524793 1250 517523543 517523557
    0x15010f1706010c0c150e0307060302090a051e0306091606090b0a0807110d02070f0b040b0318071d1008060108031b0307060c0c05010c080c030601030903021e070e060303 74
    0x441454001c100c0a51060703103c01c1c615030003007800c20201c555526800c02455480250b03c400100e00c80d60200403803505101c030704000c0c0030318501541030451200004484140c10312860344079205020b604202c20052400008003044000c099588900c0d00030703441e64654a4003400300e00b02d02e2440f0b80c04505180103503ca4425517656121090074809d1a1a06941010018010509100107494418180403040106c482090f11aa015008061a0107455819100b0a82103024410814401440344902003010f803903000104004000705001162171141c01c1c5030003a08900c5031114400110030801c646849034500444440118460f021fa0390200a03440c0d220a004443c0207820800005002c240c0003844090300582c900305a03840c02486da990301c400c072181c0400400220350944c509009005003840ba401d07031390300c60f4280b540b0145055034554401d480300400c400d0515130344800c01d200741442000004000c801540d80003280c40803100c4400c2d900c1c80f951140a44003480f100001c0c40341d0602100b60b45903 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 517526043 1250 517524793 517524827
    0xf060905100813060605041803030f05010602030304080f071203050105090a0504201804140f0a02010e100507170309071a03070f11030d0605090c0702090c03100e15010f 74
    0xb25110203e10481d040d61032007041e138829484010124855540d03100da100c10160411010400d0109440c014082e030b0207000c15510704515010040002c5a008400c490307020b940214103a135580ba400d18180d099004592026103c246000e0200b1800e6401da806036059400031504c41d4060f0351181c01c050107803902220001c04120b01e1800304803084000151010341c0500040c8240144911000c030f50805540c00c4406a51111056502450511060100c1c002b444550006071441c10704640000c0d0400c03064007101400743d22100d1a8450a902c1003090b92000b0364009c00d8806500c2803000314403203541003603900c29054000c071000080d4008020311480d1413054050501d40c11a0b4a85200741e51115058000304180210110714240c0f6402c18401840034904000380083c0d601c0c20f25080c800c206000034104c851142e001c12000015079201c0015603400300304464103540e00e07038840802c807088041d103034010380d102b140300c100740400041c1040d41c84400e81000c1c2d80c3d01300d0254210600302c402c1010850040c0c8 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 517527293 1250 517526043 517526057
    0x110603060f04050603030c0a11010807080c030408030c1204030210052d060409020d0b01080d1403240d0606091404211e08100b040f05060903010e070f06090510 70
    0x81810143c01ca41e0340400c0c020152420011040102403c0c4855090100d40900c070503220055150707000550f984d0040c0c51031034002c02030310f002c5181250a03c000381c00034203982030110000d5101020310040b9003912000d80e030054840d0901d03180103503a41c2e444031613000c0c2031820040001d880522003030040c40580d175540c400c41718000c440350416802c00c0c0090b000c19041a12007000c0000742c1c84e0001c444207824403d10440a40750300d00461036040c200c0a5091108014190305a810b10030a60b0f0103494105908440620840240d001528140540f1020480d008007551b6201e5061109580c451000c55510b54002e0050b448500740321304200404540003040c648812414500400c0c1aa02100b003824683c10001d24600903d80341c16846803900003004000355800040203080400406400011b0000c0c541a500f050b080100718040b03030ac154002c040c000c060120380386038140d500350000169100380e90140c401582d12540280c2d4520003070300038080402c00d01034002a4a0400188100d07010100780d4580c2 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 517528543 1250 517527293 517527319
    0x1008040515090c13060305010c1808060103120f0c1202030a1209051513080d02030702150c03130c0b030f0631020a0c061109040f2a1103040f0311060306 67
    0x541228107a0f905200b842d80d6880200002c4c20274801c2c026072106903118203081003c0f0380100c80c500c9074607803c40c20254105100410018880030301011800b01d4909047d0b1a0814000d021518003480d43c1001e040300d6400c5840f030081c00c0e0040010701c4075010555038481c0521a5481550a6901d040c000410507400820810300c3c8408040002e5080031005000304d414403465100e0390720b00c2d044411411a0564004240800710790100032030441481d003040034201c1c605d800141586a03010041c180040351304901c01c01d0007004441c07418003000d001c0e820710958807400c01c1244401c1301181180c6507801002c15202c030074214502c040c508107080c0f58000712403030349141107840710020b50066405041800282c110000c0000d48a0042114002840f000ca42c0c591400c0400c01090b9143c00400070041890b00142c81e529941100c080c1910000305501600d1040001c0c0048034644848001c80c40d00380004240801c4800951700c849044900803002400c00d00c01c0d00c3d082110074802aa42d1582c400113802c114 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 517529793 1250 517528543 517528549
    0x7060305091905030901030b031501090f0b1201020c070e10150e0d05010b0301050a0204031505060319050601050f040c0e19080d022401050a06080405010204051008040515090c 77
    0x9503804900001030380d4141d103100c06280060303100700c8000c445613040442c056015590600c100801d008085000b0503000031031110031801071506004009001c1c4d210100d04544241d41d400586218001400d001050500102c0c260b0003900324001c0d0504601401c640090030a8a007489140503401d0740c2d008064062802c40b101d0001690f80300c43c0020721440b549100712580e00d1030316100c2d00c14040c40010030012001800c01d404c441c4000c00490000d44103120500104151800b00c040140c0180e40010f0306407610b8000038038200e1509048d0f410900040c91032010010042000d50490b2026210602040c204404010903101e494001600150000140780301619088500885016603610900d07541030325540d04074100196841d1102c0544d110103180d41c2d85100d82d2003076480c440442d8603110300a505080010f0207040b01c51081204114607800072606121083d070495006000040c05200c0303010300b200010b003021034211015105c0340600c130a0304001410380a10580b05006600c040d00312844650700f0 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 517531043 1250 517529793 517529801
    0x303021902010e06030703020304060b0316032402130602010e010209061920030405150c0a080f0c030a0903050d0f021c0507080d05010810150b0d020d1d0114010305070603 75
    0x8142d041014510f8842e0042c1c58400045009600564016035249028207020090b180010722460103a808814000a15231700c3c1c3d4041c00c252544003480040305c02007400705101c0190309203500b5908601c009084e51001c0e40e0300e07950008442240c1c0080c000c6200c01d0b00503030300301c0c0206514290421170402880c840f0003611030803894446018200002400c590000c0d2440405510813039040a03800010309005500d44087c17115080142201e041d8603041d120340c180d82c2c941e10003c034000c011010200b9009007407401c880030b0300c0c03528081400302da80310404208000e10003c154481a101070141e914128a070611500d01e0610702c041da50010305400e03001c0394a851031652856880340c1000018015800000d0b0140010801c010316000b01107000d50400030ba0750b041c480d00e0440c000d4028507001d0700d141e40c0b008528075141151113000400f40c4802c40c4881140107842207030044042140742079102450b06651021102c020301a820080000c8001c00c442ea4201040c00e010140540d80082c3d4100240362180e08 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 517532293 1250 517531043 517531093
    0x708060f10050d050702102703050c030418390e01020109020402040e0702060105010924031e0603060b040e03090907030207171c2c07080a240501030302 67
    0x5042403510f0710b6966400125501554510016042400309644594042c0034010150460301c1c03619a11180200d40f0180200500030020280301000c10002201003042c01600c0041c01d403199010001c4481d20403c000526401e0301144000140540c80120030040b14161882c401d03403400d94403025080100141c0e807508118502c1c1d41190340b940481700c0140c880380064801800718902c0042c0d1400d01c0c1102a0424a050300502d04005848000b049402d04030074032112880f40c0007101d503203101a0440100c1c041c02d00c410201c82c0c41800d45c2e02d007070018412035114070100ea020703a00c100f003132a01140070402940c90002032000e00e070303200707001017200c0c3c0c034105400c03903023100e034508006140c0205075035403040355588403107051541600410903900341a500b203202180d003000326200300322400c0015185031401640000c85030080444008602c40f40c0c13400c0000502030302d01c805c03c98900042da481c000c220700c84d07010080039031070040d000416403100d1940581410b132941500a8500030040c007040150781d4088903 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 517533543 1250 517532293 517532297
    0x10203070201033b061f030303050712060b0a09090614040203060d020d0803040b073e370206030c030a060504020f03060325090f200c060708060f10 65
    0x40e000107200d0a0390005455281007498208003030340c841c01190030a030000f030045003580045421b85845070b40d02d10080047e6a49811f00241d90f80f5005402c40785070204030900c4a40030303e0311101280140b0b056001c0c02408101d552820481c0c1c0c1c4a1642d0029240703144550403080c038032403000d1115440c15801569004002505202c08003030150001b03516409500400d45240c5000000d00050226011460b0b501c4651403c110400340355881c0c160a403000820009800c94491054004080c0d41041100130a10035010444421100c1080a0302d490103a0030010290b10207c1140d11100c80e22820381c07410b141e60010162810359644602c5501c081e0320003000885059543c94004c640c030317542d92001d00b20710b40d10920313515241c0c5480310600d0b103420f4080500064030300c0706d444d004803085070021402d42030b01c112003408603607403218480c846c01415041c201c100c20364081c3e00343c0c04240b501901c003510010341d140c0126000c1380c80d41d0313000f80d40c0c004050342c070203801208622000110341407103c0900c600074180c2c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 517534793 1250 517533543 517533581
    0xa05061f0f0c0c0b130b18011209050105101e0e150a031202030304060e150402150d110c161815051e0f040b011b141c03060e010501020307020103 64
    0x1c1e584007515420f5903089424041d101040c038104094041c00120040d00c00010f050b4034104002c0c889a4400c004808124100700140f40b902c0c103c540030350400c44445034410700078807060524114045110800d40079079088003004110b000101c03452149000700722646030600701401d44801c0c41b1006d10010030369000d50464903294000001460b543c1c1a6027281c4403130b0740a107440342003514094040c0c83c148040d03480c0c60307071041070f1171800c0c1190003480d80d804ca641282d1880c5000e003d0003014082c3e014901d0510960b51400c4d42030701701003c128004001c4603c01000740c1701c02500c0d8824000c51520f031341c080d05125411558a00300e0129180e400503444514400c03030b10101d240e503500081c0c610030b2650002e100074500000300c0d21460030b040540613600c08044505204080304140000c001c50ba0000c982c0c0021315985501005102142403180c2000d02500d050b540000c140008024000300b80451003400a031a051b030018000c60b411038064180da105074080c40c64940310742c00450150400400c030209031044 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 517536043 1250 517534793 517534817
    0xc0507021c290a0902030d08071e08220302190f0b0127020a210603020d0b0f010501020601050a1e23010e0d08040b0a050d0c080a05061f0f 61
    0x14003810001c01d00001062060030305140807030340b40100500502525400c2c40d9140005075400b04100d51058054601113202d0355845030102c80d621400800c00000ae21100364403552960301c01c2d11248201580d480700d44c135605602842e0607172001c0d14400580160010030102c081d400c00b020b240d134007007400b0b0342c0c803140180380c1900c1d12281410281d1003100c81d49610040450480b001d90002000c0003200c4404508141c02614058001000c820086400e0300400203843c0c03a869266015a01031600030740941008181442c1200946100784c40c00c00c000004400001000d41c130015105c0e050351000340c1800c8100345001c0b40c0c00344103840d944821510710000b50020803403c007103000a5442c01254044007008104100014003003489420119000c0c0500221020106078405c04460885411001c469603c42243c08200c40c240a5240710002c064113002135503c060b640030b2003a42c0211040c107004c000310380702d01007003148281004008007124003d140190710250300a0298404416150511a6422135 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 517537293 1250 517536043 517536053
    0x6090c07080d0902090a090510050c040b09150c01050f13031e0341010b0318070305030703170601022103130c090f0510120f08070b0f06040f0c0507021c 67
    0x8800c48040719a103581d1007c0ca02806030800c0950900c5144040030130107400c2403a0401c0d06440342e030180d455203070000110752460341c5444030200d252402103888507890701c00d1921901d006c1c00b4296444140c480d08040800d0411a2480004026030f500d6101c4401030910700c0c22808400003156074040515613034880318007440e04541580030b0001200c0c0c440c04450001d40164443c9404400920401d404003d0010b10200d08014100d83d0403105c60b10500c00301032090741c000d078501505a08010030900010849804050300b03c001044006441d4207070325142d903030f800012640c40301d40096000c440c5020030f480c1d410020422008540192160010303038100401611804403260480d489803014555035243c0ba41d184042e0b10030a900a11400c469043c0701e03140c8103400280e0342020002030202c0e075011080348200107186007254609940706200740054a000c0d26485015001142c5403805103043c070000300055641c5109551851045891f0b290a00030390b60280103c0840c01c40340841c0b100240103544000c90 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 517538543 1250 517537293 517537309
    0x712060b120a02010f0f140f040308040b07020109060f02030d0905030c0111210f04060c030f18020a050f13050c070206070c06020714060406030b030c0a080c0906090c07080d0902 78
    0x1c4488024200c2040718800140300740440300540c0c08004c00c9013a0b100b40c55a10112021507a05403035065900e40da5260015042c41c41680e02c01032200400080003d02c440300400580b42c030318000d8030354044066a0700c10030303205401e00c8946a401078208001c03445040d911035003c860785500501c200c90a14024403000780c2110710041c0207041103000420803200004031140060f241c442c0c188405006400c3c50743d400600010007070401040c503610345540032045032007548000c0d11002100d0041c008406403100300d100d1902c40c90070580c0101c809003c00700c1c050074140295103d408014002e1005001d008015000814010b8014000000c01300180c4000d07944d840c0140c4019030280326143c140340e180c981c0203807506885602840d0308042062500a65503200c1c001d44040720700b5401c0c0800c040d42420006800d00f04400945940445030308004200c0c00e03400224940c0b1480181c07864907681d1036282c200005120110b542c0d000c070260030030054000828080150a02d125108000700b40f50050b580003440c15 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 517539793 1250 517538543 517538569
    0x1140d1505040c0b0409060e011a1b15010303050301150f090501140c060435070b061f030501150c1205130306090f060b090405060f070c05010f0e0c060c0712060b 71
    0x11501e840c001d208900b072142c0c08900501c00c100b501102b210300900c400c80c66024400e10b01c00170320304002182070254018403221541001041c5854003d607160f00d0040c03c0c2d41c000313005804000c603003400320611107805520740404144594a4000034a40740a0045507468100100c3c00003c480030b05c00e58210041c10098240104d20555a501250312201c0a0044000010900c1034090714a0b40500040540400c115514240c1000c041c003020f94403d0041050140c08024071140142507418001c03185078594001030507292034110b2203481c8003000dc021a100c1d458244040d00b00407000314031049850066005005601c0402403000d501c031350701d407691821541060b00a40b09500c00c03e4151080200078130690100c1c160450341c00c502030070140c54480c1c1c0c0e4030006000c2e1500007034050101d40002d01414034500082d44c0800244900000307202000b0181c85022441c072514031801d000c42903540b0340801600c0c503c558140041651a1034800d107100359100412042c4c030711035501d9295050b80d40720704031040c9003 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 517541043 1250 517539793 517539809
    0x9030b0f0105040b010f050412060603021c0c05010311090910050907030e0d0c24020d09060f0b03150403030506010e040e01150b0c0a0212030c060f01140d1505040c0b04 74
    0xd1585000184410f9132484545541045001052211b00f00e400c80241c605540040701c9032096000c035440c3c50ba000b0801d681020b50b1011b4020903008101c2d1481024805d1148a001c1010540380d0750740055040d1401d2003140d041c00310b8203005210203405c0506003103070302c8580b00307002c5c0d81e1940c0d07900c0c08a03007515002d844c40c04c0040d0311440700e402d420300c040100c5e00303190b0414030704150984501d84401100d60500b0340320800f00c5019100449420401d5010b1f51480000c0f55402c00c0118040d16007100100007000852002d00d0030040b82c007801d0b24000c10001509250864080754566480c0d800328020704000b006541400034000c40c04085440d00e10400154003c5c40000051007015600500d203148142c1c1d1001c1d0f9100c1c02001009503008003c10f025401e142d06640c82416407105c200b40500318040c490410350544519810400601c0703000f000b081c100c4a064403404240410300e01070006400300c1c13480c098404075030643c61804204c010f50000350301c64000c1d003400c4803498956084034065445a840004 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 517542293 1250 517541043 517541071
    0x308031e070f090605390102040609080106080309010215340e0f03030d0908071a1e0c0403170904110d0c0203120106030c112b0806010804110109030b 66
    0x4581d98000510102130f10250400b03d090a04080018580c084040041038000d012005208041406080400c041c441103100035900d035500c80b04000d201d943c41d4456040300398240640003c05810120407030707428100603806000d1101c40c080d0001d1980d00050311090340780c0c60480c1d1252440c00c1d82000c1e1840c7c64901e003e4100c81c01c00d0603000600d4004140d084902c0f500084103400079076680002103403240c0d0540040440d200010342000c1c44e0f1802265406820104184242c0c2c890984c0d4200301c500c0344440710b14140d45602410307100e0b64080011215296007038420401407012400855141a40c12520b4086620f49518800070901351041e001c40c0c2002550302142c10900c10b0310300e010b00414100a84011400e0000044036185054010700c100014141d0318580c01c032107984160190381d10241200c048803a014030080440300380c80105940c9503e018011085460381031b00c03c40b50303a030142005a58182003a11a92038a400c4101e078400b0701c41c14854070550000014441c0c00340b09210b0442e2600e144 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 517543543 1250 517542293 517542317
    0x181503140307030e04150e0a0609050406060905013212030c07050108130309030b0919080c06010e04080304140c21070f06140a030b0d0803041a0106090308031e07 71
    0x1400802007602200c0c4030f181018844420300d0303041b280c4001210215400d500c850340320154050010300e080c1c0c010181c4182044200403c1c0540b680000c81140c2e50000104182e80ea203443c880c0035064102052801482d16102003205e000390b607040c0c0310700e02c84010004161082020602465640040c588038910b130001d40c4100425a00440300ca07a112031140c440070301400341d555000b09100a54080140918164000315940c20f1b403c01c074001e10041002e103206120500c034180b842854101d07510108061085600110f590380c0e5840d500d40c0107a40c840c1c5c0150031512203a4681b2408602040020614800e20303803018030700e0303036001001c1d90102c400001c02a48507541e5050070303050040c50381100d0a210540c0382d0400c8965801296000c0300c91441c0026511000c882804401800c001380c06a54885240d410070000d0068a000031400f59100f0018995001000450410315400910900d0003246d0003d0302080806c851030029684030f04210390221141304400406408120207480f40d1001400200b180 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 517544793 1250 517543543 517543547
    0x902031507030e0c0402340503040806150d0f020108060f0a1202210d0c0305090901090f05090d1416020d06050402010239010c0c080309041518150314030703 69
    0x2403070030043d0964040d46003c408401d0a01f41c20301942c50754071200240b08041424946500a400300568400140c0c0c0e42c07143d962742c001d0b540d104255480c103800d00241c0022a4207140140451090703680c4600f454204402d81c0c0c006480d1003800410803038000d500129090a150707111400b0754058040740c180d8101c10501401844084c250b5011025148036540d0403400401c034001401c1c4801f4000d61901c541500400d20781102c1c2402116969034002035904008503280b08150014407000500000c200406d698019443d03070b4038140d4404542c04144205005012400110002e04040d0b90754201c1c0d4101c44415404200350300394050007a40c0c6190b588081c041150790521054070050603da5803654580b99a0f00c440000c43c2c08120101c0d925006c4411a158990145403038021464120902000643e41d48142544035440264102d21440c41c207010303044101039041d692404d88402d000041010303a400c40b40080200044844000d80215031080080040e01100d800081c46203100040c41e180ca0303d034500 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 517546043 1250 517544793 517544803
    0x5061321030e07050102210702060712030207031115011a0405030a05030306010e06071101031e05040606031509050715140307090e0f0c030402010815121518100902031507030e 77
    0xe541150050000498140030780d103030551f11845440380c0d882d5a8040c510000b1000d104941c0c004000c881060460280e00d601603025060881c001d0311070280a01101c0e201c07a031200750785203100c900c81d1050340040c0000c0b02d070a500d01031403100300c035101c0340b40c19141c1300064581088010201c885078000407c025181d6403080745456019400c1d00d4850502c01c4a581d03502e0080d13007402000c0e040654404504010b0000c521a1007800307a401e840800c401e0506091000c0686190700007502c036860508003400400001e403149030b0701950400080d00101e4201042003c0802103090b180080060500c460000151400003d41c0102e403a515040c444907e05000b492501c2001420055440c412030b04006a40b0001404c0342c3d03011750b091810381515683d401c0038090010071003030440d400c100a460b21148544c0f000a0071079081c49084000ca0b40c581e02c640c0b0000045541502c0d40b40181c001d40500140240342c3e4214820b0b161006098034140d25030803042c1b4801d103400315080d00009489500400d885402401 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 517547293 1250 517546043 517546049
    0x15040807090c05070809010912050607021e070611030405101e0e0f04020310030b090705011e021203090a1505330d020a1a0a12050405061321030e07 65
    0x1105110007070103102c001c0c00d14060307400d024001d500000342c05001c0da03214000c0744014014410151150482da41006541c4900455000c1c1c0913104054005090720309006a0780340c4941d5404c02032940300d040400880e103c00640078442c4840c4000e11021a443e038444010301810241039135103066a20100300c030845e5546810f4403180c10701c01d0240707401041da250511110f50040302a60050381d81e07143d440785e4101003c02680081c0240da09a010b001000c035011071034000303d43d42641e603440390960348460140f40710007100d5604c0141c1d00114501001a560002855003c240e25096568000403070301c2c1c1429031403461400c0c0140741d6403141000103c003501007440d40700740c510b940100400485994070112400800e1800b6120781c8826580008540d0f411002001910410f0070b103082c030100c01050403403150014220344012558104103080e8040152090612958110004003400d0303c42c0041440503a00c038540c183c56110860042c82c800031600322906034495000d40e070014400903032090250401c04660 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 517548543 1250 517547293 517547309
    0x507231801030c06080603031b03041505160308060117010311010801060c0506010519050d080d1d0c040b01050c01140403110c010c1106120a0b04050109020f1603030b15040807 77
    0x1100600101d0f89140c502c02c240c031100c0c101014207440d07201c0002d255002d40320010005c00d4103c241484440d801001a03c115035a4001c4803d82c400407030000d650718001da424100e04004c0c51031000000c41e01c034101e2240c01001c11305040e0800c6921011054003440260008d07904103404814504030b0f540c1c02000315004040524080400f180240e58141e11114180301b618070682d090004c500604585400d288000d08004140350009041c601e0510b05a40009a07101440d61602501070301d8040f07141000d0400009450180030b016032144100401080603085441c1080805e01540d5050003091003059103174240c1c92404040386c90107140003003049640c0d0000740c8407600024161780050b40c00c4006911103544c0f20100107560103d0750041103840c0594a0302e8000d060450091115110bc20b034172001e0a00002d40301030007030341e03250443c08090744116030000900a00070814010744482c15681503403480c0c400d180101c1d41150003030004402008035594803c011000281c00c011070307d400c00c4400018a444 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 517549793 1250 517548543 517548589
    0x8070c1a0306030d0f020f10051506120c070309050901260d0906080c0f04151101020304020d02130b0621060a0f050d050f06010927080301050d050723 66
    0xb50010076100c84400e82c004041c80b062503002003105000b880b01030f40000ea03460460301120000c0002502814081c0c1c0d4400402a0188a1440c9400c2600c2121082ca001c0001c404440e200c60014070304941c4411002e80401184460220307007170f52485903290082414160800003010300319040001111540c00a2501ba449a0480710101e0341001051080300c21600709221681d48800300b00d8518820150344400d0f1030400030b80824100140c681c000001591507451a80549804500608038401620060741c0310380c07110f5a440040c9003070791919030001120040821003154a6000c580150005080038800c4295083d075175284260041003594422000c640b511480c1d07240ca0308a407015a80780c09028001d0f030180d0003090512404025050780701222204a6003590ba480005000420101c0900e035100039440d00c440320414128030f001c02580e5048081c062440e480c01040114001070400304541038010104001001c071006014110f12144101c2c604072540154000c20507410042c5405000740c50907 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 517551043 1250 517549793 517549801
    0x12050f060901120f0501060e07020d08090c210a060506041410210f03080105040c1d040b0112020403082104031202031003051f180f0b0a02040308070c1a03 68
    0x9900c5524112078040780d650343c401c652030812401100400e04050515030a0401c0060040d00d02101c49204410b544d003590300440504008441c0300005603042e85040d800f6400301612803400a084040c0009c50202c0806803149a00b50181401280902038031099a618100b00150800c0d00030481d01070800c501d0103010341340c403c1f0814001c00c118080c949031303540103a252401a071941d03c1c880021540190881c880c8142c0b528000307002e02403d0040500590030044d6506049010380304155420310403008200e01400310209000003480c01003201d50401044000d0b1188040726032000744003944c001d00c2c1b00d03a034807400500c041105a1140300307159443d0182d42c0130400880c0e8040290065888609005640c90300d460f155001c64504503000500240110341e0f0711028064203a000f100c04e541c2c01d44080c4403503011801e2200d80450031401c080c00c400000c42042d00024901904242d0000c01d1400050030551292258411034002c1042110241781d158014400030341140e1040c603038000404012451890 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 517552293 1250 517551043 517551049
    0x411040816080c120714120a0606051c113115060e0a060c0c05090a0c08070813060203041a0c04090e0a0321110f04051203031b0d0908040612050f06 65
    0x85403040f4116102d000d00954044d640390920110400c10300401c403000e07108c6500300b90005040314480c0c1c911500380400c0141280b0f02c2800956541500141150041c0007100c0030702008000e228124580a000c0c1c076008071903485007071488554500915400200c62800d000540c0241c01250846d00034040d401a840350307039558580d0b2103801e84501e4902468240214503080805580e1600072550040d019010800d0008003580010180c9480796508207040d02e8024081e14552000c0d28118403580d44c141400020480e1038000319001031203101a40501d0030a40c0b41007140d04025a1218a072500000e0200131114040c080c881d500b140b0315000d481308043d180d402502001c2004001410008a080c002100700c4069000089075800618010358a0800408500191f4403d0154038410b00d0000e104120110000040c0ca101c0c0c000e50481c6442d00404008600894000406a07582d950f155411080040c00820240004100070b40342d0204e101165103186069035001419104c6041c2c400c1c0030440507036 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 517553543 1250 517552293 517552303
    0xb130e06010b0a020709090b1909030212072d0b0f0106080103020d0213090605190603020603132105030f060301020304021008091006030b0714070302030301050411040816080c12 78
    0x1e0301e403002c015510710041d54182d080060981c05a2010b070b207040c441c0d406110044024600c9842c00c0380240f0b005490030300d55a412100c0310540600164498001d500701d106990004002c00b6014444d00f0640380d1940d4890401c1c4a00b12003c4d9844408101e904020840e1a250558001d180d040a42c1103640c100f0305c00804800f41484041d1081407015000015034482243e010040742c960030003071240310a40c2c10208040c0000b5118500496642034102e102c00c4468403886090b00e80c028015451911802c0450b02072408440050300c15640803c0141803006002100c2244460359484480d2a40740c09003966000841c0241440d019900401c104001030b0f4440d540801014181d042c00082030321210b440914088003040142c0d15603142003004030610109180e510b2040c4295692038480c81000400c2c05054007031208010007513481440140502c0c41c098014074500194484200d041590342c8c90240e251a03a80c15818100c104072038802d01100d01c090110300190042906d07080802299031458a40e18 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 517554793 1250 517553543 517553549
    0x601111207080c010f0509070503030a0503010915080d08040c0608040b040201030507120e030d0b01020a030801030809030c041a010305060a0602150604200a08100b0406030515130b130e0601 83
    0xc940000c00008104207101568603180b1000001c200c1e0aa41810000092009903485444d07072040038070004a41c81c00100b00e460844265582d80d0075a441d202c0100041c0c18840080a19480c0f10580410104403c22000304e45880c15a69600d81d4106800c10650402254101e0310807c80c01d078080001182d4254a050740055080c0790004890741d442c0000c0700d62080c1c020615101d1400e04601200d00b135400809402048006241040b010000e40d006a030b90301108000140440c400c10010004512a100544504440a030680e5030f103000900002d011110f2031602c0036107030f8005070041d60141d42d061103403039484542550703140e1400d0f0411501031342d2100600c035440916042e1000054084d1916044100348490402200701a600405241d04c0b1940000202d0030025144500041310031400a100e4011500d5548126252a05045044000d000c0041c5803100d130342c1c800483c0d4541612600c1c20080600c4006400040c0c01100c0c508010040398203a40780140c1c07500f044e8124116000100d003107811 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 517556043 1250 517554793 517554823
    0x7210c02060a02010603121206090509190501090215071401060b0306040209030a0819020d0f140706140a0501050f03010902030c101101020a0906030b101e0e030f07030605060111 78
    0x90b41d2044204074050036590b00003e0401c014503c100c04c590b608103c4c0c908220003104000d104070b0b80c580420700201e032011a40d02c0c2c516801040700e00d024822040c070f03080c1c2c2c4602400c00440c1c02030054001c12186500402e922901c00d000059410500200da5400c403615507006000340112494089404034502015009510480d400600b0f50f14a83d000c0201c035407515401002c071501d80c0014041d0348014100003c90b0070141c0960440407a8440c421145c0c0c080a4015440e00b9126908468400c29030313412042007101c00b039503a01048210504000038081c4120b0342c400c0c0c04109507042c50244000810300290007406a81008013500060f9004201d0700034405054940c0140103d110408640c1c0380c2d0800c030303122515440040d5078110280c2c08401903081d1522070320144454011101480034074008100980b0000e0902c0350441c00e00300e40d8900050310307010b0624000624800410000f4240620818401801d40c8071807070400802c001c0b40140b84c0e0005003400d000c007440f0041da001949038000360442d0b43e0 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 517557293 1250 517556043 517556047
    0x80610150e0114090307080609010c08040507060c03050f07110a0b0f27090405010b150304020d1106040b18100311030708041e030c0b0a050915151507210c0206 70
    0x40b01c090040d00f604d1a1801c02012a888a5503418481e9210182514124030075401c03e2203400a844c0034050041c0103680c040d0040c004613241c5241103441c3d64102c5411402c0007010858946275010386405408c1d003e000301c0e96480c03603404202c1000f0990fa0a54404100c01d00b013402044402141e035019100b0103c107180000e080010441c94081103118202000c903070156400c400c0c4800e0000550007100c244806032880450340c400782d004802c050000320380013948148807038603010005950403803101130420040e00207418207865030101041c03504a190026400409001090064500320b02d11080f03540060070300b0410360014400c181e40ad03210081c110020b001d19800410100460301d02100402c0305041c880715400901440c00030002c55a540083d5402542500462202000fa01ca094007800c8041c000b07103003107003212245280f681402840f240039900c0030000411903407584078420310741c40c02d4620303440e0350740f0550302c1c000303404010161500031810075490042c031209030004400804160116000390b = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 517558543 1250 517557293 517557317
    0x10e16090218030109200d0b0c220b210106050405090c07150209030f010e07150909061d07030c050d021606060305061801090f1b080601080610150e01 66
    0x20340b050000e145210303010341c41c1c00c4080c003e0010001c3e5042d1181e0041c09000c0103030036244100460280d00c24030150001c10b05401040b24561160010101d201c4240102512850382001303640c2d00c01d09a0703000c0c44c03090500040b070850f10782103d4400c443c0403030300c900800f03441d506140004003240514015140110304860208401030480001e907809151300c0150b111114080d0003065019412074942d55029206401800300c01d110306005402c0007182c004001c0440924000e4030f600144400d0080c20140244d00d0000f241c5110540603842c05040e20b52010b05450f01c08910040f90020010308820805280503e21548244d00400b00c0d01042c0a0003805a19006245c041d00320485080c00000c02c0c07180303000b0b4004108400813a055200f079400314002ca80800002400a00f40c880c40341c07005004031002000400010248154031b100a0f400c14141d90030162110003103446c0c20001c0e00040c1403917003c902080141811a45ca08000d800c04400020002188190144c1350b0681c2c0c050950607c10710410314 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 517559793 1250 517558543 517558567
    0xd0f050c2209050115082208091809030304110a03081c06091802090a11190c0c091b141903020c03070b0103170705030a050903030d0c11010e160902 65
    0x180140c407890b40108110359540084240c0202c0028000c0301180100c4d000400e1502e400000514a400054000300c050380d840d50382e000c66a109c039140741e501501c02c0809210f001c1c407440e2078610944111004507501d08250030413108030b03a8206d001600c82d1400800c1440010501c40c00d40d603280801c078040d15407080c5200c9984020704816000b400d211464445001003541c0c1c5010102881c0340217840303030350745521440441c01c1900c10a4103000540401000505611100160000b0400e45a0301d4400a200034030f948400c261512a403000042c6070b22051071141003032056404101321003860901040395003401e00240168060010300c50350808200030040010341c004d4044592041581d01a2507807181189411034003090300707010503101082c001c404034101c42d280004851a0341d812400842c00c246030b4410844e101d41c003204444d50140414001c0f040340c809507010700c0803405496200c2e4068042d02035205406c451043c1d81503403103039002c0000542d2410f200d20030101540d40307444001d0b0780d0303080030406 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 517561043 1250 517559793 517559857
    0x50102030a050c0106030f060903231b0c04060806090106050402121602070509070512150105070f06090602161506051e210102031008010506090c210702030d0f050c 72
    0x4064201f0342c1e925010001c0051070380c086100300d80b0a4440d0740414028041080c5500c44407402d10206141c20070039421111540a402054600c2c2d507021030b0380e03500c410b8002c035055506552010b0350540c040c5c414030401000a00610001d403005403800c40c180b082c0f058640c02c0814001e0172418424040c80c0c14244418802c2c000c1c0e002600303002e400c10120341003c28004100e0f80c0518100560320191001040c3c6815030b000322051040c2c016903070b25050840f04e8403280001403046504440e80c582e18884000010480d00240c500b401455200c04c0c1141601d0528100120b00b019103941414609038007070215a56158032100ba0001c4480041c1003211090040f4864815150000740304100740c0041401102054000750310500d0084901c415582d03490352190f090351801d55095030311001c2807000401d510001b0000d0f209620340000180c900c00902d503c0056018030035a801001600000342610003080c0c64014054442e840b42d03800c01c8a85800881014607000d00f800d54440f2400f5401980006038070155 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 517562293 1250 517561043 517561049
    0x1c02160605040c1401110a06050c1b030316080402030706110f030d060f0f0f140621040318030b1617090a1a061018090f020702090c04050102030a050c0106 68
    0x6010880c50402d401c05000401d51441124502c1820f4141007400e548101c0040d804d10343c07075200525011150f596080060040141400886c01040c050006282032185071690141c0c68100913560728107000c0380c0d10149001c61440320051003554030074080103850005204080300d0207071a0802d00000c0c0688035904202000780c002034a440301052032490f0b154507030302140031585868034180425940f041070180c4030300544100140715420071003c0010a90b0882d07100308920f4010805480c003060741000d0400004502d0310130012810000c100301c101500b002c2c0030a01e00d003002030103001c0c60785507980e07000d11114010a06c10712181c2d402c0806111034040d00345040c40301151a86040c417890489400c07a0b665072003d6060314414040c8108074245420b01660703d002e0072010340048081000c0001c00d4906208102071110310701c10920000880c8600703481550f0b40404220303400350b0390b2080c50041203060031000d040000c0700801084104280d1b0f0700001154603414aa00f041a240e0540a107550b0060009078 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 517563543 1250 517562293 517562303
    0x30e0c0d151a06070c050f0301111b03120103050102031009151a090604080a03030513020f011b120f111915021e0a1707080123120d02060c1c0216 64
    0x13140100412020100310750684100b900c440d1842107410b03041500343c03090608000c4d000502040a0550300700b40221002d0360b000448101c1e03141082c5142e220380c00c080300368815a190303503000c4144541c80d5041c01d01e0b2401000c86d10310a0040c1c089040c3d41d0132000b11948500003252060740038910700c002c0b44a00f61510104001c10030790720b5a540c1c40449454208010381180028640f500040c40303820010010041a40c0140005244140c90070064880600c1203001d0215400461041c10004480e04a0058000c20590780d981c05521302150291480d602c240c000c002e01e0b000340441036103003800703052513044450b005a4800a005410200f107802441080c54014501142e041c004200084080c014044003001d580c8442c40103140c01c58054050b0b406a03120400030f0501001040f100c0c8001e0301c0c055103d105d540d440d8440020b1000001d002e4440d20300c02c5502500a115424801c41c0c050202c0d40d0311034100368129140c000d11103540d40e1815184141101d00c0303503011401c0c125103c0044190303080e01d940a = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 517564793 1250 517563543 517563547
    0x80c090406090e010b030601090612080306030f01060618080f12031b27040c08040b1807180e060c0a0f11060708040203010c0c050c130b030d030e0c0d151a06 69
    0x41c80e10f007806070040c1e03002c1301d000303204880c00019140214840e84003103030804880c00b103008c811561081603a074005852660301d4810000c498070094020301c51000240310383e88031542c190032142d28039500d242082e8445401c2d5007010941e03400071200032885081807074010302255541d80e9540ca02041100f010054039107030748008111161220410301d200c03003620000d00c070541542d5034040704010a55009071801000119001e012400080c50520305903044000c900c608600000c0071001a4174011496000001014440c3c010000c14402482100c07000070303c003006400140380152016000307205210107442000717401062810b603c0e100307001c0c010300e4140500545a8504090701c00809420040c0d400360310239460460f891050b01d0040902c0d1044c103a01802819440360344004001c0019002509103440c0390319840011101d0341c0900c4031103411000c5031400180719018802103458040e1805405010b511864003440100c1c1c4c09070f0551007021554040481c98642c040a0007112844c62a9403603000140 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 517566043 1250 517564793 517564811
    0x1d060f070b0603010605040902011e0e0d0c051f0f08090717010b0f06250203010b040509102720100201090203161a180d1208100501080c09040609 64
    0x141c41081c0600811030090180c0c54440041204650545000901142c041c0b030451010265050048002e00c915007031000090918401003410014004411200088002000d001c945031403c43c0700c8282e9070000141402ca40c2810002c0c008002b461106001d200780c1c42c0c0000c4810300c1c03c01c012009000c1e076041c40421500c00e00032542c060490780d1610f6114000c401c0940c00305050402c1a80c480000d4009102503810402846104030908150166090354039001510323800d840d54040e40b40a06081b000030442000e40d8014441100c2020701c0d0f03428520006020780ea0040301210b43e1034102500709044540041c08030f8003a010b200d00034800e06802440d1004070328050b130f4044d84130121090007a800d41d0101c01043d46512640c02c41409609400c040308080c1491900c0305c44e0241680b9030344030800d0801d043e40500020501000395400f00c4884406c00001a0220f500c4401c0f66044101ca0390704441e10780c00c220001e40016030082204442c080c002c20918547d94641e0071210007840854410419464 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 517567293 1250 517566043 517566053
    0x706061202030d210f0e0105010806010314070302060d0b030109020a1e1a1603090308030f01030c06030b1807210606020106061b030f030204092c0d1d060f07 69
    0x800034401ea10a0003082d09040d8600e02034118901110f03d42c500b9065442d24010024000b48414611105110750765403010300081030074864280a007595600500456145281107a010582d0146915403034100314810801a11014269100c1400d00c10340421a1056000400d00520071036a002e07600990070b41e4001044c250300c12045c2407113120107045200040d21210380309070800c010040d9644500042001c2d650b203050709811a10442e00c240b42088541e0341c0c07a1190034090308180c903c200a00c000000400400c40c10308030381c0004110500f401c2c814440550000b0741a200d40c1411301030782407240390004140920036049860b010031070410f0785145100030f0300801d00038031907401460095841e084005c10158052510300c06070b6040c01801c54010b0309140d0341142c9441030b10719081d040c940c09000100350b41802d8001c9000c1144032406208040742c00031071120f244103281d115285146c000010201007241d10a04c800540500da00010914280d00c60100702284140c0741d40d08450040410840b003000 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 517568543 1250 517567293 517567319
    0x110a0309080c010504060e06030903070c0602011e06030f06050604150602010516020604120c05031603230921240a05010f050108070e01020c12010b011202040f030f08070606 76
    0x40d1a40d044a542c0701e0810010340315803145001d45404038215907628451817514000950784114000c0940f130812100780d6951307100711310580200c03000d45d4490046000d0700c00101040c1103c943c10102c1030080b82c1c5151145a503440c503008014180e16194000100151910340019808400d85140324498503134030403000b80281001d8031500360700ca4503032420300031043c800100c4501858228418020000740c04400750343c5036607841d1381181c05020034480540e031040c118000000d03082c081d450f83c182d58512005100c02c03080d48400c1045024070240302007011900e402454681010103142c1401c20105419512483e06821044600030f03209004481050b04c00244412030203074803900e00510150341c07248150700c1034003294025280000c500100185520380300c3c3c01e00014101c4180182e500c001e1407000441c0000291340c501d95080e81d141d0b8408600c550b07110398100c0783d80188040450030242400c03910302240c0130a03c0007406980c0808605014041c15200b1101c510b98810010000c69503074207292020a = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 517569793 1250 517568543 517568549
    0x30e01060506160c172a190501030e120f090a15180b0c0c0d11120304170c0307090209010212130f0b090108010e070207050d0813050a03080403060903110a0309 70
    0x1a9814000001e110940380310110007411001c4058001d8031110a2a0386446504005041c031030360f1001a020070395140e104801400c0b000050031f020145040a0001d001c0c1c5001000400050b80180700d4036070b500d0441416201660b121b0880755a81f200c030040042c0000241340c00c01e1000445900100c1e40c3c00d41c00020b0b01d04400c1d180e1075102c08542e9940f8014000d07009010841c0001e80105006141c507192009580000b03d1150407c42c400c3c43c0c95001041042c60f40480350165544001810300150740280d0300d50705d070f0442c000b00400042b00b041000c0381d241c2000b0310030000800e0300865008003a038001d1003180699a2101c001c903454078081965130950840720710a103040307010310801c00304000e42804100c401815041c2c5031084103900c0c2401c04801c003007008003075104602900d1004601e80e80c400c000a04440c1c020404142c4804022002ca01514419444030b48030b00344201d4100000b8108000351011240c101100050507105800c0035503544811000da040b03513001d204100b504042e045082003081e = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 517571043 1250 517569793 517569803
    0xd151d0a12080705030105040917070501050a06080f07090903050f0304030e18131b080111070b010e0403080103060b010201020f0f0a030b0111030412020312210c040f06030e0106050616 81
    0x48250385032042c1d0301c221065070840d0024404000500c03d41c20300d9040b04000d03e1040c0c080c50f0051140c07801c078042d035070054602129a41d455105204041071507005801c05420500080e040540c1c2d03030001565251b034644100c01c2c069844110b20303001d060286040d24281d442c47c111050340ca24051500070140380801c030680b8070a000113820a601b00c0301c0821036600c6860340039001d22240c1029110202402040c10701603160401600c404190241c00780900645541e55995407a11344a042c45d00300360001050301f01034027500d1400200008071f94410131903811260480c0303000480c800001c0040340a4880c1c20b88009031a5400030300d04103107080001c010505141a540c04200d2501c1d2840112002c610180030302c803003640180800d1010780c000085420607a032005017101e446110411440940350001d4152031124072341c20503c15042c481c401c0829a200004402052806003083c0d003085071000c060059204050303444110607903440c400d40c040c001400700101a10b40f5510326800315002c40011040440ea = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 517572293 1250 517571043 517571063
    0x302071502030406050306010c1b1d060607020d1425080c0d02030c04020d060e0901020a020d020f030a03180609060609061e030f081303050c1e0d151d0a 67
    0x48054070200035941510182d031381303451454540c0c00044550501c00c40c401d8480074410308003060425900c0040e078000300b410004d520800328080094009a01005049034021070040100d4001650b8982c042d410096200d02c3d0340c400d0300343c2494203a203003a001204071610500c0c83c01c0000705e140410314003a01210b000d80b0860311403013084818044c00b0300321094029095480350042ca006480d241c0c010701210542c0100000c0c07841e40da00800d0070342000076188050541d40c0025110082541881110f188066600040103003031443c2c0503150741d0b881100704040405a0318402e0f01d0076010940300454105410220500032440c0d1814020300502980c4601c1110520300f840004040004865541c140342c824105203c1c180d1a5071100a000000342c42e013151700f5042002040b403030402a0b81800003840c0244000c2210003004010300612400a040704000040c064640c1100d0755140d0450032661030380640d00c000c7c1c000e40d041c0d40754050040c680f41000800780200c0c1100c0c80030000110380c0340756030148400d21 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 517573543 1250 517572293 517572329
    0x40623130618050d120f1b020d080c070b101707080f0d0909110f12010503010606050403080a03090809040c0206090c0109062312010308180301151719030207 69
    0x20102c102c80008189410002034540c2e40e03809403403120658010604040b0b0200703480c1e4013040403190001e071000144c08000c9101c94400340c0c1000b017060055141d04024001e41881c080354446402000c0e00100358008540c005005819094082002403007140140e01c0c40c40031140f107643d1104203d010307414a6224615101090901c00100425210442e450384100305041410007001390600341c0c194070070b046007005032000401c0d4100c001c020020003507220303000c1075040104143c20f40d011588034004012090005002041c04003003120983c403c00e00340060b41090a00d40803040d030240c2c800c07059200d0b20b40003d0f107040b1900807400911401c402025195003013422001500c078201a4002d00c0006400041003140002c01c1c1000800380c220504813a038240100450b02c0b00c0340c4031007600202d610314004a07510503001903410076981084000c40c02444034010041200305540058400e00c00c03002e841c080710343c410201c18410b2404400068204418031034140c2000b95440f0120700c10b40c511007a80000103 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 517574793 1250 517573543 517573571
    0x70302120c1e03010e241005030402040b030a080304060f020a050415030605060d020406020111030915220c170a03021b0a05040906020a080709030201080105010e1306090f0e07030b0406231306 84
    0xc061b540c0c10042245082e0b002d413075401c48181d04028000c03a002550390442000b142c0d420007480410600c1049203607520f2500d0300e003080688402c2094004180e00620041e02500e4110f82510103550070303246e0210402440c1d441c114043c0045a1203282c104c100090402c2e8801da154000300280c2d41160028007024000c109400e046200448032582107410010701d5405041115000d190024128508807294203041e08600c02c0880c800c4408880c4da644501d020084202900d402c2e070700031140480500b00f249083d480207520791001c080070100d00c10904a070940c4581d68003800001524020340104005902468500000c3d40300011890124000500054000d8450b03207152040e6a4103950769442a4030309401900c1c5514030300e0302503510440c0085d80340c410307281500c43e80000342000d61012a45490402402088407517220820104d6048040180041091481010b820583c0504002080641040c1d5a0082c2c01c103100840b01541c8080240400340070020724104c0101d0060313a08011100d822908 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 517576043 1250 517574793 517574851
    0xc0207050f06070213051b1801110a051b0607050709090209180a0206030c070605040302061008030f09150c100501182d0b0a060801030b070302120c1e03010e 69
    0x1c029808410045c012280365456082a608420013500c0c903840300e0421488140c4907005000700e56034a080c0c041e07441007039684c00300d42040810928000b80085051a40303401d0b40750a40c1c10042e0150200d6501c6060094598a080301d615940100543e0050b0f600d894021005e4280000141d10071030b15403020400c0107480c07014001c032002c46000102000c01580d400d012040d080141080841c082c01d116a802007521380c000c1c2031155100b640948114640100c45801e10f44054018480592092100002441d000c004650030f000e000c43d9103c90302010050000c00e98411000180045e0282000c80d031500d46941d00400c1c1660381c40c510800403040d0b61100e000855006c05440c0c0701c6071600b202d80e2012102046054a107070b00342100c0c081815040c85022642c1c501050b40701b000050120001081406113642009801004a00c4d066107444e0203800480d410a6018110002014001810795883c030703886070181c0300e00074030712040300d440e0341c0d54110984480108507a21501071850203203d100086407404 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 517577293 1250 517576043 517576057
    0xd0f11040603090f0b0c0d060b03060f010e150712020c040c050307032423030a0c05060a11061014040c050d0e163f06050c0d0c0207050f06 61
    0x80020309181c5054001c501a0580c0c2d4000e9039520842613101002c1114001d520348144880d441e002c0d510920009200c003106c0d420390240c040c41a040c030070300c001c0390b40d054007412455100f407a10888000a40c000615000d0320348244460603680011041c0810484015000c03c3c903803585c095855803160078050009070754103000b4203000240b0420000c1c00050003580300205001d0504025805052040348010f0360b103541d504a210f003811101c452507080318903510441e508482c2940030303120790a220f9440080b480d240380079080c8240c41c00700e40d0307403000d030b03c01d50031500e14942030fa0494041d410031040c0030511003d50b018640403417184000b0030160382414000c0e0b100c5424155501458441180c5404c0003c0c0282c00b40da05081c01000320068900381010007240250450300c080c204209100726158490820440191145980086075052621942060340e070046800010200e250341c1c03401c111507000c0c03007820303c0401d500d85040c1101c040d070703580066000180c0c0c2054031080c944800c8030b000c1010b84c1c01901 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 517578543 1250 517577293 517577321
    0x20a0e0a0605030610120e010e01050105030d030921181e0e0906010b030a020d090c0504061e0b0d2901021216060b03030c0304031506050603070804030f140a050d0f 72
    0x2880071045c0b28850f0307001c001480900e0b80d0000d0101581c807002400e40700d00c120034608982d1140014080d9150512485400c0b0031982810070683c0455601c1c0903890031010340c02d58151110921680702c450042c54103c00c031200c1e02154080032030700d07a119121941e10f100110340f43d1490040001c01c40c4410a500d050007a54500010300e42a841c010400400741c0c00202000360180d024001144040c0c42802200e803c54440d803c11a802d03801c0c0400d1008480c421b90008485c07416030b9001584000c1070115140c20f0307404602405a0701d108952040c00903210315239a030440c100403034800c11510004403041c0c502c0b03c0b10907400d03108030524481201d90a0700400c000041840700100c207c800155041e440500b1408000d81940e040c210781c00311507800c58000740c1c01540c00c0d01c1d00c1d4482d51002500c9210303403800390a08a550904509003c030005008040040c0b00038140050540764849090040c0482130b20146c1d248070701581c1c0c4800d9032008105800c0007a9542c1e056042010301e4400c942c1c0c50051001c11103a80c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 517579793 1250 517578543 517578559
    0x3080c090d020405062404051f0503041203020f19201504020d0c12060b030d0507031b230105100b0f030a0213150216050a0b0913020a0e0a06050306 65
    0x2580030000182809441785034441c0c00b04204000340c400d0140202201c0120034002c2c4d4845140000f405411009105440080385603e4040380010341c010080d00e0b041074101e5160840c0303030f07142c4006800074032924100b0350450368003103010040100340c1c103940507426440f81d8950a1139443c4d0400320166910380d500040c01900300401c4c5c0040c0e80d10110303a02e644140014901c2c0ba04102d507407520007a5016a800c01c0c26150311520050f814402c40d0b01601001c01d106500070a29a5500100142039000d034150003003c2044444e605448500d0340480d0700d9585401c820a10000b0440d807154003041c0c0072122466403a9402e00d400600d412074802100d004444003445418601440d0040c0d110381c46c0c0c401000251060340c02d000e0a404102d02411f4600175000b540002e040244600c880a842c040c1d14044c9924513206004061180e0f07180c41003000102d414055100e603c611619000071079440b2070740d580019480c030100307840c408c49500c0300c2d170410766020075654044891340300c3ca42151305100854a0542001710 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 517581043 1250 517579793 517579819
    0xb180603102004170d090b030105010305090307060c2a02060301030602130f030804030c170a0303020d0b1e04060e07020303061c080a090e0702210d02120901020703080c09 75
    0x120340c1040d8502500c4803510307001e5030380c00100c42600d50496084190141618004c004a4640030070070200c4681e0036040c1142c40b180390101000152105006103410183ca6034042030390040104150741506a03c800d0501c035840e000071000704102041014003503030300c02c80801c074005000c0e80902d944031190081c0040b46903a007151600700103980640710b1200003004507880010600c2101c8580c41c003551240b8201c559681c40d500306401c0b52190b603009400c6c071980d018605041e1420024205450316454180980c586201e240414000c150701d025903500510f40307480c96200088403140440d00d000b000c44003000b040342c80d0030183c05111012240003000d0b9000b04045851846d000d0321800c0c4c20701d2039004100131403017250303622002e42e000810502e0209505c4541405001c01e0b082c41c441d4040454402451030008824110540405980d64070310810000243c510313100b64076404440c1d200141c0230340c0500909002c8140f900039444500c003640060303075442c046a200b50001d400c80d0890b42c00181080340c0c0f514 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 517582293 1250 517581043 517581073
    0xc040605030606091312080103050d0e010c141e030d0606110a0b100b120a0506040e0a0f08040503070312020705040603171b12040501080112030f1b0807060b180603 72
    0x72001d00440c40c1c05d0b20b01e000a6000030012038050001e0900d540c0c1304801545103140040ca404000c59181040c032120022990300c40c0d1344800c00c0f024554000c1244104105007042e0541404842004440480361803c84d94a110200100420244130b40d070304204a165682c00302103407440e4244114903d43e07005002847c0220301d1510791680c0040c0500300d84050140d540d4000000c5074004030100b19245090001c00042d80850310540380c3c8614203480c00d001620b45580185e440d2150503034018907a091410151083c000b440381510040c29024044500036616802c0810400082402c40f000510802d0004209400c1c0b6001c2c07007040740d03840104020340c501001403003190342d0415101002005030240f10359500103000c10210400014a0003100c0e903c0303041000040000030142c01400d00940d0100305440001c1e40010998007481d650700d402c080054100c0c80198003016030b40b030040c00c0001c010500303900780300203580101080b48044504442044d11a030100c07201120860b00ca613403580003458401c00c034030 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 517583543 1250 517582293 517582309
    0x10804080d0207110111060103121d04110304021201020405100f0c020d060b030f1504121808012a0c080c0a0803040c05210a061509020a020c030c040605030606 70
    0x51090540e203052401e46040c460880c1c0000390281e480c0c3c0410408244256080301c864040303005a0005480d2075070441d107030009080ca060b1120001c00010031982d0700800480c5540c2c1c522a80300800a03c010300ba14210b00515803c01d9800b0b9120b05c40c0074600c64201001442168201c5101401145892000880c1901c140c60030341188400d000c02840100011b07030714031281e1300082d03110316000102a4111002c2c145001c00000c14581d0b9039020413403010396444000c10349640154814105071000ca11100304441c0c034850b0506218000a0002c1c005c10b032030006401c0150300400c000700d140b0b041d005c8a04000401c0c019101c0100c00300b800c10442601082825004003a03042c07842040754484101580c600202d9030040702d06540400e40014103012034030f005003044000a14010182d20481c450000007030312510382c03140080440d96104011101c1400b80f4603244018610600210344520204001070340714141112203074802d000350303014507410b49081c1c4910000e442c1d01a00401e11075030f03441c0601c0100 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 517584793 1250 517583543 517583551
    0x30f0403031119080a1d0109030f030204030b0103061d060c030f070903020607150b10050d0506040504020a0905041106070809040c051e03220f050c090f131a0720060408090108 77
    0x250b00c46d0000301e00700311391140e8048035000d8100006084620b50500501081e10201c2000401d40104800c1020404140680e03065a41000001a030444009154800d141300d00c2e100d0940380c0101010420300e8601540518440e090b514045051070303680c0300b01116001110b00000703601c61018800100400c00d0220100403103600d4800000d07200005800050082c0c2a60342d9a50001c0e0002a00160b030303000c60b0252035002201520241b055003426400102d009049029441188d81c0d603100003000d1003828514205600d40140c01180d64816a081c0a07000340e001d001e03418041c034140b0502031001c0d481001140e4100c10b842406211022a420100d4003d07030010300401124401c0480f24041a18034617403401026124400e40610b403825407a12a0600c01c544a0141c03046441404221103002d2818810743c3c0000000891400c000e81071902102c520001c420061008542c1e108001011f9000342058070802c03450b408c041c2081c010b01801c20b6862100b110010700408052004036180e500681c0c0040d08 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 517586043 1250 517584793 517584811
    0x30c0d080d0603051e100e060c0f0f0f0c010507090501050d1503080a05120c0406020309010c05100905030310050d0213050402130e1c020a03020c01140f030f040303111908 75
    0x300343d903130300c0f581e18001000010441c2d40d14608207405020b201004251402141c0c2a003d000e002600c0b20017a8803407030020186119031000190310b0a00340141e10403148003889a42146484003545654100c5540102061840a600e0300010480d0306000300441011590140e44442ca0542c0c46004071002d05001840750305040c0a0690200c00201004043d00b544440c41c0d07030386502c4007403000b40e600ca1035801504101c0c04100811081c0b00450b03011007181c00e400c0003030038000c0e645c04981c64074510389000b404d400c4004038540640102005004002580101c0f5a154494003650b1104104603510112a10080d400b40303200807060081600c07030704255031083c00103180401d0b4082e080118010386503800303c040d0706070b000804c110f540b00e8071002c04020400028402041c1c60003450390040d40d20341078800d80314140450000c10745040c01c4800200c0360341c2c54025684580728103210b8881610040c00f6202100460705050b020380d000c2d200c040907140e003405881000000d031581980143d45000c4044d00350701c1 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 517587293 1250 517586043 517586051
    0x1202120c090402040305010204180c082a0d18060c0534020904050d03060f030f140c030d02010203090d050c15062d01020c040c0914030a0b010e040b06030c0d080d 71
    0x4500c0a1001d0001070ae2080c080207849408120854202c903070382c4400f0028802c12000b4449801c459a440140082c449803000c4d42d0b0481400010304113000b5000700040b00c80c10000c012240081d0380e980f00e802c0c544100750901410780123040c1a40c15000b0401d8070501c602c100070f440c0340e850f1041c0c03180a005010303203009642443ca103034000c500d941b207048500351070341d51000043d02d04c481c0c0d151050390014010203104000f49825541da4017244645c5002c01780071a24880348141070020180010380100300018101c0d80840c0d00520301902030340040307c040c0720038002d205501d8865800f60007110041350044010b050b42040165240fa407036a000780c40c1c96000b1420290009918958082814104000c503a204941d40d480500080c600300014101a00031400c081e40c07108503e4010785408155401c60310071101074401400803e1601441560160603c5024000095120304002040b405503001d840e16620b2a60748034145a035030344030060b91541082d00302d41142c0201d403600700988008c81210001003 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 517588543 1250 517587293 517587299
    0x102250c08060117120a0c060e010605060313060e030c031c110d2a0813080c03030a050f01080102040b04050d080c060702011a010206160f02160f03031202120c09040204 74
    0x1803815100760411041301071004030b640c14400d801c100507910351841d103400b14601400710078000c01d1900c1c03424009000c5600d070044620524000e40202c00602000340c00d42e0748918101d0491240742a194105940b0b051502c10013203070300b04000c011a11070103403020045140030143d900380c1c1222403c4000ca40885a07803405140003400c00d041c020101000c0b030600100c1c00c6001845002505081e031988007c08546006103c20215042114681c0c41318850b070b0b9030003611600c1d041c0549203110b01c800004a9000000400c983d092456025a0060042c00d41000290380c0311240309081344514042c103004c105080c04104041d02e89040605081882482c280d41007043e034030000d5143c00010f9a205000d40d440f5401c06036681801b8060310707680082440100010b0400c1504003522160390700d00c4070104404d800e800e103000390081000c210100c19045100762a2659081079041501440c041100060401c01418520074101c1c001d460200b030121400c3c0b500c2d502d441c0011031840d0312140c00e164019800388400 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 517589793 1250 517588543 517588559
    0x209041a15010806190e0601020a080d0c020c0d05060115050408030a0320070206071e0503030109050f01122f031f060801060b1207231b0102250c 64
    0x3160241c040038000941540e40c0c1d10001d08810340c000c080c580555003109188a0907551841c1e200204e55008200c0c641a03101c0c100100d0501201c4034028002420025903011005010b07840a00c50348080d0f400e9801002c00301c02041441c80301d090313000d0102e0380b02d500140300300e00c2c0307803100c1244142841c142107250555071009039007590030820800003c07a41d00d508001c2c84902e04101e1482061040c9400d920b45a660b0b80000c21902803094050181201d000558030004860315040840d2608001201d4980da52815400040d00c0204c404044600d13206000007181e9420620322040300b075001702c90000c2d10340a016807401000c0c0ba1003014000c9001250f100c03086440901401d016401e01c565228100b82c0c404000c2c2003a43c2c5a5030080c5156858403408100046015040d1105020917000c900880c1c0c851407003c9540c139040c41c505006411500302a02c2482e1009001003200180b51449007180c8a01c0000007801c034050041103506540c3c1800d0600c0c004527548444042c074501c214402c0807580c0c3c9a81c02 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 517591043 1250 517589793 517589843
    0x3100e01060807020606040507140c0109020d0c080d05130303081e07050c011a1536091005010f0c0c2d0f060e1e030a11010f0309050604020904 63
    0x75002c52000014880b0320380d0b040c001c2c66400f00c8151000e100314207050704002d001da400d90350324070323000c480216610410101c20742000003105e800404c5003001c000c180c2010b881000c600d10070075101f4030414242140355405a03091b500000c1e540070407001003d02d0b54406441c900401003401c0744485400350440a03114800d50002d0007501140d60745603c3d9000030010508403400e56034210104d070301c01c20783c0e25402d41d200303025a48440000c2d451240c6801400b2404c5c403483e443d11054119020601010400c80c524012503003800003c02c0341d12040a0f203956283c84d210491500a03140020b007052044898030f80900f440c4d081d454400d09070614035036503070f003001486082c48032050301403100582c1c030903680310640d281c2040140c0360b68000d150036107141c080090507607201580c41c140104081d18082040021b0051003000050014056071f02d002846c2c50440c42c6903240d84880307408902c3e00c80003124590711a21401482a80c00001070002c1d446a808002031840c0c024000c0f504a0104c500c2e4090500706025 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 517592293 1250 517591043 517591049
    0x607080613020d11090109050f131d0106081018020906011d0a03120905060c0c0f040902060c1614090a09020d1a010302271807050406180e030406021203100e01 70
    0x800281c41c5c0c9144c0000400342d02c860351101d482240544000300e40d030755500008614044031528000b50764000480c128070b901124013542000b9502c6c0600020300c030301000c9049510004080c8040022042800d41301c03901a4040303001941100700d090001c0d15550050718052200070038903000b0511558207000017a54024140c100f260f40e06071005441a84640054014020705000c445803400e010300b400420742e80348190140c41d0310905100400300074646a0f5400107610580141c0031131750b1b4803403d43c503060340d034298540142c030004868040001c005d160140076800c0b1000040805806880301c0d070782071015000075142641d010b48120703400760000d4800303401000340842c4e0544080045d8550300400c003c001d2801100c40003007104620b40da0805485910b9140c0c01000c030900c0441d02c512248a46113000c00940249400918042010840a0310301c10b0705000d02007000340a0003800300800ba050303168010b43c4584400741e070080505414401c0f50720061076104080c1809405180e503540151961034400b81c5c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 517593543 1250 517592293 517592321
    0xf01060f0f18090906050a0c020a0f021908010509060c161b0801050f09061e010b070c0b031008010f090201050909181203071803080901050d11070809030f0607080613020d 75
    0x5070401017180e43d01840380e00c105640c504001032100f0481c00b944076001100020203210448560600315074501945014000c9500311021645840c1c1604500804003030340e000010384240000038a0a50b000e038100e50322255a404900012156a501d134400440c900030124424180f150002c48c0d130742ca00f4840d00d4070850848024680c10b0070f02d403d0325030400d0340c0501401c002e028665a180100c9940703542c0c450450301c9401c400359075a90310b4203000d03815400d5500103140e400c00000030f0040b80d600d049081415510301c813000300030324000c240105040301e4001000a000c21030501800c001403070a466020341c8110b0025038000c40e031400c1040039082c203100f404004141c0001005010149030302c03041d0400704180107411f121030309040d91181401c03400b90034166030400900290ba00744589694115041c964800702c1d030030b0b465468529001540f6044a94028041e200301000d5a485ca000005c10b280281c0142d1150501ea0b100c01083c40040d1181c3c1d00100c810a40801c032900c0c1e00e115900ca0100084801 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 517594793 1250 517593543 517593551
    0x1a0702060d060e01140a03080307020a050d021605010206100501030209130908030a051612020a11060f0702240a0906020c030703091703041a03041e0311060f01060f0f1809 75
    0x10300b078142d50f184183c00210305200b40100d081165142c042c002016660008081904da46d41c0c81d80c103d00d030000c0030308010002e025190a240c00640c00040d02c035400d01980c0c1055501c29100c03001203950320740864a20601c040114003c01082d4041e034004e100e10300d000781548410000961654042e00d00d880c00c02c4580040000130010110118030409800240080c0e600e410342c3c0c80420010f0244080765001d138203040d40080e5215405e4001d40100c400701c480388040d03525910b440c01c0c4440c0842000c450800150041e42c411051413120402c034100c200c0500e00150311141ca035100054020042c0e09070880c0c580b0341c20010600010401c02c090280350f40b1a5803000c0005080c4007000c1c03450484c84060600070f6105100900ca003038140840352840d0494000625129640e60802c4080c20607180c11440c44002c903441103000f850382c000d81c03550070a14000100c401c0e58980004a0010090034070400e00002c1148080d40c4081e03210340010141800245411b000124840c030051070040480da0210b04411f542e = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 517596043 1250 517594793 517594799
    0x7020a050d05190906120f021c0905010f050f0c0c030d0204080c0f030f100f2d05130c12150c0c051603020f09090f010212090105090708071a0702060d06 67
    0x550040038410b10402d04d0410703030003490a5405042c1c40d00c1801841a1140c0301c4503201500c1c280c1d541510f0108020728014104515078004000041611034000c0d542035080503601c0c03025200c680a118020074007511a8406030746c411074040b41c690800d14846503a80000c1050140c3c511039800984050501c2c000642004200c0398100012000d80b01207083c0240c000900c1c031210503002284e1105000c002440c042161240b00b00040018030f07203001024000c401910340c030071801e0000400031a000360071510400030350303e44a1015007566011078004160075850704041c00b581e800b0f814a94610b0348500700041040c6144024101030341c0c3c13110103600025104200d0501803103803c1051648400b4004400b400a030f0450b00800d03102c078054034449010b958400301203518000100040c081500744400210340f100404105203180180c01c2d50503503402c1d801d01020900d6010003007428422114414000d244ca03514040154003003000201d81910700180070720550000d07071100002031944900007800000d03d141 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 517597293 1250 517596043 517596067
    0x10021218030c0d030f0e0a080d020102070b0a020306100c080702090903130b0f04051002190b040218070804060f06030503071b2403150314010c020d020f1507020a050d05 74
    0x2c80c03044864440c000c496008404039402c1844074900141d1454182c1c1091540808118110390a42c0300c91920b22956854010381c6034194013401003107100d04100d00e1a80c03149400a0160b00054900302d80c0140920880100e42e4040c00d6000d4189100b0885181001c1c200d800042c00d101046400c43d019800002d1b45000480402c800c41015003000c500a60404400306000c4103140960f00583e802080000a0016003034000c224a00c459190340401d0080b1010620300810b45c59030a0740d0480c01054000400e8050000e810903051050019548885403959240c82e0324010301000296244403aa40d43e03004008640244000c1103110300459080a84010b0b0000c12140072004d035005001c244480b032240070480c007005115403240c45a0707240102e07038000031411303100003111a0780c8010a010303060340041c200900190012101044190280c0d4050710342e0150a0780c48020400c4400d036a40c10031070340d4115100000d008a50041c01504c11110507007002c0e914031740762602180200020403c08289070103001 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 517598543 1250 517597293 517597303
    0x1315060e0406080705090405070b2205040524041512020a080d2c062b0203010f031b050301020f030a060b071505180d27030c051002121803 61
    0x10400740d4082100d145804160381c0c484015000e07203031103075446402140a00c038080040300c02030041081c00ba582c3d0b82e041b0940c029100c030640d200e604c403810700c0e4000040d01d02d82881100e00c118414013540401400d29003d00103210140c00c1c181e1380c40340d0355002448101c04000340345c001500443c4081c640510160040011100e819402804241e00c00d140f00c02c0069030081d6810301803010794540e0f00d050441c15086050a169a40c941a08501c0220b16607403266403100c40c0340716494940410860744400d00e212901617100c02d0040f80110700f9480b20410025400d031100741071251040c4d00540c1030a0702c6900007400c1e64490b1112400b10316021003400400d4805200e01c4004085203405203161080a036030703038480382c6101c0d10181c0c051940d62000880305010400c4001d2504110801d660300c44030504405803030b921005282d040b02d2400d40701e4249003c2d45070040b040540340c104103142800c6241a00300541c2080780c0c4126002c40c014070318807a440880c070001402c0792401411907168103000d141c2c1414500 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 517599793 1250 517598543 517598567
    0x51b0a0e0103111c02100503061002280c0e180d020319051809041514040213020906040b0d050411040b0d02040e240108060603030a0f080402131506 65
    0x1909620010030029003030a40409a003881560700c00d400c1c880542104d10f0a03c86140b0280d00310074240c40c01c2090a0340b007001944646003c44640010942810003240c0c0d4140f2234581c4544401400100050032544001814000e845241c544c08100e880b20640600040140d404c000601005070580b50a94030a21900b55419030520003141044110701c4644c203a03410700d0540300c05210002070402c030025006204098041c0d03024000301d201e4189881c00b0040380449500c2c0d040309616191901c44481d84814101d8003483d00180b0302d1000403200c2402030000e600c80c0c03900c103900803000c000000c1c80300d8042c400ba04c5807030070b801e02c00a400c1ca03003810600b58280400482e18400d41c54005646683d0f030301c0480e411182601030b5000900004602ea14510300412180d006e403010407006c1c0742e010301d00381010425040e941e902c2d054511546499003030580d24081c00c9001400f2501d00d884451005101d0100a0b0f030042c001000f0300765031801d0441090441d01e5a00f181c2c0e0040311300e506c00b8402d25400580301000 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 517601043 1250 517599793 517599809
    0x8030d060b12040b040807021804030201060f03030e062802010c0e040606080a2007060911031603080f0f070807030806010908030403060e03120916060306061205040f051b0a 76
    0x290150850302c510044400520003884403c00101003400c0c001c0b4034090360081a0b001d040212055024080881d444504880480056003810408140c0b2550b40920100701c80c2c2c140c50b85811450181c04001164005001030008903900405207003225104002c62102e481e00307074000080184410000404c140890340c41c413401141411420080194442c000c82d90084a0101c0050066504020064200710f408503929003c41d010450320140202a4402d440c86441940080c940ba43c11b1010b06417076294410704642d07407180d081410404103080400404640c036400480c00d00d002010102e9801642255000327840d2400c02040400030190030130003040d0042400d007003040c1020314061030f01e9032724840c81c08020556615210301c0c1c044004204156003420254980754107042c5498a100e45c0c2d10990f815642c003c0101d60080020f0060280c442c02d4107540e103035a03400c0d090002420711000038281c05441186c1c0c40007080c9280c408500280310b864690707000081480d038200c0c50382c0304010301201d460f0000c1b12703 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 517602293 1250 517601043 517601047
    0x1309050105091612050c18040b062706040906061101051b0702010201060b160308070309020a06110f011401082a150f0c0606090705120417070c08030d060b 68
    0x80241c1d00c001042d03902550312003c40040b409035081c100c0705455082e01c0c0d0524036003040e00340902a001d040103070845115240d0b014412401d030004100a54102034070313443d0014000c00490300c1d100c0c6044109088044a01c0300d001c1c02880c3e031404901c095009a010b00141c559508060142e280d220720320607008182d8000a22050910400307001d04043c02511079010813000061075021a4000c0d0003e10090941d088d810f61140303c4503080104505100038100c00186003080050803a50180c0315000f02031380c0103081003e400342021015102800300030200d000c5d503c603034503000d0b4680400f4092020032071000307014440b41d54509850b01f441c050038003882121018803600d44102140440078031a031051001c0769841802540000010854482c030b5844001c60b91001501100c1c0c6400040da1900412003a1013022081e600c0d03a8088500d80511680c0b1082c4010300c00224022500003800496402c0c0b1001d5210b02e0300b441d558642489800a60188103950004118500c0c4441c6030f100300d400414000600034 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 517603543 1250 517602293 517602299
    0xc090429091605220f110c010219020a0305070206031003060c030912020a0f06020d15060224060f010c050c040e1608031e030c12010909200109031103012013090501 72
    0x4c1140524600740681a03611349014440b44015000002140c070405840b036a110066900c1c54040e6000403140320055408401d98000c0c140700103110300407e601070b5103103401d1074441d600304126a0b201400500380c901061601001080840c86800d640e5651500c0009040f40030740381040c03002c03a00d42c01030b1040d50440000c0f503000c90489400c4440075070348803500581e0f0300500c2c200400200301c00102c4c10038030741c640b45000c581143c00043e4000c024007410203c2852140b419044110340030101c0300d080d04040a00c6c1c080000354000c49044d03003078511601c2665880e00c0658089000c03503401c403001c01c1103503110b43c062161202c66800090042d00130328015519183c02200c07096503040503143d4000400b040000020602c80c10802612640d404a40d1003400c256076458215010702100a4103480d0a080700395500f05840603001401503484042e11514050792035031b224040c0382c1081c13540300c5405540310412203c2170f0841410325460340c9503429400b0744038202200243c1040c0c11542043d840c070742c035040040c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 517604793 1250 517603543 517603579
    0x3030f170129090f0d050a05060c030901050a05060a03021002100e011413030903030c050309042c0a0308070e130e01050403260606030a021324020c090429091605 71
    0x4c025030103440308010040d142c50424a00341201d50050002d00407a414030400200c560020b5000f241d45000920454454005800456106a4200d5480800d28038200018180074007065000080b0f8010b0321500404403840d14140c400810ba030326143e0b5900c40c000305042d000a400d5582024540300c900070343d054165805007078120140405414413054603411405c002c020021200d9417640035005105690404501012210380203034000b070014005441d0020100000610307041c42c981544d100d8919480d001000d990b07411f42c80d0942500403420085031910b884150107080c1c0428440000040d0511305814002d100214007240e803100c0403010400e41205c0d010014406170805811503c140ea247c940c0c1078003c00134402c0c1d205822000025440020310280d0001203a4a030050600002500003c01801280c403900c18081580e442403400000c06c0c0415180e18202100d60090030704a10443e071642c2c0d070200d424008a030780319115404000c0780e080310740c0002c03042c0000b40b809032180e414104a902c51 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 517606043 1250 517604793 517604809
    0x504050607060b0d1208180c01170c07170a2a11280503070902040602060c07021903240b030604151506050d200403030f17012909 57
    0x101500441d20360031421419a10f44403041c0b1300039031280a000c0d41c000b680c81c0251551720700310f4880f224980c000740c02c840003d001051807d40c50205a450040110700c0400c800b60410b809082c8c00c946502c00d001c0080000e030a18050a44140340e1400d40752100040d8000411400c1a44640c070054295410359000118a200548001607400466110280030b00c2c00820b03004001303c4541380004410100d881c100000c01035081040d00d4065081c0d80700d03191920074130030a0744607511030000107a0204000810f1007140304007500c0503610003007609001495203007465011005c286c00c1915100018111400c003101d0002850504400f0544107000550121001035110900244007800c858103d100074081e44c100bd50001d03400150b007001705e0a000e51600f4000b04603400190b0b204000e00c2c9088402e240b2040c00c1c4605200c440701908510745018259501260020b03580407d403802d02551400382c800303078410038014074060652405004a0b00c10070840d603990a203540d074255030600340304000c460466114481 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 517607293 1250 517606043 517606057
    0x15020304120201020118061a01050903030d0509030906070320011a0f120118030806120c0d03030f060603020307030b04051501031505040515100e0306060108040812010b091005040506 80
    0x1d80c0030900d2040c0c00141e01410a40b044d55407a9044410104100b0101d50702528603924110340281103a8940c40054a440c4600d21650f07034140d0040c00350304040340603a00034039440391013801030700d042a03000700201d04079400c0f140301200455118011107801014400c2800101103c0400030302c201c0d107240030328036400c080100e6028010302e0324400744066915008152000290007038000c0042c05d030060140d1050030725100c0308030005800700c0042115417414074480d10415842c00301400020320700340108021540f0f108011803e01d5140e4141e8180c00c00303140f04a03402412651005039503031500100090803140c0c10004240700b18544000c0c881c4c1d02070440440050440c082c00c0000d10282c08200f0080461135030f600456100b81003908014100c00c403440344004400090360018126540c000f001d40d003005003a104643c040e440040002d100750710504102d03401902681c1c0d410310702442c680b00c0040d0382800740c22501c855500000c0800403420301c2e40d0181d0500c4071600c0d145046c0b5007403a0001e20381e849044 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 517608543 1250 517607293 517607309
    0xd0807080f010f090c020c3303040b0601030b120a0302011d03070b0a0f021b070f0b04060509370e090c03060402040e011506030b040606090305060711120406170115020304 75
    0x45d551542203008008120b40d8076030091044070701c40200e1031003590541c11060008202c0340d201c5100d20391032071210141c3e03001d60b503c01441a01c680d64000110010b20744001425440380d0400740c80c0d441004d007446a5074002e806603002040391054412114500202c203c106110769004200b00004030309000300c2da0760800500d01c404298032418107051400380c0501c004041074240b140400000880001820f201103401c582c1c80a103110b540c030000c0b55102d0081d44648000b052082003100c0e140c1c98034a00100690b0002900c0880c0f180d403424102c1407102d00a0070500d0080c440c9030003803001c040c00c001c2c81e5603c9403030000100b044250301008280c82d00c0700a04024003ca440d00c400d507005078005e4200c00341c244d03030085035064103da81d410b0003006805d4048940c2d01440c5003c0c1c01188291281901c20160b07908030009140d1501e64000c1182c1201d00341142050b9405038003205d11103480711400400040c1101e54891300c1d84254102c5006200c401a030001003011074418a0745c441c0e580200641d01114600 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 517609793 1250 517608543 517608551
    0xb0a080a090c08031c0b0d050615060417030c0c091003020d080c0d1d2403060f0301050c1308010c020706111f0c0206070c080f0a050405030d0807080f010f09 69
    0xc0e1a007002d200080c0d400030040c6010100d032400c03070401000e40004240c450102c042c0710103000c120078040300c41001140135016400c66000580905501040e214903641c01900e800d15040c0d4403811181c0440840b118a40d55400c0020603160703100b0200701c48180398400321045001402c1c0103603d860114a030340710007402030f14420f4061040c083e981303042c0c4d02036140d0301c0c098410040c684200103040840d503117041104168440c881c0e00b09030402402071b612554100d1100b541c01004010a039040d60802403800e640700102203107076401c42c1c9084c0621400780400e140900c4d01ca00e07076501c200c000391110741c00280880e85031206070b82c00180d000441c80103c600e0b9003880e01042452103c0103060000450303003001082c80411110321501190b0748110b1028050b81c2c20390b141900c42c203c0c1260050340c1c00b8005000b040082c0a045944d407010401444441502d00700f85160903a42c40101c1d04100e0540d40a401003aa040104021150420285980a00888200b5104d9810504862840c61060062410407a0f0b1 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 517611043 1250 517609793 517609811
    0x3090f0402070501020a08040201080f0c030a0207060b0d03031a090405030403030c0206070b01060801150503070915230c06070c03080c310f0503011109060307020705280b0a080a 78
    0x300d034100c0300e08580090003550f50f8240700c08045c11101082d45d040340026105000200700080704040c16010340c404005082c5580c9541007040061f4000120541c3e1041c0e55002c03420b0203a850a610b4038440c0e200c2d803000f04018100780300300c0c0300314502361000c41d02a03a001001c100c00560040211816641e25080601c041ca040d400840c660b4001c15030010058030905002148142e08080ac9a040300d00b0075500303403558018044103e0f5240000d481402c0803a0500d0014814481e81002c202c030307503640d9490184030803c1d000301045042d401600a190110200258502200f081070188a40c00480c904103109040840da400600d00d141c0240040000100821240e0030700da80c041d040d400540a5000c826140410507951015401a80c402c10060301072a100004860406025800c14480c1c07003202141002d02000c00d101050788020401c0e001c41c012290701080645d2821071400004200c0940000401900511000300030f01c01d410400b21803009000d030348a4554070550107603014800d00004210f07611 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 517612293 1250 517611043 517611049
    0x90c0509040c12030306050f100f140d020d0b0f060a0206180a0b0c0d05090c1012020408030a0f02010b0d1104090c050405130308220b280203010905071103090f 70
    0x203640c021441103a026040f010074140d0581058042d00c90403946101174110420401642d1450b8101c42c102140e2014584200940540005254501028140c515012680c0f0040d0120b901425080099554515440c80c0c1c504241c50140303102d803000d43c0d0081c901100340c00040e6996500130040388a9151030410345464034400d0080401c00303944002040c0803810450100e802c9500603c0c600c120051070000000c00087c2c000518403561a009800ca0701d441006140813a0900b00c0f21120031203040e000c000015110308100002d02c5030791501c4d6034600400f04490402425139a890002e1841081d48201010102d441401d01030791170481213a0006480589250030180c4070969480030754800e103010b0030040326008138010502154825500c0750b9042ea1081280003103800c44c1610794182141903d89a00006ca20344d5841e900030349241c820190316040e01c0040030a90350205603201c0446c0d0040300400940080c1d003d0f094000301b132410300038003052400e020aa900d004114815206110f000749107481a1 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 517613543 1250 517612293 517612313
    0x3090f0e130f061b1101140a020d060f0b0406080c0a02030a030c0e03060106180609180506010c050307050d201c050714030702010806031207031d06030412080604090c050904 76
    0x2540c080e109204120f074100c0b0b54121001130296a1011030381380b60903a580344406208485426081c4010184d40e900c580840000a402028085a02139507580700414007031003034601c8e0001004403040e45036171241230820040046101030481c005240301804541c03100c80d0040305444099809150014010404000c100d0700020b040981d170750940030b1800042001c0340d225468071003004882d1441000127507110011550100c00e8400c6940405030000c02c0021160769410041d04140145401052a04583c80386802c1d83d101c0c1e1801c40f455481160314940f21500f20b000d0440c0c0c440c89442c00d1150701c480b404580c0d110041d5603404207245a07032190f5074000c01c0c0140195801590030040200b00b501a4060080d640c0c0e00048044c1d01141c58400020703182c0c580042c0e00d43c818518040c40034100f19050354144c8520010301c0a40706200c55070b400400d055180d01c400f85100d1400342404c6082400e040b41e000c1c4c074040001d44424040c0c1d003000807441c081042c005104007100c10565610410340c1c1c850030482100 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 517614793 1250 517613543 517613573
    0xf16030b07080c1b010518070e041b1706060f0414070c05121b210414060f0c0c15090307140406030606030506090705040b09010b0a0e030304090903090f0e13 69
    0x111405014107613581105601252068041541c103000c402080c440c1305907152541d102e02a80381c54440005000a08401c000600d120101e03041c202906486444218200c10791a40741c50440d0b200508000d07103032801e0360b0741034040d1790250b0701003262085248040e69100002801c5c40305001d4400804800c00100f005982503004030200d0181d1a11401040e15039000010f544402e00d604c00c81d6041ca05502e01250340c2100c2d440d02111080ca001d1034109240300350400d00802a51200c03007400700030075007030045000304040035001c00a000c15210340070401c100045950107101c00003206002e002c4882c0c0b00081c00c00d0a0385c8041c110141c0c400350802c00074000e0038641c2c200606590910030000200000010564004d2290300706030740c1f0240e111414002180c1c4031881c101d510501c03d5004000194100c0010400c083c1686803d8021603841404240396502607842086650f80d280d8002c1c00303055110104001426880710b001442c2403800101069200f0084d0600604001e120301c00002c10a104c014100c1e0 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 517616043 1250 517614793 517614817
    0x9050402121c110105090a030c03090302090c030402030f120a050d0e030d050103120804050a080d090b1515070b15030a051b0f04020a02100203060a05030a050f16030b07080c 76
    0xb1407040344103040d900909070390320200483c10000f106040801d040c025a440ba102d144000c09042c090303a24100d4441501c1c01d01038040c0611054003201603104d12560510618a42c2d02c0030b0f9036400c0601c140b51803c1d0403228004055081302d01c1c40a004070a19048030a98002464090b4985900312170710b100070460323024011075a03c00000c60705070619003608501d04890203014500c44402035000190360010f000c40f8004c08075049800c80f100000d0700310001e011039103840200080d04801d50750342e120320b186e0142c91806500070300800e280001d20b00400010203114078903c0c482c0c00c4c0b0b40c49a5807401d00c0c4030b01800035820b2130403500c40c241c100e8608229096050340c100c07080b02c11001541c5815440581c802d151140205003440d0080109e0600d4000c0b1a0700844c0ca50003008100440b02140000b900041c000681c01400182c1c0010035079000c00c001c032820b5000da800741c030803402580c0d5078610b410361105c08648042030320380c001c00c0440d0610b25810350154041c2070841c00359641c81503540e0345100e20061001 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 517617293 1250 517616043 517616053
    0x1209060d02030a05160f2114070c020a06030207020d020d08160c06030b0a03021e061306031505041e0507020c041802010f0503011404020d0204090501031a010b090a0905040212 77
    0x7002030301d03400150060003044003040400249180c2140c101a8000c6100d0124800e4580c00c071184c2002000d0300040c0511f1400002d43c031035840159074000340c4c240c07011000603955500000130752038500d40ca90003c00c40c0381001c501d03121940d80403415015420030042d01c600800d010039400d00c03000e041114200c141c4005850382955a9103080c0c0399a40d140d018000c00039140134900d42c00b9040c01d5a880c3e0540c0c0e001032182d280000400300d001040045840c070301e83c100c0b4050000034020003d044c41d44014002c6a10041851820101c0240b514900b60744000d2055041c402c51405101e5500310800b4503c991020100303003aa6422000d80ca002c0341548699013040c54070207036040d02841c0d8500014441c1c802d80e070741980300d50300483c102e50070702007805011840441d4419240503441e06500034010021301c0040982050f42d1a403841d400c94000b45d2080d908044030208624070b0110a40c4010701512110b41601e0411000c05c2c040380c0184102e024203030803590750b0800305040d590b514416a003050301c003000f194 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 517618543 1250 517617293 517617301
    0x1060e0f0a0e04080c1b060d051e0a0606141603080a09080f0405130b091302010c0210020115120c0b280906030f06031707151821021209060d0203 64
    0x61442c5e444807901d03084501484418803110111603aa200c5001001010300b17003856420029240100b401405140d201070401683c15050741382e0710141442100071501c000307a96450304c40c1c0130705941d48251042c0601c204c10002c1890b040c1a234401658020740501c0d010f101d030755501c04000d0080c0000540900441804076000004450410080c02075403c1600c6038640304450f82c491100b6105109031171070f03000001800040c03659030100e11041207240140340c0b0411802494001c2001c4000a1441c83d006035110805100701501a641d504000c1c8024a190f200c1402c0036240c420400e2460301480681400004880340d030340443c0c030100c0807041c204141603021500d8040015156424a11984011074200350081006082030b1061001301c1c1e40110300c420203603020401c00c4229a01261049031a061406901c10000d8458032580441d0702c80104161801880d070b08000040358041000100030f90103c48090b10340950128000204081d0f0070042502ca2250500080042c000e0047e4540802d20200802c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 517619793 1250 517618543 517618553
    0xb031806040813080c0d0b06031f090203070501021f020a0302040504141501032912030a110c0d031d03010f0c020601090f110307080c190203190801060e0f0a0e04 71
    0x51480703840c20f6000c18001c96440c0c5145448074041100c082d80b01c4040300100d4045030000390440d43c4100c00505480c5140500e0414042c4003c00307011110225542d20702140460404100d9440079007000d000800103243c1c2d00c6200b200004c80d515001c01500d40101311f8809440c040e8042c0e40241200510500007101c1c0315905405980084400245024180410f031a555000b40f003001d94583d56600358402d0550040a81560408449005600020406040070050390103002030101415256a441c1040003400c500d03520b05401d4100c9140b003441c41480340c50000350050100321214051030100c1e00e80d80344283c006801010098610000f03207007400500c40342cac164085400b5041c4d4101d11800c11000b80340c1325020003203904402c28101c590900300042035986001e0904a035212502e00303c818601100041812071000c01217090b1005070b400031800a03040c0300d002d4104502000c031881c0031011503250040043c900c0c07401c28012402080e011443e4103d80d25000003020141040c203400101c0d504052903d = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 517621043 1250 517619793 517619797
    0xf1504060e041401060905060114031005090103050303041415010915031212060803091516020319140c0a14061b07080d030c0207050f030a0212160509100b0318060408 73
    0x30303041444d40b0f0100041400c0041d44504c2e401100c06039a00070f02500c1c01944e020080c1e2025044a00303005082c000000c9940da2100340303901a600c40d030b001d07580700d041c0362a0440f4519005103504d46c0b260458045408001404080769044800142d400319000701d40c06500c0c50307500050b0304050b0030300340440e0038113040941108042240226122040003519580c0c00015283e02882c68043c0d8003111886180710044500b01c06401440c44810804c400200c055000a20303010a01500705800034030310000105000b503100e4001d8485010700050400041d8881c00501032244170f000d1211480031b00002114561500c2080d00d401d900b41d500b1088044446c0c3c41c442d651201c440c49654902c0c45044501314015109000f4801c0307000451b0000c00050b4102402c0000310140900f0031600b40c481c01840c071001d039442200340340c0550100406406008078000c2074150010b0250000c42c0038100d40307014040303040301d01e14801040303412100109440e52980101c2030076100c44880d061045100d5102071105000c04540 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 517622293 1250 517621043 517621073
    0x30e010e0f0c190b0a021606120c0302030618090a02041d1c08010b1605010212040c090608060103080a02030702090f01052d040b040b100e12060f1504060e04 69
    0xb240c80280504040103030801140d0303102d5000d89040d040803c41ca50307000d0041d044241c55801034504102040003002070003615a402140040c0c0040e01d510b0351070603107119080e8010704034502940f4511384900400c20490310400d00b80c0c0d00c08030350030009416490600080540c281c5c000d00a2002c110134000c401e03c0d00f82011900380e900d008480c041d1140421064248201458540b2610811b031b203403101d212006d8010030400403114040520138000644288000c10015002c0c481100c07450400d07040040e074100c0aa000b448915151403000c6c0280720001840740e045940c881c403415039030000440100d0a5000d103900082d00700720b998003030019016043e01c81606940d4207941700019500c1c400c46041207800020540c50541140610a107614201a0003d146564015001080b442000004140210f240c08240c1c0c00150036003514800c1482c11702022001c020f00c400084c100c80c10a603c0c410369080f03000d44201c038100a42900e8060366140ca4015200030000601e5810f181d1516040400000c20321103 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 517623543 1250 517622293 517622323
    0x30806042004080d08040b180a020604030501020d0c030c091806080d09170604030c0209060a08030307030606110309010f0c050111031e0702060708010603020a03021314011103120a0b01030e010e 85
    0x200c180040c45c0c41600554404c50300900c136100c40c0d8441101b9810365582c400e2031410640116183d00c80543c6503240144021842036000603541c0d54110b0343c4004841d5010000301c01c05007001c940000c40c41c2d0048640c01540e40c51158800000d180c000c401000b0134140c0d102c1010350107021084800b4a4018880d403040300d400260b4031039604203240c030301502c50b0001c40c0e0080126803404500c201508100b11400d41c4401301074090341c04c0039140c200a0b861500700b1128500041c0d01e0300b0041c032421b5440344070004c8460b2068000c41c2004948400a04480d4410248a0400c040061300d5810300000350411305682c0e0303840c50060703504e041c00303038091030b01a500000071140f00000070f0108540d11b00c0061003e10900341070742c450341d0b50390a041d02107000c0d501840c00d1004040c1c0074400450000c004180035002014281d915142100d804000903003a5045030102503c2904240044451084050303c03056201908001c00155803801d10700580060494075020000307036180201d803c404203c00030b5940c5460b81701c0 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 517624793 1250 517623543 517623553
    0xf0c0102120c03040b0904090515150307211b0605181212031807080c03060c03070f0c021c0b011a0913090623010603050105060c0a03080604200408 65
    0x3070140d400e0350780300b80c4140c10443da00401041080c40050005004181c07001000402c406c0c4060f00c0700d519103a03040d8060303844041e1310780501000e02c000005c1014007003000c0c0d001c0c0c01d413a481c0c80c0100d5240e10030700e006002d1a842c03c20b02c460800c4404003480203040000c245185100c0e84446008040341c00101c03080f07059882d1201e040103240342c0030103501155003840d0020503025060702079030412600003821003c103011005804c03d007108420320587c4080e2246000030040145442e08040c60804040c054244100040040c0048246d1121450f4031002082c103260301003c80900c040fa1b040c40b9600c602000340c950b03048003281048001d0100c10704880c80e1340c94080c0003204000000101d03119031019154000700c0000c100c00e0002d1542c0002e000180680c400091615004004201910302409850100f44106005021954051162502410050700c1a500304282c195010fa81d0f01c0c400d0401030f05200090000494650307954010001403038086081000c88075520503810801c0d001405504024014 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 517625899 1106 517624793 517624813
    0x16050c100203090c01052502030307170c0c0102011b08100504061829191a04060e040c05250609030e040c111b030705030f0c0102 57
    0xe4000d01580e41d142c1241c2090a1400301d802403810f000d81400400030341c0b20103100c164510001040700d510a61194000240785005d1800c0c018092680300d04161200807528006d0650421010110f86500c0981300040e403d0f01c058004404058000d10840f01134244035450082d00241d103a9804d0015a440724042010382c0ea1a4000c0d000300c40c030b00f01980880108034400d20130040c2848291210b4a1204401020789640b03122209104182c05006618000b01c07104c401c00c003d00c04013004501180b0716500700c1010f074000d403081c60041a1000d18020150401e401030107410300d0140c3d142c070b00e0203100300c0c1d417010011800001007400361a424105000607001d4468101420300913114070064a92000402c010354001e5400141004086602082c03070000015282100c1042c8a14a00d80a984280400e1402e050351344a594180b003125011039200002143c14146640b00ba400e40d070f07841c1e003 = true := by decide +kernel

theorem cover : BRFrame.Cov 517446043 517625899 := by
  have h0 := BRFrame.cov_init 517446043
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517446043 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517446043 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517446043 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517446043 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517446043 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517446043 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517446043 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517446043 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517446043 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517446043 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517446043 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517446043 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517446043 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517446043 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517446043 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517446043 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517446043 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517446043 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517446043 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517446043 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517446043 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517446043 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517446043 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517446043 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517446043 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517446043 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517446043 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517446043 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517446043 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517446043 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517446043 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517446043 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517446043 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517446043 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517446043 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517446043 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517446043 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517446043 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517446043 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517446043 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517446043 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517446043 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517446043 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517446043 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517446043 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517446043 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517446043 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517446043 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517446043 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517446043 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517446043 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517446043 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517446043 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517446043 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517446043 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517446043 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517446043 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517446043 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517446043 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517446043 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517446043 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517446043 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517446043 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517446043 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517446043 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517446043 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517446043 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517446043 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517446043 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517446043 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517446043 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517446043 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517446043 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517446043 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517446043 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517446043 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517446043 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517446043 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517446043 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517446043 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517446043 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517446043 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517446043 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517446043 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517446043 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517446043 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517446043 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517446043 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517446043 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517446043 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517446043 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517446043 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517446043 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517446043 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517446043 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517446043 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517446043 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517446043 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517446043 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517446043 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517446043 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517446043 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517446043 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517446043 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517446043 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517446043 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517446043 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517446043 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517446043 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517446043 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517446043 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517446043 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517446043 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517446043 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517446043 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517446043 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517446043 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517446043 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517446043 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517446043 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517446043 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517446043 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517446043 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517446043 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517446043 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517446043 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517446043 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517446043 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517446043 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517446043 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517446043 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517446043 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517446043 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517446043 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517446043 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517446043 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517446043 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517446043 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517446043 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517446043 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517446043 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517446043 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517446043 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517446043 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 517446043 ≤ n) (h2 : n < 517625899) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
