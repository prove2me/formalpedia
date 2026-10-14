-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3156
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:49:38.715998+00:00
-- url     : https://prove2.me/submissions/a265f315-17d0-49e2-94de-02a56dada5b3

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 567446043 ≤ n < 567625899 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 567447293 1250 567446043 567446051
    0x501020409020c070506040503070509150a2c070e01110f1207020909010501030f0305070503070c0803040f0e0c0703031e110d06050904170a21060e06090903180105070209041203 78
    0x245c2c1d880c002007580e094030070240061005508040270711080a03005840303080b4520802d0350b000b0f000da8590140c60301522858142280404240c455200c18040e02a54501010b040d0300801203400d41c8040081048031092074815510001561a5070070440100ac4081050103001207101c0f0301d100250040108610a03920120b040c0e651580c0d07a07003210005e0000801b194403009442002c64070030000750101a0096003981d03d021546e0340d8942c00d416441d4010700a541012070102300e81900e13541e0303c100801d440c918048003450041140c1919101d504801014160341d4500e80300054030700307810071030080c0e6544000c002c07103031112440403460741010425000150408801041c541410f40d06140625402108140721261900314078441d034201c03802c40790810036054001c03913030001d0108441c0c02c1010000400070310681841041d619082c001056240501c0c0e09100b4000000c10006c01c5074541c07440700030425018228800102d0b207522402c007029600c58020b40c10b000510030307100f055090701c10985d03c0400c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 567448543 1250 567447293 567447299
    0x7090e10050f0a06021908160b0405010e0109050705061e0a0201020715090201021b060d06030f0b0703090803010b0f0d0e0c0a0906051e1818070b0f071506030501020409020c07 77
    0x116000c3c5900036100160001004040f5200111089200365845000d01504080000801044d1405000d90035260a5045018001405428410744814078200d00081c0f0440160f901d40d10b0380d4405511803e80944070014151a00017881c6206a44564054030f049556007c4580024080d4020403c2a26802c0000000030325141c100d21604040382c0e03040e00030305090f0350b062507000440c0c00340020250308a0400c000407240c0012503c0b50742d014600c82e00c204030b107107441410003040d103140c020501822b040c0340185420100350154180c80c1128400b40801e59915a502c415401d24020a43da00c01038604021100715980c03000715580341140f00941d01d03400015900c80c5144107135181445180d8209400b41442c4a41e404406c0f620510f424024064040c2990351051390a4161021160790554000e142008000f0050500c001d60041c4240c0f40100c7c180401e6440b0344010b4410340c03c00500b500725000340440c080c0401c1d04601c00554101000f1511a40c0e11101170010758486001602c1034000d642000c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 567449793 1250 567448543 567448549
    0xf1404231e03131e06020d09090e0c060a0320030702070e070c051203040201120b010e06070305130b1e0406170414151b070f110d080f1804020309100507090e10050f 72
    0x30515101059a0b108c40709407a080b4850014660160501c106c7d01401c001d4003103640702c07030340249040c0c1002e650010f4040044e440700610003007844000c0d607880070200148241d0359400101030702a106060503040554031410b0b01601e850440c07a034010414001d1080b0003c15191b10005140b1660003a260070000001480e81c0404859103a042c86020800c240d80340101e42c00c4c644c024010b041d100782021490310710360004034011200164004a22600001005a030b11440c07118003568440070710811741e040a040c03150240c2080308210643c0c007a40142d80001e4280b01e0011010305564008100340c0384020144440d44411b50011503802084c06401482043c0c00300a000445810540ac00d1082c1080d8007550740b9600002c0ba8592901d6012203505031a06c0414081c20091036070840070400a5a00c10181c144460001101801c0d6031013544180104090840c000c14031042c4800e41c0300001606503101d02040d604840160015038000701180104800600c4081c030002c2541d004468200c2051090410 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 567451043 1250 567449793 567449803
    0x10020c15061831020d1203110318120c060105040f060b0a0c2607020603040602040b0c010606090504020a081501030e01020c0a11060901050d0b01030f1404231e03131e0602 75
    0x1c001d41250042c0200e402180310381e8041b00301c04486180c049207030540080038002031382003643c08842c54595040301c100c440d85c0801811a034015001d01441c100a0104102c03901c441c41485014025502c0d200300c202d4100741c503030205003d00200c03c01d8075212804040d00404066034104215202001100344509460010080d40071042089500da440d1462903401c0c0003458002400440d0220b03001d10000c1040300c0c0071b41c090540c11080100004100f0320304403000700640c4050b40003500952040214200c0c8a9002c0c0782507511920802c0c05a90b404031003001240200f020340f982500315480801d1184440f4001b01d0b07080b24280c05210301c06409403405007000b28038440c11035018041802080312490302103c0350001045041c05042c0015040307a56540340040d15a80030341c01c14400500c00410041050b9680c4808005480e44503500090080305046556401c1c192022152000181d99080c0c00810410480354401c1501000b0740e0180c0c1e40e03400c03985124184207213540710300c400c010001c07035100c0c030000f1 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 567452293 1250 567451043 567451141
    0x30105041509020102032106010e091b0f0d060314060f010f050126010f080601050a0e0f100e010303050304120306030809011202041701050f0a020c060711030912070810020c150618 79
    0x150b00d07040100d0714a330000309030300c440c8108840f07150030b000d2405014000c6c482d1100440c011007070081d06154915419003400c00040501084e6440c080040c13014410b1490b00000783e1383c0030b00300301c007880c0040c814207003006000c4035802c40100140400403d1a86041d118402115122002c440c1e159883e00100a1500c001307000700407080806a0005001e940d143c5a6660865000446018440d444c3e0360051721404003608180c006c11000002c0c001042004c41c8c40016008c40f9207000c0280030306541d103110f118804d1030300d650b040158545510010030344c150704880c0181a601007031910050307950080c034083c1004540002100b4078200004601d0803440c02110318441d80c2c04090041980c0e510b0003a652000102030700143d0344000d01c00d1940c691581401c0c100c0c2505040d0040c0807203880e1200c25440e00480004a001041c01800031080451001038044000344010200f0103443c1e075208003045140c0d621400f03c92803c04d1b85414000d1000c038403a95107010003c41200841041c0d103445030b400200f40010 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 567453543 1250 567452293 567452311
    0x15070929090d140a0812060118261c140304170d3305030c0a1502030f040b0304060c1704030804142505030105041509020102032106010e09 61
    0x150414900d841c0240d501c980b80303d00d51034001c0d0100c034203d80e4030700a0800d104503428240099181c0c10072061851059105400346400c006581601b6440b400082d40c500c0f0b141c3c0310124140c0a02d40240d50448104240301602e000c680042205074607504480740481013440c0070900d24a00182c400c01c5800880b84590b800900301c01d00c0c0d1035050301c1041998856400c140d0001e03074030700090b000000c490040060300c60240818114441b03401009422000c12540081c2c0300e50320000701c1c0c40c65a2211a805400c4858240c00414155031020f0300783d04500c42c072240310542e02000900481c25681600c080d5000380c0c042d180805c203811688030251152000c1400b150043c5022a0008000922a03051940d11074411600850400c1c020b00034189411961455004441802c0e0651117802c441000d2a80003010124020301c0346081c00d4881c040d51b84d1070389442c040300c1521030340c09030709590003002240c0000340002d6100360000031410035641d24510540740c160000c0d500114038812417a0640119001d03e1101d = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 567454793 1250 567453543 567453547
    0x20c060406050d090830090c09100f0f06030b041104050603040c0b18030624010f020a02060d0f0b0103060b030c0d1506030c080c0a0206070f0215070929 67
    0x2540588542d04480c000b43c09103500c4e16650000140500c1c06042c0c078185000c14403061004071340070540c1c4880442c000300c1e034009a03e4100620300c0780010f0100d055507800d0710ba040154a0700c2c03080d961150000d801400010404080c0013401708240001d10045906a80d020414204607030204400d6580003845171480002c184130a00851030714030002c5030414440e8086c0d0709900d030350b401200c40c2c1e60051080c2c0441103c3e050317280005800c2c244112640805101180d405420030750081702d0300711580c26070321810440306090940c0864006c002e803000498004286548818020407090007500f2a0004e031902241421034400132540280030740001e44800b83c07120760a613520500c1007001600841c60140b44a41c5807408a551080c0c110070650141c0380c580d4021078020700341712001d800755501400f6034811040070130588805e2030b030100b01141c0081c1c031440c2081d4242c2042c902245800c40001c580350307400e69080d041c03010312a000540a8203e59801d5900c00c0501d0410511400203144802203003550401 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 567456043 1250 567454793 567454799
    0x40212092a010f030e010e01021c1103161b060b040b0f090106050d0204030f050a0b100b120a1b03060303120920120d090906050a05030a0f0302071a04090c020c0604 72
    0x34203044000143d40d02d00000c00321111401d407400e4038005e01519a8a9500145d42e100c1903024108a1207031f4410000c090004440c290388504252000400040d191172200c051a034600784a20360200368170403000455070143c0c0f92414a0001810703e034968038803540c5001d51003001c0e401c03d000140f55600c40104111056842d111098070698022400710403103d500300008030018845403100715505005200504001103903181811030290098040941c444400d441044064035410441d40c2d4002ca07144500403036105c4e121800050203118242860003811000030042c41a410f034880c0046134025940c82c4510101825400121600840c0191042074050010112043c4094084140d03180290080f440c0740984003460f400d2480720010f040008a15100030002040316000d0750000c0c3c5011078091131038518050000744e9030758035400c00804403078030303280b0748014503009101c004020410b80c400302000291a00580000f603200703010b440c09141c64280c000001510025450809840c09800c2e9807030a82 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 567457293 1250 567456043 567456047
    0x323010803030402010807110d020304031a0402060d090201140c0114070305060d23030433050301060e0a09060b07020102060f070e19090c03020306043611040212092a01 74
    0x1d0f00614060600c0508d003a01c0084103403c00501d0302c0c52180b0360103152914203520701590311082036003102401007080d80a120260303580608031101804910b400090904043c0b005a072000c01c1108a20103141e40400d40d02c40e008010f412041002d0a15a440c541c1d9940f003510960031250180c540580040e14030311a4000540d005541c14928140401482800501215820700e5540290004000b5200b0350a03403852011011002e1018903041c820007100002e4901da0040007404144102420440804100f13107181e1945400c0d0070291061001c1030103011f464a0800a44e6440100704900520503103000036412100010954050300b02c40d941c04045a18440030050b61800358000006800390740103000070100f8607885040c403110044d40b0056201d2401600b000200c5a24020350076080d2190039040d254201c0030301214140314105441d003041c1c0d9440b810300325550881d40034031039000382c40020b012910000c200c42151044075000100c40b044001880703111480b003e00004602c0900e00c12203a480c0540c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 567458543 1250 567457293 567457307
    0x60a060509041802060c1e0f030711040f0608011b05041202060a1b051c030c08010b0c0304090203090a140312061c061406010f033803030a032301080303040201 70
    0xd900800700c00706490990002410760784400406d0b0065440441d0805c3c50099222a4100001061018100c069045a5415128454900010b1600540f60300e00d02ea1555203901001ea0b03da40b01c20101704980d00e0f80c080754000d01d40c0402ca1040c0400a070020f0000901c03e5044406440703004000b01741e00d00c0705509001c2190400c0c1c04d45c4c003d0001c010084050100041c0e500301074a4011340003080c0f040c280c01c165103000c1c542c00141c401014100610401d003d5000307628641100c0c4400c000703030350710711144290700c3c02c602594101c40e2a181c0004103018031090700140d070f140018041c2030201040c51084401c2d658034842c1c00701481d449100d000000d00e0900c2d04003102c0001000780d044640b00b09100365542000c4840c014520400c14284405001c0c007560f10540a00011019003010003443d47240305d8400c1401e183c240c3d01d0704801010f0900e00b41c034004211406800b04900502125103c01c12142c001e0701910310048611400c10800e207244101c0d080c604801030403504000f028501d113441d981c004440c44 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 567459793 1250 567458543 567458561
    0x30405030c121f02090a05060a2f01060308300a1a0a06021b0111071202040921030b040c0503060402030a090b09010b0a050f03030909100b0d06030506060a06050904 72
    0xa4001da0710002a050000789680f1001010030f0030061703560710014100007011711103422040c0144c800380854281d854200c1000011f0b60361004640c0e00c3c1c0040c4282c124216500c83d801c0380c4865007040c0c000010444c5010240c00100030ba198030606406840a90300580f00e40709540311440d01c0c9a00202c0c074503085030f40c40046c140c1c1c9400111128003102da400b00d282c02005510102c01a44a00c84041808248088210403031609103455a17046000c0b669195940b6854000c14004800002d4000115580c5600c03140c80b0316030040345440fa40002a841e1114005688980c90110b81410748000c5280303858032030014503262a44a6600b0b548415007800000e40004010031506a580c41c003c50100343e440020b20310a201d45800410707030790500f0081c010006100d40c00703540101d1441741a5841d03513401006032514586c013500c41070002c0d42d070f41405443e40222603010354595080050181c0c100d046540081081c1c900410031108251182c2050216000300b80c4203201c001101448441d07000c0c03609030007110728 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 567461043 1250 567459793 567459829
    0x90803130b0a11011d100605091506090409210503040503120916090c0e2b051504030c060507020d091503060801060b091906050904020d06080f0609010509030405030c 73
    0x296024603c07841c04c45403904000c04110440010f1240350040030030645000e0980d06806202d9503117864003240c150003020745101600d40304134074040c0716138444105595001000800521400369182840d10403112130200307121401039419400e6104e14010710442e0f0059034020011482d10002844110f00010090011196402991040000204581960005488003410000e00c0609294024049062080ca458000d14000050314104120210464000700c0e040c1008007106800e403811908068205ca4900010003c1100b072009240d402200740010512519040040d903c90b08800c0c1d0f0741d00c00c504420381c00103100d4a82809004d03003821031001541c61a04001c03500640300c525890075a0400d4020807044080480e8118852801d40b40b8003040079001d0b51840402030900000411600c504040d040c000c50b00060455595a00b40c1d00c600b009103004001d484141ca0b007050181c1c0c030b072001034400804940c28880030454071a00841218122000100180449503800e0288102d00c1e8940342d007050 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 567462293 1250 567461043 567461057
    0x8040801020a03060e070c03020c09060406080d09051e0f0d0510020a0c1a040506010e1e07020c030106050108070207050d060605061903050c0f0d051b1306090803130b0a 74
    0x11024024009010040c074140c40115071a410190110180e010041c402ca0401010f0710005004c42e4010514881480055621403031540d00c1c000400d010b000c1c25803110056125400c034012000d5405030024042c0c44003290b0b4261680d60740d00032260f0440011403425848030140080d1b0009103456403c1004d1940310308183c51180c90b41d8001d10040f40c00483c2803402050f4044100e0007081401094400340c0b918540c4581e4060401c3e84490750346a505014000c110342c0c1c40b5002c035928503040c000103403000180031803807503041c0b1705484020b488410810310a4000d600303020000ca5558001c00203280b09090366401009007510700000c0054400f03a03440290703003195a482000c15107444400040c11004e06c0042ea4091440713101c3d50003000c80c2c000501ca1000e074078090048664413a640030880300c01100382c54000c03415444080010b00c5451321000c450110120010312003080c0b2018601420480b01c0c1d50f01d13001d6072a590756001c55224419071440d4101c0045100c0280a4051404040e010000041c40c04079 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 567463543 1250 567462293 567462299
    0xf0304021807030605091602070e090a06050103030c0b100302060a0c02040e07140127052e090503010e0f0a1e0c09020d0b030a03020c0616060f02040806010608220804 73
    0x441c0840641c1c0b0100025203600701480b2030f0501d1005250000300c012410f030501c03809000700070344800b801d008001a004551021a205000800c40c3d4000e0a40001c0c00f0046075070340e46005000030b0300010088030703004000b900180300c110f05000c903a81120b4010700300030b2070b01da0058411100641981070499200b640c84880c01c980f01400c0040300c0c0a008520100300840859000141c0541c800011800700040040900185030740c00d00c503200d080303130802e680340501d40c1c0346003c00260725042100000c0600c941070444108041d4040129070480e10150000c01019042009540d00c40441345000f00b902d61144500d8030000f00040d4a01e0480c3c20448206162204c9913030b91458499140c0d071004100340e4001c02c28880320f45061089020201c000c500400b56002540c2d4069181c5203d4100c0c03c1c4195804100e404e260440e86510340e40c895400b0000304010b00b40016200d000f0742040c0100c00451086000110310b40b801031710424050702102580d180d83d60508540700c1000311b903c52007210703107900c184800 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 567464793 1250 567463543 567463579
    0x102031e0919090204060e03030a2307120c060b1503130c0806090109020906091501120f020a091503061a0c030906070f060c050901050f0904062705070e060f030402 72
    0x211002d0514183d002d03070765510704200146203000160a06101c2d800070401d1070105600461542c1c0048241100304151160b54000381c5081c0c01402c90150004200442000240398030404030240c09100381c40c200450980c1800380440c2100328a00b2014a110400100e5000d00000200d03000c52880b0f202d010300c2e600c6e11140380c00d0a01e01c2c1699544a03d17034452540c2e07070452510165680d801541030300e503014240b500807140c4a40e04100c4107124184502601c0303211544005402280840301d4003030041d9521204120000c2c6000a0b910400c181a980d8012500010f4800c0c040d00048030b0911407082446207410310042095808950300c0b000d2480101310803111b41c1c460b00b010b000340b0750003410400e032040e8090910b50161441d1101c100100413040146940c43e81c0c011040c1c41854070901d00058441201c030020034000c140310f8214642101000d50181c0d078948183c143d0713050088044009100765182c4040c2543c40e01ca03030210303a90307101c42c045c00300c4a0306c075403c3c00103164018001414403800c0403c0c0551 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 567466043 1250 567464793 567464839
    0x7050102040e010617060d032001050c070c0f0b1c090605010b0d0e011118010207030b0a020a020d080915060d0b04050609010b1e09070203040f060e010e0102031e09 72
    0x81280d80d000c0300b1004010164100034820800d00308a034807104640380c0240007a200501c545c20040c1400030034007126024146103581c0c803209041c038200805c02814007050400312034001e10f40444500307500712008240d5814540f0640c040350754000c1d0803424400c26141301a40c0c549816140c0781300990700d2803d44041b81c114040c050003400340907482a0741c0c0e00e410b966074003691102900c4250a80c18102910b0304625030404950320f404200b0000e05510303c2c0280100d040c40466440a084500302005001081e501580203040f002b03081d03000c4074a24030100f9006e403502002102c038580950041c2c07400d11000c00012802a6001000425096400205507a244603402041e0313815220741c3d004d08208403400c0000d101d0f055508038200d943c1c4a1420f002c080d070303894a51104004900034240d9001140d4011300070821313180907049410215001d40e84402d40140304c551900c24450005800c00302500c0c0e01e50010085034414174500c0701c40141c0103408079925640380d0104e020181c00841100034900a0032480e10 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 567467293 1250 567466043 567466049
    0x917030615040f0f0503010506010f120b06070605070f0206010e06040906240302010e0a0e0c0d091202060403090f0e0a05190903020a02030d0503131119090e060a0e210705010204 78
    0x4410041d01301942c00c800d030501500680e0080c0e141c403084c0031b400c2e0307085900f01d942e0a19500c0d215078401000c1c044440034000c0708020b160402030204100f010441c8a40185114405a44d82d0010340044100103d035030b405c080c0b01e07084c00085003001040e4682000d0300700c144890b005d148007145034800c2c0050000c1c05041c41c0c8488200000b1001e0030320843d03a01c02c141907040d1a04507070303003a4030f14201400d5150519010340075a071150340024412103040d00c140c02008800380c00003803a1903814a80000a510b0709070841d801c0b0001751070200041034454900e91301c101616075504440fa02c7d0b039600203001005060160030018540e080ba419248405640d0107540c02c803500c6640507103a82500c1e03205062410808807103403811b1103024020880d44c43d0b004a040e0b02d000b81c000000c01440e01d000e00102d03102d401c041d240c61060005052003c41c0c81e80003a00030320a404034900480b07040d603a031019814101c1c1c40c1000400b005030032260101910495096402000d000029091854407040355034541c2245d21641c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 567468543 1250 567467293 567467309
    0xd14030718141e0622080a080d05090a0305030604020711030d0f02160302010c021c061a030c031506100e03061f0603020a210e060a1d01091703061504 66
    0x1408810103401c000102e0000c05102e2a18200b4008901000030450b004010a0604040c0004441400d898a0105c540e00500c0c8a8003910240c40c028188070000d075205c4815109014100340119000c0b030400107002100c07076013542e9a00c0c03d5880d083d0800029501040068400b0b00b129241040903950070303c4804151030031500c60104440d420070001c2d0420031031682c0e206140c3d055210400140c0d03000481c0d898020341c1210080e1040b2841ea414125000c103000307018007001e1034104207801d003101c551800d4203101000c0301203854208a000805994000c008900717890501044003185041c1011000c2c01e400b000c0d241040c510100e00030020901e4400c048655900b40301041d070200d00403244c0c02035500080d010600d8254901010000086e0446034440d001040c3c1c42059425154440c070594071044d098010b103000d0300c00e1800d1040302940074029903000d44e07100303441e404140c2820303410500c02d01c0045070340500d8030310310b250501386a50060703000104095089a0310f445100d043e40e518800030000b0309211 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 567469793 1250 567468543 567468569
    0xc01150618050d05060c1b0a05031803011a10091a030f0c03100e06041d0601050126010b18030a060c020d0f0813080903070308090f030d14030718 64
    0x5084000080e280c0d200301d0044030b101290f507012030030220303100d43c0c85001d400035195503290000701c0c6084070201c580160380c6801036046440800c80040014006102c45220344001c00a2042c10142210114a600c0468400450300c20140b03007403040c40502d000860b81001007105075640f4001c000d100346007600050034030001040101c1c00c1c45c4522029000b014482416040d4940102512603003d804e002da04100032021001960551712034100011010170790094420b864000e98032240d58000078064075012070383c081301d103401c07010501c80202d50340e054144002000c0c1e482c01d034200c4280e50212523000c50420710044c0760baa40317803801c001030384460340311b59000201406407801c000c1c01d00a82c04400010081a5007081010541c030110480e04041901c04607840141a4a0000120310919031000d03010f00404000009014400313015054540090340c4201a1000340c0041507211180c40e10483c000c110b40060408507000c01002030360340302600b41011070b001847c00400e00001d41e02640003015201d90307 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 567471043 1250 567469793 567469817
    0xd03050109060603050c161b0618081b01050702060919140915221d0c1c080a030204091505030c01030e0c0114041503062112050c011506 60
    0x280d2041c0300052605290401003070406d03404005284c811f401d010030b51040c64414603014010b001c2204103042d89402c0e40040020b9a841340035002035201704039080440d00104c000640d0748030104007400b007814810554801c0b5080d00c4015152a041104103982100701807141e4415a1101039041c03401e420f01c1d649180c039041ca0b000075504a000d900a00c5e501411055081c0091558003414050301308074216445c00003a00c0c90f80302c00c105040c0e001c28000c0c1c0603083c8448900b83c4400602c07010a404c214009842004056900340840581c16590910201851030301d04004102c0040251a01600d5842d01515081c0c0e20b120300e4060b1075840940007049014a030003088685000c001282000b01d00303090038081400d2007c03c0f1601d07801000c0005041c420b282c5018400c2c4113580c011600509030200b0280185c41d06560001c00400d1103019240300c0c01c4a440c0c030304004200d002915440160b2101210000740c4a503002114039030002800d0f00180d43d01c0e103801724180d01c2c510403020060304066503000d0384507003 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 567472293 1250 567471043 567471059
    0x201140f0904020d0b120c0a090903050903010504030f030c05041d062d0405011403060613153b070c0c0b0a020120041a0322080909010905061e04020c0d030501 70
    0x1c00b031000e50547c0d4808082e0b80a19140c926500044070f0b04043c0026803a00c0608081d102881070303a00d400c0c3c0c95480d0904200406070000092a41101590707410042da80d07122000303403030900c2075026402180b1840030340a01c0b51695041e81e1540640c01038208461120340b45951201d106d140f0190101d4040400380d1600d10341428807886005102d10015006400003080110361529005480a409490010b0103415600c80c217070010120011014030300004169180e031011308081014a28046010301c4400c4005e40700307440e40c0204d0085441d010603091580300e010080ea43e1900c0b00c28203c9a01800c5031b0001103980c0c86074042c00407090540c0011420600780b9030300808102c60040c03181d8000c841800700f803014441010902c0b0740000511140c6030b0b070751100d0b8100900341c2c91480501504005401845080000080c0a0704141e1810b42d08900c85981702c031600d6003920004c445079a00708045114500207402e001c04100c40c3d005028000600d4070b01264440d0741000405042900407a8840e00100205a = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 567473543 1250 567472293 567472309
    0x9030a02010f0204261f0501050a15051803101a030f0f0a020f0a0512100f0513080307090b1305032b0503090f0102190e030601030201140f0904020d0b 66
    0x1200442d001c525044c10f0890713003400c2c04203485000c1d001c41d440000d6520740c0d4004000c6d5003840204865640300031104903880102412090003030324000c40b5015400245803161b030352040b00044070381d11520304201c0f04040b0062071a104054169040c0f0808800b108003071518450070200b180d03007400020307003031300f004041c589440d000400400c0694000501c440c260310002c00d80e4440c0c242d0455510074003409490024080d400e958000e140c0c800c1d003584082c115100000341c411040c100032502804401c000d12001c0c001c480302241c0802c1003004d14200e040010302524000d5501444500340588040d494418070180f98103e4100c1002e080341844051125241c1003007001c4802511003c3d203100900000d03902458844003c2c1750006210340400803840014041c40003a100700c100030001c40d00c1d0800703010b0101c4030640003c188000300c3c51074a4041c016040100e04a4140d80d010703183c90a40d12402c0d080d9084907840580040408d040601000d801d03940e880c0020030308003800700c001150079540b000400c14030b0 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 567474793 1250 567473543 567473561
    0xf0705060906010e07030b0301090210030e280f0303090b040b06210316020307080f06010311031605010503060303130f0806090d0f0302070303023001150509040c09030b09030a0201 79
    0x1650002d801004107508a03040c80307900070000e24001c6030501411001c60701401d09800000e500040040f281c2d00900c1d4540c0c4480d81c07410200f0102c0d101c1c0c2801c1c80d030b40b6414010030000c04030303101c02884440340440c40c4440e030780000e03d02c00d250015200c541502c1700206042e060303804a855803504000d0004625011b10a54040100e00302d00107280c01c80c40000c56074901c40c0b851040050303543c2e411143c0035940c05001050043c000241520305405c80402802d445107024042181d200c0e0f401c1e02c01e08072700d0a00044500788889540e007061680750074172005560f65080101980c0d4144002c01c00c02010440c01c200800041c403451103c0c0c2881410072541f07030b003040001491303400d455104000141e092035001c10301042d03d0b806420300607590038080c18200d000c0d11400a145000012130003090b4119400c032036000070f20110001080e5803990700c0e800214040a8040c10800000340184401466464180c0c0030b611311032000d040084125640b5502e000542800320340c40001074001044140001d03030280180d00700c0d = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 567476043 1250 567474793 567474811
    0xd0807051005090d020312180a11040f0c021024030b090609030304030f0809011112100e011406130302220e07050d060507360e040c0b070c0b0f070506 66
    0x14012a10600030750340d0044517a106181c00c4600301080140c100e40c8032024240c03c004060700e4058174030b41004542b010708810410b009500e80380340b01400e00140c2c8581c2e00a0720342603003c0c041c2d508503035100360040c01061565154004038404103c245070311a04595004510074103803c3d4091514088503410510002c00c03030601500704008000c0005c1e40f0103c01d4001c6002070600951903210354030200d004145071020b201841c40006100b640d00804c0c58440b030300c914450006e00784210380300d051451725074500380304205141c00401c0200b00a4544000500090462501021034580e41d0340c001900740d00d001d032220103803242d959030f060900f81c0150140301844030640004003c0c2e14504408030320190400340c13000d01001d035110003080145118540e101c1d8845c90f19400380c000e039038207032031007480300c0c3c040b0300701c2840b0546000000074024540f101e03100d03c01e94010707003880312692600c00707a404184e000e50421551049450f001041501c4440082d0003404010000d194407044c00f490103624244015001d000 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 567477293 1250 567476043 567476053
    0xf0d0b060d0603110d05030708220608040b060a0b030606090402130330080c0c0f010501030804080f0f0303010b0a02070b0a05040509130b0606130b040b030901050112030e010804020d080705100509 86
    0x20401c00811140701d10b9200d2921942d548800d56800701081c41003004d41c0c03a400d10302c0ad002071403a90025500703020b54020f1250f01c08948904040040d018003501c03814600d00e009200062042c503180c0c02400b1149805040580f4200b190034401c410003406800841d440038100c50150b4010b005108070f02ca200c0c1058403901c1e1040114940500440c0000f400314140303040c006030b107a003c8081800320300c0380410550300038440765840b841e240486800c540511000c40c4100341c10850f608c07000289428030070281d000514607603401c152400090743e204996001c20343c820b8000010754010410024848582d450348c40a49441c1807208100ca20784c40070301704030744c0141d080d01c0b15000b01e83d401c0c1010b6005041180da5569a29250001000c403110a81c07001c29281d85c04140017400e500d0780002544aa0983c40003080b407a030b228094007483c1e0340c060341c1c0a00020010701c1101065402001502c3e08136000030703c00021044503585004440c2d0107600308807556040b940b0a002203c1c1c2038040c0607004072445001d00 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 567478543 1250 567477293 567477319
    0x2604020108091e01060915180c14070f110604060c0f03020f0d080108070b0f0904241d07081012050114040f050f0712080d020c01020307090321050f0d0b060d060311 72
    0x7600010230340784441ca040e9904940c14960303001c0c04d0380c0300102d100c488a03c0e8603041c250505408180700241e00f52003c20030084449024074000c0126030035201d17182c4406441d20031584441c00d5400107110106d0641c8224000b4031140102000b01002d182d8540d0788004081d81000d031080e00340050740d030000101cac00d002d0101c450401c0450050310300100080e900025a0350300d40c5d1884813114050a20340c01000725812021407000841103141611100052007084203444c0c1c1c04080b5410b400c103c2d45c45c0f07284000759200780500944031003e01000c901440000c100c4078003d10a1903007821080c0c030300304c4520154000c07110400c40c2c1400707000d6480d1130000103054524034002d0394541c841018000100748a03000211500e0248950341510b42c01c0e00c1c8a40215103c0c6000d10001d4900099404207071801c43c0400e41c0c003109004014500f022032401075690a041900503055007076281c0000205071185900c51440c2e041c0f0b070311a031001d4001d00c1141074010071158075506011555030819019175005010300f260403 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 567479793 1250 567478543 567478559
    0xc0602070b1318140108010207020f0a05010507150f060605190905061e120c0702120109050d030c03090203160f06080103080403083001062604020108091e01060915 72
    0x80340403580680e20100404400c3c10f1a00024908180204031100106002061a29056001d0b25041e442a1070400c03403552984100041c51405100725800a00c04204c0400014884244a045480f0a11012421107806500c0b9001c1c1c4103140c108000140c004144480311011924140004842c142054804117082030041451489046030380c1101201d20b2800b102a9003140045605110312080c1c20030150038007003101d0980394030000301648203681d40402038110030301c10310410340f48a40c0031004045000e0700a50950140c150301e60010300f4541d1310007418015803018080a80480141c1d140c4d503220301c4c1406800c21070b89501da0404010080750400500015031400100c4096a402080c840c0d112544491100f412a04410881c441a2001f03507000015020700c04140341038030802c4d154500c046450b8070700320030050703182e0f54282c0003000c4507008100554024424617800580071030075501c446c0c589203200400e0301030416445417580e40d901c10400c02d140b9140b0072020303820b4890400701d92980c43e05602e = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 567481043 1250 567479793 567479827
    0x2031c02070317180102220501110703020f0f03100f15031703250306141804261b0607021f050a0f0c02010906050a020306031e010b0d0c0602070b 64
    0xe91040c4510100410019414070030707000010054013000395030360917880d00c0781094100c0d83e05400000701007080303001c20703291b000305201466480801c004040c07041c556020170290304020f40c0482e400408131441d088180d14288210880718205880c0401c00b60041c026880448e44508601403081f40d4100702400061b5103000184205010b080e409078483d1901d8000c190450911002403000c10b94202080102c142c0603002138045907809403411a041c4950300621100300440300451009001c2640050000340d07601c2686620741e452961024500358940b48058176a5000b02042d40d0120726690741c0307109542c020800144e02000b10720203001c840640d0781248408541080c20b10a01546410001d90220740f03949c811400801100800e201e801b5001201a000303124922040e1403007410302d00001c0700c040c13040c0201c0e402050042d000b442d00c424041841c020405070b01076240700954071140600400d0740c55131003600081e400346c018210f10600d0030030042c2c50a81c20b0b030300041d40e0080c12f001c103000001013004 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 567482293 1250 567481043 567481067
    0xa0c020906031905160801060f03060e0f010c0909050c040503031b1501090603061a100c02010e0a032405060d021026011509030203072606010602031c020703 69
    0x351020503440c1d190019051809090305441c0c00d0b80c030b03000c152090000018541c030403100b92548480d48507407160000c500b602c103030303005200710712080313031030410004049504c24025522503405032540915a189002c2c01e5604c914102000615001c90a001038a1544140768008540707800c403600d46450a00880d8490090701d80c804201c1d501080800b407088018001c01c2c1300d04d80701011094003503071900014001048240806e4484624201c2c8044043c90340c60759603034584100034100c40030044007241c00c4803c0c0700d01401c22030402c1261441d58540d40c6545c542e07640594441d48150f00f2000c2440b030441c480008504804944c54140001d1146503140e65078009066601a2125203541e101080252046e58000840302203041d00f425a50618600d00e0035001c3c16240c40c04409640f240c09080119003981d124040a54941c000280030040d000c07500710541c40b50510303003038241d4150380c50701030050500c2c0c0240e01110160308005142d000d0340621010803249421b138007070110708040d002d0f100100880c0c1088 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 567483543 1250 567482293 567482299
    0x603060a030215070c0306050f090c030a200a180c02031c0902040b06180103060b0403021f02070b16020306070507050319050906210f0103121b1403070c09020a0c02 72
    0x601e59843d401e800d28120380c4003c0e00954041e02c0c1950b01d142281c0180011600c1500b0500b4060120311260b00100b8009041d03e0300400401c800200d545400001040e000360b45420b6134801c1505c200c1644482c00d0340300040c4010034242c5500099100c4401c1a90b94140d4210115081003040490840d103424520307411804454001030900c1031403020600501400031015480751001c15850810400340c980078107000c1d021380c0d0501c08142e4400414035075000314000258801074100d01d0b03529610603165040304030301c0b4a204a9542070303a1913242100720744c4489140f0404802e0700c50340303c00350300b4104035040d0800541d2526034a0a84180c44003610b0340034180a943c1300740d0540f40420400b5220f041503442d203c000070030841d619400044154952402c0d040b41407a00c230b004c400000c0740a00c68841107412030381c00c5125504444410f107001c03940200c01d2441d40011080c3c102c0b0035000b10301d000e43c0c1c00d950120140000d564034032041c10b003040e80412980c04041860300400c880420580c2c00b132041c1c120310f6419 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 567484793 1250 567483543 567483559
    0x30c1204050307060f0c1e060605062122050607081b0d0b01120f2702010e0d170711042405060d06181b0f0f0e0301090b090c0f0603060a0302 62
    0x2004040f126041d10641c090884c8407c028035a5071940c01041146007507104400401096682e20b080c0000c42c040c641c5001082e03101d03100301c07400c41001207001540c00701200f403a43d4418203622000641100b00f400f41607465520907410810709035000f2a01e660001c0d44814a0758817070400c22000381c41c0d44140642e6003100c503103071580307407400764046c61070316007503995194007440100e0a6410807001031410b1030050318601e00c90b801c403034002c0d1038990270084241e4040e91640759000e2107506002503a02c00000c211210003074501040402e01d810009805410f00c61744846101e07150400c1044240c41d142001c411141d20742d0601076080040c4006000112281668035940f2040c1c40307504800182080c2d030000e41840c4600000700c0c244c00780c3c0d40c03110241c02080c805d1455403c0d0344c1c010498100001c800304001003031076581a4194103025800402d4000b00c014000300310380000c0c0d609c205009000340c0d0b588841d540658003210043c50310480280020380182c44c0b841c150310b003000000700e0b20300d8148400381c014101 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 567486043 1250 567484793 567484817
    0x405060d1e0c030c050909150109090e030409050c0309061906030507080706030c17010603180515010303020c04140a020307050408030313030e06031e06010203040f0305030c120405030706 82
    0x154210011112080d14041c600211514041c4050491041000d00003440e01c000040303054051020394850140142022003207035607e5a00510490003c0071060610a0b240030002d140000c0c0d0003848030904445024581b074a181caa84a020340f400a07001c4d510f40700e4103200b0042d03d92800200b00ba800b0720f80050b1003c4500c2e280c2206002031065400240c0203001d01040440e05001c00a4684100c4005607410000c0500c140c904039100700340c01c0e05e80c65400768110300410031913101e03401c880700d001d074031400c0d209540401d0b90301c03149031050041c0c081c42c680604d48010014160103000c1c14402801c191011300c251140700c4082c200003070300202003041c1151b001c00442d43d098424815600580110300450743c1d0703070074064100400391106890480010384641180c02d11400c1ca1004d484c003480c0b004030a0010400d880460400440008000d10b0452109200c0054580304044040c4005c6004102865484100044150410b895003102c5610b800341000300b0040c0da10000384440450f20039180400301d20f0340c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 567487293 1250 567486043 567486067
    0x10c0f062007050601050105030103120309170706050601080114030309010c110d03021c0e0f0402090112050a09060b0d0b0f090114151206010305060712020d09050319090803040506 79
    0x1581a00003030046007041002603102240080c05028001e40496201d030380c1e290b004480354402400000c0890700200700041d0745500070b80120102c240300d540c216030b40d01c1200040c954141c01012042e11050749440c01c5c03000b2540c01a0b0701d14003400412928511602a03280401d40e68840d01e60014104004281c074102030041c2109144606074000f0321481c00d06c0b2450038000e40e101c0a030840c1080d6003480c5c07484581c00c2401250120340400010780414140201841000025042041c0c2e05051040341d40101d4480803091040c0382c07040100f040005080c210900302042141c0c0d5000b01c043c00b82c030048903500c0114642d044c0490b4001001464080300d581c461a0b0706014000c6134100c0c460124000041c00184a003454002d0f1003203000382d42d46071b184840f074580a56100ba081c44082c00980281002c511100e100368044d5002c062222000b6180091903043d6400701e600d0484159810f410100c1c8070310b82140e00c082c00c04071b10f0140345007074a00c0c14105904c06031248117030f100e8903200e50780c0019803440d110 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 567488543 1250 567487293 567487301
    0x9060d02011d010509060a050901021509070b0912010f0f0b0f0a03110d06020d0605090702030a1e090315050a200418230906071b170f031810060302010c0f06 69
    0x1185c050b0a194a41309104e101508036001031110318050b0103111a0341c80c4d5011000c40e00f6100d01d80410080c244186880b201c1a0294880c0541c10741042001036580c50301c02c400d02902480c0007041c071001550080240a40048030210340c1114480d0890101c641c506075074025212040c0c0c0d8110f400c01003200002c8000030fa17406a00c410052000f400802c0503a03140c015544071f1011980c1c00d44d40c2612030380e43c0030000ca0703c85c03144e01505d00103e0700d11460040141034900c1c540c4d0b035003030b02030810060007504ea03150780881c03e0700010030340c45040c0c94004000702410140034031801c40a41d401c04055500300040100014001c5001d805031099096011074041d40b0250400300c412044100954000040c0c4e07c1c10820908007210a4000e1b845030703202159410707119680d0020b11620b0000300200d2209507540d030004c0031406102000e1441c5050141c01c1d2103060800083d8040c61300e00c0c4210103035081c02c222450801c100f0145900d0791510700001003000d0b0b6041003aa0499552100b02303a00a00785a00d00b441c018 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 567489793 1250 567488543 567488557
    0x1020c0411071509030f0e010c060e0c03030d05180114040303090c031712060906221b020a061104060503011e0b04080c0315100522020a0e09060d02011d0105 69
    0x660030501e2034080903d59944402c01c210b000340d1300c654110405840540c0e07079444000e07400707001450300000100411032035400303400c2100070402070b2100d5403c0100041c5c51030700711020340150f03159284140101d00c903040d10041008052040244119010040120403902c0020130113014503860760000400c1000c4000071274040c4d50b001c1400041c1d05801a0b010600303811161800080c4684040440c41c01c0c0740452800d4030400d8024810801000c2807210850104050003a40c071030542c07503202c8000c01e1070031007900400843c03150b03009181e10040303400c0c6201520049406605904010007040c08001e900400703c80c191079000d030741c0340604031052035442051201c50380702d58000c0a0100d40401c1c40b0f41d01056904880c00210111605500c412410018400003512203002e030094801c0c0411071800d000032400c460031074260705420207032085030f0040241c1e800040c00d80005040055401c00a140520815400c01020344161000412a500181080c8650441c00c08444620761215283c0d038454011034140b = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 567491043 1250 567489793 567489803
    0x1b070f0b0106120603080a030c0e13051e0f060402071110081801060b03041b0e070f08091603021e0604030c08010b0607080f0325080103060b01030b01020c041107 71
    0x22609080506510800380118000515107420804100079903006180649400c02d18040c40d0049011041d40100680d0203400240b0802401241d42e9a075008840800d20070301d014042034528069001800c191940a0301490400d030341c500380b0844400c0210800e41c001d50a9a0040c0e440c01c0c0b50908059450b00c4ea2010741d07100600720b0103441d5182d848000940201c040501060382d24141c580c0c494241c0d61140500300400c481400090049103400c020075125400c03884041524586800500c0f0009400301c5a80020510340c030303217104506a01004603a41301c01140f0182c00e000034051030301e0044103481e2102078403d071043c112a114100c0400c09604480d04000c003025601c40d520f24005502d08001c0c0301e2900b0f036501c0d102094030359052410813100c1c150743c04601c89152540851104e0005d40000d420800d004007552a0365005800710032059041851941391820550b24500e4120141c440aa14030b41c101414180d60700c00380e0f600002c1040d82040b080700d012805584540689034180121440500 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 567492293 1250 567491043 567491063
    0xf39040507030606140a0c0b0c0412060204241b03050d060905040c08010605010807030510050d0602030a0b030706050702040509031905040305120906070204020c070b0c010e010605030c091b07 84
    0x442e400d41e0002c022078041e0340354801a0030000c902e6a240340502091100030440c075203c40c50000d240c0489103548003c801c603147d41407603200c40c6c00c41d294941800f000ca0f50035a00007000d03c8195108011645a0080c0c2501d000500c01e0940c0700410150005c807076000c2d2507059440d00420113028070141d40c02c6841b01d0500300272281e1340c0c0b50702e00d02070301d4291025070f109501e40e00b0228fc41141070281c90240c50040e1036180c20b030b40b9040d104400a100040503420340d6420f01c2c801045030303614008441311940c0584000358403410302400c0481160b0048400e11300c41e81c48450100440c80c8c10406407424241c04540000c0c10b6030300c4521440c118440c66018081c3e1340d1103500c00b101480d4200000e04180e901620486485c01c1c40080a01c1c81440351800055200e801841220014036140d0010880c48010701c054607400c07680c8940071000c580000096440d2039460309040e12804100f48104c030001c140450040c005200c44101007990b1040240503001042c4826501540d0554030008807041d069212441c09 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 567493543 1250 567492293 567492301
    0x11121806160b092d0d21020d05071d03190f12180902030108070504090f06090602031f0e041e0f0606030b060103020310060e010e090a09050f390405 65
    0x1501d03000c03600040c03000c0e4101800060304010425a103d06004c0c5008001c0c56000d28140f82070700d1448500d004c0d016000102ca96510744010b560000d07116126203a0700c007141d21308000340042c22085010310b4802c2c0355880749a0b060441c0c2c3e03000960034400081500c121411032441d06140100034031500015220342d0004040080003540041034054090340c1c0d2044240980e01c8082c1359090744001c3c490110961300c00d000a100f1842c0a500c810724a6100310b0045410404694071003054980400c81521010b81c00f00c00c109020f10644000d100c040c00c0400c0f914140c07070501a42042501000d00301800c05c0d44c6413150400300c0c0500d00441c0c2e04403500280c0880f801c010740e261080240040e030004030348a94402001c141694024001c5d24010300b101125081e03494102881102c540032458465410032242c42110031540c7c82e1074901900074511102c000ca100101410303d41c6c07402c80001000701d5140c1c0280300e40301c014500d03c0c4405440c00b15403c5810350300300c0100c1c5001a40e82e0541e000c294401d1508042c8 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 567494793 1250 567493543 567493561
    0x130b0403050607080907080d0513030605070801140103060602060a050a090c0b0319050403080f09011d030408062a0d060506030a0504020405063102040b0a11121806160b 74
    0x21502c980515503c1c01d41075030b02c0c1721001e5101c0c5044d100c1e00e005a4043c00c1c0042007140944c0240004040d0140065800c1d69241c072910240d860564000c4042001c210041c0701c4030500284400b071402c020308050042ea860104021f50303515004207440400b0380c1d5031020800018960300840c040540042816a0050301d49440508640c820f8903100f802c1c42c5484d9210481342602c1c020b4522650701074a8440b000d58505800d841c0c607000041c61052035542c0c0340c3d400003c180d108025145170200400045480b241054400da240440c040c0102040301142e5044c03080074800c14159800080080e4021503c1e0241c02d8011005480c554000729400f5002004010440405910180c40380780212024441a00d03079000b44023200e40d0303260075010110542c00901008441c08000c4c040c0d0032288440041c1340c076558440360b0215400c86410a40040c94040d01e800035079104001036020702c06501211864841c80011540120032440f040500899002c61a0081402e0305e82e141140d454000d03100c40c045240c05011 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 567496043 1250 567494793 567494803
    0xa2304030b090709050906070503010b0c01150f260d0518040501060c11101223010906030c090203010501050a120b1e03070611060a0519060e06090723130b040305 71
    0x21404d1162810000a01c5c41200083c094081c04690b21120703e907909002c1c12441d6030f448000803110315929080c440c1403203003815404400502d0b8000c0b50130390090030401856245401000c4481c1d50320904400400a99008500000301192504005136503030642912480c4525107402000d030f00c00c0c40c0c00000904250446004030145200d80480390328542240c08004803841c0b0030052000091a461100100442a03031015000d04240303a0103100042810600c00c0303c48000341c119090107500e9060800c00c001e1130b145000040c0007140d100394115810103000904601400000d4030030084500c45845900d42650f00008500d800905100c0c0310400d1038800810f460361120303000d40240319907580014200d00c180c40c007031051a5202e0260036141c8641603100054070000d41500342aa003d5130020600240a00c02c1c00e0040070032a44d21700c903a280203001c225407614024158800e001010708038040c545a42540081c90b005180081c036124610803049100c00202c9410804045000203004820b000001031 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 567497293 1250 567496043 567496049
    0xa020c0112050403020c0111030f070f060c08041a07050c010e0d091e090b0a15030903080c09060304030f020f031308010518060403030209010e0402041401020d02030a2304030b0907 79
    0x80c0c450804a80c001c00310119801100c0150060704004041c00f01c3d503114040308840d6252410442e1304009030200c01800e01d9101030011a44461907018400c1044401d02079205584840d0501c29036504d05601da44246a40040d41000c000412400040300b0780d0160064411120b000b5008100c1188100500355031200021810000300341c186000054010782d4040300035034031483c050082400c0c1e1a00d403290029083c04d040855001601203000305040fa509104004000401d80c0c021600c00203500300a060740901900b14204260f040098514070342301c034011a0740041c1c0c9850080e405605c803000803403c101411542c121302e80800540c4420b0224110614015540710000821107038540d2041052002d0f0300b02c1450342142c2244c0002804a4040e5000e49107040040c10141021802040010b00700d0303000c1c2d08002142203c08107040c81c40d5a04016040c5d020700640006c5180400c1c0e004003801c403113020300001402e100810ba014a0b1a03240300e065400860f808181d413401801d1000071a510781070390380 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 567498543 1250 567497293 567497297
    0x5041401120c0f0e061206060f040b0d170403140a030e1201091b1e05031510030c03060e010515061b030705030c010606140406051603030b100e0f040209030c240a020c01 74
    0x50401b5450503000c68894050b107002010320401d000387e0014480a400c01d040b110740e0068507000d4540c049045014410f10704007001c1c160595403400e500d0010840c13203000442400981c04001c1240020f45c0203840c4500115044515010140d2001901809840c5906000300b418451082250031044120303020000e4410365040002c0c94000d01a02454107403017881010340c154000fa0f01d503c600b102c8011120380120468900d4201680c0320f84540307030400d010350300450320255a4aa0507400f1103083c42100e4000702c0882152a61100510009859000701480c40103507288621048804031800c20484100070350003000d803a1211070034a92079000300300c80e2080401044111888456540a607800c403001e403201a00c0d06428a0320060692003d910030240440c18140e0307a0303a1114560b660551042995000f039690000800e007440103214808010b156118000ca005005000c0b80d03650100c0d96400d0000c0c140d5441c561000c042010481090800c501038560380d030002144410280d0108001c0c0d186803007a = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 567499793 1250 567498543 567498559
    0x60a05191b020d170a0203100e010810060909020d02090601020c090a0903020c0904240f0e010e011107020f040e1501030605060a0f150305040501060503030f070c05041401120c0f0e06 80
    0x70405135840d0303900741a840c0e03403038082e0000149695010342c00b40d40c1050081d03190305d2030542c07110407103118400203070007400c10b82c1d2141c65848840c1d002405003002401609801340202207840d404036403c0c246a0000038810b4503c000024900c4e4402c010091a560008001c0202402c0c14440c6100510700c0070780540042c0549419503d290511110050040c1e50044c2074003891000e021b00070200f61501c2c502007202c1c40c3c80b448070000804050141d4038410b912180001036440c00c0c12402400c40ea5a09840c0340c17559000d02040001d81d907401c80703980c107a903410ba03404150b40304090300310340c2002e03c0a860400090300e160b00101c2404925482035100f0101540c4180e03a40b91260559660f400081c4101c26203030941c503458a003c01d1290704104d4001e48540004180d90703403110002802d40e00062920034103100041851414407000b40e011000070030095070201311150303a45842c1c07042e01005019600c0344903524140720381008001c91451004010404480c044d403900c0c0c00c00c0305a1078000f5140075101e8208 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 567501043 1250 567499793 567499813
    0xa120c08040b040602390f06060a051201020409060308040e15090403110c06031f090e0c151207030212060414150a0305010e070807080f060a05191b02 66
    0x505906006903041100c03103015030388135900c81000c1d501000a0600300c42d42080800c00d040044180342d02c1001001c1005076038918001c004a1a2071b1080b54020303a158004401d121b0a82c540605150503920255518101030300d02420040c0a0700c580c2d4400e10f203da02c2c2801c00414000104060419240740b02c540c14840d8035228424000c100c107820540da0700600c1c0c10042000a8050f144410300405a84141d410300b021039000070300345420455101c6000000060340c4c440c10080c0c059141d0240c22140c000f000703424907000da159134508600c41c4284c01002d252805003650241c0c401030740c1020303042d8415040217141c080001000307900154411900b03c5400004100b1030300c1c240c005c1c0c0041640340e0f82c00c510303280d40e80e800c52209511001c007a1500154028804408254203004051002022704000c00d035142c5009502d504d0881c481e445805182c12900075103440003c04590143c0001780c900001c41d6036140c4056500c2c200e003001e0f01540f850303440c2400c20012203071241801c10f00e4180d42d80036560710042c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 567502293 1250 567501043 567501047
    0xe030d020d0e270403020609010c082a16030909050601050712030c031112090706140d02030c04052814030a0b1e070909050c250311030a120c 62
    0x8101c1c20314901048480c10465114106003544a02841c0a55140480502220f8506907001000e40b002d900580054040041d0f01000740590a42d49c1c200e80382c0b00e07070103240050000500c003002c00c05d04030049003880c441c2090380e01820181d50b0440614450940c021500b0301c0e0240c1a041d091080c2d829050070040003407501d60041060320722140d04180c420050718040c11f0101c1c020400e914008050503a100152513411002c2e030082c06400c45103a40b40021400e04c05103091a10080d0b601a2080007401c5408980c0c4902c2001550720002039444003603100d031922200c171081405580c00513070308802c680684030340c402a0381070003c07980b12041e10140e4610f42c48020700c20380c0c0e08030b00503555015031245c48810001a800800544d0040304811407801e510b0f0800502a0200f00c10380d0b5501c00034400040038002e0f202c4512506801040c000149840c08a02a1050400c1c4c2d61380074111208807008888102414016000c0440c4e615054054a94070840350030050001000151204c960a251a242100c014 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 567503543 1250 567502293 567502303
    0xd0e0d03230322080a0e1908010b0909060c12060d200108071b021e0306010b0414190303080901111c0b1207031e08030106050702010201050f040b181603030e030d02 72
    0x60300100c04920740314005801b5214850101c011603004030071070b00a00c24528182c076954000d440140c0002c0307003030040c3d801000b004860251072240542c01407010b10a00403a20320469005c00e07004002981c443e52000c00040e03410030608405090520580481040000401464111080242c03180a8161941c00c400c584800c1d040c1d071642034940c1ca01321480c001d0318055800072111200800131480312640440031a05051080c0d0000d000c00304081000d1003e2030303081d00002071060080d6480088891000c00942c1810307814030000c0c09001441c1c0100b4500e240070342044a2041d48011420b50718040400000140c801984440d07548a19007107000c07402e4980301a06074503007540c88000340415030031902d5001035811400d4420008104be4241c050000b218940514024a8241c4403140c949005000290942c2c500400207140d0301410f1040000040c0501c0303200750401e9000d83d04e460314070307140f17401e9600d4205608101c14011010b950300104141d0b1090000c52001402e4060b15241c008080701a0798031 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 567504793 1250 567503543 567503611
    0xe1801030321060305030a05031b070b0c0a0e0d11010215010f0618090e060402010909140c090103020d0509031317190c1e170d0e0d032303 61
    0x5800c0c0e10280100608a21074540c9148280000283c0a540e030399409255a2001c8580c0000ca0004404c10200c120320701190001848804282450300300c403507481921000004142d001d01601c08900c0e100103500c14034003a024104050074004e02c44085003807041607007840c114030500520900705030b2580701d80380c0c2c643c85049803401c1000c0300071507040140135148481000800e075454403070443e001a101c042805503126a800c407c02602186c20039000050001d582600005c1039241052544128000303a0310743c5c2a423248080e0748060301c400240004a01030300c02c00c01103840340c034144800e011040101000a21200c01c818021330b01e11a070318500c2d40721220190196113919048054081d10034880b4111100403d4811007079015079945482e81d900081d01c60b00035a00c42143c00550a2028407505038104150f0b107950703402080a508001e40003807408a0411109025845030030303410b004c050082c101c0e55a03d81d40c1046803003a4800e408840306541c1c00132240340242e2510b0301140c0d0a002442001c5003a4 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 567506043 1250 567504793 567504797
    0x60105031204090b1f030c0f0f0806012a0b01080105091c080a1103070302030a0c020c0d0204150b0c0a050c0a05010f032004080a20010503011a09100e18010303 70
    0x1003d142514803002800c1d21000c040c0c00040c4020b10005c0c41c401d042e40200c1d406281c1d1000642c80c021014010050603004c080c02091000242c00d45044681010b80c56510520907c0c200700762200c0581000420002407488041d1814510303020b07002c00c5042d0075685d0603642e40200812069840281c0c1a0b59520200380c3da00c07214401e00ca456049a00c101c0c0044d034030a105100204003c6038102c56141c055204070b0b54038001a50200c140070992000c0c1c000c904241c5801d100800c11614000c0020710030018004000341704956030002c214501d20241d901000034035035181e10300c0d1520501c201313007500c8480400e011a03450261007000060351400c00c110000761380e03040c0d60701c044880e0a50340c2174004180825444c101c011601802c050740c2d00c20200284041c0c18082e01130310310300e200c0f0320717000b030f201100980c4081940d048020b02c2c00803a6480415241101d2441003401954159840303910310780d05c5040030700b40c3c2000d00404400c039607d4000c90030301140c1800f503aa9202142c04c20041170b0010b007081c000240 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 567507293 1250 567506043 567506047
    0x10170c0f09010c0f051b0f12030301050d0f060509070501080c0301080d0311072102150f060d080408030a180501030c020c0108060a260c0d050c090a09080c010e0601050312 75
    0x20703154490071850b0401ca20503082c0075150a00794079002d10b0440d01c0648500c0f0b800204162040e14102182940d01503c0c0039a409003001c191014150b450f0700050140c28001c1d07100f003168906100030b03081524817a0f508072000b00101c2c200009403980b074074901d00074140401c40320740c08035000182c031600703c0313040340d40610207444080d02c00c1d40202c3c003800c0d80e00304d4011042000c1c01000c001c102e40001d0320411490200284500220750180039042200321404510030341c01880420800b0080042c110341e102d00b0440b58021003410f249083d00050141c2d0b0001c8002e0321000c200d2108003604000d05803100b5600a04150700d59a03500e00450540c0c04e103100200058100d161a00010350050750754640055005006082180d01c40084400e01082501102801091103142c0d0f0060f040c1130001640c0c094040d60007152280c00c81e1502e9a40312201440c55004d0f10307010300040c500c14410b40c0489042a400046203903030324820f0000c68080d1400e03c41011081c0038000000606150000700100080c1ba2006124 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 567508543 1250 567507293 567507307
    0xa120b0f041103010c030c020f030705070506070203010e120307020705041107060f0209030a0308041209031707110607080714012705030730090f032010170c0f 70
    0x2030035580c015000300c0307000d080b07540b6040032550f0a000e80100700e001c40d0360000e040341c0c01200081c07400c04424103c0c04030f5003041280c0300205e00e021544209a40003a6412507030b45045101090040c040050342501d81c0c0160ba0740000e03441035240055004011541c00c4601160b103d8040004490507004460300021081041100144454110070010b042080c001414074200c140841d080131800082240000c101c0c4007000104403040c1036004803102c86142003490641140d82e1071091400f81b507009900114007180c3c1800304001c030410402055009031850741c6502040c035040169410000d4125008206010040201c520510441d11003198000c49290041c0c02d502c844090702d841e9075000d880c0d0f4040ac2085074041182c002d08034003405a09500c140d020100c40c090100310a040400410410000070010010040e00c0c8a000b000d603504441c2d8080b08101c440480c000030b1031203064064000729500e442c1100d1640168010011040703e00e2440415601c1c1c2da03024001e031085050316020207405000074 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 567509793 1250 567508543 567508561
    0x30d080f040501200a090b0702100c0f0210121407050306010f020a0209040f0b07080f06121e10060902040b0f0313080d0218010201090f0210050919050a120b 69
    0x760820300500000460346070f401e0100c081c40316822080c00603003e0005083c030030290300c90f03544402801e00403d41e03800c0050711760000340003410101c80e400402008000d180c0520196100c050301c12640141340d84c448186406010b4207482048a0042c0074a01e071000d0340c40044442890144554078a6440501d103035160f2005462003052664a401144100340d041e03001a144c0039402070040e8002d2541c0e141c02c0740b5900e04080341c850021320ac2c00820080c202484103a8048800340d6030003d804a988aa00c2c0074032181da1031403d000035211040b0150180d0802940340310219420042011000081c03210380c0d200c0380100d0591050b4800c0000f200400c1211800030b0b40542e02840d0411220040710a241e0015100e0030f485400030100c1008082c1e002440400444e4200c4905080000130700090100250a4544541e00c011514010380900084800100c009100b5000c80e01171680081101d00000801c038140402e40b001030090a001f10040400821548141e10030300e860b0603400030f0000d04c59600c0c02da135 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 567511043 1250 567509793 567509821
    0x11150307021f020c160906080d171e190501090b06030408030903270a050405070512042405100b07170a0905040c0509132903030c070f060806030d08 65
    0x18090083c1e03080c85100e09407441441428208080c0201110015081440c0c2d03200b251881d600c55225680222500045150400c404c8665140700b520844c0c115503458502c0c646d50701c6482da40c05c1c00c5014501c1040026240010f01080c045501402045580e032601c4418089a440701040b50307001c02d080c40042c0014402e80019035006005a00b56070610611841c0302211030074405200c0d4419143c10041001400d10b4207200c0300600c02284c044c091410f012002810718420400038a440360400740c0041d080c040151501855014580d0000078480c00c0e83c00b030030008040a407100d10960030b40300800281b200850b01507078092500021030000007550020759890b06d511680400f01840303c00b010001d80f40e03440d48900055080c0d1a202e0b0f550310307854001000b40b1001c444842c00780582c580010596498601d0418416414983e5682c4400d0f69000001914500450106500a204140c0042101c03011120b1910443c0c00b542c48800c4603071607880c1050f071150314081841c4001007100002500e02d180c0040 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 567512293 1250 567511043 567511093
    0x80a080904150b1c1407030b011e031d070501170a0b06030a0507120c05162613090207150c0c0c060509010f0309110108061c1115030702 60
    0x1000480d207080e181c0742d218040160740460480b0501042a411082030403100d80300b40081103e0800c290500c2400c883d1039150064500f4007015620151052140d01801305940ca0005910719030821a43e140341c002d004c0c1c03d540c10040171007944c400e1030410010000880d0410755070141c40d842d5056071202c01d10040840000e003074041690301d5042011036030b1907990086000300c00c1c82401040d10714018002900a0380d1320500400b040740380499a105aa5000d000d61b00311952055580403910b00c5030038a0b18403034851101900441542c004120b03000d030310460041400b640003240341c07820707140d41d421018100d014505024140b0005020424410352b5254080c2e68170346124204658a00455141c00c21695150340222001c500000744c43d404943c2c004090301a10340340d51400b8001007503941c4e9080098444451820306000707400b0b02060389541c0341d0110000c90080d49015001c6459541030540c00c9440c024445801840091500d101040018044a00c51440c5030000c2c82c610550038603114420680740 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 567513543 1250 567512293 567512299
    0x180207080409090501150e3312010c26040602131203110f0d021506120a030206010e06010305061c02150d05190915110d022a07080a0809 60
    0x119020b5010311038044403601a0000081660192650108401c082c0d0081c0b11002c2c15102040400c040645c200780c1420030700007904000c110303001c080307201c128403260400354008266070b03215210304015170010741410120b59903000b55805103820340d1075600c200c10404c054210b2800014020850a07001407540c02e468a60988031144c0c1d800c4503141a42060f20b0450006a4020400d4844c9030100072603490031403084c0180254903480c0c400607541d48103e00144c030314255440f0020365980e890307040800301036409100b601e0301c0a00034a8020b4546c17a09000d00a18011102d001c00c3e0694424401c062050f54054880c80e40c68030b06010380c3c0c8a41181e001c080340d109080e00301d002403e2a90310040c104e48003007401d000c13801d41031102c84501003c800d001009602031a02103044042092000004540c00c0c1e07050303001401c00031801d22021355205900d00a9400ad00014207900d50300d424440300111040c5c40102c43c03070b080c00340b1100942c5401d010300c11102198000b0004c980400d14010060030424402 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 567514793 1250 567513543 567513547
    0x516090c141608030a0207020415050d060e0a08030f040308010e01180e0a0611040303081e01210f0311010506010f090b0a0c02030d020a03020f160e04081c0614090118020708 76
    0x9559821100d500485090003179503004100441142404d01840c20500d205610f10b8040b50f08101c00710313815960070303c004ac048a0f15014041c1304810140980f003e00e6030048112036491802440f00c000c201015a021400140943d0000440c42440c4006034140c0304a1a00d10342c0c284481d0110780080c4c140320010341c889002e61919100003038210f104101000c0103c090841d251340c41c2d03080c09040060020240b52484031013444c20302c01d004030070554030f044d42e042c507040c80c2c1c2d4400700305040358542201c40c1000b450707900308003044800c0c140c000502c501c0e1240000001d1009076540001151507001460441d0b001c105542c0040c40740049400241010a11514000c1c0100130207400103486c004c3c1c220080c0001d42c02c52070700e5105050b03060250940c204646030082c01c8419500410b141ea851a51007445824001000881c081113a04003c0f1882d10114401036a428045000e1040041450b4450711812160795400c0542c43d040242c80d090480301801d40c100d03410589040048043d42c028441140d4131101 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 567516043 1250 567514793 567514837
    0x303010308030711010c0f0f0305150d08070f0f020406060c0b0106080612011a0405010f0e040f0609060c1d01030905100504060204080303010803130f05130c02010e0a0516090c14 78
    0x910031444480050303547d03e6281c5071030360000b410220705080c1181c03c1600307040800c2004101d8551145250300145c2c3c10a614007007909203a14540201c55006011000308410102803001c0c0c0140c10070038500880b03080004a030b65040580300b005202074001c080c0c8000100410080d801940010703408030014100c0310100c0c1d8840b18040c00c5035000d845100c480d640c155100180f909192040d140909040c40c040101d403810003082003202407008000038020700c1203020795800c00296400c081806a40000c3c10301034841080d130050301444403d25100303040c4266440d800c102d90300c280101002d403500078015040280781c100102000e030078010015610640c003040300044101080008500a000d110065911380503040ca88401c1c2c2ca2107503109403080d081d4424180880d507502100d080744030212100000d00a6149102030380584950300e032850580c0203a00140c03060010104d9000e9142c000548800c00d444d8842c6180b5044505152580001440b04100b40c8002e8002400910541d001040c120070143c1c1 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 567517293 1250 567516043 567516077
    0x9060a052d01080111030108030f03101d1806100e09120a02030406090506040e07050a0c080a031a060406020a081308070b0901021935030903070b1803030103080307 72
    0x2821880030784440340541d00410080d0828403c90b0886842c0c003a1407859549040003243d62401114004100d407840000461140d0844440600003400403e41c3c100c8040005806500c101a0880e91550020880d1200d0240e66401003000e03482000070382e00c0c00a505040c924054a6401d0040c41803c29208105120400550741c10180445005a5000710303075490901100510700b8075541c0c001750182c8000d10003400480c0303034803141c141e10810303a26240d0780314000008100c4080d040c0c0e40000e000d68a001034000c0e00b0540c03640100c031000100820340a8000900c41c140045031145200d4100183c001485000004000c08014840768005150800e1041d0700c0b20251414060ba560000d0380f104000211103c403960180980f04480754003100c4440d001000b6142c55000000184080c4107a46090b8250f0881e0b000902410714a1010014199141c0c5040c1040c542c2d00d9100410982d41074200000044e5030205402c60390350410843c401950a41e4a140e689031607980010303001c40c050008018003062801 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 567518543 1250 567517293 567517351
    0x60919090218060111070b0d050c07021e01031404050601030f0215030108011a030313152109020405091b09061201181407300c060c0501060501050309060a05 69
    0x706954a110b80c50341440c100241103010107440c0306219400c0808100311089100056941141070a0004640c95850710480d00c424450384200960181101009440b00094032032034035003600b0203032003c011a1600c1e41032140728441c11900141640d0011005000045481c5202c0c14142d1002e0714a99442c0c598000e0070810f50000d0300600200d030f6580080b81000e42040485414001c420745c082e6150081100c43c2103500c0d001402a9590501e84029105005203c2e4521160711650301031804042c81e850001c3c80f01070b18000f10140d103d141440c020400781440070441e6414101c2c03840e200347c644015141800712007030006009603404110075609400001e0300303014400d000911200c2d003050620182c9498440604851110002540810001c0c85504031100090041c0340011090b84d200c075110711385100a410464000403e0506a4880019403542113104854840d1103003000b0b0006544075070044480340011a014241a40590041141196607501498014115164801000068204a080368 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 567519793 1250 567518543 567518569
    0x70909020406210b1302031b0a15020606120114070810053d1b1401060b0c0118110d1401020f0703090e0106090b13050a0f09140609190902 61
    0x32454050f105020400300900c02035110410035a090741001d2941c010a0f40c0e48a10081d000c0060140101d0030000e5580609007801082da8480c0c0ba610f811070400001e40701c010a482403409183d04540041c1c50f000103000b03d022261417210340f6082c81d940c480040f2080c4001034528200e0031900320000c1140d8540850b020000c080500404d5800703113402020001c160420700e882c0c01018515803000c0585581b000310700064201c8011a43d00107180c44c10020603c00c82000e10b008250f1924600040c80b211500c050aa803802000007008481300c503014900b240050710b100240b00302981401da102c280b07442d07180c20304583c1c087d080421041c030748043d0084c03ca03405a02005a982c03800710b012000c06500c10000400f4001c40e0f51120703034079450484003802540c4c17140207480e1510004194400c0c80007030641c1c1c03240241002810300c8010380e600c10b44038003010f6a038050160000c0c1040070340c044110145081c01d01440c070140914006a64094801c503402070007445030480345407902046800b43c0d480c46043c0c408 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 567521043 1250 567519793 567519839
    0x905070f0509430807030902060f070204240e010608100e04031803150e03120109050c0c0106031104111c0c020c03010f0204080d0804050a06020a090e130506090f070909020406 77
    0x70707030303001d80e0000752402c600101740400700340c04c2000000060301c07a41d0a40b801c00d0998183d09445e210315200240c06071084140700402c0808998100c2c960301d0701300c62100e080360480c1404680c640d880d0343c400c84400d501103880e1501254620f07405c02016200703145481c0c2c090700070f01d00440d0341c003408080c5103218010ba074405c0d1469620706e1088440d203640d911405100310400302c010f520f880303014040314401050522030001d0003035482d0006660100301d40212403041038024002c010441e00c0f450241720480d9040c0450740514a000c280c41c144508080450b0107200b01c4a0008202841e4501070308007070140443d00c2d00031801038030114100ba031000d00071000320311004100981c170380d401d007486141b82c40c0d0010a40410000d6000c18132010600110b820260b854101002603511921404141c4601c119507011600521088017044024a20f007200341d90070b5032003481070b1080d544940c0301c1c841d5206103108461009811125040119401c01d0b4041800c83d4809000802c51a80c3e41200c055510504051561 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 567522293 1250 567521043 567521161
    0x2220504150b2e05090d2618090910022701020c010906180506120f150303221509090c03020f07020607061e0905070f0509 54
    0x9031000c0540541d4154403030503905404140f0b190f0f51100490311403070046800c0c80c82c121a001c04068801c9003154910f0740b006d401c1c1c6c1024411440d00d070241070030079171301c008900f09500307248a1003400c0c08080355107190a00031801040c05542c03040000100002d840031019202d103107807032160b51003140050158210241d011b203a5000c000d6070700c03800207000061103d0440d040021050902d0381c111689400f62041860900d09181d00c07003c6c0b0354408095500426840080032840c0c0b8500d503151400c07244034007070f40600c0c0502916100a0404032007142d40c00e4a40c0f542040c807083d0030220341000c1c000400c1a1440140b44030560750620280c2948650000343c0c001604d040080c0850b071054040c0d030300c2d540e1917072904528201e000c01200c0807501030008000e2013914001807200a0104030b812110080700380380001c003155060700d514540280040281190343d40501e071400601e000d41444031f0003c88030b01600c20010340d541e035010b405125000c10319401403100e46580c000100007a0540004040c0c5904030800c03 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 567523543 1250 567522293 567522323
    0x110c1c020910030305040e090718020a110d050d0b18040507030b01150e0f12070e013303020c1603050d03141b0a121128020a02220504 59
    0x30040030401002c1c1882c5152140302080000c0e44501102e0440d0000c0029409681300c03417509a00303002c1a07500905407174512180f05000740b0394a60003020b03800242d4890045035110444c034943c4610125040002041c1309210a00312440380b0b8200100b5520018418942e101010100c2500406c042d20151040da1201c0010b2041000110b0780d41e007d0270154001c1101c2a40c03c41d401410164001d0043d0300980101107003031030545030701071615261011802034581da980c4881d03040001c1c600c02d103c1c20510141d18414200300c1e90560b40d2403482c0c80c02028400c0e00c500601c001c11782c00f941c0b1542078090f091198040303428241d83c0d000d1428001e184604003034062a581190024142c0d0b070580c0c42150b1911030482809018000c00b103a010261041e001026100c4c82c03e2801070728880ea501943c07034a180d0034002403800c0503040300010700d00d2084100b240200142151410780c10002050301000242e80020300080140c51300030384044204542440c2c00402c241558014030070344605540032202d07500c80c52898 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 567524793 1250 567523543 567523549
    0x5061c111216080d0516151103071d0103090215031008030403141606050d0903020709060303050403120507031b06020d09050f01052a090303040801090803010801050604060312110c1c02 81
    0x8070000050500c1d00904001006d6011508215510f03002414a0720b005000c0240f071030030f900301000303c100d0700310410b40300c0c9032100018094446100359042c0e120301d40d20964a01d03600911842d40800d401408140c6988080061090540c0c0090101800c1d031840b040c00180c004020002040594070480782076200304101c07851a0f141c80c03075034071f401c8901601420080c4007181c0d024007500c810030a01c99002c0f401080e18101a810080d450b088400c185050040c0402070680000080040300c1c803505640720280c2010404503503a000f161001030000e03400d500b00f0059848408501c80ca1180078200061a28000070b40890403900c610004480030740007298016013480083c8502c40d4031542c1c46090003d4807440c040e11001c54a204603100411f60800700c0c101d00c0648040094401034900e240c000c2205001905002c101c580092045800960820001945a0805028000450f94040029500711104010640300102e82d0820000107100d800c501c00b415542c2c000841d0a4910303450000784441a01d4014 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 567526043 1250 567524793 567524803
    0xc0604060507060b040b2209020a260d0206060d05070801230f0103050d0507030219060203011a090a030201030c0c15050a06090504020f04050612030304050303070305061c11121608 79
    0x4103215034606003900c0d0081c0c032118810f007c07443e00d0100070410a804003030007200900305101d02a400030800e00012641c40805003012750a021080d21a0030b001e020891025500c1d078550300054016084140825a64103141c04090849032040341030305e240d1612030903005c1c211690354000008240c10440d111603210b0700c0c10f03441c0750402c81c0841e5000c40340d07065480e8655034000070a0f40030304002c0002021000e161003400210101d003682c0265190b058514103004010f5002030051203030080d00000384565201781e4030211280003001900b15410285075400544c014036031000000180030201c0003941c00100f00380c03007094030700c402e00e030000585040c5603a0350004c43e000f0b900400c005515007010f20025988101d94204416402c8401103400d07603e180c0403441022403001403640522011007070000b000800b0010318880c1e9800e03682001243e0740c1c00d08026122040d100a40c006132403e1349030700080f034041e090803154800050050118420140030310380c0f03080e150f0120701048a080031002d000714a42485 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 567527293 1250 567526043 567526061
    0x1415010206040f0b130209130203190f03081b0d06090c021209040c0c0f0b011514070b090f03040902180a150f1806081801061a0c0c060406050706 64
    0x2004140d2440c140c3e490f540714081d80c12020307145002d4100003030441c860902586014030741c0545003080608108505c142c4122203e9000c034440c1c0265006581214000c0c804011a10340001d0004d00100071520b0599009401030724880311b070501485800a611b07041001042c84882d11080081c0b480d1810407001c0448820220002c215003040d200b0540001200c0191800c2c54800c41c2d00103180c21b4810010345030103e50031401490980c0354000c08041c000c20f40d5143c0e04036a1401c101000c0030000b40c3d02150a1400b60718025085d00f410702c10034010910801145034865440e4040f9a0800b6400803100d1864200741c0c4600c01c003d4000072050700e2441c0141da0f00d035602000781d645520a600700340c0203150401c0d07160b440e14104a0404034a030780c070f1841010414002c50b50500d121f00003a8460b60010505082180c4d0004048040d400c0540c10010500c649000c98001414503206880f40e01118407050780003182c018814030601900f40e4140d65140001c00041000e40ca0706651003080d49440000d0702e08080e = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 567528543 1250 567527293 567527297
    0x2a06060e060a03030513030b010303050408010605150d09141f1d0a12090302060304080306040c0e01200c04060914010b0c0616031508010c1803022103040306141501 72
    0x50180011900e800b070549007a254141002d0b5103580b14010900f41c4030310703240c0c005001d17110400000001c2c950400001d2003520402c0001b44825902e450500650300a0b008400507400410885407080408035800341a041c1c3c0306078045600458a07602c05894001c460320403e1030a50039121a9090801911a01440e02c0d094a02003151254182000f501c40701c0c0362802070080c24005001001d19031189210790081c5500801e61503c0381814241041150800c89400d1301442c40c124501005500486d0111803400d8144d41d01800e41b450541c403040321008801070103100344902c00104d940755403103015450140a0028001652007010f503401451404181d0000041d10400c201518a000c00030400e13076030001e0402d004000e0348030042c008070001e110f084000420482d2903000070550b4031040d042061550030955401708070030300d208400c40945080c0d00c0003e510089000a801c42800b12003030040e4900e400b842501c0c2003070354a4440c0402d40e041c09480910741000c1004008100c038189414480b071050038 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 567529793 1250 567528543 567528569
    0x70608091005040c030f14030f0d1404020f0f0f13090210090b0a050322050c0f04061202210f070e0c030405100b06132601020306090a0c2a0606 63
    0x160b142e4074104546408090080040e0491180600110203000010318210070203c8c0d940301e141e03001721542c0e2b802030700084400908055041c0303039080514159902a44d0002c01245841210108120300e03980300a4840d46c1003a181c001c011070503650310706101100520314101140002c102d104020000c0409804c1c042840136110090203422503010a40d1100c00a40c200540d40e42c070303405420030302083c44425a1404003e2504007408101c8042054083c0c00c401760741030a841a0104200f00580d11701b401782000c0010307a2805a009458080c00000e4090800c850750020310700c884079600d0524034003101020340c0307612045080294460545041ea4002070500515043d030400303950b0f480c3c030740528180241100703854202c80c906507a01d0350100c0d002e40c5607420780240034603540c1d1010010024144001c0c40341a1400c0c0d82c400301004180200d030310420740203240407400d0790351420748801008150032004c10481000c601806001242e00c05e10701c0d2040705402ca4200803614609007099582940203080d1482003 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 567531043 1250 567529793 567529801
    0x272717070812040201180b19020601080c06130f03050616020a0b040201030504320f0111071b1d011829012105041e0503040501110f070608091005 64
    0x78040a03114101165000d1041c56103c0b800100e6a0340091411082103081c4407a0004503450440c004000605011194a4150960503400c2e42c40310307802d2243c000c07550004401500946401401040700c011954902c18245440344c0450030300000b160030483d642d81c815800d20001084005040502e41003078070003001c6001c015a06c0e2010100d0150009044c543c594020408220b076402d40742c080c5481c4800e145208420510783e49042d048841c6110225026040106c511280107010311501c0d80307806122140703015281d54031070326128440c80d0340503411800e003440030401c138410314240c006c0200081044e404035414071625804100d45000030403511841d1a102c141c2c5000740d0711301510301d05084c00e40700607108180401a1018010545145002d1526100307072681ca601c1a442030b030065006082e10b08100e01e84402002c8403161a0358041d1150384144030030402588542102d04034421a1410344203c8031032030301a103190200b25040744020500c24020029210002c20184c00341651114007404903080c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 567532293 1250 567531043 567531053
    0x191202090604180b030607020723060406080c070c150314091f09050a05160501140301050f040b030105041104050a02090105040b0c01021b0a170427271707 68
    0x306510802c200018004103040340e483c0b550740130154010011301034541e5450b01100c0252104298012910300d004512803c02c2ca2005a4800308440500070309400d2134181040419107401c10010201e8842e02010441d0788001034944030358070002e0504004600d82c101d403a10002c0c0030740f40b00d00c00c0944100210310800ca94200000b0f03454140081d10707800290070000f036803418000340c80d02c5480505a88030341e5901c142004000511296480e22226003040c0b141c1d00c40c0011a94480015421070154500b0710061060b4070700074102e440c51070380c01007000408461110102e802e40e44110360a8a0b18404c141d040611410240605684404180802c610f0110aa000039240d8000c1d80140403400030b000c94202e0712010700358100d860381e0138034190b81c203142e44921106658801020700e0841c2e42540b2420000e0076220020700b603405881014250365138a602c048000220222201846643c40d52125002080702200f208141d8995604011419031083c050801c4d128100b0500310310b40603c4d1081024402280d = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 567533543 1250 567532293 567532297
    0xc0b0f13021c060b060313030309060f1401090c081e091e0d03061403030708031812041806051c0525050f06090906090903040b1204031e090902070c08031912020906 72
    0x246c1c2341c02c0000c0c0032040c6007050001009501305070304440b4508150300440144950f40141240d600b05414041c0100c1514101c1d0803c1d41030368081341284001d1b40b07480038015401c0146501400324000c90710341d010500c46405411549610142040d04070400083c0703c1503041c00790340041d10090f08905d03985072442c0040383c0e89120305000038041032004004078148400c0c0c8061444082c25040464030070110070f10580406901501c14000c410381100404081c0e050180600381c22204028a407600ca4404191002d9402034140000c07101402080d40d079480c141507429010f07a4119448455405850a02c014010b00021b01111584140c6091000e040550703945101c441d4030a0040e43d42c0c00a644444082a185000c1c0d0f8202c201c40140108a00d0000300407060098800c80c003e0f5950030403804a640810104000505064001401a5018003800303805400500f0714900c10080051a40c0d50385140d5801e5170403000d242035440c1094400308070610f030b0042100f0781c280054401103140449080000d9030754 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 567534793 1250 567533543 567533581
    0x70e07030c050705070308131a0904050627070e0d170a0c0c080d14030403081b090414010906150c021c05060f04120c0b0f13021c060b0603 61
    0x41c0c46001007080140301e0001c3d240e440358407004039180c10344c403403500c0e1070190080f03028520b0306403644800081120341040b0054004840e240a585030204410610002c1c00c001060150403030000800c802c1c0d04003104003451030303a8402850034017903801c0904004203050680340c0c2651103039841030000d202055406c581100e60140c01e009107607440348145800c1d0303074020955034080c010140410f00001c1141003c543c0c41d0744215140c1d61070081540840400c80b440c00162000b0780010790302800102020303685010440c40106410103e802d20100324009010b49102c00b10640441c410400100480c4400b03008140c054007040e1340300b51408810340720080000440380f5000c2d118030020325001a81284000410b4051900310080c2c03159494464100812503900740c404030340c80f209108000384554450b008280c6002d41c416007a0500b6203c44072038258082e40600390140f814510014800160345001e8640c200d00ca01030213070800724003541451400c031103092700302c103004400c200200610a00c1c404070144035 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 567536043 1250 567534793 567534797
    0x602010b090a1a0a2d15080c0f0c03040302030c0109031a041b06050705070b130603020d062c090d050a051e0301060c140304062f03030c090909070e07 66
    0x301803041c0d0701c80d00d2480c0c400b80c04c0343c0006804900c80d00c40b452061700b05921040c8040d400c100f10410b0000c1411148104e07145c030341803404c0c5d81c441c5910814601d84c10140708144c1c141004560958000d4903802014090030540c000141001142014800021216402d0a1549200345940c5030107001c0c0e00d1a06119141200200005081101c1c1c1050101c0c22181c0b00c55032a0f1144d254480139001e984200c800b5a054403890300002244221074003140c0c0600c0c8480130101c42c0d80d243c010b050340030350008030400c1060b540716172012842d140c10099225466448044590300c00b031495505200b1040080c0c0305901d203800c42481c414685d600720b411188030603c20b1601039525507800078410700c00c00c0d060f01039081e1070302c00100024103e07038000025508903001d01140c2000c0f0452001c0c41c1e81d280728500c20701010903625841000004402e9141c051881c0208805c41480c42d00e80c1e0b800c904560003191603074150f4802145141950902965180c0c0c01800c920080411303078108030414503800c1000b024682 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 567537293 1250 567536043 567536051
    0x50c1606050c070f0e0f1801091121030f07030201020409020703020d110601050108010506180d0b070908070e06040b06071205071202150f07090806180f060c07020105180909060604060602010b090a 86
    0xa0041440740718200d031f00040000308044c82da180ba01802c0524420030061181500840c102d10308070341b508202e04068000e0000350b00e000740001700034107190807855050741903550030710002941e02c1c4140024811144641e015006012030340760050400f404111441d40c05510820052000341d0b040030a07981510317401c0302c003640c0303540b00710642001d640000a5a10341116401e03004030100108585900d025030100d440e000003035900c6802c5143e4441152050000c600340300b00203d4a01c1c20203600070f030384030720000d050300e480d06081391148000800c10700e1450000400c00102c29082c40403111001c4101000340c400b800c582801c4840502da8580060118100070203094081180c0706d0051048100505102d400c2c0c494515201e44020041c035100301043c1c00a00414483c1200c089000c503000c0c1c0714038182000541810815001111160000f40000001c0c07401d12f800c5d01c4607956101d00e02c601c1426403000511052400d01c00b80004d5410300d40c01403096a04141022800340e84043c03190340c2c840c41d201c400107 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 567538543 1250 567537293 567537301
    0x80d050d0b040c0e120a02010c080a022401060e04060e060906060412030201023403030e1e0c010f02010b0a0e0406090209040b09010605030a020d03050c1606050c070f0e0f 75
    0x8002040d00902050b4001e140070040d921150700b1200281c01c1400403035900070544900e114440e280c43d00e0310300c0240002d15050410f0002070b0550045c2101c5c060701e104623051138107055040d400c409000d048650039920340388010000a50712500355200213000380d4061220519111008081d400007804440c440c10940b800118580c070395000b510000c000300301c0b0f0b01c41041068280a07000b9807141c05038805c450359649074034040040100c03845012140d1800c074805001450348003200107101111280966004190240803000c103403002400440c2c86400140544220500c005840800f49030800000d59040185002d41c1c0d6499810141c121411007107000c1c0180d80da40341400041c01e1511000b54040c4480d010b010074024801d8849106401440082000c10b0716501015030342c245a0f14025445403601802c00000b030f104001a020380150002240d00604d106c00e00201c0c007c4880e0010000900045100740011204005170702c01444184648044c41307082191010fa00b0070010104140c0c801001c01207 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 567539793 1250 567538543 567538567
    0x24020703031d040b06030c1206041a12030903070b030f0a0515010c03210b0a0605040e040303180b07051c0204081506030a0b0a091203140a11040e180d09080d05 70
    0x4104c0c4000070186680c038901031414503090f07045440030060000b10b03440040c4450a0920600004d4020209100300403000038040140d109140c540586060100303010b02200da407030030022400038000316840e2945070b1800765801c1d0b410641c010712110019080000340700e40081c2054540f070190000b841c10007200c074000e040550b14858115514680103010360440441c00005900412860344121084140c0340d40d200800c4038a40540c1c0108903400c2c00c0c01c030101e80042c1c0268003110564202040c149141c00454441c0e08152a08541c14070100b200066045482500024090781880c5801030440c1018207005259070303181002e4405500075000030010032000c0c0da02304441450385c1d600081c4402d240c6400d0801d07201600c480c040460f07510b020b195544586a0090084203100c010054440902c1e503a0408500007800c20a001065941c0c1c0030440801c081240f03652207803048603d0000e40382c0b500740554441e0300d0a152140c08004203c21214180126030f000305003812408482d00c3c1454072003d480281d = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 567541043 1250 567539793 567539801
    0x50405150a05010e03160f050a0503060415020315030d0201320604020d110706020d1a0607110a2c060306070207140604050418030906050f1e0c0724020703031d04 71
    0x20340d1b400b003c1d4034080010580c854030307030700d6017070354801d442908009544d00d050555506040d44c00814548074041008a555200d03405140c2c040c0e12400a140034821180120b401c0804144030070b801070f512190002c10302403034aa83c8080c8100d480301d40800c540d82e018100484840040c2c44903108540000c0c0510440b0f8443e08042190040016403682d12541d91030850300940c0180d604611080c2041c0ca10b4003ca950110404c0880c1030240009241405607507460b6001900b0312200c51b071101603010046180f4400103140b2809000ca200c00c0b02d0400340d220141486407500a080e648039912542c20003803a5503010540c24111540851901d035180e0303a50001038103900a603042150414a0300c00d4803944100b80c50b03d841140c0b4001e07120f0710328158980004a4041c0306030421000480410030081c00854407002c0611305038030150340c5036410140d4401c2c1c114107080c060351001224144403080d04001c5d04d4410b483c00000c0d00580000d044061841c0da0152a8042c41300030711034540c0c030494a10f00c041e152504 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 567542293 1250 567541043 567541063
    0x1d06130303020913061d010905011211031005070c020a0e041101230a0309060b0904080406050c0109020409080406020d050a080a0b011e05220f030809130e0304050405150a05010e03 79
    0x2005d010094860a450104a0810f5003580c02802c810300001170a902c58407a4505880c4c50a5410201c041725880321500314240002e80c1d03825104408100407460a01d1141600801d42580c90803018031107030042211070a03280d0454822600d86500b072100045076042c01c0c0761040405e08040161141800916440c1c1c0080403452034088000150070410941c10741c02142d0803803050400704032030003250b42481045a8200d800400c1000104010301c07170700d030150015210b2103804100110381403c0d06d50229054541e10030080b1020390011500f0f21103a0b8052200d002030031541c1ca441c50412004d507000030031804000c0c2c6141410396642500c1841c03130340305030a0f542082cac0100703103400c40301e55808900424a41c42004101340b0301c0a280c01c0c8110070300245070001c045608074560b290485086407507041c0d00d40d100d00401a44402000811440300c2514040c06815039612005140c45500e480f051205440e0010802d60001c0c00c5c0248041d0340759208140c0400342c034400e203052090b01c03840d030001c64a00f0340700e14 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 567543543 1250 567542293 567542329
    0x4090f05011a1e0d0204020c01110c0c1c0308011206020712110f0c0d0605070c02100206010e010b0301080a030f02030c0316151407030b0105120108011d061303030209 73
    0x14081c40c00c0465001c1000035550400d0300c03c1200500003e414070714800c11241610f6001040038840009880d0980140444032040c03000003ca00900e8100b5041551046503542e407142c00c00782c0e00450514228980381c0310320200113690440314401d03540090081c00140124a12201c40c1180c4d40103100f51035068507052079022524030038030303c412103016200103448401400c5901c51264840c4420401089103066084046d040b8008100181d4410300070b4200100050108480703200300ca0054dd07902d0660001011054000d003441d035041c501655802c0c2d00503000b848510b6010070040106220005996208640500d814007030103142c0701c022429481141e0b001c141d0351001044520b20503000e060403050291103009580724440b40000c0750030544403070014003e00780c81c041d00092045402074100e040015014940f89181c8020004903e60301a42a040b20340e0980d074501d903c0d5411400d03050040c02040d45403000304803924004406981e40b4884200050426401141c85842a101d06101c802079038080 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 567544793 1250 567543543 567543551
    0x11719141f0506040c030b13050a0e0a0b07020f0a02280f080c0f0f01080403260f0711011b0c0f0b04080a08070c210c060608010605040c0e0f04090f0501 67
    0x41448003020b08029601a44074920380080d4440c054000d12a0b910002c10144c81700d9101008901c100009120003451001d400d82c440344c4444100c3c00034444407483da03100340841030540c14000d81c004d1030b1440f120581581d9038440d2130f0325400750b59001d07400c22104015504006084440c503168000492165119201c482a44031000c42c1240c00401c1c0901400411380c1c4040700d40d0000020080c50404042100740412104404200840c0c41020b00d1320b0f51142c411064480036124045000c0441d004445400c8000d860340c0601102640c410010341c401100384000740402241d0002c200413041554040c8014002d5506244003080304c1e051081d15866000690000d07246480e040c14480781c2d2110000b000021100c03000103509034003503051119a16001100d4002c2408130120b00c50b220a00ba540714030600108c038514070006001e50241c0c034007403c0b1074000410b07401e1401050005503841a5134400a1000c0444c001c0482e840e4a003e030006507070112004207514101d41000c0018440c1d40720050482d50030 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 567546043 1250 567544793 567544843
    0x1303110703060f0b0607020a15021906060501030b06070213020a021006090c02160806070302030a0e06130212070e0a02180d03020303010608060a0305030a0309080409060e01171914 79
    0x7103640f040300c2c6402030001c284910014101005405d1060204c0298000b03e0600140025450205010860a0709004403010a86c60444180088025600841d0f180307031145c0f4140200d503803500800b50154819109241072103000e5000402d00303500040c100750516400315408200d1403080003116452014404100a000d8403100203001410b10307889142e00ad840b541680000c0c8050181c0c2d50000c4400900180a898440e07010840c0658805030a003e09a9210190300d14008002e000e4180148402c40788010044518414040020106601381000750001c580c10030503100808402d40d4008151140141e40d54a188807400145c20342c2c0b104280c011001844060805800000440c141d51040d12811281c1d5907103001c025802d1101c6c0001000c131341080c484101100e020742c103d101c00030f124514031030909484401c000704039015640000d1408420000410094071801e508844c804403200103001028140c056907181040031600040203460044a4140c9070142803010a80113900d100c610281202 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 567547293 1250 567546043 567546053
    0xa1d0415080703050c01020a02010923040e0a0203010f0203070507020418170a0801050d020d0807060e030c0109031205040b04030c0c0801020a090602240c090609150a1709061303110703 81
    0x40b2408111101c0c405c0101d194090740c000600d407403074164140e4400200600f40010900405410741c0b00c025130415008100318a40d8a500540c544034188000038003160f8424010075003512485403903c1003451041080c060320941c000c046400c0140c06031404152840500d01e404049200c088001d400303e4401809012003c204100034614000182d41e22010741c0d80b9641005001020000c0c000e50085504004c00c0003c2e1180727018150b90790240138001404140a10b07030314219801030740070302e18603555000354408141d000210312400111b6140100441e1030a0341d01e500030410b01030806002e0002140041d000c009980e240400506610320096464075002c501c0039104911034001c3c00094003400042100b20001d160320030660806514040103e034941c0c18a1149a912074202d141d00088204400700150b1254801481c2010003501c40710360ba03400c10f2100400d00c2c1c030340000c030750310201996043c007024290000e85c1e41d800408040c10813000341101c1c602a508807401400c80301660081c1c0b80c0000c1849 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 567548543 1250 567547293 567547303
    0x30e0f1309081e0906040e15120c0301061a070212030c070e18060907050402091504080a0b0f040b160306120c1e0f1e18020309070603020a1d041508 65
    0x5100304046510701a6540b5001d9100c405411080030306c001c102102c1c000102640048400c0c584060060380c41d40030800c070002d04011200f9941c4109415201414240305080041451202c1b02007942429450900240302c0d00101a11405084e0340705080041c0920031101c4004001c1d00700ca05840e80d03511405807504044815a840d0542c013409980720307032008034003144034481c3d40e40030708490740c18002000002c0d0052606560401c0321004010700f00c4400c00700030406004400010401500949805c40044a0042480101006640c240000522210079654001544d204220b03002e4426030300460003445650300041c0c1d641104c138050010b020b8064255419509060b81c0c01e0095001d030801000090594464200d00c21070f00e203404c00c46440083c80307c04606182858400300c503659640c14174500b0540c00701103446142c0c004107001401d030080103084003c119030f0905608002d00940050076003602c00d4154070390300c3e0150b001c203020b07580e840e80302c00450300e4150000e10480751991b07030740d507030f40c0c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 567549793 1250 567548543 567548557
    0xc0909090c031b060d090318080f06010501021f090f06050708150406050f010c0c1508150109030b040311011b05180411030612010f09081c0603030e0f130908 69
    0xa00a0010b11618001446207940780c0f0303007010700701a05d06540c240d40700703000707040c441c40583c10810310200d161401d402080b81c2d0401000e507100181240d4580700141400c00c401a403045040d9409442c070314035495009200d4200012030b00b0340c00114005182410482e030010142e000b0155407800b0704101d8101d4000310350a0007034084070a03c10280c921078046c0801c84103c0d026651f8401d0300084185580e41c8a00364011a0038410312041c0385207a034540000c801c11008018820200c1d00400401c07020012021203460140b00c24600714010700e282d41c0f034500348414082e1010b07040094200b200708003003100b500100030084245403a01b40384402d1000050894105c031010150105241c64100b030545014024a5822800558160b01d140c48000030011110040c942440e00c1e9501e451074590042c074a8402c40c030510b0f005500745035454500703400800d0807802181082d03030a0343c9001014404130f940103041d03c000980948410394642d002000151384d490180e01c5c5079942c1800c0548620070424003201400075 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 567551043 1250 567549793 567549799
    0xe09152208072009060d1a0708060112050712020a022b030f05041502032e050a060201050f0408090f0a0f0906060207060512040c0b13030c0902090303120c0909090c 72
    0x34070543e03480b1032042159515040c603440000c2a000c59820724144c2c0c07030104100e1144141c03858070b581c500301e03204072442c0403104031021810b414208085940c2002c900c1c01070410604c81000303186407102c0c014048818002c42d00d010240d020a2900815000300024017170304081d00c0003003030790100c540303005140c030340d140204c050001f03007000140c2c1851032041c0541030003140e03c10350b800b60f0407210941c040c000750001031004440418101100c1c041c0842d003e0f20b404039004801e58a8074003400d1406000040f070321940900110f82c981810400c102e02d2411019400c01d60002c03d02e07a80720300c0040000d40740b05185500640c03148040c50000f0304103034040108030071500088010310a084d030341c031400e0761030344820b100320400300300100158040c4081c01c810042d48a4807038004160090b896801c103004940010030b09120340804c0f40e0342842440b65001c1c001c0014640c210007589002c030500d010a803a4090b080c3d071010120b24280100c2d925040a800f81c44005402525101c0d1910740346078016030b580180140140 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 567552293 1250 567551043 567551063
    0x1090b0c0d20060103060c05090a06032c2119080103060e0c0310110f070f0c05040b06040e100e0408070c05010504030f0b0603070806070e03070e0915220807 69
    0x35680c2d440d001d5030400c4081d207070140490340c2c0307113845441c0903000c0c1c220720300d003000001c00010100e6602e0307003a84000f4041a03500051081c0440030b10340c000d25522041800420719000401e41500000103c1106240040401c0b1000421000549204d07001d00c9140003045501d40c4c8807448581ea0004409040f40d024200501000d00110f1404c0e45a040c1d000302d040d0150060400c0400310111a0080c030b2410790a42641031600c0c1c0c0c0d40011050a8110b075004072140d42a030300b0124240135031680360340301030301045400f000440220300002d560383c8100e00c584460f1208880008103c0d40c24980b41000414030041c4851440c60b00e440e000340f8079442440212643d80d04900c003c1843e51244040d502540d621101034021040b03507031502070b00c1031001001c41e03905205076200812000342c01d00c0003c1c080c80c02d94540d05004104c0c1e03400c041c20192540c0141c424080d43c0404c10800c480d0000701000386c04103440c1020b030540c032905101f10202070200c1101d40502a5095000c0800c000c07403004000c0c260249031012 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 567553543 1250 567552293 567552317
    0x30b0f090703140c03040503030606071a0114041b08190b030d020a030906030e0a080706180b060301110304080f1e12070908061006081306060e0702010b0315010e0601090b0c0d 77
    0x4083d400701b0384000d00713039500910006505041c0301e0000c081280c09024442c406200110403140c41c800243c001050740b01000800c80507a0909000351140601c00d10b54400c822040b80030001c00c0800024032000c840340b00504185c520820a034400407800b207000e42581c41210800a01945c1c40044210031070004852200000e0500d05c61b02c40c405558030071001410030b030602d81e241c16030765401c42102a111203645003560083c1e1030138000c038540c3c4603106400f055a507203420001c050868501811021049800300f04200c0000d184204550384040110442600c408140719540101c003803264400c032880800040d0080c1c3c88a50014a40c41260a9610f81a006880340d810703644800050390041800100d04005002890181041e15800548a1031705a80d104c0c40362114400e8514944c007185500040c035003400082507082c000e8052070034090340100140e50040b00c0d490082e420512400030146c0c05000410f212f680308100840003400f003142601e850b201c60344861a114001010380001041032641c000c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 567554793 1250 567553543 567553561
    0x110408070509370e060a0b030705150d1d060903091c030509090411060f0403050d020a0b1506040512100b01081b09040e1e0c0a0f06030b0f09070314 65
    0x280f40411004160700c0300311203283c00140400346100b8007404806882d10b82c960701c00142041210b100b080780700008501d03890720006040c1050002e4102c3d070b001d8801000c003110000c070500c084550540302d54000082c0c0620011350441240c1417440400d50718050380080c0600b200001000c0c1406040032a04462030300e068a8400385059003150f8018042071050110707006500d4000c449d130b50700c075000cac444043c420f001e100d00082188c0e000001900c410880401c0038000c0c09410400d0410ba820a80020309280e0403907250300f40c280d00010002c182056440312040c40d00d444120a881c0207000203003450b084421a00507039625000802c0703204d9812454840e00207129071007440c0c0313a4050390b0000c0c640030458000c0c00700201e40d43d1001c40b407140c00503280e5400044400c0c04000d5030f05031050200144400041540506080c8148000d40c148128402a414440312026840103000c6501c00d0a000550517505008075080f2282d1042d10b5a201c00c89800704405160140c1043c40e20300216145018250b591000d8 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 567556043 1250 567554793 567554821
    0x1b0206010e24010503070c02190306110f091203041e0311031b010e0a0e1305072304050603150903030709051f0e0d0f0c15050703020c01080703110408070509 69
    0xa03180d003007810b050001001c1e50140d4000c5030414802d1a0000d5880215004203010142e05d51100c0000c0e00145001c1040c803942c2d11528084114440c41b181c42c03c036032000d000a00b4020050f045114101c000c2c20203001c0c4000f0000c5030300408030b1309803200148050081c44106c580c40d41c40140c2c1d42191011301c2c0030702031401040c681005031402c1c00081c0c551481c8070044640c00902d240d060f4020400c44030104030300d4203014001d0301c51140c10048400c1c1710290b140040c20300c0b010b50310005070f0640070846404512007880040d03a01d8001a207000400744c0c0d4480009141100905041c44040e040301c0600c604000c01000070b43c8038044a88400b140c0303554030014000a01c405104140070b080100280401076031140714a0320000000500c0c40b13601c540300d51103003082c810f00b0f800c0854800024201c20048010301069211741d8054504280307042140e15200a5120007868100c14100201840002c40700c5002c0d0f031011200311000d00881d5250703900c92a016641340c40d1402018402c40c06240010401401041 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 567557293 1250 567556043 567556081
    0x2090306070e030a02031c03150f0b0a200d0801081603120e12010b03011b020a032d1101061e09020304050c0d03020a110604060e060d1b0206010e 64
    0x2008000da5521020100c0300c159a80c0041581401510480d90150307804002420310041c2c0d04103d41404280000040c0c225581c01c04071103612170105504200d0980410800340460700001c641564540d04280100c821007041c008000d40c3d200d00e040c402c85c001d038001034040703140c0e146525800300c6640c03581025607640480d02c182c05600e0707441440900000c2c0028041000a641c14104400000132101c001038504410302c004c42d8607690750380d080ca4160700e0300f4010300e08020303c101c10b60b56012100001c025210005c402015081c050105030940e1140398540000031401c0000142e50308600c8e0060005106540d007000c03c3ca00c0e0340c200a408504800c0b41e061144003c9215400390014500e0005850081d41004009451f04d0248140c42807050300da0723400d241c2e8010301c680d016007083d4040385002e49040c1c00307444101e030150005200c1440100d4016a0054040008841807501c580e0301e002c0740c001030074851526000440e421038600601580010320079046c0e8000c0f205081c1c1c82e540c0c8060314150040010 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 567558543 1250 567557293 567557299
    0x30610180311030a0215030a0606030603080f070f0b0a0f061a1c0902060f1b06101a0903010e0705011d030a06050705070b0f0a1104030507050f060c10020307030b0102010209 76
    0xc03808100003000d40160124100c806020b48008480a400182c20f82c058840c5caa005014000b04106801a903449240044d010314103040041d44e0858803500030500a5900060303c4000010301c810501c4031000400f6100340d0b00c241012854501071600d0006450000280e642107801c2c50b4000c42c81c81103c2d81c0c1c502841510701401c03410724100382d100e0f8240c0d10010040e83d00d2070750354020440168a07004020144c10707100030301480c1d4541c42e80c40b482d1400c03103a0207884052508100706101c0041d001c4060303c400c5440d07242c3e5024086401c03102ca03402520440003029815031a000d804c03050300d600031603c0e004954090702c130105141111a1080c00000d060341c902945034120303013480000a95281d20041d04400c0354904103003418529a94078681c810f00303803650840342c1c5040c020000782051030b02072048030820b120765040c02c207840c656810359540c24038020716110364604441c5c42d80340e403140000e503208981050215a1004446183c0038020362042d907850001908062421400f94014005caa01060000d = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 567559793 1250 567558543 567558587
    0x2030607030203190e0a0b0108010c0801140a05131a030d0507061a1003060510050f03130503161101120c020c1005130303020303190605090c0708070b0c030610 70
    0x8184214000d5000a05080030150004007040484d4014800c101e01c0d0852140108005041820074110240059000c1900c503030408491660171944000b03001c1c1114019a07a09005039110703000542ca0082d1070b000741d80c003d007285010f16440c49981d0404801ca8001ca811901c440a030360b8107240e280c841c0001c4007000304004115020004855500c074528002103603c40b80121181900054050010081290002901c65409001d00c0c40c0c1032003840c03528240c604103d85400c00e9803100c8842d0740802842401d00311000500c2005200c800e0007113030a84080a8280d411004052811111220b038002d502800034443c00d100c8000d0800c64401c000b40c0b04507130340090910012480c10031035030a041e14003610030030000b4020807d10410a03900d17000998800d4000e07540ba03280c0000020b4500c69034603444461641091b208012070f03220041d03c50f4001038115030362139a40c041801c2aa0342d40c0302d0010002c058981780020099039011010145008050440764a0507018601700111000002d03003080c0f072000030710 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 567561043 1250 567559793 567559801
    0x150e1f0e0702100b0310090615060e211507110c06090d021e0409120f2d020a170901024806030114040e0a0302071509081006180510091a0307030503190903020306 71
    0x2c07000c080d60f03422018021374054124025105194413801d545040100301c00c810101da40c140284880111240c094070b400782040350010018800059403203020340124002885011000c80e0b42c100882200c0003e402031001e0500c0b8601602000c40c064070203400a0034200408010740d1280ca0844100c8100745041d910310711020700d224801151842c24001503106d5204588006a003040c2070b81c46604c010040f8948403800c050019007050a21250781c0c4081510a5a241c20103401501201000182034410700c851810800d40c480f01400c076075070040c0e0044012000088881340040700d404055010f40d8184000f40500c1b80043da114005c440040250f04034003400c1c411440c000e5815481c021092510f400003d40d1460601d0070040315035221030f01789451702028420a0b050301c844010344100210100554940400841d50b88003040c050304282503103440c0542c055120700ea5a415001d00010b090b03c02c1e2a40e00d02d040d59403581f21903a03480000e1403025a81510034020104242180c0c1c01501500244d40c0b = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 567562293 1250 567561043 567561079
    0x302060d11071505090d26071b110a0608090c12010b04020c1b0603100b07082101060306140a09150e1f0e0702100b0310090615060e 58
    0x8501c1007000c210780310602070b5001154110344402848078421100040600709915000e0a007200c5112803010f22103401040107a4140c84100c048065032008010030b07140d16a5001243d0040e00c0800481e00c0419100c4080140b190140170b03d216100304680300750005070390b503170140c40d501070848124519811112500d850760410300c4103050000700a0000044051200f00001d0890b004185000c14a0340710100f6101d0002c1030307040c0140c0e90b20040343c4040c11403520703071301e4102014014001d0787c124600215a007001c0110450540b444989140040104001c0d90841610303e00741c00d119040009e410308900040034800c06002c070b03224102c050418642c03581060340f43c001500460a0701420040d40d01c000081d45840160050b02460719240280c1c107540d4941901130725540541c005000c144006400c0c48003460b0002107080c0c40d20341134100460803170a02e0340041e04101c03090800700d40c29030400c0c40e0030b0100015a070024411044100c0b0b41c140f00e81d10784504959400d031107a1709540065440408100c006 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 567563543 1250 567562293 567562301
    0x170118021c030513030501020706050105091603110d0c0503100b160b18010e0703110402030f0708040f0b0703020a17040c05060d022503080604150b0a03060b040b040e09070302060d 79
    0x14040d0410515209207516101c41ea10b071356500949187c3d60100c1e40c0701c00c1000600415004007000c491141083c10600c0c0090b4400000c2c1c0c4102080c9595400074000d4050200191240c61040c500d0421100000303a5010301145d20865104580c1d4100080c08291020a030040c2c0b05410b040800084c400e030b1030383c1d0341c4800f0040c000d031059030100c0d0840c00c90701c501e001c00d0003107010141e400f00c083e0050524520344000d032582ca031681c50b4400d03401070040044803204908507039404061450100700701c0c1c445050a4403000301510700608070300340480c20046065007640044c000780a00d40d403407600e41400b0300580036400006403001810503400074420011454108058a00442e0340f05006140c81e04200340b00c1a5011088002d200107103129001c0c409145d002040c0035407005040e5014440c2550030b070b80e0590340c0d9449004a06105a0110304462094801d5104401522040c3d50715a43d5580341e00c05010290003c0c8184aa137000d80c00000b29080030224403001201c0d03003e4844d40c2000418103050000d0 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 567564793 1250 567563543 567563599
    0x140901030603020a0b1c18030507020103240f0b040e011401020304090903210b150a051b301c090b070306030c080a03170a110417011802 60
    0x1601d800000c80903a42e18216a4002e008a11042c0d55841003c0c0c4055000445443c00b40e0a4a2804501070341e06c18410501090039a4586000c81e074403030301c5200507402450088100045003020101d0a13540400c00c280b2101559820361048070301c199141400c50719072113103000b107000206041004121b285144046544118030500542e030a06441d08908403c96644800650024032030309000c440c10844003d00b43c04200e0498070502514400d5000324422507a0b09464220001001650f400c80c0c51146042e599004003090044509410400761255103441c84000300741c0058050805042c2040c0001c0d50102174407810020900380090500081c031242583c00e03010140076100c280d00000289100c0d1b03510b216140646000601b14118100106100025081107a945e4004400300010030b401851103801040e1588143c0c3c25569a041200e01a0904490268090310b001c84d0204d00350a0802d00c0c00c540240c168020003401407007140320b42d07540e9098400039400900c0c410001d5141c45000d0a16949 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 567566043 1250 567564793 567564797
    0xc041a09180a0614060d020f0f0f03010207151512080d0f021911160311150f1902010c09030b0406060e19060506120f04060f05070509040e0d140901 65
    0x1c45210680c100e8200000c5000c1115400d5884601c1c0748002c424a400c150004010744200040b85403e5001c110480d6042660030b22501040816002c0350fa070b00034010f035060308058025903d910003440c0074511900010854030b1054200316002092602003d0620100c4802c040354002a840c181c0315a4899444079a880d80e82d00e0701d42500000513201c4e80014040c0440c8096004c0140944490082800340d40058001d06d13504a101c1481c0e49031840b505907410f0300e802011300300074501c01200159403010342a8004035070030000303d01e008600d0020805000c9455483c0409024503090080427422a131000c5501c0c40400ca20b01b0003400452500800303158440c4c0b05100c0080d001d40c480303d0440c401c420440701941080c0c8080b03000390f0101c0250103031600030001a10b469082c02c00f24514080444c00c0104500b04004800c80014140041d682000c42000450071040082d8201148001d000e6441b000055005d541801d250001142c40000c000070404499034482e02200d05c261680c044942c820442541 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 567567293 1250 567566043 567566071
    0x506031e130201080906010b09040f020c01090c03031b021305041401050f010f140a030602160804030b06120a0b0420090f04060c0c080a05090a091503050c041a09 71
    0x649100035030205030080c5948011411a024180b00040038054000e02ca00c42d10b4215900401900c0e2003402500d910755800ca0f1b0100f0240103d140107002070051040704a215070078290448103001c256a07444066a01913504c3c0b442e01c0c000f12500740709107801118000e4208010340380d180c03a032007400e9000e00c0c1c105101c0c903001202c401561b008107003035800994035009403000c40801080030041c0c8020406c001d00e1301c804100404003590001a00180ba90710000c0c1220f0b4000815010b1070703515184580700307507601003106900c3d103032641012400c800c0102c03201c170300402e00f40e10329440c4d150380060080c002c83e91041252a09640d142d41d100c01c12220740c1c004200c0f0f030740c80301d0b03102100355580700341c191080d21007410700d80030fa1600303040240581d01d00060540902c100001500e020900c90743c1250410f2032941072039a910004039010488400c2c580d406036000d14a001c6c140101d08208048080403a8050300445034032a424800704021110200302404005600e285074003000e04209600a40c085600c0c80085 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 567568543 1250 567567293 567567331
    0x1e060106121b0e130612110a0e011202151213020604051002060a1410290705030a09090b1c061404080a021605060a18030c0909111504050603 62
    0x115030311000c0040781010075601c0a4214060030500b14280070880b0030402841090300e043d5405c8105024001b0240c03002450100b41c01c002e450711881c0000400354030302001c040d9a900d02009030f590044020480c030546011035412007030249a0143c0744400c02183d103070411512515072000c107600c08000704a8200343c091000049990b10200042205c0c2d1454025090358601044448104c810080c2e00b90048001e070300074484c00b1009440d01505030755035194408803605c03040d42c040d4010b2007440086221480c00040d07a03004c000001c00500304c44800c9845880c0c0c1c0c1600c81c6009000d50725202e12081c0c02c070202a108088031680907401103400d40c000c0c0000640084202c601072011407040354150344019000800f002c04940c108403282d00e0f45000c8000d60b00a6041c100028074600c203083c0c8034010099442c4402e0580c01501c2c2c0007000940c0c1c041c08101e0540d555500000c041c10402c80c050b10b40c081c1e94151900d1504200000c0c00400c03501540862415040504120f96600060710009d10f4102d110307506 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 567569793 1250 567568543 567568571
    0x21020a06021b0406141302040f0f0314070b2d0403030306081b0105030f07031d010606090f050d1b0b0f030a0b010201021c0c1b06020307021e06010612 66
    0x8101401469000e0011100007841440662190356001d5001e50f16000d010441085040c8414529540072114078405000c01c000d10000b0740156000000290140c0900080004801140c50110783c89101040380b0b03209030b00354050b1510300da489080da100300d04200181d12400017580004c40341c1d01c02c007960000421709002e0060180c0060304103c0200303030b40348000c2c0300f265020400701c54a05640d0000742030440d01800000c1c450300000e860200c441c802040800d20540c06a00507202c040803c1e140c0c50220303038034003241c0d41c0038000c82d20400b0042a110100404d420903550001030664501410010592a081d501d140035078005451402c0603411106000c5070007881540244040e8100d000d41a44074101a60000100d034986804181075a104200402246d400f1354040f1680c2d10fa0f00a000400c0341c0e92500558007401c0100410503c000311141904c00c21440798044c60061600d81d0881d412001e804007403401c1c500800c18102d003a40e12803001084071a00c10810445510305c80040401e401c0407115807 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 567571043 1250 567569793 567569809
    0x40314040b190e06070c0303030906020c010504061a01021615030605030a03050d0c080f1305010b030d08010905010e010b1b0a0804060c060b04110702010c0f300c03092102 75
    0x118140d099400070b120b080e140d9001e200186441411100d90380b400e0103650703400c0c403605580c6c40000d0a05071520721540038402d01d98183c4070022240b000900992615260604c014960b0a4400e01c03015004078140c0c3c802c2d480041d45584140403105044240e908000c2808604142d01d441442095280c11000c079640e1024011ba11803188130b5180d550312554414015020742e0a042c1000040024003410090022410582140c2100d1a601250301a003500c1c1041e5001d40b095981d095058402d03210081c01007a8440f18a6040f182405000c11040c0d0302d840c0e200000e4202032080c506007903c113014038507820f8900e00310100c2051002c0300302c413a82c56250342c07800b045030042e034000303804104604682800e2110a01071403084080c2114108484245000084858014200c01a040040195908003000f840c141e4201295800280b0320740160011414100941c03041486a100c101c3d442d18a98021801107180003d86035140d00c1d0006001e06241c004030030b0719500c048850f0540c651141c8440540c417030400c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 567572293 1250 567571043 567571057
    0x30c1308071d070504093605010b0d030503070f091802071203050412050a053903070b010608060d02131a010e06120606120c0414010512040314040b 65
    0x80c0c5081850600c84050b540680b020034001d50801d04100192203510500f00e5055556105000544141e5801c1004102c1c039400510010103030314040d9480341c910f284174804a030300d02c600d00902c603049403401400300403001c040c00100403c405201081e542070051035081d640c400c0910340032100943e40c4140b0900f92069101d41d90308164000345034414060510307806e01019466041c24091402d042d603600c2c61a820100e020001c2000105411030024490000c50f10f0401c0c290f96510074495070019054805080c1d030507200348003d2200c04001d003200c8040140c81c20306400070040352440c0e2030200c066900040080505908c40201d00e0403c005030340343d0b00b21002803001c20f4030005e42c0c400580c104810901c0f41002050510a030080d094141da0b552100701c0b901c2c59601d85441d90a520f5050210307419000e0b5405c40d451849a4100b00140c47c3c0503c00030b08100c481c02c524041c3c800ca4581e0040d03415100322540c1c0c80e420030010340050040b85c0111b201c585946410b0304500d10301695244040340540001e0 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 567573543 1250 567572293 567572309
    0x110f070314070506042319080d020d06030813080d0804150e06040b010323060406150f1211180a0c0e0a0f15050408190201031107060b13110d02030c13 66
    0x745600e04a01c946c40c41e4492081d4220007032040c4d405061890000c03880520004015a40005040300024804d40644841000c001411f12100b9103030303c1d140742941c0100303002c02e42c2003030003400004220b0400915803190710040c1e01d82a1440e04c40d502d40e4107000c800d00800b1903003961100c0100c0b0211008100d01440340303010300801400c6505610788010f8440c594418581d104d82c010140f1020808046000c0b5001503115500080500617031142c082405059444240306480c00580000c00c094201078800801d03106160741c407006240942044040b10304021084450038018000600c1d0880e0743d88405160710050400310401880040042e2010000780c10840d00c504400e0801c10298030080721101008149051aa0915003460341580e92030002600400455000400321003e59000b80d1001e4880440c1c2010381d03070348000a0800c040a0b202d510b4001c0e004801411003011031900030b110380c500c88078802820720f2810403240c0760100a90000b070213400c024901008030320b5448040034041e6000388004 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 567574793 1250 567573543 567573563
    0xb041103130c090606140310080a0f110616200603100302030624090c12180607170115031b02010509060906060d081b070f09110f07031407050604 64
    0x82e2400380c007001403550001154904090341030050765040000002c1c1498034035056034603035458440c86039817882c0551000089010b101d03562000c0c0701d00c061170300c0300c5a030040f000003282503e12410711540e84902001e00031005988541c440010f580b60314580c40000d1601c00090081c030340440020303802c0d8400d0320250038100c0c040004008506060116a0380070f90111580c4e4a8040705403145025030384140c41013449013400c40c0000701003219006c02c0d0b40701c0000e21342c85040e180c94008000d11036218034064998061081a000070038051207900450f42c034104204200c0b1007a4030b08040c80c100b0300c45410881c0145034031094480350540305403043e48460050307503001280ca410455804d80c1007074070180401503160410350401c1455101c0c030030401402940700b45841c0e40e510091802e5007444051241303809450017580c1c00040c0c16410800c045042d82c0c80c011003007180504906400025108825050340700f1082803084c0400320307004d100700d5181480a0700d40d05150051590310700742414001c440c2200e04e2400c3d = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 567576043 1250 567574793 567574831
    0xe010507031509020f040506131d0604110702010f03050c0904112a19020f030a1b050103022d04031401091110020a020d06060521060705030115030b041103 68
    0x14110040043c42c41c00401c61a203007680072000c00e50310560140c0c502510000800b00c060080060b403243c018050303000c8210844c50035604008460b00141e0b1158403490402d030030700d190062201c04035110190f058640324103241c41a03a098001e060000c0120041700828880340000751164092380010580d08620b0b19076031300781348008041c0300e03980705d0381104225004c2c03c001e91500c0002a00d04503070008011440050402c510001d900a01422a03442e050b00502c80c0e014100007184190b007040c2c083e00389180c0e000b079071510300460807401040390031000391020303140040007800f2540c0d2030714500c1c2c040301d480f524060700c0b81c035415070304c56100c103240a4984d9201241000c3c0200b400300090300c000200c0b0b40c404c148603200300c004d40e11000382201070700c40d81050080070700708212b41d400000245000380200c554100e500c503113a404103000c141c0b080704c140548000101d03114450400c0741c4c1a00c0c0050645807201c0c1101c4403c8004120480c0540e800c50b585100b09050340d041c00020794444e04940c2d8040c00f02c911 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 567577293 1250 567576043 567576071
    0x709051008030301080304030f0c120605060f060a0516081e0307020607020705010804080a0908010e1e210f0409020d1a040605031207020d0b04110a080f0c060d0e01050703 75
    0x141d0000040d41c0007440148404800442101c0440384c100e004d00600380c8032410100307510001544000c1050200320400000c2105941203d03108241c00c0352495084c280400902049100da42e5850340040c00400103001c2ca40c540c01d24070380015010703003246400c000402c0f1901035150945075680701c0e1014084200201179604001256019540b8409030a03d50315243c0040e010150191000344000004250051220300c40d8409100070040680240040846942d005455000b004007084200740c0780e6a9102c0f40000003e00100c1e00030601c0002e0b41c1600220380d86003055086540001c00d42c02c402c10000850b0a007900140000c007444001c0000d4411410207c55883d0070f10710202030160307043c00005c02c810341c0c2c0829500c0200d10060401640e90000344000307800c0800007200201101992801d11051045510464020b07445c1a180340207060b4859194036907496221303401e0803050f440300c88410894201003001d00442510807001143c0c041d0014803003801c0d0360301102c0040001c0d95a8900304080c40d = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 567578543 1250 567577293 567577321
    0x1707080318032407030203060f030d030b0a0f050907110a0b090c0f100e12010902040f02181203300f0a24050d050c0607030504031b14040b0f03070905 66
    0x100300314180500c0c3c8240302803420006400410103000d06601200142058440d4a903e03002c1400041c19510412100320700603005041e4403240c4c6001d80d040c05e101182c412600103481c3c0582d9002050024290b50721b03d81103c41c413000a5070300280340640c18a4100003a058911503000f00580805800d4070040c050501142508124005102d281c00c807150001036030b04a42c12180d210707400d2723841c00c0901d082c40580e18054005944000c2d001880d01c0300c40c4045d1071081d8084d0100b1550305042c1c40c54542084104004910040240c04294208004000304028600c044400d2207200f40003002000141c072128410301c80c4101c90364440f2a02c000c0c00c001c542840d42c811816100c0c00b40f04013100e0710100303500305906400d650041501940b0388039580d0040c080c082148201e0301c0401402156078100c076140007000340d00039100c1156030404025240c0e8080055411046c00d44103410190031031040d01004002c0a40404020590410040c089084450320280640c40103070000c2d10000c1640d040600f40c0d20025 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 567579793 1250 567578543 567578563
    0xf0705060106030f02160b061917100b0105030c0a1b080703140331080a09150503070806091b0d0b010e0a030209270304151101060e01170708031803 65
    0x1350380704100f03003560524002c070784000150b0000a80300c55681c400c80841c840d120100c12002220754a241c0019441c80809100300a03040c0c0002a200c0d00c1c2c03101d501c0c003c1601e019212207804585c060002804c0800804042d28152007075141c0300240b1290603840303080c01c0c0302042056640150002d035080038941c000040c2d410307580c2100b8031280341d468104405900042c0307540c1400b00e007801d520b528207120403030244641543d580103000b030365440b4803c82c00036009103a24468283d01c2005001b4400006001d101507a102e03114076242d0000e141d68030010043e990a0041002000000d9803500618030000400904019141ca802c00110f0000c8400090030216840c41c105114410500c824001612826000750300034884d0500c1040b8074628526086d48122429070044039032102160000d4600050441d8003c0114a9114500e03441655a9002d00340c42490080d05200000d1000401c003582d514840c00e170304118480c0590b95078030381702c1d40100e0460303100c04100c81514074200c0e80d1a000d4170b014020840b00d = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 567581043 1250 567579793 567579821
    0x120f03072d0509010201020705011b020709050f0a0b19060806010e030304050d020402030405070306090c030c080d080c0a05070b04080705060609160c11060304030c0c0501030c0c0206070303020f070506010603 91
    0x910075844514010610029900380c080200100710742205174000d406413003185a201d4003c0c010050011032003803a42c170308850b090740140701b02e8000203640c142c6845680e004684510420660b99260188403010b0302c0b50034080b60300208070560b42c8031540103001c91840030b0100f0350390301c0007582444000101640c1216035003034403070b0b042004200080d0381c07082c000302203ca030705407405a180e5403541001c600f09100d5510103040c160400700c6940070002100034030000d49100b51031034515503031101c86242e0b03252810421b550201d00c5880200c1c150400c0d00c0087d19082407a45400340c0703405d000717135901c0c080e000d02074400f1a84040301060320f000b0888240000c0e98480010b84000c1c4030fa02d860541c20024510510541e400d105402c09030000b80300180e140310381c044501812450b96802c080c50000d201882d4100d05039400000e644020400f584203004503850f0200d25554500ea2a03496020400c1c1580401022410b1540c2080507001140c8020041c042d4035000f5000fa00e070540c0741220180a0320811408100 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 567582293 1250 567581043 567581087
    0x41109180d0e0f060a03050106030b0f030a061503120e030d030203041a280f060915090f02090d11030c040c02030703031d0105011509050a0b0d020903121801030615140a02120f0307 79
    0x3460780300003d02c0c41c0f07940d40054000c180000302601c401d158810c1c0380c10290100076a818040c48030ba030000ac220305803800c16811079400021041080b8204c0c04241c0e40100000140d00b1800c44400f5203245140e0000e070500d4011300c0c00001c0400b400840301d0264509441d45495240391540018503104100091210079401e0180b074282e207100400080035400f80c984038681c0d40307510340307201e0020707505403a00403070040d091300384001d502d042a110340343d4034038200c2d0300c00d124001c00d090035400c15006200310303540c01d50011410880141ea0950103400322000c07022104813404401d000c04d84090046500030861207200c102400031070400240b2035811504020300500c6080030800442000342c04680d940c881108006898103ca800001c0c106014514413000304800031503018100b000340100728040341d400341c800300304c1c035039450803d0b01080c5020060b4002080c0c40940940c102c80c0a040185559011481a100c0c841c004400401c0940c03c24040703142003100110030010b071182c01030350b204030408040d41100 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 567583543 1250 567582293 567582319
    0x20c09240a03030504060807050d1a130902150d090c0b1b031e070206090d03030e010608010b031005040f05030f03010614181017041109180d0e0f060a03050106030b 72
    0x15045202d1842044104550900064905031140c2c02b03079541ea100c081c0051040c10040c101d0301c252030380c1c0c4104c02c80c0710f04000001400400003500c5410741d840c0e4080d084c80003040d8160307040c00c41a00f1842c3c00c0865551603842000000700c0c107281d000d0103886907400054941c144c00d040703d0107000980080110030381c17003000303040d101089450f907040b000400c0c06149070b031302d14551002c61098043d072411190040d03604441101055050b811080e000300d41a4003c00c41c01c0e036100310190070b13600c00300340881c0c068101800c1650f00d1191a040540d000740601201c3e0940c21a950341c042c61980110501c00040c500807006124540d405648981d10001503801c090404a03094482889955640f2400c0e10400c1c07400d0039a86403601445240c44180000c10f2503104038649401d101d20b0382d000d0071a8a41c411142440001c3e2420481700700002d40c41362001c01001c1102403060140c45155255030306582c00b0b8040c28028a5565a646c02802c82c10501d5802240c1549400c1c406010344100d84152413051190034060 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 567584793 1250 567583543 567583547
    0xc020304060c080307120e010f0f0b01081801020c0a06021309050f0f04031b05030d050f041e050705130e120a140904060807060c031701180c020c09240a0303 69
    0x182c25182e0300801425540c2c0c848120984020391080c2c07400740c40e1828181c0b0000144010b42c084a92117029940501c04041d070b21200808441c5440301c840e02003607a24001c24040c10543e20080d60404900000600e80150070340118642001c3c1d2404031070f4290001000801c1e0481c1e2210200200b91055081c02503050000700c072142e440000380003803801c10f0341c44c1c0050141441a40e1011340326001c20b035445804000c1e03081260b1070b90701036101108460300342008550000c8007181c08500c12a0048481c1038550034039604d00b181350080d040296034610407054080f92035030301d0410281403040100703030006203503030260450f03814200703061041001c054046c848914055084450401c24006281e00b460381d901d80000001e0041000c0d42150301140300b02d08002c1582d5400c8001e50f0440b42c0241c941c0e440c8400c8500e60740d0712140c801d00455500c00c84e04203c54104941c260080181810103005031907056143c44080703400300000700c0301e100022280e0a0407600603d0b203803078070041030b8506a030345050701404d40c1c1380 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 567586043 1250 567584793 567584807
    0x20304050706090e1b1602040507021005010e251103030708010311040603050303060f190617090601080d0e0402074b02122b0807051c0c1b05030703030c02030406 71
    0x2ca6482c0004250501d84202d800d04096287c0c010003c0140d81010f0134000d540b403001c155900b54a514250000c9645103460b140584110f05201a0781040c1c4a507440046642d042d412104081c00404181ca822003d8140061407103603045503207800442d072460400070290000c000707a042c0a80d142100c280046900070080f2a0301843c1070b2420404902c41740c002c41c209503a02428050a07240152000c201581e0101c0024811082060a0f403582c0c0c403108001c60301e5050a2141940c0c0f44c0c02140391409041c09907010990302c42e00140014240040b945400c40821308500030004c42d0342106009100321190f03d0b0100c5036a60089800e0368165511402207140e0310507451019200700807509035408100c2d0100102c1d0951150005508440c03102411132103a414021030031400401e80c0c031400280842d200398251640c000c8002d0443e41c2102e085443e0100410700b00e00a40200101d0f541c496020000132058a0791092081004640c0c1e20707050f003001070886811042001c21074004020811415500c906 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 567587293 1250 567586043 567586081
    0x2010c1d0d030815060409140f1009090804080610080d030c0512040204090f050a030e060f27061b0c040b0303040b030a02250201020705010201050721020706020304050706090e 77
    0x1d040c655030711903a513035841e40041ca0b142603610040004012480c074032182c0102c0701900c512940f000c15616408111202288111401c2d004003100c00810008440b05801140056004d0f40d0218901503d81d070600303051440844d400e00035400425400c1240050400c044416000d841c80c04001002030b14000401074868400100c605603c0030020400359a1243d1003020003550040032554a6101440d02a41755651071009030042620100c965009040500845038840e10280d0202d18004083e042d503156050181442c0e60092003100640d45076032a80300c0286510007424110f200c0790981d50181c2d6240170010780f81c9034016070815101c81c0c00d5803000001e5a003a1981c000d03a072601c80d1b40c0d41c4078840080c010380c440c406181160100f90540ea505400380802083d000b80d0035100648c0c1c460300160f00b43c40c07040d12030000141989003804251805400c841561514a4602611700030706600c82ea000da800c00d07030701641c4070b4024030401c200258015800b2001054a00241e02ca2440c05021209010900d00b03 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 567588543 1250 567587293 567587297
    0x609060c15060b0307080103110109030b041e050d090807050402090105040302011d0d0614130b01140d05010e030c06070e0906060304020d0c0f170c0a050f03070e0702010c1d0d03 78
    0x201a00203880d540b60000c101600780f07415010380740d01d0074000092840e00284010390720f044017403030603100c0780d4410640a41520303001440c0700c90584650b5100c00c0f88814148007003031440c102c034145a001560910104080307815650b101d142c0e25042c410b601e401c021642d0b0289200314810415542d059030000251401c403602403d020080d400c605c80e4002c2d0b146030b810390740c0c1c1e0710000b00c0c2c810008220303150303000180002c1030440600855503040c090741e4400e40203d5025007024800c1004101100d80070480441c0003030003505010000181e0303542d031401d40d00582070941568001040ca0164803204000c1c0540c400b4581c501600c40622090100d00081005801180141130000000c1c003075480e0200c03400c1c0b85a0384101540703080c942d100302c80c400d8100903000f070700301801ca0b130076400c4500c110004804258403001000424124035190030448400803419100303030076000300080091800300c0702094910900d00e41d000400ca40b80030500080a01d804a0200f2010290040d4070300800c1d11250b600f002c486d6454 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 567589793 1250 567588543 567588563
    0x2010b100f110613143d0e03030a0507020703151a0607050105060102070f18050901090f060c020706111507112d0a0203030d050a06090c0e0108010609060c 68
    0x1681044075102e0902100001c1480b40744240051800c0070304110f00507900520821400c04001c111564841e00340b13154506642e50b020001590340c0c42e1503e0001c5c603c8016808421304407885550090640d4445088840c40c0e400100c20803200c2c0c40c3d103001d0140e100241c0e2015260481c215612038201c04070440b403040c1516900c9410b42c0d165041448118081c880c0102199100e503407903d410740c0030701012107040d4018090440d001403068010400348050300c581c50081c0003004418801c480040c10028084d007030541d25121140d011445585e800d08086000d8180494101c00800004e0f16200c2070f94003483c100300c0c05400842442e04041403214154120700605e4200342c541a004560801802c00102c896007c0d090641039070403407140c28200088051505020150030503a80c103a11020b01c151301a401d904100f10000f4400890340c0007076442034165800003152526030025108a901c40032401d030100e003540420048540c0c21a440c070b801041c50780341c059540c50801000134110701507010010240c2c009 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 567591043 1250 567589793 567589817
    0x60302010f080a1508010c2007050108040614010f0e071e0305071815020105010f030503040302010c14060708041a01061b021807020a0c06050301060203040b0c03070506010b0c010c02010b10 83
    0x3103038000c00d01c04e003407901a8901d659180c0144600030242041c4107004901c01c0102c0380031040360810300300500f044500103056035528207401528405002001158400e603284041c1c80035080403d81240a03000c03000b101c80d0340d541071036011800b03543d000e040d11040c0179244010042c480790200440b20b03968404d00d4003040584908a098603070004c40c041e44040500e00c9403000c42c02d064211042418401141c1c000c2c00f0b5642d0b11490010851314a00025100360420403061026501802c4100d080c648168903000340351381700d0329102e800d002c0b0030380c2c0d604001040b48080c0400e100c1103546400a40014401550040d403401d040070385481c13941c075400b000686502c0d442e00150f5681d00d90b008120761140b030400c031541c80c000c00d000b52a03030f0700c403a0700f2101c00003a0680850041d11800a59050b240c164004510341030602c0030a81d10798200e8003040403240300c01c00070305000410600c2400e008080540300540c451440805075420b442c08103000400711380c500a0103075090b0355400326007140d42150303040007144500 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 567592293 1250 567591043 567591061
    0x812070f11030a061a0609030a06021b030a02030706050c090f0f012d0212070305040501120b03100506010909091e050319020d020d030216020f06090a0f05030709060302010f08 77
    0x1c2501d26690705009441012080c44035a40043e254042e000c1e03079401c1100035260801581c3e000d01d0307041940551000942c20b0001d1070507030044c846045c41030f040d1491040003008040c5590b011380b24070401a00041019003c1200500032160030401c4e01c2d0721542003850440c0401c11550300b09001620039219486c18002d0b590041107810300d40c428080029041c881c3c0b00d9143d254041070755541c0c60041c0720f01000107502c1e41001080e0380b802c1380e05689140ca0300d0b10b0400111003940c9138161811a1340c0e42c0c1c0c10a80601d640c1001000d0b881707000703041c0c086443e00e82140054200d0700b007540301150b2a42081c1d40d00c00040d503501c4040400348031031135150b06182c1c070300c3c03c1903440c0d03000311030100e45800c40d19901107290603000582d0404920040d4220b40c0128031168044003a03005034400c03005190300000b009001881c044009409450001d81482d080801150000d0400e10032940500c2c08000c9030502842107080a000c1c010180c0b80d401c10500c13003545107030f0000704604041c0c0700031804c02c1264808121100 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 567593543 1250 567592293 567592313
    0x1a0703020412050610080d02250f080d1101060f05040f0603060203090604120c02010f0c0204110a05040302040e0a02150f090a180c030e121b060a06030c0812070f 71
    0x84003103515200c5107500c3e20035500c1d042596001e5490310007610018500780001500004040f1a6018000d51420345010040c2468900001c42104210000200d0190b0202c1ca80b0002041107600501860716001e01c090995864204c07404013613414036005214203074988039290220b030020307900019119451446e203401000359410040440f03000000340321039600d001807814000c0317001d00030072010300d94815801d48111024060090203e81c60341c240c0c0c540d041c0100700070140780d130001d00702103000380003800b0700c1d8802d0b489500140080f8001007000c2c41941454403a60a0700d0010381d0007480103126540000b02c035464503030a10044e4050001e00182026480d9095a000d24405443c008849445904e00000360b03086100308150203142a41e800700300381c4240118000904c143c0b000d00868a1200c1d0b1642140c0c1c40200307101a41c4c0031480c840b40000d4410440345104001031140043c495040d86820060702d603880c3e10107205684515840310a002041d001c451900368003001281270500180340a1000c0 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 567594793 1250 567593543 567593549
    0xf0801290904090303060302011b020d29071d0a0e01050607080408010c020127030f05030a150e070206070215070c021c0f020405060d211b030c0302010b040203041a07030204 76
    0x801d040500d00004c15406070481002d5a200740c80e1410040b20221f40e9800080d60948044d502041800c0c58201250203055000c512802154000040c81e400300da00300340641040e0342c203200160f604900001c140103001c14184c00442d044950120342490951500003162042c00f91034030a2600140300780c10415400f08550040080400178003542030034030400780c002d025003014500384a005e81c00b16031a2492110301c0061042d41030301c0780c0440c0038184204840940008007240c40b5540d130b9041544051606803948002828803440c502100d1909210003402c144001d0801c10956002e00c01003c0710920031049c0d26400308861612229010040c0005554500e603c02e84041001241800c0c2090050041c10506c41d1402601d090059803901401e0001110360440054040c01020110200034080c125841c8042040b034604400c0038600303450032402c0440564012804299400c48000400d034082c0200000c1d2002150218114502603c400113543c454001420b50446240b00090380540668192006 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 567596043 1250 567594793 567594799
    0x3011a0c07150e010c03120c0e03120d0c03020301061704021914030f1605040902130507110c03010501050105040e190e07180204260c130c0f08012909 66
    0x22031503071031044082d10140b2011100c0091a44034000c031495000d20342d00c81e82c441d07161342ca40d5000c2900301d0010005080000d2001c04000342d0460740d140c20340c2c04000a0303500380e003420411030752521341084140c21207810f455110281401032004203c9641c01c0403481c016100c904c5010000c07036890b44002202c0028001144001c41104a07010034981d03540b18400d80110001d074110380e50301d5107907400a40c0c0c0e10515211040281d684490902a90800e034000154040c80980150104200710450f18144c40c801c480c4000010394400502014a00402c40707080240410360081006504103c0001c2041c0b042d4000c00440c40d4044012480c3e18201d42d01d4652451407007001000782200030b041d076507200c45032403107181116414402040d00318030f050b00c2113400301c1f80c0c00380541a01050182c0c60400c1c041100022407620f0145100300c2c80e803900c448550701802c00c041355001580701e00b07400000e03140100840200c000c0062100050000781c0d4201c0e103641c00300820b2000003c540f4400601c0746d502e0301c980c482e00380d0 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 567597293 1250 567596043 567596053
    0x207050303040605160206010e0a091103010203040b060a12110405090f12090111030405030a020d0201050c0d1701170a03030b03011e0606030c080c040909030c0602220b0f03011a0c 79
    0x420f200066004c64014200754480100304014280304a0750351078207024150300b040304840400e08420155110001c0e407403040000d41c1ca05100480000c1c00c80c0c00468060b203490710301108100042c41c00494520103484101c0c0d55086c00305030b94841002d0b800010b900507005580d03400120744000020800c2c0c50020410004030f031801c58504031010080d8114129041c081344d58407100e00d00c190070100985040d580c020b0700900390102160204071405041d00300682c1484010041011608014030085c00d11403000d85030446840505208208003160590260244180000700c190501d240420144202c40d01031801040c50540300300041c5c010400202c0d114001e250001c01c3e2000a840d80d0881c100b281c4454804010040034072100303a1f00710208444e17600460704204420b03c050603c0741d00c0744c4070b032602074a080d48990746a959000100ea0086070340200400c0c5500359020289020755010000d425214051414428820f00c1e03c844d40c00103020754030b103082c2d5031140c8404090382c81c0250f40d403400c8080100e039 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 567598543 1250 567597293 567597301
    0x70807050f010603020103110909061507080a09080d090501170c160f0213051b0d02040f03050f070504061d15030d080708070504030f0803060d080f0a08010e01030503040e07030207050303 82
    0xc0c003c00395480201d0100341003086411190300500217844480720050300e00b030410346d80c220401c64a5081d007504440c9940091060300042455000903245000160b11401c6549003481c5581c0d01d4151500800420491803c1c828829640c0c810984811003400007070f140c0c001d80703c2d05211002800303041320b030003185129030710030b00d050140c40300d44e5411450083c0d40441240e24200094800c1d900100c0d030382c851000c0142110300d29054848000d05505400000042c18141c90343c5048505070844e500035106640304d541c4054100c4418041d09008240c00c490403c001440e001000b40c9042020303241c11151940d8600003401403c600640b61a030140042c00e564103210087d10180c6681c401382c41450000d500403001801e1640158200c40a0726002645503c5594081e9654881e90740002c06480d0441040c1502000250121010345040e03500c1010175a12003a8081004042c000140c1c03000c3d100d00070203801000403800200848050310b5034644038008a80d14214107401900c81c29100615a200c008104 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 567599793 1250 567598543 567598573
    0x9020a0c0209010f0605031906030506180d0f020c06070f1a040b0a02090d0602030a0b10020736020937090b0f040b0f060d0b0a1211040207080705 64
    0x101600350320840c0d0b10b481a0f40c0303580b5031307003c100001d00070314001c40c900f080840c00b011800703400d0100c02800b041010507140d403a40d454504142064500a086200080d00304005110510032007110464502d455076002c0d0903424020350380c0c3c421412a07401500c0c000303a00d105009074132101c0c03601150010a21250b01030341580a00410000720313010340d6003c05030004900c0340e04a40c006c4074240b51008280091302056912110000e60001d41800c41b0b5568925040314a5110944001e0301048142c0142041d9841c0402c0c4a40454806200700d004003d4101d140c0a08d407030180806002c403605480040c1c50303200c10000305510300c40c280e0074510f400c40040b0200d1103070702468010200d40d148001641048640d114044010b5070f50564420758004e40101110305903060990140300c41040c010925031080341c041000c100d084d0f008a442c00d007199151031b1045103904040020100500001d560308114401c04c0d00e4070704d02d03049001045445560001501000e022180095844079600041030b01e42850b03180700a = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 567601043 1250 567599793 567599807
    0xe19022202160203240114060c0d020a06060f21030216080c0f0402040e0f0912071a0708090706030e030d0e030a140405030307020d0203120c0f0601120c060c0c09020a 73
    0x104910900c200303076100741e20481c081440c040300455012505c8031a42040c15640840c5003103422907800440500c01041c01d0007040003202640340c2e464002e072181984d21b003400d2040e9105a0006801c41661031010009130181000580d01101e81120346075803041039140490420b075030b808a02194180305078010510600115040301d082c0000c5461141200d58042800140c0c042c920529140d2003a18000034a00c0a4208030150b03c40011000e80300007104c030a07a00419a003001c0c1051780c42041c0c4042c009031000b01c48050542003062410b103021140381c02d110f180d9440d030590081c003040585409020380001c20400c00c1e14000400d100c0140440d0f0304002c600d560b250032039401c0c01e00084080c40b06c3e5010030440011503058803000b602175031601500d6001d012911a00f468100d07090320481d09a5140780d240b8801030140c40c00c1100c0a0800d11607510031451400b041a04001600700002c00c98400050705201c44804807083c0741806403040055040900080792190b00445009000040e0b110400b540040 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 567602293 1250 567601043 567601087
    0x90615180e0105010b0904020a120f06090b030622170a03020c011a030c040c020a060501080a0210030506060403022b03082233020c0102030a0e19022202 67
    0x200030803141603035880d410b00740d490a104200300301000300038502c203d003010780081c1510805400e00c0d501c400440c0c0300000403103121004070b2034150f607a0318042c00561024044c1c008111400c40003440c8606224054105542002c1151034442c0c2d1403007208001c1041010703803442d4080c000920030b40c0b05c03101d061014000e9030290040000c254078040c60303015000e030a910980091440034005140c07001844052000410002d064041944140c00c80a400160f19029031070181101c0380290071402542c2c8140720444250f5450710060500344401c1010030389035042030324120303901190000035904002404411000848803100348815440300b20b002416004880107019540e89124034031024514214508803529029005010000310113004421114181040a5241140540504007620300002c201280e02c50603400c4080c0c0d401100b00320020711b40d881000c1030440440301406c0310404061901a00d5024014000c0c8144030200c03048403113845a1485901a00c481302c3c0841d034505c0903507000d40411007550 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 567603543 1250 567602293 567602339
    0x30519030f1d10050408010509030c0601151710031a0403090b0a12020c070816030b01050d020d150b1c020f0105070317041704030f02090906130204090615 68
    0xd24848003841c0b00d18480300300c0e03041d0180140054120802000381d148520100700c420040300780400300f450007080c400c181c050440300f0300a590b0781610301fa81c0340c20450140c0c4a828000342440340c17045416007101c100702518103c81d5050059540e185d41080c00300440743c1005d0030400b401380e40c6490318440824200e0055000740c44034400300c1d50303271044001d051244504000008004440411003141c8139000380c0542c21480c4242c80507252200f088628040090322070118903412044104240b00c3c2c4030005a024100c140d03a818809519500414507a03000820000c00e40c00110b0100d03100480c641d4056035548038002c00e00c16007030581101080e0707941b40b03a1109034030031184119041c09940c00340c000c84443d142d00d510b801c1030550740140c968840389001071003a240300b01208424400c08610000070300242d07120f90848210040c0f940148061170000505020b81648400203000d013480e44100c13071a00403581103030082072140161a01502074402040032040c10482d00b5001300300c40d5030800030003c0903207100c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 567604793 1250 567603543 567603557
    0x3071a2709240d061820010c2415090905010608010b09070f0903060204030309090b0a050609040902010e040e0601150f0e150c1204081002030c030a051003051903 71
    0x205001c1c107040c0446050306140034a10b0107814079505203841c0e80c1e050640110000507120441780460605d4130454102101d41a140c44141c5a034032003503021000f40c01000703207000038a0381282d035030781c42c42e0009980d00c59451100e411824044120913801510185501c1102c61181c3da558104a80c0504100401220b19500b803c5d004074038000c05124056440314000c0c100e914580f1013081c16102202c8000200d02004511040880803e44c81d000070002941302765280401036141007424000c0703481092540740301d0240250100015a664010b64010a00c104c400041e011143d10050351001d4110303156a400901740313a50700c95451001b0034468101d4454060380c201c54429007008a5110781c0c01084000460400c0c12061807034185100d9010344091040c0c440d07450008803d11191074804910b5151700c40c0000003e090080326021b020040e5105190f040650a40c1481c1d024003030103000007401e401295a480d03000401034005112018000d6810205440d4821520184641c0c1c0b1031241905501140d0701d = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 567606043 1250 567604793 567604801
    0x151b070f05090408040509090f01021602120307031202030601020a050a12031d0601140d020402191806120510030c08010c1d01080a05060a15170703020903071a2709 72
    0x119030310743e00c500d0b40000d42034505400c0c401000382042c40a003000c0114411072120030604031003480245a007888076001001181d00520400c400c1c1e1054400d1040242c0042c0300c1c500009800c12417141c0c029251080143c1c40382c0da2075004034036080449002070301921440710300c21300303020851600ca200d004c0c140c0c0d0240500e120201c14094403032440c40c90704010350b001c0c400421040102204142080100400d4040100035030f0300010181c3c0c00007455070215103460088003402c00d400c449070b5610300c100c240c0400304962414801820030001e50410110858031080012050404000240041c59200e001c10301c00b651640b000c00e0082c4044000040131480440554102440002d404005003405a41d68212680c0b00b0b40c1050113020054881a0807000785400891084240c0c50075543c0414240d4500c01f6050b54207600303d0f64948040d2400081c075104001942e00da0f10082603200580d074281d4112512502482100082c80c800c1d012880000284012000c00140302c040d40d1004407842181c18240ca82c82e = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 567607293 1250 567606043 567606049
    0x1b05030a060609050a1401021905010c021e0c1203070b012303030f160204092103050a0510050603040f05060f0411150d1d01051f170c151b070f05 64
    0x2400d003e8145c0c4004102801c00203c035081c5110101d0300018410350700800c00c00300d0400c01060000d02d0882d0140d4507001a1494290b0400c48840c4c0c250600070103c400006690f2490749840130010014050100e140e12030006010400c201d519140d4048215981e0b0341e0360701900c20780c5400d42034078100c03051000041c0d4500c0d4076001064540125032045014a0b10030504840b98100080b007a0407a003094440f41c100000c070b64032021070000b040545615075203101950400400315a03004104100e01860032003842103d44414426a0584030700fa203d41c0d40d030344c841c5c0c01c1c141c2c2d186804940040091050f1070070003071080302c054901d5024505c40c0344100d00910300300e400c00c4150705050505d40012201801000d2014071190040820080b90f81030042460500200c41c900751003086402a1410903060300070240e01000c407082d00700800617540760721a41c00904214903126042c80b18150300c20031440b112084030354038070021603040204800085103603549a820050320f444442c855a00c6003200c40d04001207a01b = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 567608543 1250 567607293 567607307
    0x3615020114100e0f281e020f03040b040302120301080114010e0f0a0c120e010903090503120a18210b0a020408061b04050603010e0a05010b040605031302041b05030a0606 74
    0x2801c0c014103240030f035143e0f81c44540581c4020242c0c01c42c0118107171031a850b500700001c80000c01108100205482d034200440f40c10350314511510300380c10740c41004242e170301884482c10b81c0d8001d64401100c40c07031503c0f141422450103545200310702d034014002000091030501580b28802d42c50407030a04105903a40c6101d04250b0160840341c40220300a000700046001c4100da104445100e440e0801c1903d00d011506800100c6810740d50000e40caa54070083c0c0c8040c1a0002c08200007000e00320f00406c4080c518844e0311000d0301503156014240110038000015080c220405003000d0201c4464072035461440007120042800341442c180e40382803100010445c042c030030380229410346000c14010903c076240d4854200c9400710044242022441c10b00010940307554000055008017841520b425040c204420a9400c94030180e200c0e40883d0b40411081240603000420740794002d4000b044140c007240030b03001044c007a0801c60202901014604000d000140e08840a94043d0400603000c00c180c1da11008190303000 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 567609793 1250 567608543 567608549
    0x304080c0607031707051c05190c050412170f03041103030406201e0601080d030b010e0108040c09110a0201180c03021302190509010f361502011410 65
    0x1c0034613007a00c3d155041d11071030540122081c9440c0b8a880c4812030180c040303180e010440100c480d00d40d8240b11504a0009c80b0a1040720740c0b0300208000709007100e000e803491045210350403040c1c000054450070f01102d4260b81d07441510820f0882c1e501c1400305031455881d841204d04491507640f0716003103030441c10004140d800b5100c035603e8000c041180b14201c0c451031100d419804d00140700b0055000d00d0845d40b58140406044e0140080420354100220241010107000190082500d481449402a039000703000b4080ca0400382000800d0b0b4a0300d040400c1200315035000344140500300b410009003001144000e01840d1700c1a40208003109100c00d03903085035080ca103400340420360750580501c0545000407030b8200801c00198014a00311b0280310560568031441d04c440081040880e0001c000d50b044886d407540740700145440c0d0300b01d4140401c0c01c200c0302040b4445030742e032205c4481910701009021003004003a00d8540c1295070502903c0c01c1c001e0180084940b410fa6400425001c140154074803034845c010b03 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 567611043 1250 567609793 567609797
    0xb0d050f0a0b1e03120c0d0809060f01210f08040f050303070c03170408070b09040509150a0c1116090b0114030c090d021c06050601020f070312050909090304080c060703 74
    0x502580c0a12007660a0f03070140002e0391502a101c6801c038150407200c01040c1d803900250140130795030091580900061002401180e560f0061010402d400813501a07190640302c1c031940d034000503140303001d80184e41502404010003c0441441160601c61003c0181007180e10098010500b03540320703428545c582c0502c0034010031440c0140020300c0000c80d280c04079040e041c089801035050036a1562400d140805a901c01220709100042080349400c2c24081c0e2640302e05540b004046440c180c1d00000d05071000108800d0b501c0707a85502c83c207106403081003108081c10342e010441c0c0641c540442251b540c0c1e4414401c0d91821840c01c0130030b8500794022000d181c460075600d40002e0450340c0300281c040c050f0b84a1280310b44d00100940d081b0380181d1311080700c010400c0d80000a502900007038642403007110400342c82141554881041a88511000910241640d038040039640440310072a0b8261000c0c021008955444492941040701003680080a00101c604410489001a41074014440d9900c00c002000d00 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 567612293 1250 567611043 567611059
    0x1e0207050102070317070206030a060914091b2706040e0c0105182e090602190221010204081b0d080d150806071d1f0f05040b0d050f0a0b 60
    0x21421034004245c0c100420182203150684990000e40302d5402258400003039a600c540a10000000b441442c034030b84140010107106040c0348009640c0c60070324054400700429003030b41440300c1d525a040030b035007003078400070305038078290440ea89880c41460704a90150241d80307010b03482c040131f0200241100c0c03040d40685a00d4a0400380b080360207031030354181c400b80344c00c0441881c0285492140e045070b208281203000d00170340750100c1444010200b0040358001c40441d4000700000045014240c0234030309a0354101c1d81c020122400340310b2060040c0400d00d140406501c041030004248401059101a40c5084042101d44090722002c12440005401024001ea00244444030700102c43e540304c04559554408042e41c0e8036a00e4003198513040c0704031100c1d000560f00d4141a0041d00c40700b01a81c01400c01203482002c45000c0c0038440140440c00e1780103200704503096003600d030341030f0141e01220098226402c01550700d9800c450820b001d44420754480305140701c6600012541c0c441072241014071100100340d20 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 567613543 1250 567612293 567612299
    0x80a03060e1323030903030706020406110607020c1c062d02030112020d032f0709091205031e040c0311030a020d2406080c030105070c110418060c1e020705010207 71
    0x1241209010b84110321403008000040301583e040029282c6244a09d001507070302c2e4140100284031500030010002c0e030782c1c060001d000f2002c1e00810040342c241e1013920038600348a81d030340c040d61545030709001c0070b0102c2c0e150092010368014413440c440480503050302c2c40306240305002400c004901c001d1003460991600300b2030400c014a003004a80d02903a00a1032301403912040300307a800103182003000d00070f4207001064844a403180000d208090052003006010002c11003a074403500400d480515480042003400800144070300f00460350100100d04241300d13400075103410700e486c007100c40090100f40c400800325130003521240340002e5400c0342140e010781610040c0540e41c0d1502c1030070814400458102c1c2641168007440051403107141d006001035401840108203c0e030526084500241c9120100f00d007031060000130800805140c6020081580c0004601402da11021600604140002c0c919410710303c490250315403003904507001c00c010040f01503907128a90700980e030b103d20a01c11180940c100d07100c20 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 567614793 1250 567613543 567613583
    0xb09010215070f300911030d0203070f060e1905060f13020409231501060923040209090a0b01020717070e370b0409020a0e0a09080a03060e13 62
    0xc400c03800c440140200851103111002c4a000ca000c0600804081d80e170721501091005241016030f088100b079002e00302550780c03844001d48034480c180300600040990405401080003e030302640c104000641910030f42c581491200700b1070141054150707100c0c81090302151102801d9240c0600441c00b005040c0b40d80310b031543c2031001800400d042500e4440301c254281034481194600c811101c02d20801078403044480d0035140002d050b06801c903a04001c0480c9041c40800c2c0c0d40380a84120380b1098903e0b00c80d1068000004010303114020406802600030b60034440000e0b01034100d990036031426000d0300e4000d5201c0c03406400b0380c011400001e410703034000d0104000207240c83c00c009030007441d15113110041d1a0b4020107299040c00d0300c4140c090000030782140e880181d0042c4503140b9021001c5400f031025400b9500001c8030301e40a4000c552640021102050351242140e00c00051903034098803040d11107215810290050400d4030821014100000000700c00030300d2003a1010040d9405031501c0c40405001c405 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 567616043 1250 567614793 567614807
    0x40e1009060e191401170f0c09071404091401053f0c03060c0a08150117090a020a081609090f0609150207080318010c022509060b09010215070f 63
    0x8400b4034590f80e111030103100c0d0040409540640704006086e400b00ca51500b1642c50a03660140314411038210005480c05942d0300215141c121820385007021800100f000411014802d541c0300c5050b892420f44845081c1000080c4039049920498202d5240505140c5044011040001688020900c01c0c8001580c4ac00700400404190043c0110b81101d40303000040391030104162a944060b810104918500541c0650f0040d400f03490800910450201c80002800c8854008030550003e8100000140030080800a000049800910400b4019603c88020f915200c6114024002440a00001c200c1116a0150320103141e40100103130260b10483c5ca4400040200f02012501400340c02c5c1c401900d0140b9001900b8458002c03da07003036603400c0508180d007200c041c3c40c28912459040104402802d500420a09413000041c2101039020108044030201546550040c031201c520700540401e21718186005000402c40c00c1c3c0889101c4402a0f0f0100078141c030032a138010003d00c0544500b005103100d002c0c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 567617293 1250 567616043 567616081
    0x1080712051e0109050402041b0e010804060f0c0306050f06070b0c070303200408010b0d081b01021606020405040501060c0f0609020315011d07050c1005100b040e1009060e 75
    0xb0080d0340e0440c0340d2803200d555030000e0303000c038102d240c0f0364041c407003075141134400e05400388102d1002a540c0030b44c402c00a024401c4c0252114140304c0050001810720030660840040c1e03081c0200204084c0ca0104005802040319003e40c9001d020403202100440c100203003102c60140d00b2010021103540d40c104080c4465201c1c000c101c00705030b191b402010001c80c0c942058034500f04480411500d0320305041c071407801c42d0400e400c12403040705555400808103154400300c40046091820080b544609109150b002e032140001040b4084000b243c4e440c10b0003010f0340070b0000d8940c01ca074140181e9a0360b41c0211a14034010901074109000129198000781e115070012804604c0030f426125107802000740440c022100340e00410320200c40d40700c5010039400310f0300304990204450909500f441c00654000d0350f601180c000e00c02440b40e442d808a1441d41c0c0741d04605000740186003c1954407a11100501d800000a4a644102d012101d501043c5440a801200306903000e000641e259aa905107000c040003207104 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 567618543 1250 567617293 567617311
    0xe07050d061404150f09120e030c031c1107030305090613031a0403030b090903090d0206271302090d03120e0a0c0815010503070b070302031201080604060b0108071205 73
    0x200341c902241c9800b5840a20480c0240c0c102c0c518014281c144009803801d144420303151515000c2041c00150308030b038040c00d00080914101c3d08110310540401d14084c1d91010466041c130404440681d4400703085149040381050340d80716030440f030741d43c0c01d030f1983c0c0d8070280801808124140f000c05003d0038410003800e26001f0304281110520b982c3c0d1a81240c1c0403114503000411114442000281a01801a140c000380b050380d481720030f4600204000d4490281125680c49194980c050070309554620302910410b600402d00444c41344001c1600000c030703005110b8258007c40c6017108116061901d8030a541928401a182c80708240f008d41c1d080741c06030b0100051440240c0d640c0078140d0b000704108200100c2030300c2050482e2186060441091800707074001d920055207111800103101607100403038007108447c00d040d141900c801d00c5140907802c601907440d00e11703642440c10740006800c550000b52103000741d009810411107000c03142c00444008400311100ca01041404081600d054032550107185d010145c8 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 567619793 1250 567618543 567618551
    0x603060f2203090501140a09092c0f061b0d020a05040312020a02030712080412080705030705010b01080106080c180312041e080a021f0c060e0616030e07050d06 70
    0x1001d440030032101080001d42c001040150705020550300705003000d8400007204091030918075403e030002c0c15030007140140c0704040d80310030b20040840000620340310114440701200312111401407000b030361482c00070340c0210303644038280100c0e42030941b000707030700b1014407022803103616201d810203100c1c3c0039500c20004401044010000000807401150b80010020050340c060320401c1c501f4010103207001080e4005000000d00440c0b804001202901114101c0381172414100017540c481c10f1900c0907000da400c028005000001e00d07102082810340c8201c0703000800340ca55400a90b00e86400f19601030044500c15101c090030419645450240c0c0070203101004001e04540d0b80c400c0c1c0c0e44190750103030420f91140711200390b540801c4148865000310740015003101d20007000b08040310b40001780f804003059425030741490302e42548100203100d0400d404c000c64000300140a0382d20500f18581d90360404403a0b402c80c0044072420f01a029200740540701103c40280010a41d0701c1c1001d0030444a0ac0320b9580460341c05a031 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 567621043 1250 567619793 567619831
    0x30f060d08070b0f0106050c0c011107122904020a030b0603070504020d02090a1706010608040f0203061008100b150c0f160303090906062c040f0e010e060603060f 71
    0x1160010480b41c1e201c0c120210542c10092000e11145506800010622a0030b0013085200840001d030b009000d0300903e40305002c98111240d0501b81160340d0030040c41c04a92207820400c2c459000742a820802d00c3c0300030307504045019100c0641505080e58001d510070006070040000c14424403d5a82040d802400c0d01c1c00d540d90744000030100da00801020107601e0f00814443c0c540d05d01403c50034010288403600040708009120502c1c0c40f9041406000180060314000c1001e02001d0040f5001207036024007210300c9820100741c0305844403810320400d51a4072071140c03074001410940c01100807205e409810b01c00001c22580c4508482c3e04115118100c0d0320030840f1500031000204441005c607104091a504520700318280102800010381160641da8240b060410006604c62012000d006182651120414034107203001b0101e41e824565650103401c0c01e0581c210010b02d5031001d81f094000c01b0003006840011140a500e6003412a07107194180c0000700000c5600d5030101303000ea80080d140c1d0f15251420a = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 567622293 1250 567621043 567621053
    0x120806060d02092101050a062403020a2a0b060d1a090f010501030b100e161b0b09150a2a170c0307140f0703110111040b0c0c060a0203030f060d 63
    0xd1305020302c601d070744800900c45c241d06244501c4000c1e0181000d91941d071030b100000ca8851300405051842055800180154400c0c410384241900d600c1c0764043c0c0004104480b10114803e450f0a03003528258800700c040307159443c20151a4032815441032050300040010103040c0000c039001050505107003c1c01d42100c0140d2020310805020b1803054110800d80d0801d982c0742003d8581540140c2a03600300f10040c0600d540d40400b002c000c001c494640848102c00c00f088503114900c503241d00901a142c9141071060680700032030611090700c0440091401d80d0340d00a000401ea42c01400c0340d0080038160350200d03402060200000070741c020a0300344a01c0d1341040344041001004e045610644a04002c030a111900350301040e02295102c9404a01c1d04006801c410140780d445010401428040b60340e2508241d80300071341111031203003500344540d510b03070f580c5c4d0541c0130607035001030101c001d58042d0440e414030781c1c946101541d00d65249507004508542d0342000c1c90201030b0740508401d90192980c0b401c800021 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 567623543 1250 567622293 567622339
    0xa0603150b0310090c03060507020c0303041a1e0d0507140405040f02210919030e010e0a0312050409180c051e090a140f04020906010c0615080307120806060d0209 71
    0x3a100342d01400666103541440c1f0202d5401511030002c640080e1001001075800006860940703854000b82c00e440380d0100d100d0500e0341f00c2c8509403500308145041052143e629040507050071321034a80e09001c150740d4214122100010560f40040c4030030188000d10007801d060b4084856006038010040c540400c00a0240640c0110408020381001e032204104410340280700d0f050080700b00c0d85002c9910340e21690701400d2180008150350411841c804040300d6651000300b000002d50700705d80102c004106803503000784281d02c103000340c61040341041168602d541852100c1c4c008036030401407032000745040c101000307407080342c0b00f014061400140c090203806541c4c0c0786815004450040000550408481040c2c154200081041501650803003c1001603152009040d520a0091030450742641803458450001c011100852a50000c0c6e0320001c1950317040040105402e41c00b8451810b03800c091001c080311050700884d00d058121304140058407582e24241c0180000000003031040580319414540007070a2 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 567624793 1250 567623543 567623561
    0x305061b070c080f070f0f0e0916081b0111120c0a05030310050906190303260c030609090303070903111c0b0f090c010e0f0114070b0a050a0603150b0310 67
    0x42d400003452940080d0081117000010071070f2500c02c14000f4901503080e01003003618805c040300c031000b0701d0020740b004d802072082081c0003441c4500710405644a450880d039801e050320800c0800300f0a81c45440f140c4d07000d400d0000140030818010034000081c01000358481e00041300c2c0682a11031007040d07000150013403000c0c61103901c01000322400c003841d1100708900548017801803402804009601e0008010b1041241706036909030030925405e9804003911400502c5182010f000007110b02c0078016840310142c001c502505040f2401034144d20307001d82d007545038401039400b240400e440b80e0040000903401c00c000754800400402c031138046814182500d1031201c6a03001103d1011251040022032841d02000540160140d001460748014040018101200c4091180d129000c40310041c0106e038819180c80e10320703c0700c0c5e405040d01c81f1414a80300504d00d40550b048c142050600740010440711944c070820f400c503600000c0595412900007440c030024a400c02001c2c0c2c05d8000c1c00e941e0b07103c0705400e0043d2110 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 567625899 1106 567624793 567624809
    0x906061203090904080f040b030114031606081e012702040506070201320703030c0c0c050103150503071205010e060609010e1302040c05040603150305061b070c 70
    0x1440c005e08514000d801c40005011923442c2c01c0001035412104101c1784030511001c14410962595078002540350a900825010841507110b2005a6044401300d00c0c20400010035000b15000d50038242c0221071408616084100151003121700107440d00805036045060604100018019104d511800307410048190540c50541941c02422901040b44021940e4415a40c05540445800c140c00c20740100b4078000d0340346489805110344c0c4440a52213104200c4090500e0b00540090000c45076007003ca001c4c01e000070820342c07402c00c40c210143c4043e1031008034116081c40c0190a64141e244940744070f410040c140310003070b01c58150b81030645280c1c0b400d40c00715950700300c501c0d1346454003864081c0d4070504000c04495240d0b04400144191386043c0d405200b01441c084180800c1c0d540c0340300042065200c1c000040d1501d0b54034107001c0006c1d490842c414a002d056446a04080d130450b006815 = true := by decide +kernel

theorem cover : BRFrame.Cov 567446043 567625899 := by
  have h0 := BRFrame.cov_init 567446043
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567446043 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567446043 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567446043 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567446043 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567446043 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567446043 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567446043 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567446043 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567446043 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567446043 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567446043 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567446043 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567446043 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567446043 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567446043 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567446043 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567446043 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567446043 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567446043 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567446043 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567446043 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567446043 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567446043 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567446043 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567446043 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567446043 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567446043 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567446043 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567446043 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567446043 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567446043 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567446043 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567446043 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567446043 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567446043 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567446043 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567446043 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567446043 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567446043 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567446043 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567446043 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567446043 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567446043 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567446043 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567446043 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567446043 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567446043 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567446043 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567446043 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567446043 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567446043 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567446043 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567446043 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567446043 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567446043 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567446043 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567446043 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567446043 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567446043 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567446043 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567446043 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567446043 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567446043 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567446043 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567446043 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567446043 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567446043 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567446043 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567446043 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567446043 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567446043 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567446043 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567446043 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567446043 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567446043 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567446043 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567446043 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567446043 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567446043 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567446043 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567446043 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567446043 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567446043 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567446043 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567446043 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567446043 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567446043 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567446043 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567446043 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567446043 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567446043 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567446043 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567446043 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567446043 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567446043 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567446043 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567446043 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567446043 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567446043 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567446043 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567446043 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567446043 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567446043 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567446043 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567446043 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567446043 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567446043 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567446043 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567446043 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567446043 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567446043 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567446043 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567446043 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567446043 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567446043 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567446043 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567446043 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567446043 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567446043 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567446043 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567446043 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567446043 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567446043 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567446043 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567446043 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567446043 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567446043 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567446043 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567446043 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567446043 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567446043 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567446043 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567446043 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567446043 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567446043 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567446043 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567446043 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567446043 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567446043 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567446043 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567446043 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567446043 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567446043 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567446043 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 567446043 ≤ n) (h2 : n < 567625899) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
