-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1621
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T03:54:19.086507+00:00
-- url     : https://prove2.me/submissions/4f771117-2aa7-4f48-8739-274a1ac75e58

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 291366906 ≤ n < 291546762 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 291368156 1250 291366906 291366941
    0x90a0b09130f0204090503070c140d03050d060b0f0c0c010504030804050d02030a1401090b010e100e0a0f020301030305040512010501060203160606080604050c09010605030c04121e030e100207050d0204 88
    0x3681c0c000134203542c1078a00c06c1e1069040091444204194002d02c0d60041000c50307507609040e0180800100180c00018000d401d0140001d101940780855034030642c050f1009140c0303103440da03c0e140705031401070b04180c01820061240303403003c244d15070040043e101202c1d44511001c0c505420300050010405a1101c101e81621a00d0354600c0054400d64181c003403010300c24000501d03c42941020034028106034000c02c00c0345030100501c41002d089500c0301c2c050703440c400c4948089880d140e00701c0c3c0060602001c41c809552001c80044101648200180200c031000c460020008034030b041460303700c0d00d00380706010140c1d06c10440111102c20403c000304030540150300005103030703641d4603c3c6404c1403411101100c2a400100100c820707881c0034034925014100c50302d4040e0551078658140da00d035100301d008100003581c101c1c02c030000304460b003e4441a0500450701003007030380000c4e02d0080d000381901c11845220f0141c0c010014142031001841c01c00700c1c2d41c001d1030032044c1e140301d0702031000504c2900540d011410b1b = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 291369406 1250 291368156 291368183
    0x8160b09030118050133090b01020f0d0806130b010207090f0609020c0102040e07020a0b04110a0b22050301020c0303010905130c0810060f0303021f0f06080c090a0b0913 74
    0x6034070f05052a9001e0050001040b00da0040d0191000c80440c1d038008414195141481000c185a04041e0b0703040d282e440c000002c003540369500507440d00c080000d00f03950510503101c00c00441580b0107200b901030780007a030b62800030f0b40f03001c8070500650340f40c50035450060303004100802581d405500145c00c00380303000d00c00042035a210b601c500180c0c1d21001c4441d0b02690000303010403004040b08100c0d0351160171440030b0301c1051a16a13607880b040710f0142c4045c1038000c400c09100c03056614080440020034840c00600c0e5640301c1521000c011056680025020a0103003000080a0406000b290303803035104200514510380c200442d40d801010007400e82c0c0b954410401610000034081410f080c042e00300440107001031004140c5032010b54076103402c001e0401c00300c1c0004000007500001d00500108091b40413400d00303441c90241c00010042c0110380c1c1840340c200000022010400b0680550310141500d00b0441e44d91b54520203401d0b05d03002000150407459200000f00c082d111001105110343c401e4a100c042c18 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 291370656 1250 291369406 291369431
    0xc05030408030a0b0a0f0f150309120503040611031503060f1614070501020a05040e010909020105070b09101d1018021c050d050d1b02031b24040c08160b090301 70
    0x80049400012111411f140140040d0526000c02c0b00b0b0361429180c1030186441130380e01c901001c0210070940d0280480400483c0400c0703000d811540b1a00c1c9520456501c910b8a01000307034080a005098038043d0044101203001020782296041c0b040b010044c5040301a020407a0854525107080701302d10400e08280036031000a4420b00041080700d42035518a51502d0030504075441c55003041c0d1008800514280c400030050741c0100540785200d402070b1400721980d5548000f641003016404201098610b400da00040f40d0f441342003112118280d00084904282c9074851040494403000b110402e41d04020881c1c80042c0781000310100d010b991552103000c0441d00d80e49047c0342814481d1424042040403540b0111780382c103842401400d42c0400b203201c015046c014ad01075101d11030b540412100035404e07595010550020043c841905440d840c114107800790784a090168460180c40440d000759440400080d10140041c566031582c101010808107907142158204803a0300c04203075a50195228103103050034 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 291371906 1250 291370656 291370679
    0xc0f32031005030f07360501150f02060103021509010512071d0619120902030303040f0302210301180b03011b030b01051c090c21060c05030408030a0b0a 67
    0x1c1c4500301d106165641004101401c3c540c00041c03a0b80c90b40c1c0800c2d020081d440400c00c1010000c00f01e855400390407403107907410882d40d2514025000c089821b1600028441013001c6502001c607030a942d50b4403540c48003080882c2c0b601001e05c801381d40805807001c072005080d442c0009044101d0141092854007100900300694203104840c40300118640c0d1701c075090808406118152021400c030b40041c0f510ba1110010484140820203401c10424490580907a10790958450101035800400301e944078079040c50540070514198104030010300500c80c8120f000005040711680001e1005002420f680c02c241c024041410100d04110400d92195103c1c11191030030710915201186803805000c044406110180a680c5804003950400034100130920b10709820210341415815400d80c0460480c00c2418840302c102c245401c45a9190400074517a00b44030764020002b00c031a82b003120f00780052004680207a82d80d01080780c1c080c00d4800300b00b001401a004c00d84c0003803070742c4000809401c803144e11450150b40 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 291373156 1250 291371906 291371911
    0x4050f0613080706080c0a05190516060501051801031e0302100c050306150f07060209131104170c1f090b0c010e190c0b0d140c0301090c0f3203 63
    0x850743c000d0a002d0002d03d45c0501003581c01030546100b10b10701510110000c100e881040c1b8080758034034036036a00e81d800c00c0c412411998205d614911030003112415081503001850207111725403050709401044250751643c102900e040329003012804a00500b1510398502c48070010100300d04600031302400c4030300a10300b4031512607240c000381d455584915203c800d11501100e2000742000201045c4071707100700000d11070b0441d40002c0d481a00542c9802140c008184035512285110580a041c00c008051078a454005001114811500100b10b800440741d240d40f00c0d1100c9800c5034020010f007a6102c4528081c943e0002c110308145800d1002c55603074583c1c542507400c1941a80101c0c0d44803180f401d05807a00300140308070209040140070100d0f41e181c1e90804e1210880c130030310384003040100303030140382c80c0107940507070340f213654410080d44103180011801c0c0241c0e1090013103000c5a458881c0b4161101d108071031a0700c041031a1746402c00a55942d0551a01102140e85030a0a01c01486c0d207407510428140040d50 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 291374406 1250 291373156 291373169
    0x30406090201030b03011401050f06070816020307090c090603110903010c020c0120073606030c0b0702010e04020f09120106080127031d0d0507030201080705070804050f0613 76
    0x52540348601c001002d44d01e4454200d03210b0fa04242c9a03403502d210f6040c0c440e0448004961881c00f8080c1900070401e1401040d001410740c0d4004641c4071810302c013121104011910803015030f0303031302a00c43c01140b00f2120a036413000300203103188400f440440e000c1d602c0800c0444844403541d060050050000307007529070613440100160050081d8120a5070080b40c03411403035034000b55800000303000caa500d80c2e4900c1e2a01c43c03003140d2202040074411803860703100b60b9800104d080340c004010003080a412000b8114500c0f04a91a10940d00001007040c1c82500303486007158140c1d43c02c0500e452410400000e500b01913141242180d041000115a0703440ca40340464402c0c882d0004202d203482d02c0040340c211182c880080c24103000941202080c521040f41802135107515040801800c0040c45100c4800d01c1c00d25441500003100c10505030500030001206400c5901c06d0b43c0710b039a11f0b65a0a0300700c03418082c4200041034048140000d019518041c041c41c0c1c45450042d0207182000032181e2802480b132419845103 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 291375656 1250 291374406 291374411
    0xc0209040609110a2403020c1c1d1309020f06070606050f0a08280c0909061a0a030201080a270c05030118030c0f080301260c10050706060308030406 65
    0x240802c54062000c2400c4007044072103402041c501249101a042c0d10200e0407030000380e0f4000c51402c07902a038141c0b2015039904048841d031880d50070303036051490255546279004c9440d48081c207000c0d01600550200310000035112405c1101a012040041c0130320780800c0ba4803a180e0405903041751280c40140c25036500070b09000c205a441c1500380401103091401d003d000e5248035000388100c110000e1021508460901e5104010380d4080c0c40d0b11031003070805801450000c000c6000111080e4503001482003d01490b020050782d2442c809500c2d58020b41010150002c0040a040000d58040c0306803c1d840780b80b03c0000302d41840703c00201c090220074500c03805e03030201d02400240280400210386402134503044e002000012050080b5001500b502640102005040130885c81001980588184c0c0240d00002d070a40f256142c403000c80b0403034203100100c800451903005072524030000064441444c100a070817504003002503201124503510180d020750b520343d190140000003c124100031441240a0b1900 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 291376906 1250 291375656 291375671
    0xf0d0504050f0f010804170702091305010e010b010f230c071e052d12060901110f0f09011e0f09090905060c18040e150106050a0203030a0203070c02090406 68
    0x204800001c2006215000e00400f40042d11903980202034950000d4004030308a41072200410b039030b01c0038450000003d400c40044401c1c0820350603903461403130409210304002c0c44a420304180340b6003280c003038148590000c5e141c002803c14250048110010400320348a007a0051514003145000c10380c450f5551043c1d0303070b000d00c3c1d04000c10b1210000071442000113616012929140c040042c01500303c80205140003d8250110441148404e15101030703054003400c10f00030065551180c075103e0b4400c440420841d401c010815911146407001c44900d8051103440300d04090700f0400c0501e483e001844154188940c11041035080e80c1900c00310109090b003996011044106100c1c000c000d940558403103007083d800c00c04282c2c0040d0300420100e90102c4501328154640243c41d400303400c00740c0002003068009240c4403240d0040140814003911610410003481c02d1071340e0700c403000c866610070b0307400f00b20040c2c00038004a0f0045900303070011a007001c03041c0740c1400800d50503000590500d4098804542d11079a0310300 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 291378156 1250 291376906 291376909
    0xa021209100c140f0d140709180b030307060f0b0a03080a030b010e1305150a0801090501061502150421020c01020106090c0909092a0e0f04030c0f050f0d050405 70
    0x50000d02c90301c149482000307511108108041070141800c0c0f1480b811011a00000d40040d55200b00020007030300140c9807803810329103800340c4141558050703e0381c0b010041c00060300000c000d014510404c80050029403500e041c0e5103580d001050310840c00d91240b62a8002c8540c996030311541d00c006903008802159071105503034000350844144003840c80c140407840d00d55480316507807901020402d0303080003408200c40e55205000404482070600c01540b1000e407010200358900305501050080b48110020018591038140c03001c0e545c1070110b0340e0380041e4008202c80702108401200325410502c106a58554011440003150036480301c0454040140c4c0320611441c2c02d0f44c5c6c24011070b401006c80c0c0300d0801148818810041c008603ca0042c1e1b0b00b0789803101140c0d810810140c0c81c000e22003d0844031849078190700f203d2210b40285134450680302c2c05644001c00c4411203142030b21030182c0e40c59121035010010316620161f694145540030340d00f9000d0000140e914000500c030001c088402640c807141e80d41d04010 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 291379406 1250 291378156 291378161
    0x6090c03071809060f020f18091017010905030711011b03050f0f0c0307050726031c020903070e16081509092e11070b010e0a02120910 59
    0x590003032196200e828100002d01e0104100c0b01c0285070001d0210f40b00070941000c1c40038120480d60480090300c0080c140034003900c5080503010310840c4164010003140c45004201030303a074060700c146494541e4504100070201a401190040c06000f4001040e00d0800362100c0d07007180c01c990700945003602e03035003c42d00d0503603842a080a5031402c0f011080f9002421618020464000d0030054601c20761700140080b2032905034001e07034070310181c89001c40c3ea40348020320700b054450343c16110b02590014140764002c0345600c02e5040c8021414900300a41c2031545482030000344aa43ca0b5456800c154200030710003080d1004e211174000381095000651143c1481d000c2c145004400c04180b104110f00041441034034000340040e0003d002d0b017144d01c0840ca80301d03801005d0900c503000706058007184000036814a1451101d80284080e880c6143c100090098007403108090700c94224014202070003a80180044001407030300c0d5801c0105840014104242c0c07844102250b0002c0d1800340255000d81c000344802c14090 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 291380656 1250 291379406 291379423
    0xb01030b010e0708070e210a050105090307030203090d020406050915030601080c010e090c2703060709141504051201020304051606080f07030906060b0910021b06090a050a0303020609 80
    0x24034246145003c0000038082c40340648207000f0410155001c07003881e034400f8807050350307072a072001010041445c0c4620300d40e5504480104950075400d1000103840c074031002c01540c86080c2c158018516001d090401c000078010b140200302c0c0d00076650540441c1c01d45030f550b80240710f070301c0e40c0340480040302e0200c0416280c039005034000401035001c1c034a1040c50366402608901000000d5404248035264100500e5013401212048041501455420282c41180455a0403021019420f8982c40e44900d0412035240c2042d000d01c016003c0035181e000036500744449100d01c42c111080a140c14603403039100141c2c00c03825160145a00d61f402209110070b000c0b052045110402c001003040d05024600700000e454800002c0c0303600b0600e00c10100003246d460080e00a0411079600942c10045c194a03102d615059820090b1010302840b43c0c0640510744900006104103481c18104503030a200c44c220702000202d40c00a1040c5400104490000843c4e40310003500002a52090300034100e945820241c40e0f1400106 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 291381906 1250 291380656 291380669
    0x5040909050c130519020304051002031f080607090311031e070303020c06090a12150212010602101a120f0102040b090108160c0209060103090507030b18011407030e07080a0b01030b01 80
    0x140014010440c21300e185c542d000a032049005600c907070ba68140b080c1040c00082e40240300a000204209940c94517004c58441c4d440202c224020700c0b030f11080e04aa81c0c400440c2c5d10070110303e07501e0f02480418441081004c0c803800050444010b546d011030421500009500e011916502040c020703c10160144482c2d0016030381a500207080808075000a24400000e03c2500900709442213003a081c00161031982002d002c2c0b800c4c0c02e542d1400c0f55003004540550034803410300140a090740b4115480e40e82d0249840342d14548007482c41070301e400e1041006040c546d29040e04940309e240c0101e50610002cac0003a01c0100f20302480e07907440e8480c5a00141c04a8002404602e0500c4140c60700e1044903000b5003402a40c44e0140c9003103501780e9840340141c00400401030042e140388164003000042040e80c904141c8600f0f1a0310f003101101c666151081d00fa140b08403c08102e84000000042c0d11303601c0381c1d002c142d4440d0782e03500320b641480d5105003180c24800c42c031500392002044080144180500080c805005102 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 291383156 1250 291381906 291381911
    0xb0f160e030a050d02030a120e0705010f0224060103060501020d1205070e0307090506030c060f0f0a14162009180102070b010b04260a0f050f010612050d0c031e05040909050c13 77
    0x1038031f40c849e92507008030300445061040305014810942c0c80bc0001000000c40851500e00c04907083c14082c00c0308004580083c0001d04000000c10654804100409148003c0d190640c8000007000c00310050b010003004502042840b8021a525640030003130f40d801000100b6002505c0c2c201305c030625040c01200003525005540c10000c40e1030030100601100e551041c5140b03143d450391602d0600b107a1806006583c56131401d00814010890030101c2014005144030b480030302c01e007242001c04060300840d1420003d521240d1680050541e0b1038452501e030303012040c00001031a0503403503035a1120b82442078020300080b03400403a080c4544414000c1e50848602189070a02400b09a481d01aa0b6001d907002c0042c84a03264880c0070082050030040c841c59440c090700240304440c0c880300c41141220341d8520a0f00c1e03a21511030080f540c1400342c0400d17010b181c0c140d03940c0c5404116039903134110305019842d14402041030400c400503001c030070380c4602200b0510940290034030f109648200304188804108118100380b = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 291384406 1250 291383156 291383171
    0xe01050c07081905040f0b030f180c010503130210170a05010b160609060e0c090c0a050a080712050c07020310110301060f030902040c09030b0f160e030a050d02030a12 73
    0x1405075040e1207100140c032801d0411083c866104690a0055a1081c15a100e190308046410456803000d14401d00d0101d08940300d6690320802e80340411303510054a42c45800030601d025441d4031070f40c011540484d019811403880d80ca0380e400310f2000c0d103141c0c50401c0060840400070308190504013459070044c04800701400765505042440305c0500c50300405050109110304a4000c000444d0400080c19070440801c2081014458072145c40b00c20304521130b0b108a80080c009101ea800a0301aa45071104595039141816421001a1a0309101a100d40140524440055000d03402402124800c1001946240c1c0b11400ca106040c982403500c0c2010140c01d040c041c0d0480685200c02c00da81c11105145441191100641d078284c008080000e00a0341207410161a0042203130046850390449110f115440c142e81d850302140e510810042d034181c1483c1d10f4881c090792200c1c2c032400c0c000003d000001c042c0c400070080c0703542d440e280c00240c000071000350b040030030f1480000b07401c100b0b41c03450401035900c14007590 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 291385656 1250 291384406 291384413
    0x150c020d080603030a08070c14030306010201060501030e0705091008030304060b012a0b060604170703021005130506090a05040f050f070c0f060c0315030c0503010501050a030b15030f010207060e01050c07 89
    0xd00824842c1020403003600001035007907228000c00c0c808ca6800c00840c99131045000340741502c2c0c4d8000ca0b05d0b1030242d070a2440000d4603501c240b080a071000800707800742001c82d0504003049000040075200340c1525074410404603100c03006100031402280309541c0002c002d01c405c40050f0041c00c500c5084c09103517104070050b0760407820740c01c1d48418690780424281001d5491500162013402030f50008070240300d820100c0002c0410004080040c2e034008c840700340c003c0c1c051507030844a0307208510303c09004210482d420001ca00300b2001420549174000c0a03410495258404141190080011915050380307a00900060214007088a03401c071183d485c0c0216600709540381c0310191504442d000701003a55805554503071500c00c0d1720081c1c500140101405a850b52428400c601351054082c040c843e5107480000295450000d00308030403207910007441034159580107040c80c0440c042c0a011a090b01032500704031076040003840101155846003d002410002e9011524219140100940311803c010005440031 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 291386906 1250 291385656 291385663
    0x10608090a060509010e25080a121d04020d0221060f131d1606080f13051c09030b010f0303140a02010905190b09012901050403150c020d080603 63
    0x742c0d000074000c2440d460307000500f40104140158400f25020b842c00003428207880b48641c10450301c0940e401e65800391903041064603a100644c2c0205208440680516014040e40d81d08044d26000008007609210400101d0f00f80ea004081401c905075001032f2940010340d040581c1c0c480702c441000b580d10036240002c04142c0700c45003125124070a0a8500d1110310b0b501582e0400d4180d150203403400c505c0c0c925034584503a5101180301d9a00d1100d01c44480101d600c600c1030341c1c2c83e88668044882035846460b001142c0e180c440c0f5054080e0741a0141c070481061024051209290813410742c0d40b1050f40c0c0f0724508000c11761907010b800422240b20402070410100f980545001c3c110003105540a50f6100140070690050580382e030010b101e03001d8a480b10301981c0418014134100f600a90401c03101e9a120700026080342d11060414241c0707070802400c9000e62059001d00c040b0244181402c81c034040d140d807916080c00038002400081a522040e89092603a810b011003610841107080010050400b82c000907203 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 291388156 1250 291386906 291386923
    0x3120c0f1c030f0e030f0715020304030e01080c07051b0a09090b0a150312030b041410090e010f090507050f0627060d05090c10210f020c070b04050901060809 69
    0x101925140c100300503243c1503000400d482d4448088954034107800010802c90f4116001c1660300614007007030841c642c8401c1c02224861503040d9a46000032043c0310048d01e881d8005810000c2c00c41042c002c060002c0e400b042001c08200c03540c440980540074010030800070070361a400c000c0030541458007100009044080c1c00381c0000403203001080c00401c040c141e0b214800d01e13071f001400301d5034051800c0c1c42854040e4440014001d0980b400e2088803541003882c1c14038038040c1e43c1c42c01c1026211100300588041c40d032068200c481d41200104520110308d94160950f018408241c80c150403e1000300701502c0c01080310489400162081c0e41041c0e40188441d180c0e004080848410440703c1ca1440385640c0c034002269200524403804200302d0401c086134560f60001c00c58060300517402d080d0001a414010040c284040b246940801c405004021031403015102c22100185059001e000e05500e002c030511600b00684003403420140c80380c1c030704010400d240c031041e8010410321030b401044c0120100c000c01c0145 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 291389406 1250 291388156 291388213
    0x6060a0503070e0a1802060a0306060905090108060403080c04120804080f0c1516060c030b0f0405092a0604060f0e0402160f03020a0219030b06100203071b0503120c0f 73
    0x41848102d88611090b8245c100000d51040002900d840080d4042d441035040d20020794a500f107032911031082c00f200a00070300460115601090004d03000038824400350fa404000c02c40c80c40d09180d038440180311a10081203040706c100da400320702031100d50020030690840342281c4004041900b140400318403d041c0d45850600501c43c0040da01c040c1182060752030300c10650001c0d0070081050b6004000b07000782020140f0b20b01c140c203a918064814a024000c09006000309000303402103101c90442e61002c04034011071980400101c04020b0420741c8c03008050300050856490b00105102040c00c01810303e0030b900c644030311442c4140b1407034024004036114000055070100800401c3e01680c141a45040442d45000798048003043e18a00d01c5c3c209850405c080381c3c07180c4003111240d141c003005c1010105225140100681c0301b4008000820088440c40ea10702003800425461246c84001113400c244620701844548140000c88042008080091040c6180014060840c801103201d83d07000d00c01d0510a00c5 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 291390656 1250 291389406 291389411
    0x209070c06060e011202100807050a0c0507030b01140901080f030a050307120501091d07050607060c1407031d012f1006030f03020114010e0a0203040807050f06060a0503070e0a 77
    0x140304102040d40004060300b0800140712913984d441c0300c43d111081d07502e5401c9014001d00004503194502950350705005407410348401c2d04013070038240202d541d048402020748241c40b54000010100c0c80d1080c901c0d001e400c40300554286020351a081c410b021030180d1011096a0002601000c110703004030a443c048142498113903a00d454080c030440d048580100000e4205190500010306079101d680306000100d030440c008058103141801a42c1c884041c4d110b181e422242c20003443e4006100ca03444605a2200d90800301160240e000c5a9446500411011008110f2103448030030000e5030044003241c0d4074024600480c00c0b03202010b9001c00c03000f22449100c045008100828030210341841440008502c00d002080f51a43da801d211000c8000d540054015510f0200062400c1126111381416181c28100092094840300340c2440298801001554101070502c00100014414031a00c56541d004200402003030500e601084404c8407540c0c02503110f54000303901040201000700f005e50380304d0742c1000700 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 291391906 1250 291390656 291390677
    0x70809030315090a0e150f100501080c09190605090301050c030114040f18050304150c2303040e15010f020c014401090f091104020d1b03060503061003020907 69
    0x1804043c010f031000e0340400d4024070f001b500c0e4952160840911810341614506d0b220345540001d8021081d0394058907002484510010b090b2589800c003e04403c030000d098801c1c440e140804030040910340d030304940c0000300f00084800d800c1c50240141c0d60880c50030080c0c2c0e45954985800b051241254080240c000c42d100c10940d01c0112050740081e08080c0c450000340007040c0e16203801512580607028100d14981c40041c0d0521440c85604c03030b0641030364808032400b180401c0c0d4558110724460940819003600c410000803a1030301100c0d4034140588000f821140310708401c000050454030709045001c1c21940141c0003500130340ea0240e942001500038449a01c500200c94100d0603501c0c034004040c1e0903441c450020044031103103a004050407107181400401005422224650942c0d2001c00043c150098904501d540c5103410360003001162600c010004180506180c0e90103c4124805844046135588030f08003c58101031203107683c000d000e84400c0c40c0c05811a40010300d940e070040d244404124150300b5 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 291393156 1250 291391906 291391921
    0x60e0d020d08030108031213080405130b030106090c08070f120e01060909030c02011d0303040312020a2a05040209150c19050a03120507020715031401090507080903031509 75
    0x100605030a0b0403080e0302d0750329138580d00c600d690783c0d0229421860342010a800a02030703194401d01012596440aa01c030711b018606800c000c90401c10540307002d001c41e034403820804665024440d0300010005030102040b1100c450030080c180ca0401006038040c0422020701c0d080381580004082d84c3d240c000840040c0601c880c1807914018030b45604040c010901e4588040c052503040201700340654800d0f61144010000344024100c2c18558506003605540148820700008000c150302840c0a402031049400e169003988034041d51a0005d4100d208039540b410314403807401d1540c010131000c0c1405440a52902d404103020036440040400c120500725004140b00c805540d06120b80440c241c0c0312040501c80e80a0303402e0250329402400c4044011410341d0214078043c408901406d4410340d6560040c00d02c051610080d0315044603038250600c00c040e0b8800d40100701520503070f0b0290190044a03000101480d0003080640444406010011140e1044c420010b0300e0349143c0d2a1075a091040c1c440c02910380b9038a4 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 291394406 1250 291393156 291393169
    0x2120f070606030602120907240c08030a0608010f0b0607021203070f141504020319030918051005060408031608090402030c07050c040510050108100305030c07030c0f060e0d02 77
    0x210010719450502c1d4000050100d0ba4016000c22540c0c40141c0b903040e02c5501015940c1d4403544582400e9040b90b80d01954040c0c0d10502c4215140118108080850015500e4030815402210011640e03a0759101c20300c83c0d000700744200964824000e030b007003240300e070081c001801a00882c90024450300e12104000b040342e60500980e100d1030360029051607194064688804e000100c411790000521405c802d0551148920200c14012a00900a0301d071503e0300c10386400c4880070041080e01840800440068031640c000d4040740d0310200b1620001d010300b8031100030a02081c440d071000340f11300002d00003842148408011a00039480b104510041d21900303182151160148481480d4414404810000c24410702d6006100c200e01c0782d0103841140c0100e00c02c01c41101c0c42910080d2520440200a114035401264000c2d000083e5106016041c3d5482c0d5481c4e20b50341c8001c000c1000f075000004200308200740c0c000d4010142964246000e20f107420000010981c06030400c0d21071183c15a01d100c0410754070b030354 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 291395656 1250 291394406 291394417
    0xc0203040b0f04050907050d050f040818040b100306050a050f0108010e18030f0901030b09010e070c02030c1003090b090303070806090403051e4b0d0c080103060f0b0102120f 76
    0x81c1084001c2c1c40c5c40d090140c01c41d0008ca400c3d4104a040c003000680140d00400441c0c442d40e030104030a4100000c1c074114550982c01c0e803180a401c9607582d1116955aa90080f40b2051101c1c2c942e00800e090342000244a516809a400540034951280c101c0e02e69070303001011141903690000c080003107507031100c092500d1184090355105480c000010b080c481d610140004004400003a00c080c040c04094205012140800b4410000b05d49580800300300341620607030000704c29900080464038070341507a00010700d0010b01c6d200188048dda90710744420402a0110006910050680141d4290720380b80c0c0c00030f030101d11b0040001c0d1150071880001410540241c055030011105000c50307450240c8412411001507104480705038270541000c0c0e9041084500c14005990f2040d807289861103030a441c1078040c802c204415081340c54407401d2020050b1440c0e148100515980190b6075008d1030351560030034400303d44c0c04c0340302c207000303982000d600300043d0b41c0010300842c0051100e0200c44d901d02009814480d5800348 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 291396906 1250 291395656 291395659
    0x20f0d050a080a0807092c06040f151505070816031103030a060e011208160c0b030705190e0f090414070803070203010e010203060102060403031a12150108010c0203040b0f0405 77
    0x80f0b022100a0340c401040e501c90f901d5510358515840d242e007000040003008414034104800c0742007001c2240701000541c02c4c0c02c031802520100344050360b500080280c8405060b15400e0401d00281005030049200b02d0b550820180d0510504d003403029100c07509144180c403000d5003114007411038601094420701d00e00601558140959842e41003a07013554024021034402c9014880310311001182d040c80d2080c0100d212580311504914101d426a00480c0e03100c01c0c100250b034401d1800030009400600300c401180300d8480d0340e6a603560b5880c01c3c621804405c4c107000000c020003809170132900e400c0e1142400e4000361101151040865030b40c628241c0c01510b00c0c40e00403140e03401107010000c1c04040c000003138040340b8801c800900c50140c04500352030803408100c49550060f41300b18007040109020b50b00c100403070700351307020040b454001280204a00310140c040c4d1112a0f07009210020b158202451b10b1400342001500a00c50007525440c000d589002d81d019580103000001107d116441146003140d0003041c0 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 291398156 1250 291396906 291396923
    0xa1118010e0919060203090601050303090d03110a0602070506070f1715040b040608072c0f070216030c1712030601050d060812190824011209080c0f0109020f0d050a 72
    0x3c0a00d49034003e50010340b1204102c0c0700d1500085064507002c4190742103a5005070104035011542c2d1401c46050341a40740d041002d024907640a00403480500061442c980a14006c01d0507003409403000b800250003810a40c208006508190b60703546512510a801c2110b200045009124150001d00108414051283d01915203480014403200105141d0308850760707041000d100525022101110030024140200c40250f048002030802c0c40c1d0313400081c0c11400c0381c4115929070b02c04620324a110002900b003641d0413000102d042107151071105500d880901480c01134458009580d8402c43d42d40000b402c402d0500c000071404d82100c1c0c43c580d01032401030040b43e04842c1c20b80d181401d071a149038446c4141c0302901f9541c035401100c8034041d240140c0100452000d041e500c48148405800c1c003222041900d0401061603400401d0344218014100454043d2081c10b0f59040c0c0070510501d82208041099100d074186400800981d403500c5142100103010b5034203191840c401c0c83c0240c10440d03141f40003014000c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 291399406 1250 291398156 291398203
    0x6052101080d1d06070b04170f04051c150506060f040f061803030f05031b0a0e040b0315040f02030304081506030c010c050604030c1506080a1118010e09 67
    0x40005410015014030748401c1d215010000701040100c3c2003c8203a50450401c10841001901e074102e110341c054001c61119030810000d004c0d41c1e1155025401d80c0000c0400402c0c140882c0c03811054010200e40b0034503402510807996961070054034950071206880381d0795500001c00d9074031854100c0b080807e040c4440d980c0c0300d844207400a042000d034000c41c00000c008141c0c413125070407040e0041080da40c054840908503542800c0032a42e40c0d200030914907544214090b0740c0000c10120001d0a9400180d03100c0f11050400c1c00c060204844c404070301c45100f50301402c841419023050700703415600310750401041e0b088604580082840c51080350700042152050510916150704208082c07030050300700704c064800f11a03141c0c0046400b414030b050054115042903002c240040e00580040c1c0003640705000c225402d4180600c0801115030540c0044000e800c10000582046240180304000b0b6108480302e03030408103440d07003505280405000d49000005030001090718210200180c82211a001d001d524000 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 291400656 1250 291399406 291399419
    0xc0a0b0c1312120810270c210c0e060c030f1215060304030504150e03120409050c0c07030f031116080c12030d0c1701080a050f070f06052101 62
    0x300780b500720681c0c24440742940f030030605200b40d1000c1c0c001d40203008081d41007070610001d0401c1c0324000080d9103020311101c04804006481e80503000105800e0340f034407a5044003c07101d89a080d800380103480c4046250a44005c4c1d9280c12a0014115020550301662652003100a092031442034001d04002c444010035042010800c240300e80d80b10f46040c0f03025807007038510a403d20800e404180c80c0140414424401804031401c0111300b000181c80500c1c0020b01d00d4034160209083c810b40c00d1410b084104000707802d000e07071301c1ea9000b0725800c210b5403082c1d245808408100c01c0d0f151082804024909001c10b0807403000d061044d8000d90414140000780d85080100e1200d0304020b00162154420901036000d01079500d181c207507202003121408401540c9824650a5841c00401014641c0e00500100400d804811002101103038040c1c902040203144d1100070341040341c40c200b00c05e0312800b81c135403080c0d1040c02120740c0100450112035003400c2c910b4451401c0d808150503217102c850301022080702c010002445 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 291401906 1250 291400656 291400679
    0x4050a0807081209011d0f090408030106030b0303120c0a0203120a051608060a030308180f030322050c04020f0c06040507091107020a18090213050601030506060c0a0b0c13 75
    0x7110b41c0e080889040e211168415000d5005181d141e5010482d1038418180100d030255403440c00c000002d10b6100b01800080c001140f010068400781e4650b40040b0061140e1905442000d00b150300031401103043c20342034040340110b0040180b00c03401104001c035020070314500800c2a6000f0101c0031100e0180740c40c0c81d402080c0203110459582094407801d04588040500409100380121005818400010b081d13407002d407007504014018100c01141400ca0b1000e051042c0100b40c81c000440c9c0c051756903820402d943e21011005010480401c100c013a21000c00503c0004003072041c81c100350303000340c0c132001b40389900c14190141644080c210b000c1d0208000030842d020030040103540f1560006c20091002070304001e10b6010f1003000075003044d1015810b10000000c1002051222000000803502103040c1e40410480c50080081c14081a2038009112080d80c050080340e912140c180c50040c1040181c50013259540100c1c3e601809c400000310114540707400350003c841c92192860040e1081d1039071124091072 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 291403156 1250 291401906 291401909
    0x1504090902030c04051603091b0324022a0c100c0201020105010e010b1b010f06172a01080403020a0209010b0d0e010c1e020c1c061d100b0604050a0807 66
    0x1c80d00030220140f4a40c076142c0b05243c0115407080c008190400c100c082a0024030030b07940c00f0740e0700120100d40b401d00034150003100c4001c2c5118030b02030304281000c11005c81505010b41c43d00d240703950043c843c80800d401c40391110140c41ca800550038035801c2e04602100d044c0318202c0070340c4d60003d10280308682000d40250581c10524402c0e0f0081103107a90b510910306070401c0a002d00042c10008000c1500c003289819844190f0300440c0c4000500001001405011104140e001c80c0440007040741610468000780700c14006045010341420350703000302d4084110040038007032080e070500c14024042400d25200300321b24100c02e5030103850007000b540c5445401c0e440d60480503400c0300c0b150034107060740c9424106000d0545120b00948400d40210b00019034040350303104000d4004214400c40d2607004a17562108a04128604110340289066880381881404d90351480510010383d025280e18903480030000522022140a007280058001d0600000800c0f51080d68003003980701e00751890208550101041c24030 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 291404406 1250 291403156 291403159
    0x3080307021b0102070b0a0917011e0504021302160501060305061609030b1305160f0312020c0a090b0402070515090c0a0f090f0603330b0603060607021504090902 71
    0x342c07010340303540080c02c0c80c00c51000400c3c0140c0003a6020401100b14602500e520b04250074400304440e2140c4040d510140411203908a580d102c0103040200c0e000148e00100c242110f00042c842480c0c40c0d0042140041c00c1c3c1100d2030b09030703400100c030503a810b404505a0140355000340240126541c070300349655158015141d04420241e24111b1000d641e01802c44402201c2c0d11105214035685c1e001080c6580c8030010f0030035601402004550080004106241c8000e041110118004942181002e060031841580b01d0815075021002800803903840a006604071211403d000c1030354014203020502a0090b00c0c0000c0442c840e0100c4103200440482c0b00314802c00b401805c81320402243d0782080b1030b0401340d200798510940c01d00d0701400713501d903160041c544021070ae09021070456500d940382117080d010242c284510a4407407030a07100c00b4115812440128a40300000d000c024125030020b1010b1001401d900d209000006010003103407101ea0010650f841480c7c80584c6070f95641c01c3d808058200c210080303 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 291405656 1250 291404406 291404413
    0x90145030e032a0d030e040e0f07080d02011407020309191a0304021f08040b061801080d0f0f020705090901090821060105121305160b04050102010609060312051e03010308030702 78
    0x422440c10030f00c400441c110317059a5855101c2c12201e09000007400e40c034903038840f1030040e0340c07280381c000c101000464010300d2804000c0c8500200140c000f400c48441c958814811480a0284040c40c3d070700100303582110800b281c1421303c80642c10300c0252415016030207040d082924409603c1c40b03400000c0698815402070b104010840100c03200c404405030454118408190000e01045c00704401c000002e50095000d0600314880b07403001c100b900c07400c100360f009040c13507404403400041e410b0380801c20240107a40c905009140d12103642d000303034680226000c0d1901807405a00021340340303003007500000d100d0381c0c002a201e03640f14114001c42140c000d401c207405c4001e500c48004070b0810b52103001162118400c08900055507210241e45080e200540e440c15150b501c00c2c882050501c003540104130340100448048256900d250500290035502c543d40800641c6180550400128100800b001e408503014540720380e980b2184010b2030309403031a1219001400a000c000841000074080046010700c04607000c9 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 291406906 1250 291405656 291405733
    0xe070513050903070b0c120a1b0201050105100c1112150112030c02042d02040f0b07080f0903031c0b1806030c0f010314090145030e03 59
    0x100c8280da100341d520340e8803030780b00300309203804a00d1700302d115600306982000c0185062003107441c2043c1c0754400c0d50859035080c0d03518000700816011040c60a040c3c03034a0300081c0001e6240400142e0b10000100c1c140092103007045030007040042d140d4441c1c4681c08014142c0d0240095441d1441e83c0b108410b04e824403a51090001040c008050402d08171020b5069941482c0041d280d400d001c06800552800205c20845071800c400c00f01d036140184501e600b0458005840358901091012214441e07440204034000801c0000302040300401182c0b01d1000c80040a981c1e00c507030101183c51445450030349082d9101108408124000c9908100d035000000c40711076100707000340d1042c868442c03025200309038160302140741c800c0c04d820020308511a614050400280554400b0880310707a0340811940210306941d1020b0f0b100d010305501314540c40001c00c0c1d0b0300d40c0c07450700d50b80319400c0d12920401c2c1c020021000014030103402c01d449060855070494003c0c0075030f0345c03028201240c810310b181d001c40c010030158041081d = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 291408156 1250 291406906 291406939
    0x1a03060c190c03030b1c060c11030306040203071403040f110a06020d0c110a0b030f0a0504030c0b0903040306020d051005030f030a0c020f0406060f032901080603100e0705 75
    0x503204207a04104102459070707035102080c1e8071144076040880c2030540b5440300c100300380d55400102461900903403000c040c0c0f04c014500f0208841140041c1c0b0148042c40c6c20b2820611400001d0b01d40c0104103840042c5c0d0790b1108501031b140d1000003844e20200701400420002001307488400074100e18880c12801c0103941040040003100c030007602800c801a07115590340710545d031088022101c002e000c1c040c2c19050401e43c8003c103024149503045504554000414081840c0d0015241c561241a04100304500c0c20306507802040005558000350801980d58081010404140708447c000d66000200310b603a4100310b029400901000c0703940740c14a82804030b00080f5420702049c0c80d80c00400c584059446c4c01100001940c06903500384060340c00c05c82001c0d500c074841c1c0b546d100c0c15001d417025440b81c48400d20540c0c4018140d07042c00012a200340c40c444e0708100c030039651940341800c0417002d00340450380d5a20480440d180c0040240030b02012810100a89102d800202e054401d0301c1c4107075030b1380c81ca003a000356 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 291409406 1250 291408156 291408181
    0x5030c011b1b030e040c0309110a0e0105061b011a010f09030822050406030605010807060e030a060f0f06090b030c090103080301150909020307030b0f0f0a0306020a121a0306 76
    0x3006100401c1c440d09090039040c00e00c16070010114460300300907003582100c1c0c010508130b0f502c06c103800c80800c1d600d002d1503051002000300c440c58100701b210420300301c50900f119101130510620500f0301541e004a161281480c1c4440c240f002548004000c015a0442c4141c0740b16503440c0c2c2d0b01107404500741e40d8465824a103c5c014510507240c02503901c924041d109480c28580e02c0d03070b02080b2003481c0d0030b03d20040f035546e4450240d10025809054041f8007541025165401d141c150b40c013003400d1100044024200d503c7c042190182107400c03100014244c4100d40c200400f401c030303802245044514040e0082503030412036100d990058410750884074102240401d0103c089003e010250980d481480100b0180001d10254100d4446600d050258180d80e5001c03d401c0c1c0c1c0041d1040c41c0070a4960701d01615900303040c840c2d80079149003101c81c51400c1c801e80c004590000c0d101e0002501985c0c00044e1081c0382e07401601506e0001c942c00c0030030099000201007020034240f20207503580c8240034150200b0809150305 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 291410656 1250 291409406 291409451
    0xf15010302070b060f010314090a050c1c0f171c06060512150a0305060106080105040f020702060a030c050f07060e0606040e1b041e05090f06190203041104060305030c01 74
    0x12150000a4454808101105065500440c10961211900e401341c032308200290780581441d5000389000c035003c0c5030081c113060840320094011442c444c2d00f44c0290311b8002c0e495401e05d4001352003049412540c102078545d107480060180c101c0340009504034045500c3d04400c007004200403001c004241c1c440b0400c860500c5020b0482c20209071400128812050500909240301001485444602d541c1e030f80d0107040c000240d2180003c50540c80c010003050a040c081c901514420007421480c0000c41c0c1e0001d078240c0261340d03039501010380c1c0f51891124540102e085801000d2083d8003251104841c0c42c05901403d40d0110100160103080f01003800e6091a0003421090901000940030380c4818040e1503d02e841d51041581c0d11903210085440601e00e0380600300d80203c483e6101160034a00a00304a1514400c058050126480134080001c090b00029803014800c0c451400960742c0c6e200d40c00e01c40d0a421901c0f90345607010b4034141c0700204100d0000010300d0540403003002404104046010519000001b = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 291411906 1250 291410656 291410663
    0x100605060d050c1b0f160b04060813050f01020a02010f0b09220c030c050f0a08030906130f08150903071101030c0507061a041109030a0305070503120f1501030207 71
    0x780711214007038034a50001640103803820720f014248490756090321400d10f80c01303050340199001a03c00404406007400650020301040408840082c5000444441440759110715001c00c4038400210340710b901540c0d40d681e0502c0e001022649403030082c01909001790f200c40040400b40d032a02d0901508842c4500901d211a0f20003015103000c5d6075049401c0c8420a401d0b1014031115025a80c603e002508ae031600c4409107000f41404402d09081c0800e00540361540c904480c440ea4100800b04002100041110104002583e1154562456484000c007954041e00104034541500c24045620300c0e0004000c201020074400052485e201c0843c41a181d1048100140945c100702c900502254026004000ea540c1e1a01d001c0746010115210f0301c085500f8100000301600100001e910396117018024460000c01c881c007001d15080e85e01001996958245c80010240a80400c042c000e002040c810f54111811181c085006482e01040c3e0810403001200c003100d04802a400f03005c42e41d4801c1c801d880c8015070 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 291413156 1250 291411906 291411919
    0x30a2c0106120c1413090b18030306090414070302120d02060709080c01050f0702040507031a0103060f0e09030712050705120406050306041d010204090218010809070e0c1b0c03100605 80
    0x8003130201065040f5048502e81061115644589102c128031912400e14007880d580c1640382090800c01c0500103850b65602021351003403040c44900c0d5940c1008a0300700da070000546c0d840e0504255030ad42041465480a9481444021190701d818008201240504426400d03160256111034054031014664017500700e50703503c61403a04034994000d03c014068004203100c2c3c40c0c20306d82a903002400343c800072a00305000a0701d545100c06002c0d0b83c2c060001031000b090030305009003130600d0b25a00440c0d1042c40b80c00413001100300450120342c014001c440304160880d000620300c201e4070740068080d03400081c00b1201e51180f0045e208421503041c0070303501503944540c1d505203540c070358a04000c058104909103541002281080000e586c01c24030040c401451002405a00c9175a070f92070140f80003140c0380515052005410070421143c2000c00d0060540320780c02d40d10300c00d0b900e407100355407814040e05103c1d80c400d510002a00d00d480e40300003070030184403104804441c80c540c01480600142e0b903441c41445e40012 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 291414406 1250 291413156 291413159
    0x4090e1f0b01030f020408030d050109020f09130e010c0215010902180603070306051905150307050307050c0c0306041a070e06090d020d1205040f0b09060906030a2c0106120c 76
    0x308940181540c56030515012400d0003200c54000200d174010f81c0469203642c0009400840e2001c0d6008460040144100071402c100740716001d1411031141581080c45022114603075200c19005510805441103004000c0240d02002c1030060350b1000b040700d420324030364480c0b400041c400d1064021102041c0034020007800014948061000580025010809250b01c81d040401d8584030302001803080f051802c0c7c100f410314a800f043c40603010f100241809040d000b00204081585c020f03080740c1c0c1101c15494019035030104008141c0c01e011103690a2945401550140b00c1800740b0034014001c1002e0000070301d40c1903158400152410303000c03132002c26084801070051a4207442c00300541c0d08641d00103800b4504880d00c655994113205081300d2102c0100304040340502c25030228011b142c02030840c11250038a0822001e00049860058603c0d851141100100241d42404190030203906108040c1c040800c0c965004031099081c26054000080d942c81c010000490814074001803260760b410400c6507215a = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 291415656 1250 291414406 291414463
    0x18010c0905040b0303070b04081306030204030b160504120b06180708190905030c010e0c09070905130b0402030406052202061c0e0d09051302040e06040b131104090e 72
    0x4290f444050750b41030205104c2c00c00480d03200c0310028400e61054035643e41e00d04482c240003041d03c1641c2c20020402d4070500051001802c11032a0580000c50007100b04825040104100d8440c8102c0d002103a480d0344405148082050080e01103015560407111503a0700520414198682401100c00c2e400088070600402c0c01e036000f0b1112041421822240461320f1110303500c0c0c070347ca03590100d150206141c1d074403040d00007500c0d0180410008064102e40c4c00b140c0b41000072004146071660301400713106850000e0001c11400250b03000c0c480348240a8025516440d01d41802c4006050443d00d0000d203000e5004002e0613060000d0341040c1700c56005103494105103540d0069900311000180c014400c55460710a180406010805d500424985594841e0345074103000c140130a000c24001010011401480240254615401c040394082426100082e042400b0b44c00034060400e05c4a0144126241101030488008064010402d07940c0d8680207001c2584001c10032075981d140010b040d100b078010040410710301e = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 291416906 1250 291415656 291415661
    0x10f1a0d020112060e010e01060809070b09010c06060b07021905010903030c051009080717040e0a020a020705090a0605030f0f120706230108010507030923031e0318010c090504 77
    0x25203006143c601d8401d420032021200312519a007118243c002040010010360801160b503a0140020386000d042e282807a2690a68603171507030242041010010490420991050088500041d08490b041c483e40d961035a10442e260b214542c141c1c01107e03117205980200030082605812154180d6400464070b203980c40480f000c04420340c0403134050082c615901c03103560007406140b00c0140100112507440718140342c024040e0b5050384c01001410024041042080b8480d1300560380a180c0c400007503943c1c0b81c40300f0103d0070001590000d42d4080420b9091081111040c2e2001c800e842c0260b04a9079440b20a0284550f2010007104c0001a035101e80d801c6610310300e001016000b0182f00b22804038412403601c50340c40603032184100c80e0200c04214401081420000d009858100c14203082c20031a0765400d440300d20302c4100d0101004c0e0780c803074001e800b070840180800888401c4044100c0105122220080303181040e8401e64003000700e10407907036060ba8140f03018400c0b01017114294560480712894042400f02 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 291418156 1250 291416906 291416929
    0xb090c040c021b060403060501030b06120d0c03050a0201020c06180d030509030d0b061c020a0806181b04051504140312041202040e060a200a02120904020712090305010f1a 75
    0x4c1040d0284400000192180203040c00385100343e00941e02454082c0a009282c58881c00c80c0c5419031103003102d110700d1908803500c1e5003100e1305490200c0d0389104d01d00050740648907094140c51148605010040358904045600304c613420004256800784040032011011f40d0380174cc4042c4029001000341d103555500070b40c400c10b2802c10242c0b0143c10800c59951051021034914a000300d80c0750009014008954080104d07984900211210b82000b0602414550100801090741707140d4580401c0b00d01e002c48401096500600e130041c801c80000a0342211000c480d041803040c3e29580b55440c1d030040d03640ca00450000040700200399000d09080c0742c18507521790413844042c03c2c0d800958031101c000c012801032008070b104800071440810740504034240c800c003400140319508403621061041044090303010800b00070f2820403203034a980380c00f20440010000d00c40d05000910b4486400210404281c00460050460b40280c00070440744250051190650b5450040c1261001864100b6030b914038060443d904c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 291419406 1250 291418156 291418159
    0x1b1e09030c1509030b090a021c0818130614040f1b1b080301060302090a0807050303160c0b04180b0105040b04090f110c07080106140f01110a0c030b090c040c021b 71
    0x295482e90b82e417100d924182c41562040d03040c0d009000b0040a5090025000c8021808017008162405c190b440340c0180d4010244a0020001e03511500c25841d40d4100d00a90700407070f9080d040141c03a40d958020094130341c11410b068040c0b82030001c1800307601c00501c03882002c000701c04202c0b0030568000c1812581007280010303680d001000700c1412408246054041c42c0a0100f9071401a40c658440e8204140d0b50381e690311001c01c3d613100381010b000c90b407800f206a0718581105030407270314520102d107849403040100d43c1029801c10800b0400085500080e1401018104113080801c41d420500c0c004541a00c02c60290442d542030412040103080160360000c200410b01903c0012240b60560000a49610460781944035070311600d42405000b40030310880000b0a425200c2c0380d548100b810104241d181c07082d00e9141070140130b1402104030780080c80980c0006912130380d030a8850303480e4580410060026288021280719403130b40e290a41c10184694800628250001c100c880c40c05003011041e68044034969 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 291420656 1250 291419406 291419417
    0xc0206070510050a0504060f0507021b03030c10090b1f0b07052b1b0b040803061c0b0406050f040309031202030408011e0c05040e01060507061b1e09030c15 68
    0x2c2481c145205081c00b400e0030038804500c50038981041d201307403140070307082450403450982401801500000e0807004024188006a00341a80800290540c003401000050501541e000ea8804090316480700d43e0851140f4406107541c0c460b10300841c000f5020208800810844590a0060300354842c040e0040d903202d0310071141c1d0030303401c8605a41d040206400e141d04200403043e44000c1c85422003201820254012841250003036942c40c1c0b22140c0c140944040e00003031001011503103a451300a8041504000070054010f107510030710b0304098046040f201a00c18078a8000413852807140e00011500403901599001e40060940c2c80d410070b5858481950f10540c8402c01c00011003450a000d014080d00d0035505401044a000006034156004647c550701004410441032209149940200381518214603183d0344940c400c0c03803c01d00030304485410501940d03040712840c046070b5010b410078941031000d0582d1106e200960b0310585405036a8000240104502c0c14244003481611945030754a01e00b03850728 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 291421906 1250 291420656 291420673
    0x171c0305190c0207051203120a09020609090f240607110118240503010501090e06040605060c0a1205030c180d06091218050105070609020a050a330c02060705 69
    0x300304a80b1000b01500258100040c01c001602d442c04904c150074031504065440c013002509a10103842c4000d21903207a1680d40d00916040d5140e460540b00303800e4014040301181d09000440d0114048100c809140c51603141d1041c02c0600704102d600310b0081000f611880c00c1003010766580708440e60380030b07250b030400020707510b90004000d0f2001500d0040800250345083c00003459006d950008481841034240101000100150b0364008840021698800c180103155240c03103002802a00132540841ea110303038017143c10a401c40010400c3d1400e1407141000141094001c1d8013030710540011109a504003205001041c5400d041900810800900410b080191401c9590f00e004030f580c960000d03038031100391100100388a508219045440b40c5100219174410346403d00007070071407250100c01044142c0b03ca00b51030864481d4080c00d00030340320040414441a450711601c4e00c0c204008100c1000380d04a008858125403034200c0e442c0c4040480c0d554003083d15040b82c00344030310380d13010b140300300c49611034182c2d07 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 291423156 1250 291421906 291421951
    0x3062a1d1309150c02010b0d0206040510120501060e010e0d110409030905060a020309030d08010305030304060b030307020a0602012412080a020a0f0506070f0215060f1201020408010204171c0305 85
    0x1d50403000004650f000809141810000742100d480000c120300943c15000c1c0300000d43d03540001d503021181c0807110b40840040314603040360300c5000880303030340e80c41400c103030000c00d07050381010309154261170a80e92511121462002c02091101c2445d010301040358409800840c0c1c2890b40200000c18000d0409440389039440001c1001c0b50300c602c2d4003200603080400c01012031314040c05200f502003101e1402c80860350440e04c1c5c49849100142c8001c04003075035020f000840b510280250741071079800526500c0c0c000d60300c550103406045c0b4451803603071001c86072102e010003420160601d8142d60a107000c0c121096219500e044481e84800b580809610405031940009070498103010000d0f07108001a1245003002c5e500079019441c00c2c4109029074002080e00c18845850013603060744034804035402c0c0a0844940046000d02c041401d803a071155000140103d000b2505400810848030340d451615034801d00ca0114a031100e4a5040402a000f208480c03d00814413030f07008142c105900300700c1c01a22841080 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 291424406 1250 291423156 291423173
    0x12030c081b0c031c0518030a050919120c090501090e19060204050904121b020102151b0d05010f0503010b01080c090105091f1119030809030403062a1d1309 68
    0x8400c00041341d100c00400c2041141c991403840050034000c019401d046400e000a0105d0184950580c001e07600300703002c1440e284a40e8800401452103010008101d16507090180c0b44520723a004403032015050800000e8004941c1c4112040e1820240c040c00400c03518504030030781100788240540e4081c0d02800b020401e80d80d0000d140b4065441036941048848070108040d01000ea40c4044122216092101c140981d8011810030321515107115180d0507992202c0304280c034059030070f00c035502c4500049010611004643e015a041c0e0b01c40707030107641c000d50307543e401c050070380d4902202c2500041512001c140400f0b034420180c0150030050618904101200f008540d681725007251403024800c01840d40e220389070b00304400841e00e003441e00190118000058000b540401e07100380047c00c024503140041d034001030908c03c3c1d401860b0300036000d0061004c200000d0072101049c00d9641401c82c6082508102c1e079010314008040c4155140050b4001a64081000460f0360502040356803d038036404013900041c1e11a = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 291425656 1250 291424406 291424447
    0xd1d01050c040312050a2708030c0f1509031902010b18010e070801050604051c0503040611060906070801050d051c030f0e030408060609040206041212030c081b0c03 72
    0x80c01d2a40c5031450340c02d06031101e410409000090004c100b241404c10743e070100710a001890b60400820224108510410b29008154080300c8980030206000c4081c541c0407411105003900c07a82100c0700c0c004002404481894107603020041c41e801001890304c00c10b80c42d40c00e003000207014000012031500441c0454015450020700c02003206040005109880c0030301c001a40009003451302c0155503040c03502060303c038032550203041e105001c2c8602d076008445140000d0150b455114003541c0d10313203075121405803010364004081c19240c00342200103544064001445881110b4036078a10007103074030706018404014040c8009a4040c000c4049040209100f8003074106039104955000950728014581d201c216550010f420169400400003002408400621241c00210488285c0b0b183c4d2980c0c80001c43c07034403c5511001c0c0c80d804030082181400700d21214000101b2540c0c170180890110204115000c040498004c2d21000000203002c4058181c24040c0000c3c05043d01145e10b000002ca807540c500800c017 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 291426906 1250 291425656 291425671
    0x40311160f170d090303030f0b061602120a0b07030c0c06330303020309191d1605031e0c0409060e0105040e070617060d060501030302060f07140d1d0105 67
    0x104200700702c51504410220500111020380300d2003185502c0181031000034400502010b88587c955483c889007684009010304009001c503655024502810f15407000808084e4880c450b0070580a99582e00895039014040d0f208560280a0b540c40c1001d8006254060502080007009010f81000480750b1250f5105036105141000480c02c2c1400e550f194001648034905030b05034401410000070760008203598068904854202c500c601c10703480d041e040f070ba007a03000c80c0c03003004800c021100712030900160b1401800001d0340c030b13040350981c42d8042c0d0316480151806404400300408652070f4000c01303a0b0355a0481e007020101c0c1d01d041d54400b4004283e40081c1c110800a41125004001c00c0c6410700c07401010540c00406007242c01e18207603000d080203051403000c0708118815800100701d43d5402d400c0d0142d0787c0e88003400304519612420000d55a81e000c0700c040d45000d6000c4c01080149020300100403004a81c0840380d0303c0c03c907605840e40080c1203030041ccc00100f205082e4610806410030b0041d14840c181 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 291428156 1250 291426906 291426929
    0x60705030c010509030c101a0604060f1407020904020906130609141006021207060b0d1a0f061005090102010209030106030b060901090213050f0f19050a051804031116 73
    0x28000090071030f60013410600c001d034801c201c16400148041060011403030203010000c0e400d10f4410038003d8420003a4501e07688800c0007d000f01c4c0107a000080c161103010b6680d1032244d00c2158481e13401051103445000ba5009042a0014006140012109a200c240a81421720446c50042c0c500309868403600215450b0340c1300d4a078016255a80d040255204908050781c00310b00303141c51030103501c0704115644410240800a85901840b855800c0030034141d10140c850107131307a140c43c1800040c00751003062481c1154801c00109407181884045280115030042800c94203220186098030389500032003400341555000d21401c04541c2e000e2203900300a5004200d54242441d0440400c816404140c00c2110818414031043d416010250f5a000640304140e52000614180c00b000914900d06580e500341c2c070404040496403c00c072461918012244103031103641803540c4520400154018070800041e5400c07040f80001c01280c403540f0001051035445050318055007040302c050010f00c189130845203c03100c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 291429406 1250 291428156 291428167
    0x3050c030d031a0405060d0b0901020307090b3901020c030304020405090303150616140d03230606072d05160303120c05090402160614011212030b06070503 68
    0x1801e102140c000303a15881c0030008404104000b080e40c20840280602541e580c0c00000c2c520384410704003c0d05135400c848100d0007441d00950f110f02030741c41298624002859000c0c00140c1210203002e07148900c0e024607209061070405652050038002452081c80e201c50514040854010284010100a1480da0103141d6070303d0f10380180026100d0140142c003c5a104004010703900e030696814000d00e050480b16680d483d1180e2000c00942443d0b910094040522009443c801c44800504005003480589050000b12291250040c1401d2020f59803012405400005140c1e45802c800410156108404001c1100903540840100310000b0403445110500818100213000c4100150400c1403011021031142d64190341e8000c08200c050b403032008610f80c4441002040e0f81c0510f00391000c40700040d108540b81c0c0c030589071802102e00240b000351801c0b403034034803004a143c0340407294a068490740d40d01000c2d02c0c0070550720f89684001f42e001003030405950f80c880461565859004040c2039015100458a03203 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 291430656 1250 291429406 291429409
    0x403030203030a06050d05150402030c040606031b0f17060301090602030c030415151424120f01051f0203360a050114070201090e010f1a0306360103050c 67
    0xa40300b9800041c03080446c540c080000882c0040c418402266141e151069501c2d18800300749001088541c10307a0050038158046a01c0d070f07165000380d03d9030204200042800c0350001081e10b0340550700401d03400196565503c0c900203141c00e03541503007111000c1c00020b44220070307480300003c9070403e81da0081c08100000a11050103503504035851004d51504c4200801c040c0342c407000c1e10f200454440c0a007507802d542d0070382041d17a03075103411000c060481c85440110030401c81c65610080d4800455814002041000315000c1501500040e041e243d024014503145500c1042248102d2040d8000710210312080140b580442070301145c800c4a2100c0080c001701c08540901103004801c0c4554080b401903540e00d100708956a07105484131003112020250b56035a4805000407101d494480d00b0182040001d07030000655020748003140e0f000c48860824071240036a200d4074030702c40342c80140c5402d82e00c032041c401412801056201c0c6045078000811401386420401034468070b9080c8240e000340d0701900443e0071a400c6 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 291431906 1250 291430656 291430661
    0x206010902180f01030209030115060f030209030d050705071d1006021c0e03010603080f0a0806030604080d15080d0f08060d21050c030f1305100f030f110403030203030a 74
    0x142a05560035810300c2c810b000003020408285030034038400c584004403400706174080d5040780c4100b6000383c000d10400310a8209070b5503c03252481210001484264680d41e503c3c03080c4262049242c008015208200c070720b403000c88603030708010000ea03801d008411300000c90414003005e00e80181d015404118442c40c120020701015805070740800150b401c146c10f200b14484850103a9558550710741000c00d0984480c4020078010f004540005014400c000340840000c0d608201a1150b8074485d512004c850340c4840c245a03c540d804d540040c101a03050048050a00c99900120811610b480042259940c1d03150018544100c03401120045540d10480d40d1150740e004030710310f601c00d005840f800c165112641d40e52010304001d2660305000b035030414035401640e12a104884049060404503600c500c07642c449070105d94010b81180040e800020750004490400c800c0c000c508054a451f502500c03034000b101600a442c0025480500d150354420200001f00040701400180d8042d42c001c648a14008148404 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 291433156 1250 291431906 291431909
    0xe0313051503160f110706051c02070c030803070302130b090406090506010207210b01030818150313050a020306100306050c0c0c01050d2a081302012a0b0703020406020601 75
    0x142000400030002400c1c143c0a07010603402103480c0452844c0e100c880116015941001c038107240340a000b10008203640d116000c0c10b124494181294090084076600e5400c034460b0980040c44049500000c00c0880c10b40d00140d9440115420054944011401402c810403d20b800000a000c0c011940d00d0302c500b0b261103000003804000c8810002414040b001039a5010f08d1f10501c06442d640c04514038124221901060406034002c40440c015616845c02401035081100359019281c58440c24081d9881c0c11144240c0c80700103045100e296850340518020b0f604418003041d28280b003006070907401a101009143c2c82a00100c499003816400d41c40c06005841028144c40300c00d0300144040b50b0701078004516020616802d01f8056a0340c02c0400c5813002404010004038400d1041c01e903026041c0f9006023450b00c0b076242c1d540d2041c3d26941c6000660200b545040c2003c0d0004810f6044090304000704a9141054149408000c440d44021750350320451100444280c0e000a402003001c2000c1c2d07404110860 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 291434406 1250 291433156 291433189
    0x7030e060a05070e131509051617040311210306030f07050609010324080c100c030c021201060b03040c0305070f0608190603200f01050f0412060e031305 67
    0xb00c1c508110700002c01840c10241180d04c1072078402c507190640d140b80e504c4040c0d243c03821280b01014903580e040e62801064200c681d08a41d14850203c9800503114249055404d0f8282c1c8910803a900e42d610308882c00c000103001d03880d5900c141070840c0c180b800f4040c0c840e002442980640c90b50707458100d00340360a140d840e07040d000113588034a00c00c0c8110341d0b030b580a448803100c00f0301e070016a0305070410083c1c0814003a0007949090606642010a0001012440c04000103040d143c2103903108580340c00300c501140000c0c001d0001a41030745144014a408a84035109018450006c2416525902943d243d540183c4044a0140d010b042c01c00401105010050082c540b1982801f98249803c80250084e2401410b46481d91442c000d15810359481b540100c015680103200a50b40481c02d040c00d074030121603542c51512801c50030070645004d44c441e42c12982050441c00f40d05060a20f4940024421100060115142600e901c012002400100050001ca01c8048564483c1c28030300700900c00c03521007601c0d002 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 291435656 1250 291434406 291434411
    0x1206040c12021c060207020d030203130b0306130b01050405040204060e0906040b031b0a030b01030f0629010309080f130f05010e1c05070e0717060f03060402060a03090b07030e060a 79
    0x565107100108480180643d410001c800243c0341800080c1303d0030360025400440d2003242d5040c5039001000d8070001ca0b055410398030090311203c01e03c3c1e141c0000c40740309034000001481c0201401e40c903000364040740810306283e400c01e919040050141c1c1c003e600f2190018201c0c0349243e43c54030301886020340121041d1070400581c071784000842e8454040c244941c4100b04035501c840016101c1d084c94500541c0c001c40c4660031540c503844c090031742d0094820191222814020107504260b081c1e1503109001403120210b5414102000041d4050701c00c9031401d403040d0f030061220450460303440004100142c541c0000e142424106540007140e80005e810450401c034080b10000c0b11500d078205e005100301c00740c00c40740e0069889031412a2805d965500700b850006c9140c020701c12010b4100301981c2c0145051b25000185584d60410300500b0380c01380b00940e07450350003074004c200982059401010154003500c4d001c140081f95446c0e400c6490000c1e104003000903681c034084148114180310700da4008036010400d = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 291436906 1250 291435656 291435689
    0xa110a03020102070b0f07060921020d1b03090909060903090902031e0402132c030c0616020f120403060f0504050c041e060306230c0a0f05091206040c 66
    0x1e6403240c01d4050303c1058040040d060006c90380c01000d4518050b8029014003d40800340b400400744100b40034401c034a85410b00c0982e0700203001040c200c2012441c2e6442080c08042d0b90f500c05800d12440c40154140b001000010645a801c0d00812000c640188000300e8080d01500d07008285400d2a440061001d205206012088000e10003038100c007586c5081d842d0403515140002081094428006c50299140a0809810080c2c44072018041c800784d20407040942120241c1c0e50301c030f01c142c41143e2510f4101a000030000803040414418151711881219400d2103002c0c0d01c0c43c9002040402107280d1a40410200200300d02130203044240c80441d10240110706207603450703503030b2010b03135074001c0b441240c44895001c08401003070f00000c65058150418440e19659090200040094100184c1001c045012501d02290000807050080710461003140c0b07042c2a030001150444040700307210080100400040e0303855928410005c5042007883d01402050400d4074103240340c01040e070701c81207005805194 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 291438156 1250 291436906 291436909
    0xa0e1e09060411011403100f05040c1403070219050a121407060e0c180f06030a021c0503130305010c02010f0b030d050d111b0c0901050d0f0507030804080a110a0302 72
    0x40c001d400c0740d0f20071400181e0800c1e82d030042e10040b60591615036220800720070031030000d0450f002981285c40d03070038907594102d44840034481951030a212000200c0d0015040b030400010210055901c240944192000c1001c4907091070320f50220380f00b0554580d4072102038041403081c0c500c01c1d8440d0020ba81441440345094000311300660007035000180c21166a0300348404d002c1c0382030001c1e4121f4080207102e0034002003a910400c0354460199150103980400000080041c01c002886081c19a00102000c801408002c000e0f000036000e1031085843d8003060042c0c0c140d4000113880c1401a511840006c201d1102d000002030843d0001c91085c90440d04003a140300464902264180c410394952071b00b03683c0c800c3d0b001188000b8080303224203c180f98000140800c104481040b40950b540451001d584240580c90108140d00c1d80a00440d98015031051501001800417903600030420710401c2540d41c0596240c83c0d130036058000c1d600140c00c2e030304058a9102005500d4140081010701190074402c0141540c0 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 291439406 1250 291438156 291438163
    0x4030c1e0522090303060b030705070b060312041e08030a12050708040b01061d100c0b0106050903030a03022203050f24013f060e010c0c020603150a0e1e09 68
    0xc800311010b50f841803100c0915109410107005000a10364142e03a84c14181c0d00207040c0da101003010784081c504040407070061f1402040b01441c01c1082c0c00d905080034180340b290000c5c0440c140c1c4d0000c2c04c15401c080042c0801061000d4096400c55494245006c1040c03166101075030001007001080000a40810001031050740401d4159240ca141100070410010722114503180c001809540c030401100c1d01e21109a400b00c2031240440c41341e180000e083e45c0c3c581c41274074030780940501d031541a0018080c88060740d105c0c0e4042c10b072800801c0d440c00c003800540344480c840d04c046078005480903005280c07404002c00040104000300c0210742e20346490640d440d01e4105144034103000d004a501100020059580c1007132941d801400c80c16242082c520724031ba02d117a05090020103080f14030343d0629441c840d6002041c46000e490a442d915614035030902c6508018050f0b0004040000c55501c140341c80507140c40b03106515024040052258903982001180300d002010100284c100340e40014040010069010 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 291440656 1250 291439406 291439459
    0xc0801180b10050904270c05010c15050c040902070c080105090a0305090d02030f0708060609011a0306090a060b1c110a14031b0c0d030b03011a010503040804030c1e05 73
    0x81c0f40c40d44c1c5960701100054090010b07a05c111101103199001c040707580304040151401e240c4030380b50b120785003966000151241103864030086c05040d4400c81d1000301d0398144d00400d6021040d910b000b450642ca0716085030490301306107010b49504800c14018000818240b040982098400e401440c040c025a54001c0040c420260818020305642855900310345041084600707102c10b00f01a501c03060303160103520369150822601c06114514060002520549da500c0110800b5a914011890b5a68031001d000f001600607000107031181c3d8469001580e0200f040252095200c0c208894200c003600310031010031341d030310301e031484040810401540c922150050000d18100702c400101d10b40f281c0d210480031402da0312030a4815110b00300010b04c5104160b001c914504800c1581c0ca08203c0380502030b0615007211448090311185041040d61070b20a90701410107164401d20a221581c581a169901e0340395400300c9a0040307400802c4440614414460380c0f400002500b0107070b407080500945684282d130100300c82c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 291441906 1250 291440656 291440689
    0x1e09061b09030708031c14070906030203180f1b0f060307080406020706020403111f080127140f0f0601140906130305030901020d050f0d020a0c05010c0801180b 70
    0x81e111900b80c07024041c1000a03c500f0068940700d1103480c0c080061903003000c8100c481c482c50102c401c86410322031200380d40541030a030340310460130381840e8040d8029400504501000013048000d10303020401084500000b0307500070042e200c07031524118044200c050301d6407400d11480d00048a5070701e07034560310290ba41c050303180d2a2500287d03e070f906080c0000d1280400c003804150001502005001c0c048030454040c0400383c824882d64030800081c40000781c080b1283c50000380c4136900401680a405910a042200c00b040100c100b81803540c66408940d800c00d084c401045254041203030f0301e03811554490380619403946290452030403000007410041c142e1004203020501142d48a000c0e141c000964050420804032000ca8580368240f50303a8030f810103403e150051107190b00249450f8450010303912544ca44881890a101c0e0302c0700228040d4000442e400300b04074402c050b1001040702400f4281c1c40003102e413580129035040075402c1d107000b0305a054181c245804c1c2154110541c4501125800c501e90 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 291443156 1250 291441906 291441961
    0x20303120402180a020712050705060109110c01020316030b0607030c020d1109070905031603020a030b0405010e060711071502060f10050a180b03010c0f0815091e0906 73
    0x329440001c3c00c1c600d8a11410400c010054200450841158021b2920501480015146800c501d0003210b86e84104400200302d600f0500040081946d03642010710f0040c00141e0490806116a00050880e00200c400e4402c58030341003c4013440c0e980510583e680f0000a41d06941340000c03588001d0b00248800400a000e841000d0010081c040384c0d042c0600310880080020a413410214001440702d599030041502c030b40079041c0c000d01d00e0045105d5860813654050101d18103d480c0d9103d1030f0a00c8c100400c00c0e6481d548a10441005a405210892080906440304501030b0300d4214038501d0b00ca02074004988102000f451004c07600d80020700c450740010f400c2102c0d1500d81d10000b0503c0002c07020351101e500005005004124882036601c1500701b600004810811030756640d04050a85a240d482640400c1041c0e9071000b00c2441520402da210364022202210240b508011600071902101c500c035003442e549e00040315000510341e8068002c2d00c0c00c1c0003444541020396811411700403038803400c0d50100c0c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 291444406 1250 291443156 291443161
    0xd1802040b0a05011409150d02030402181909020f060310080d030903090506031b0d1e06050603010b0d0b03060f040318050f060a090f030f050f0111030f0403020a0b0106090807090902030312 83
    0x242c41c1c000640c406120b0700d0321f0540300d818808041e0080e403c259000ca1107203030b003103c55400b1413440190840c890b0307101020b1807010030041d00007035005210349003081e6040415042100059202c00000707500501c4165480401075140c91a080d0170255240da880041505052031140400d901c00185401d8030400c0300d055640f03440e003502d001500030003c2000041c00f400416031f0345200f078060f0700c01c880c50b603500e1480c014014824900740301140e200d03010f83e80d40500c00b400140220018130025140c1824250760019015004100003450543c00f03c40c02414810300c0300c100300c10940d0061007507480107030700000300f500d02d4240400180321150044065000e2040418000d4810741300e0003c941c0100705030809100820381300d083c44000c203c140d0000341d80a100b500111540c560051040050b49405040581c0c110b40b02c1c0841d807044101c001e44150114810340312894007280356500e5860080407141c1701d580d0018a018140b031306060036030b401004070b185440a18005070702c0110840e114651b103001c0d003055031b9 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 291445656 1250 291444406 291444409
    0x2030402030a0b070c061407031a030a060b0a0f09050105010e09070207030201120f0203090a020a0e040c051306150f02010507030606020703140f0706090603180f02150d1802040b0a05011409 83
    0x7030340040b002d05564240040d071f0b11500b1640703030082c0c0141e0706030b68280b00c44001451202540c40c10f00043e107030994401000400403c0b865801210b4264005154000d0b480e9249080e2401100c1c039006a150156984010007a80d80c01c42030550ba000000e6440f016503240190000c3d40383e454070b01c006418014800d41a0100000c4c1d9032050788890814001107440303080c02e8187c01d58a5101040c01c034003d401d51003000c1201014114190b100b180e00c000380c183c50608200520410124050300803507042d8a0308004213001c02404121009481540d44840c0100740c00c0800a081da1300180c14002450718104050041580c0450240300382c075088802d110555100f14883e07480c1a020090f000c078640140080031411507403103a4004210740300d035a000d00c290303140844d9000c503e04614100400c03441840c4c031f90f80014188600702c100024a4024a1800c081e440c42c40001a2101d0201c03401c001940206400c0c1140f81c24407034803546450945000e030001d801d000c0041c055140010000116000102c0c010039507 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 291446906 1250 291445656 291445667
    0xf020309060a020717030415031a0d050105040317010b0f071406100305010c0905012a02040203100810091e0c030f061d01111905130e06090a02030402030a0b07 70
    0xa0030040c000940d18544050000e403224011300030318040303484143c40c45041c0c1c2c0d000000c0e103090300d4050014500741c40f4605000d0300240000801d02d0420341c050f03243c030b902035070383c516108080c0c501450010031580f4141c40c0003031100d43c506140d074002412401c018081c1001e8442580d024140d19007000d80c2c2e40d100c0e42031800301800b2041d01c81e002841b07a03004001700c440c001c04580c0c046074819130003404040404402612400c0c103038000c0500240d024002c1981001141d41013100509915a20304030b0309a0540100d07069034000c4039050441060981d04014024040000c200200d8200508000d00d09180c2c0c0c80c940e1860800ba14103020284904402d024050481040e600841e400b03080c65920741401e2505001911103200070340044d0018078125020120107002e1900c2e05600c10b41c00d1450914480348a03401d0794a005841020400117021030303070414a1490001002d0700049040ea9090310304074041011010005100300c0b5928014400c0c0300050f01c0c0002c500001540c480301c91b00081d610818125032 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 291448156 1250 291446906 291446917
    0x6050906041205010c1d090c0a1806030c09450204091401050d020a0e091e0309090115090302060d140403030c09081f0218031219030b09070f0203 64
    0x45800e060300504040150544c00300c0003170340703140c1c498a10360301e001c1d40e1080c149911081c1e01c6030031880345000640314002800042c01010f00c00d09000307100c101d207940d040d6260b00d1950032401c04203030794001440b8600c1d04904100020302d0f001060341e205509030700c6418690000c0d82a4121004583c0c6809401590080c070b08c0f4141e5100070504548880e9141994006400c641080b0400c41d41ca174000415030f401d20f00807a810650300508840351440c94042884020300c00242500b403035014925039044c1c1100702101c2804540c0c1d0280c011138a59800c1000c10001c2c03501030303100799480d00d00c1b03c800600464020101104a9070100c825a4842c2607803014940a050880005060b1649500c1040201909a448048201c04995034401c105450750203003a640e4180c454010703207803401d148001014226580040040c1c009a49400700c80d140400042403030312554031031a11104102040200c210003100c0c01c2d00c400c1400e9813400b400426101004621081005011002084620014800018020400c940 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 291449406 1250 291448156 291448169
    0x31606180303060302150c030313050709090807020910080a0314040e01120b06060306031e0a052a0d1703060427030207050303031e090703150e0f0d02070605090604 72
    0xa001a03180d140090040500e800b0403485a01032075000b00002c40c00406551103c00003070001c61039512424000200c40d16100400c403214452a80301007200766030340c010078521900c20256240c59a501c2d10400000b40780007041101060503041c4c04114158000030849240d5070075007007000c01c5510140f0701407030520442d00040c6503880c050000155025291210502c41d5000300040109604c4940800a1b03a03c02511810ba040c2d20020b845004442c091000e001c000c81030078204c4880102980c0d48900305812100209014614210a64416041d011440c8208a0300b1600c400c10301d8810f07922a100d44a001d1040350717031240c010000495549866000340c0054141c0d409003103d08140111020fa07001001c04210b0043c00b0302d10000030a0b0034000162070281e202e000c860144a4440700d001c8400060041140c215032052841c000301242e10044a51080c4504a2020842c0010b480c4c1040c0741080c01240c910301540442c42000003d035011503d9400d84945251007030f0340390000000114280a540c1064 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 291450656 1250 291449406 291449441
    0xd0e06090a0b0a17240a08031c0e01141f080d03020a020124090608010213031b09020d0f06080c010f14040503150411090c1206060d02030901060f0f08031606 69
    0x2109501e004010804043d40c543c00100e0703503164245c18020450714034032804503ea80301384070442c203204804070b926030341b80480800040c007824080105400d54008010340800900300b4001c0c00205c41c29584110b110b10359100b4a040c8642c5803034a01a5550340b01030710f0750101a804034101c00085d1003908400b6040301c105090201e902e0805919040c01003580c41200078007468150b0009004006009403050924004800d800311840c0d5218080d01c03010041880c0c00a060308803011a560340710780b003c0d128154070604000b903130030f0340d17a60b41c0401c6813000d81125125900480368040a681c0c072504014550446240c0200c2100e0000c0500740c1d0f500a94106075454081c6030074080b035000300d428169201c1c40c05142c41c1206628410f00b40860f00c5000d035819401740c10700300326a0b401c0d482604507080e0041000b5041c9443c0c803544d801d014049800595035003480342d44030f02c000c21081c0030054084010f040359501c036411042c070342070600d9980d2154020007003009600403952401d00000e40d01c0360040b402401c291 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 291451906 1250 291450656 291450661
    0x50c04051914060415050d0f060915060509060d0209060103150807081513030c0f0201020a02060d020304020906060f1803030912070f0b07020a05210d020d0e06090a0b0a17 75
    0x2d0742c0d0811003102c2c0c16008519101c0081d01624030151010111600a030000302c40000300d80350840e01a802420540e0300e141c035490a140000e004e4018241040c502890000b03045051500300640220064a590320980f0321244107400f40c1e89000310a0f40000302420000b41951000020400c1034029a1110906008107680002c0301200800c2140d0b03c03550003140441640c0e02c014051010003030219000d0001809031078007200159840b02941540e5005004039840c0c2e0500340e000480907404501410030954000c01401700b141004400b107904208100da006041c441809488003d1f4050142500100d20340400000d00300e440038011640001e201424003c0b84003107501e042c1d541c0364407610501c08645040301c000075000c44101c082d5125030f98010440c4511030b10348010080112910f8490f044864900c0f41743c040303981003c0120105420080d000b034201008040c1d0060102d5000e4038035a4000c0000f0025142c050b1380710034244c4107903144d10b007806842d012240070403140d0641000c1110401c076482d109 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 291453156 1250 291451906 291451931
    0x1b08041502180a090c050703050318061003060b0d08030a0b060702130e062a0a1206030b0109110c060403030c050d020301030c050f030114060f042003071704050c040519 74
    0x20b080d0040342c1c1601e10707055030380e1350340f40c064121074103090268002082070102d030000070b100300c0055030407606102e01c842201d40351811041c2800c0d402c3d90305030801c2800c1e01007041008914014190400d10403940c18900f000f56440e0b20f0700d54030000f8120001d4070341c2e804800001c1d680701d106681c020740c1c01820005a69100c041d4070401454811402c400501c122030000b07503001241200c00702c01d10800585110402903940d500304482d08856285801d00806464680c20315480c4d00c00e01006500907a4000710551405030400d084460305144030b035401e8020440500c1c410b0000841036001585450001007105005008451034040d200502c0340b218000400081800701c1c9038040c006480702198914042113400302058220b03201d1105248110a01c800003d4091900500007221644050404142c50300007100740c0d85003920b400c00840c81c5620200901c03941940c0903480e54030301d2105110144c09420192203066440821840141c440c0c0d854800141d20841c07096050111072500b9102070020044041c3c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 291454406 1250 291453156 291453187
    0x1180b18030114220f0209040f21020c0909010b06070809100305070e0f0f0d230312011a040902030a0903020c0f0f13020f13080c01031b08041502 64
    0x4100d01c0c8690300f410f00f543e50203015011481c0c0909801d800b00d003031140a03808100034111010400b030303501900c01c14240d0701584400100320310492050095145170790403403500c1074160040300d501e18800c425503883d400c0156000a210042c0b400111822580c48e40d61042d040c0c05000d0361902c1d03d03040070f000b155080030845050080d05810104550903040d200c2007a408600321401200c6520029404a0340c951a0707052014401c19002c601038007000d51021070102203600345c6402d440c12103a50791404110400d002c80d041940117980340140c059480c00d1807000f441d2070b040d0700c10300a0400200d52901101c0306581041b08683c020404140d0070b545a260200240004000c800019000b6000f40010030348149064448414030810042800c4003154412041c4500e101507800580d4501341c0c01c000c9088100d180c40d003c3e200d14544140107003011400d01140c141485020402241818189a5002c6805603030a202003550f898510f0b003801c49075580d042500050180c20080c40803607200048482c1d00f0754460 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 291455656 1250 291454406 291454447
    0xb040e0a06181707030c06050c0d110a17090304031707033f0207230d080f0a1e050103030509040b0a0e040b0405030705060108100f05090c01180b 64
    0x4003400c00403064a07118640b03070158000b1006106000b51a404400c185825000d0001c080c000e00d0a4441d9000c2e9666080445006a0747c0007034482012410f210981000c0c0500440b104200041600b04450716001170013031402c50058403240000d250000d0161001042078074001c0d03400c4410900c9084034040c64488980c8506802e800007256401814040301016811800c000f01500d0b00000403200d5100320110354007a0590008496000c10201004c603000312042c040548071a04820a9403c0c0c3e0103642d441e09007181586800c1c41829420810708006207030310542e004807148008240c0181141c1c0c1c1054142100d5000d401c4c0500e00340000c020305a2201c00b604010006440c200543e10003c0100098034042c3c3c403481c52a4440040041c00042d0052542d6404c107220700116418003038550340c1c107402c1c82403d0b084203003298000f001300720f8414964043c00e10b80c071100d0030040106003442d03000740d600c40180301500343c10300c11412000c409a99034a64181c008140c0c2000c80e41c2c0321040b800440c100d84158 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 291456906 1250 291455656 291455663
    0x2d0e151312020c0a09020a1b1a0105030f0601150905030a12110a202202030f0a060302210304090e0601030c050609030718090807060504061505060702130b040e0a 71
    0x100400071512800040d070480161002449903400328a800401c07030280d0b01c0090002c0c1004502d02082c4c0d01060340031054200c02744602c1c44a80d6034500381405182c0355005178081c0d0709c44d60180c101a03d030f041021450380e0548001c240301e1507220345d4905059450302255030101da014441c10400e0000d00c1600c5010400c1c0740b51554a80c10017000c2c62201d19a209400d03203014144040740484a0090501400d200490b40d001810700303c80800c00401c1c0c00404076240c206241c81c25000810058280c80e405101ca80c042c0b0380e03460030841c56085401140d1024102042c40c50011032104200241a1041003074800402d0000307820b00c0020300860100b501c4040c288003c4400000416010855203488420b0310410a406401003c131907142500d005440550385001c2885c1550b24000c240128090754010b1032401d000d00300c08280d908151900b00200c1d03141805001c0100f842c03403018061342d550038049892807501201d2a41c082140012210300800c0c0c04520540c0c01482c15621115459000c524401c40900 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 291458156 1250 291456906 291456923
    0x30307080c190e0406050a06021f1820032a060301030305030f070c0605130b130209070e031603111f09050d030e03010c050d2d0e1513 59
    0xa420700310204500401c1c1c4020010744100c441d60320003e114080050768a14003c2002c92810381e1080820001801c0b5000710005800044840000507182d485007510aa42d4840401032000d104c900c00070b000c00c00807130041c031701c01c10120700d03815110000d503070700f1035281c03008040d01c55654404541803150f4100c41710500003407002420b0203819113815001d90303049070b405466440c90340d80ca1083c1c00c006104000c21020034400b804c03a0725030102e0213074443c0500c01c3c8920500c24501510904102c1c034140f500070410703071988041440c180b0058940d650616000074040c18003e0040008070002802c0900d000e502d1a00c0d0540303100300109210000105144902c1c2c00c1d500307941000c0c06030741091400304850303445001080b04240304020318200100c40c031441e03d01030303d000e1101e8a848400a825510411003074000101d02003031307031070542206110380d030300721000100e090451050200d8030036456800b4030b1588a00568031412010b2503002400502402c0016044c1d09240c1c0c9890841d60100035001403050714280c1 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 291459406 1250 291458156 291458161
    0x608061905060a15090308040617010504020c1b0604031b03030e0102030301140121020a080a0f0605011202030a02070803041208130b1305010b10090320062508030903030708 76
    0x4800c0c4145070082c03001800802c090307030070182100219403920b401c0c50100451304900202007031071a0003520142005a03210a070482e4608110f00750488103811861050703104010f00240c3c50000038501c0391030110900755103118802ca0740040c14130300441d132015020000c1245210000e40c03a001044083d07a12a48910352400c1680f001260740380000d0240c0c9a050700c03181002103481d1f000ea02030010315480f80e0b101588450a2103511020b903045800c52402180095050000c2000180116600d005001600300045031401000070601c15030316000c0841c3c190b000011a0078501241c04a941581d00075007103541d03d0030580f90181c0c40341d10a8540c0d0000810391004901504140d0004000741130f0030036040c6c80d242d192125090b164902c001e00c11180c640d0b07140c0c546006078541001176030404030242c440758401440c41c1400303180400030240215180c564040340d0390503943d810f8152400b854104c80c2601221110a0883c6401e0340801009000d08002008000150f01c0020055108803042c3d6074920440c0c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 291460656 1250 291459406 291459451
    0x709050a020c0703060e0c10031409120a030203061507120306050316060f0905030d0c0221061b090405100305010c09031e02040b13060e010b07050d0c0503070204060806 74
    0xb80542c040b100d409403c0796108101007001ca402c050310b0f12104100360380c0429003800004650368080521000400d446040c0c16407202d1380c160b002ea90107101440544003000c181c00c0900c003140728098401c41859408004030740d050329140705001107900c008441aa0351491030410a03103081903000003400090a001001c5058100441c20f40c10403101da201040c803803800e00005844078170b100030026007000100301000810381c3d01040b4402c00c0c0916a156100905002c0c01404590030a820100030507040800b04854054030000e0090b40c4068240d000d00141d4041c0d50304207400c0e21400b4406507106041c8014030030354401240500040b07901c10340003000900c81d110015100080d080c84068000b4000c40c14912040070045c02c250b43c090b200030400900e0709040303000609801c031800d00b03541090350740d10b000348107401d10261134501614030b10003181d050000994440c1e03903c000e8a40d810003007010a000c88800c111082041d40d40007580240180945919503c440d6070341c90007101c1d50f035544c40301400c015a60 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 291461906 1250 291460656 291460661
    0x312061915050a0314070801061107080a0305031b030c250f11150d0510050102210d110304050c01140f07060522080a0306051c0615170709050a 63
    0x1c5500038241100107a005220941c0c0680040c500302042c5500d9a1051100380312032a9000c3c8180c1843d00c964106504000000301401d6542c1201002030748460814400044000b075000d0300340e40d151030110f50b40c0d620600f606980740701c1411500106003010050244504010015126a1142a98100c0c0f58441000c0703403040c1d0424000f01900e002c410075840004070303d4006a007415001c001c1c11200b2000110351400c0042d40c401d4101403100d59480c800d10071010115030488000340024030040440705581c0030700150a100400d903c000090000070204c86000240d004807186210000005441c2d1030181401a15164a00c43d4140001c42c440f01c1481f01081c800241c3c1c080b25a60035840d4104076040e600d03803004250241004a215100054a108250611030091441403045040c180c44040c04032001d07095803070350381100c0c2c0718291200b1a902d0311a00608440c5405070410404127841d00c2003041c012a0303011a40241d03100b21f0710700000d1003000720005090000c440c10104104515650210b20408 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 291463156 1250 291461906 291461909
    0x3050c1017040203031c06030b010b0f191209030c0204050f100603091e0c0e09150a020d090b16020601120218070201021620010201050c1e070503120619 67
    0x80340a188900c2090707070591a02640c02480602101d24040404207912032610740207131190764080d16280d06200308901c14503082c1c0107180c0048100c0c140103010f0781046050240030184004600b03400303102042e991042c0c00001c1e01d028560002c110003e040c3c00d0041005100d0315041e4021420500401c80540514235114802c46044160900c40d0341880300c210040c0841c40c00070b880388202482d56550306814041d440066074480c1080c91091b51904104100c0303940010030b4100030b5040f00000900d01025100c4440d484420b03404011f075120401503000004202e1700a0140041c02400100306440e14084a4021074070f03025003c4a01503a6210741c0194140d40c10b40300250481c1c40100e01808807412040340c40d8004045000140c141080d030190210000c207903000960b4903c48424110002c1002403286401648083c40240a54a42204408421300c101c1c48141c078443c0c0d81035903003000f400e40901900c05c2c0c40ea1010940c3d40d01c0c0d038040494000d0b00d1041c2c605074400d1010707003c56060500501d51040 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 291464406 1250 291463156 291463189
    0x6080f04022b060203090304061106011202040914100c170c04052101020a03020409050a0c080c030a0603021207060305060d030824130509012702090405150106020703050c 75
    0x14451400280e1401c1003124440032202c0b04818003071550700060050014510594a4100a580315171801000034040c6501c82400d545a402c907000621052400361000d020781d0340c0640b1301141811503843c1c00c034580d1135106580901409020030340c9608140d036801c021502c810aa8502c0c0c40d124004101400e120b0058942c41150001007104210314140014000510701c03060b03100d2121080d6140407282640c2c0700601e07910019500041c280281c010510805410140c240000c0180142094000e803025602600b42c4100c50804030000d004013940d07030002000740d50301130031494170b04803030514942d901c282c00c3c020600824101000950241401e04261045640642e180310094603440c03000d2800a990f0036480d00030308448145001107842ea520603840c2c00ca00e00000107070a1820003425030031580604690342d8000410079a542c0507001507a020800103070110786006094480e1701d049841c1c2148610160015403220000003641500455240e0450780542c1c107848264450104212403044246c4411 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 291465656 1250 291464406 291464419
    0x906120c0518010504080f060f0117060a200f0301090f02030906040b220f05060703020a27090608030301031a06210c04020418060b070b07080c04180606080f0402 71
    0x285402c484a07035032030070b80c01c006040251030f0946900348141090001406211582d000b602030184880f480701d09030340109412a0080070f403610000c481c0c0d486000141289000b207072114100880c2d51501c410840b45d42c209011005e036202040d034003011301070308240b0480c60305514045070030745845503d0080701c1c0300710040030191400da501c5903903a81c1c011902810b5071107001440421070401c2c118511181203c980a804e4000300000585040c81c0b40120040c82d01003014014095100781da40c1008480c14907600306004c0349900c607a011034401220a031035010113051402c104001605000100c015410380303005555005032070b82c4002e4240310b0401c081d00c000e50010303c2c0f4841804506008107001c0ca1034401541602da09221000c005000ea80164100541c04019040d000350240907921580d0004c105408426003099100d403249480460300925100c244400c800004c0d4410070201c0488010303001c3c0d174102d041c2103082440044001c2040d030285c040840c8040c00072410f94550b070345d4120b109030380c0103061 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 291466906 1250 291465656 291465667
    0x15020f0102040b070b18031c0c02070e0601030f110304080a080903030103020d02120c030f1006050108011511070f0303020a030f05030906071d1e030c060408030a030b060705010c0906120c05 83
    0x1700c1325550030043c2295030181803180209110003040c802408414040c2504110701c10302e040920048880040400056500c980b0040044005040c8031a500403000d0070005801541006407901405004501c0400b440c000000c00c0108810700010f420f14001a82d18071000390758954a5075542d01c030070700000c1d61004055000300b0061402400065004107500c041e114030340c180402107450b0400803110b980c1c2c1130b00b1503903080390400305034031071079004050900c0c0810b00d0354500300c404084d0f10303112848001000f010f201d40c0d4440350380c00c106640041ca00e00b0900350b0010303640d0030001e4968840341d0040340003030720b840c000c0340c0d400d407281c0262802202814090521510b500c9410b82e501c2070110b00c141c04400c80e200020340b00c0d0741c849071140850300d03a840c60501d034094a1701c1003600700540e40d5003c0e8443c5100340414001110300000307a07a01d58045043c001000d2010382d000a81500070301c540101150700b00700d241c0d450310791b00100c0034080783c500c0d0301d40940d1142010748001c2916218a20343d0002503040c0314 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 291468156 1250 291466906 291466913
    0x105130c0e22030905270c12040809010e130207030906090b0901081504090501050912270102030409050403050d0c0905010f030906060302030a0506150d0c060809120415020f0102040b07 81
    0x310902640c2c8641444d645550b80c035008106034003a10514000701a401403001210f0403240d80710660310012001e001c034a401019020842c0340280030340081c000280106054005900801c1100313031307038072000744070128182c4d40f0400b440180d0302c240401c400041c850f4900142d428001c03400c00c01a0751000803114106503628004403002ca0006000e003206075088201000507031218403440074214003031400030503d880d10038006498281040241e1200d00c508004041c00c4085212061441d10039220084201204150040f850341c00382e500000350340d81c0341c074082c04100b46c1c0090081c188a900400281f22441e41058180d8074104680301d614046044910325140c164802e5011260300c0b44500d00014500c2d481c0c2d0042454440c010b10116065400b00081c0051f2007042e01c400700c2c0d084001c031400102c504d10b507507403526244064800c101c2131085c0000806c8000ca800e00a04905c41d01229007580c80359503c000d0540d1003002450010b0140c000e07100d20121207041802101e09a40e1003007805840d02d442da0b603 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 291469406 1250 291468156 291468211
    0x12030c050c0d0533040204020a120606030204050102070503060606090d15020307050711010801050307140d1209061404050307030b060f0414220c15090801141503030306090106140403050105130c0e 86
    0x16070080ac01c8903000520315000b40710b11032140034040983d40140c03182d081c02c00292a0184542290744a03500480800240760740e080111948140161101003015010746840d00c8402c0c003440b4400300d9607001108000308582d0000c050f261840c0203403480b1201ca0040b90043d51800b800b030007180d405800c090801c0c0445840403030009440c1502400c4012a01019200c5a8031102c0d10020100001c158510801c1071507030040941c00c4008542c40c00e41e103400e25000c0007958a040078400240000380400015480e80d50b154600b600503c0041d000b44012013410b03040d2004400101c2e260003c040c80045541107048019601e44107040d48021884400c50030005200c6403084103085400030403586403004501c0440178000e0302614182115030143c3c6003030a0454100b51400940b02a0180d4400e00401807540e94a0019074116401401d0164a1000740030780354400e44220f0b000982190308190500c40f111000446011603240101c99000c19a902d5a80086850740d0070391b503d01c64000c0344201b0024000040 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 291470656 1250 291469406 291469417
    0x160f080402120a0503070b07020d210b04020d140106110f0c1e120d0801051008061009090905030d050a0c14131d0403020f030412030c050c0d053304020402 68
    0x200700d468503816651540c0c81c59014a0041f54100046024010001d804201000030390880f070421000c0c211440c004042e905100784103010445450700d0f11000300c4e4aa503811240d0480b22500288400d40c480c10321034034030400070301c00d00001500c00300d181c881c181e4001c1400c00110346548090b14000248104000100300010711480214142d201c40c086540d4800540c0d03030300e00ca80237014101003903401902034050441640140c0c020814007900c204142e5001c0c0b0b403540e020104072014100c801000c28112403205e50b0750480700300d4528000100b814002c0c0040a400a009401000e004513a07030b0000c480107591070580308101150100000c51a0b10200c14064052a0182c0800308940307035a41c5030000c0080301c0c11001240007801d10061105042d810311100c800610200000c61a00e46011559440c0850501c030103020407080b4901c40d000c1120a201302d11b4160001000039449a1f400e0508a0310384814008034643c0f0841021004040303118001781003a8400c8101c11154203545903003d10001e984003 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 291471906 1250 291470656 291470689
    0xc0114090d0c0803031305010c0804080708130302040e0c3d120501230d031e020f03030408040608010906050303040303030e160b0c1b09130515070305160f080402 71
    0x5202c003040400302000610b00c00c030f040d10013082c45680c0b1402c11500315010b02c11801c0420880308208004a002c503400c5403c4160301003ca10b40c1c0d460710300400d80c501c00c003c2c1c00003236015091080e0047c40040014030303c2c140900440d0381755016088594110450500d0001500240d10030f0010201004650780c1c011503031559030b00302442c5030ba11020030f202c00c4031026000b0407111030386d1403190340c1200c11007109030b1b4043e0f906468504104905032005048c01143c1049154805502c200400f0f51510074895241d50010003400c03a51641414a00842c84d43c0007805540006002c1c08000280c1a19501980c401c80380045d010b180f91909646080f00603140002c0c40c010316104904030110492000101c220041c841203102c00c0d2a5000c0036107150804040d407042e1aa10081e01c8066801a512604040c2d0482c80d40c600c41c2d002c6480510b01a8207059601008a015400840c01c00c000302d0313019008581314559075a141c0030281080318095581e184c601702214009009200007a006003812282052100007 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 291473156 1250 291471906 291471923
    0x703030516081204060f020a0e10050d020c06090c0a1202040203060406080a05010b03010b010e1c020d0c0902040914010e0f150a1d06093c0703020a020c0114090d 71
    0x141d519080740c40e900c034049a40700c00050704204800e1001902c40c01c204900b0348134013545040301e9150300405d058803046030148101d1183c40780032045d902403801c0b61031404c6044001c0d511906c84821300303034446600302c2e00d500032401400580c0b0028942940b100707041d07640c00603c00d01849074580900000f500010701581d00156105000300d9010010444003468038450000032400c6602e8109241c2518404841141400343c00281407205603505840801c14a50410b10507100040364000504058409000070f403003d100d48501140d14045500200161102803105200850410700904c2120209104070403255014002144002c2e0f000a186a00714000f60130200039200d0403000150300410702d42c0001c0055843c8207240c144c21142d4840300768006400c80d910301007850004034040070401100ba400c0012030031003404044800e040801d00c1d4503500400001c2440746000003015000350b000355410b201511801c06054040e6101c1d0103150401c290010103c1c1c1000c0c103000c01d00070072030303d401e02c01c950001 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 291474406 1250 291473156 291473197
    0x10030203090a0812041104050903180d0606260d140702030c1c1713150c060501150809010c050d0905010908071a01060c0b060913020d0501020c010c1107030305 70
    0x4003c10f0241c8001c0c4d0200165200d14241031030700e0038800c00c070340307a401c0e001d24200820010107200c0403080c0c901000400c25085160b00540c40040c044c8420408000c000320b250040101c0c20211200c150b4070307044841e01c90042d40078a81389010750348180ad41400000240300c0785002d2990100840601019480582140c0b1864001000201002c082204010081169180e00020710840c0b601094079907002c510f019180c401c100e500c0c1711074540140500300c50415448110071440744034034412814107030020713020001755071101501c1094588240e1184002a081740100d498014184604170410f00c0e2030b00d0f514070705000050550007404440000b03640039581c540d80400401d0a4800074041d5a228000c1d00c0c010300d09240c407200010310182c2005c420040c83d610140001445142d5850f0484012211903589541d074081d200d82e600b00000c1c00035003102c1044500000c01405402424000014800074814103801c1d94045403101b160840822903607220403010004a40900000d058200c0900c0384009443d = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 291475656 1250 291474406 291474413
    0xb1c031d0f0f01053709030b0f040c150815060307080f1e0a02190908030706090204091e05010e0a030806131b0203070c090908191b0804080105011410030203090a 71
    0x203d40140c0040445c5503003140a961201880c042d500c040d1415081014040303085880c0c00d10305100040140c2c211398100008501800920901f0a0043c0502400881c4412078020001c0000c0c6080e2110581c8002c20b039030b4140603150070425203101c0e80340b80d6149101581c2d0680b00414580b000303086450480d01031790360f843c000d0b21840740d018814203610201580d1844940c0702104040c0001d4000c2c010446401c506004401c804070031600180e410540200744060b0500019006101210b0010100aa8054445101000d40401000007401030000700425241c0403c95502d441810000600081c15480040d031540340a0308075021681131104001000840381d14240c0042d1440c0c0090800344e480841c4610421440f40340c04c00140c10200381c140071000c0700740d980f590b050090a140c080e0300213400002c03040f41445444c107d0340c150025000e0300d1001d00d49081c0f0141540c0180100003003075080c0000401d031801000d2080c01215405407008a01000b43e02c03084000703400c058140b14250050103241c0010 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 291476906 1250 291475656 291475687
    0x5061f0e061303290108101a040c17060406060f1232090c0d080a020c0604170601090c0f110c10030606021b01020c060702040b1c031d0f0f0105 63
    0x41d501c04c600d8410841081d12541c540d0221010204d01240041001440b0000000c01c1c600916105000007054155100c9040304143e080010201c0c0c0051604046e5202c0c564032442d9040c0024140c0241c1016813070b080c00380710545903d4003410001c1030340700300b20500140c0300740d5001e442007001c2070f000619441300610031080c1c4101c0c42d0400280e10b015841c1007010f604a00300e4039801990140042c012061003402240301d0251014029046003004140d5121880c001d001c1811601d800038856581c458881c040d404030f0300008a4482034510842c3c001085190240c442d0b000f24004a8803400d20805480e201103815a24060401030b00340038001060b80d0a4803079aa0751040d00c0c5032601d012034842d080c00740003844e100121881a04104000c0c1c10f030344007641c000c00c040035403034000d171200e50303540440d400450003500701444990341000d503075401201c00c0c0300d580316000d0b12035110303540c0c95190304000c01002e100c5980348901135034030003a151403e5403180b400869400c0704900c10305009040c04100203117200d1 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 291478156 1250 291476906 291476909
    0x902030d18170319030624052101080c09040f26160201030b0319200603040804060906080f0c0313140a060b0a0b1b010b030a030e030105061f0e0613 65
    0x51540080f80c04800c00107600c04484008000e4603007040030518080d074001d0340700c00031f80300818410340c05860001205d2044e0120b40d080000503110300003c920040c10340b501480244681c01c1e85001d503a520200b0380c509100c03040d0180c0e030889102c0880518980b80c4807680621030707601720003003000b00082041003a980070141c200d248542007a50901c050900016042d28402c5061f00d100750800618045001c0e01501301144c0799410105030825200c0c0001110042c41c250380009174404004000c010402007460000c0c01a02c0d0701d942d4107001542d40302c40980300d5076020741d06011504804c0c800038140d02c00c82400703103074003170014034076001c3c842e4507501d40d103440b00303885070354540142c002813114402e204030b40c0070b02d120700d00081d110310b001d4901e0208040c4940c040c4200e0182d202808004552580009401a00c00741000500f5907440314120303d805441030480c0c200c02400303542804001005407424980100903503c5120041d950003036408411100a50704c80d05140d0b01000130f000781c01c8940001c000d80c00 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 291479406 1250 291478156 291478199
    0x3181501030f0314030f1308040504090b090d0305060a1a0f040617010609050117060d14030403060b01020d0c060e07180e1e0307023615040902030d18 66
    0x14240c0b40c0c01e00307000707018851072551001a044100144a2801c01d04004a81d1100c20300b451400d6005180c90300c040c680c42141c0c80b5950143c00c103003420050141e042600740c009c81d40d02080b1051224240426000d0f10401c4400d540d2107906484204807928801c420001d19840041b6a00e2a22291091403803031900603030464400640280442840e6101803040e42d1b0241003179041060501d0300d00030008240940000f0081e00c04504680414030544603154041a4203a001c508100c0350400204c0c2183c0e00d40091006898603801c00305800901e500224200541a400d03545101105103284c5030100a40481110724001e886012000100720240c2a02c03812104601d4002142c1c0e2544250824039010500090740c0080d1120403e100d2a018000102c44805a0541e001c2075800810306003444480401032401240416124402d0a121400e050fa14802c16104010301021483c0748280030450700403150094141d4401c480124000703004144140340d0f2a140705610404603240c004101c0150f8001c0c3d000c5 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 291480656 1250 291479406 291479423
    0x40317040503190b0a0b03030903010507030e0d21050c09091006031a090610050d020f0a09080c03060705031801060f03020a0b0304170a12091a0702030403080318150103 74
    0x81c012841d05126480b6000d4005015070081105a00c52004000014024241c0d090391044680d52030380702403058400140c8001c00800040c504400c001c1e0140c511128032078514060107104039001d50040411043c0310031007040e030096000040c1801c0e402444094403544030724006210b083c1d00c0740d542c151007920440f049807240e15050b1400802405440751813014038031101006020700c5098880805072a4007150407140c1c003040080514094a0a02c00c0d100d600195500000e58514106080b00041c40d60000a6072020507030390b41d505019450710425000c103549a04403034045203040e80301e103000d5900058080b00f0204021030741c540f10780c21a440d551000581d40c00422041080d8606410500001d241d240c00b120324510b4542d0b01c40ca100c0703c081507111110f442c007103452800b20b841003103004000e0f286020200611049800c0c848a40c108614281d100e040358040081e091500c0482681e0440740d011115078256201c08030001940c3c40050307403102da14400d00183c000c0716600050020300850150031136 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 291481906 1250 291480656 291480659
    0xf060e09030c03480d020c0d110f0306131203051e04050c030d0305150319150b1509040b0102032104141507090605090a03081605010e03090301050901060509010b07030504031704 78
    0x981c00c010b6118085010764200003261a5103846020090792030035070140c240c5e07900b61005270025400c1c8109110b000c0e01b40c80741c1e004003e11b1000d0404c046600c24003980302050703117000703141d0103c05a07032040705c0101011054030404d401d0b0394000700d841a049441002500c044640131404245001c0701040301c4030000e51030318144140c50340003500020074800258081d24080614a1032454000d502030401032804501e54085038040000d41e0110100c8600100788680e008580c180301441c64000304401c501c11441d0200820032580004101c56103a0581c017441c0003030b401900001c0300d5240d0001c0060f54a0030b1080300352015542c090043c90800c149928024105081503140180801c01c66000001484010042100e8665900602a00700da07440b6000e10707504d032244c3c0041082c540d00810014503d6081a10031107289101001401b040e4009800800c020341c2c49103405401d0b50150303c9800e4101e204d210060010780303034000c02411428041e0030454a02a0f6079501c000a0030320501c910703065407802150 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 291483156 1250 291481906 291482047
    0x60e0a0b0a09050601020a020d060e01110c0d02060123010e130603030f02150c0c010905120301090c031b030203060114120709050405161209060f060e09030c03 70
    0x11000151842c0c002c00c01961608000107903840780301c1c00d0040d125042d104101e00400010b07800c840c0840754104000d0201070680480d6014940000c0c2608509026403421951058030004c2c126040750807400a22030341002c4029002824808030004034100300d00c501d9565001c0d2a10481c900107850220310004e48185541070003802c0c0d0034012a0a0215000300445102d0f004010760050f401c9102c2008030b5980308040307145140148203481d401800ca0195014119401c43c440c00914100e44000d038041c003030000c2890b01101181c07005180210f03203141c030b0800039640070300c6580550361002c0c040c146030441418800100440340c0101894014464203002008a02540142d5100c0140000d460078811802c2c2a4051350705192044c40340e808111120003502091255500f0590200d0742002080020a60448003840680036502039200815020000709074803d4000007110076541c4000050350034199021003180000711034020f080e84907001888100516842e0004441c00310440c142d9503c001d941d00e40 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 291484406 1250 291483156 291483169
    0x170307020a0b030f090307080703030209120d020a030801080a21050405150409110f0915090d052d151e0f070807260606040f0621090305070312060e0a0b 67
    0x200f041c5d50741c0d003041c058080094402d00581c1c031142d516045c0540c60358164000300751403000380030030b803440f0384995444100b51503004190340d510341d070296a480c1c03203a03a20340102669421510500038100c1c80d10214800248400d00d40c0d1940201003880c000e031170f00360340c0e200240040c4009501864020000030302004480214821a04890f0204401609003044046210418014101018005e003910841c3d17025207045038084580c2500020445102c1c2040f5041807550b80211104090202c1c0000380d044200f400c162140141c40510800180f624020450a81019400c0500031880155402c00480c0c0e5103086e100702988200341c5000704041520704102e000b05109405001d0105102e15501d2000d60b1030652210f03040c3c040340d1652100040d4540001145440c0300d1944809103800039980e0205526a0000418503180c420141b004000c1c03600c0c004050484244d0800240842c00030001c41d00080e0040768418500042004001603032544da016810400604980c0c0360382990f694010340c1c03050f24000 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 291485656 1250 291484406 291484411
    0x11202191e0e0a050d0314030703020c011a060a0f020703050109080910030b06030a0207050a0f050105040c06030c080f071b150f0504050307061e0603290f01170307020a0b030f 77
    0x900d05a031415454801041c2c0d083c2e0280203050140b91850141c0d020300d030152803240c94001c80340c0152030792480d044a0041c0290010640380e100b550070300c002c0e0001e0b0341c1c01905900038040d00800d41880e21408003020380d03003021403240d007a055001704030001010071020701c180100180603141c140d03074400b145020803440d01402c0310060281440c0c213040b1201625640183d80d40140305040060703450031a41842d03842c1140b52000249605003504000c0d08010064220340d0149204442000041e81c980714282c0c10740760000515070004503c940042c2c1c001c90161050b98110384241081c070022070070610301c01500c5100c400142d600c0a1207816505035400244600e1510b0b0701e10801c01c000508040c0c1d2140d032030b0b1060480251590b5240c000301d0f00e034100c140c0003103181e80612620401507660741c0c1c41d12181400401c190050350743c111000701e01ca140611034025116245400118039030341e08010f6103003031500c3d0300005004648414040030005803a4191070341c001e0050142c0716034491600604114921400 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 291486906 1250 291485656 291485717
    0x190b04090506040227130f06050a120305030f2508090d020a0c050402030604060e0f010815040506060111010222050a0504180f060f050109140115090501120219 70
    0x1009003c05d440c261480c005100300304081c0000030420702600284e84229042c1084040d00d1400c988410001565071004045500598040d1503c0d903641981a400c03440008015010500420004602021000c456070707111205410382e50007803813a9051091000252034014010a4244080c0010300c0300400400c002c03507005100805d98210280d60790900c007140c601c2118001c2d40c0120100e10290b41d01e81101001d0201c01804003210f150102480d08032000c02c1c800d00e00503000ba81d802d00b1012000d220340b64842c80d0044010182d58445000464101854100045007550700b40034030100c024120211300e10440990300036900c0d20341040c1c104046030900e54481d41c40342d40b030703c80b503050740c034900c0ba0b44d1401441d040000c2000807407540c208440500f4424075a810840c0c507000000c900d0b01270541c04400010081220003450340c1c1c031802c0102403080d21201003404107c3d00c550402007580318502100b0365441d212030150030903e4062482000c01d406443d1036006c1407001543d100c00e40006400030721840312 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 291488156 1250 291486906 291486911
    0x2010905091b091c08070611070209161e1701170d05071a16030e01060f2304110c0607170103030302160515061002070302031902190b0409050604 64
    0x20942c40a01c212162826904200c00d40815140c1482e610a40d0b506445000c02c1c02445071880941707001501503004010440e8018944901080c00014100c01c0c2c46803d0750162905c20703e03031941c1c200c2d00035041e0444081001c000070450019041c1006103003c02c1140203d4986601d180000e80c11602e010780f058000e026643c11207900c1c810813110020750720f0342c07480803800c2242d69066242060108800403601c2c1c585a160800305016200760700e40f84090020200d40d0782084010340841d0303248d0903039060f4070607c0e6003565455028010f020f6001c42c00d41000003580e402d8070540b0320030b40100e41540d100300c01014080b5404504e501d40f158003801100d9019140b84dd0a604240180d4547c1c07542c5841800f0140406501003030401c1060306d4a110b211308075411100b20b960100c5042c80c4024860720444a0310f00509030260303440c01d000d00000d03400081e41d42c010094003040c10b07a18407030080b0404441040c0da004c2d40002192146101400b12203000e8400780d00060358503401c20110001344c1d01d010740214000c62 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 291489406 1250 291488156 291488161
    0x3080301091404050c0f15041e05010e01021b0d0501090804031106070f0f06090519030f030212010e0423150112020d0204090311010204180c020313090e1c0203070201090509 76
    0x5038040740445c042c660456065400e032003104003041412603030541444175004000340c0881c1c00110740d5442a0906040a810444a07486030300441e401d80e414103c440c05680984d0a07280e25176a00c24100d4100280603120103c03801c01600ca490030758480480a82d40714000003010f02c10712500c1214200040310540e02286000ca140c2e0b5102c42d030841041014090b040100c000c2c50801456400100e9034a8004044401d0784496811460074039007800c90490118450400703c03040d15010740255002c2406102c48000180c0c64265000c0f40e824008004890244090800511840d40c40454645080e0b10314002d12100f4803500b4400461107044e04650080320307070308404000603640c021402c0510382e0305031008aa680b032940b80c182c1e00010f8031060107099500200700411030001c960f0200d10700e9901410107011440846c0c2043e0b890303205500c50310b59104100c0d107003440701c48045c0d001010f44c211854120364a0000c0680040003a0300402c2c0c41c1c00058000080000035503038014607c8010300f00445681d40b0b0f50 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 291490656 1250 291489406 291489413
    0x4090b0a0e040c09020c0307020a0e190e12090d0804081f141f05040606020d080a11030c0a050c070605030402040b03010b030c1311130e0a0b030312090102090a03080301091404 77
    0x107503991161301442a000a91105111814016658660344c090240080e0940311607004a25240071600c40c10321030300e2400c50111300d40c181d00441100700019000f5008007514005c0c4881254005010150060400300c0150700048540c4010001000305102405a11102e1071080f9248801c0c1020002d80500701301d018030811400100050300a1302c074021801a0b0b400850781a0f08802007540b2840c1e00c0361814000140c0d003500461302c802240ca09a503610156074614001c0800c40310b00851a0261400a000003640c00705103030b00030302c80042107081660502e0f102c0e5000a180890903000400069400b1040c4011420540a0a140000308600034082005a82c01180d61100c41c20381c07181c07058000c0501d41500e50990340c010752400f12000d490366514405448501841205403180c91800000070380040d248801900c2480c802b000003c000e5850805400c646540800003d02800c4a40d542004420801c1d512111030000840c0701d004042d40780e616040c03100046802c1c6004d4035807014204000c10002 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 291491906 1250 291490656 291490673
    0x250521100b130c05120601121b030c0203070c050105070201140414150a08070305060a080712140712060207031710030308160c02091302090420060408030d0b031204090b0a0e04 77
    0x45100707045c042a543e07100048034a12903a481c6803000c1071611782507081030183c140f4910050342498405000c0420740c7c0800726507a02c03400c03402804070101500309105546c0b013040140400c0b80141760071001707a541c036124241c49500a40c020010108030b030f0708884550801c101d030413080c4006509910304010300ca034406400400700405c100304042d51400011855130b2a1203070303030700904400c1e0100c9130103545803910742c131080300800e40550b400821464809400c0700c0000b214020354040012060640f5021394030701000c1d401568080741400700090104649a6810340f1032840b41012541900c0c07018611305014050203000f8000013030031809240284000c68100480400b01641995605800e540314896207050300e0580320001d500080c030701e05220500865a4480388a41174240c005aa12110101081964480e6209044560300107000c80c0b141c015080c2c0c4068000c80c8040c00f55040c20580100283d00c03980f140d08000a41e42d034449110307840d420808501c00c054901c5840e00e03055400c1030b482c6c1011 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 291493156 1250 291491906 291491917
    0x60408100b04060918110d0201210f2a03020405061605070305030a120605220b120303180f03040b0f031e1305250521100b130c05 57
    0xc007a15500d9a0300036840302d910810040c4440542003059450356801c40c022800301910a0b9510048440346039020720344058000000d5078140c40317030301c9401e003521380718202c08480e004003001c0d059850b2030303490018002e4003c51300d012001d02c0720003050901c00309140c00c2c6100708510100401d48144402c0c003450f191501100c44601c8545110742040910f0701d0f0807882e00075160001020340c000031800c0030500340c11550962554070986002d01201e034032072042c41191282106004c0c01c4014016140840800960040300e203068003610801010503540d412614543c82a201041c42a03200702540000300c2050140c00040c0092801035440d00b4a0a00001418006c2051350a41d0f000c0010110b0480119000100c214a0a40f0b103041c44a203400d03a00b25240c01b0003074030156214003403c0c41b0f20125904491040c074410244195000d200303820300003440361074049522140500249044001c0d0b01c502d081068909925045c0400300b0b00c03102c50000e11907a03060b1002070300030031800c10180c03501d42a001419900c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 291494406 1250 291493156 291493183
    0x20d2303130204291c1205070210030b0114030a0b0904050c0a061b03050a090801050703021b010504030c0b1e15030c0603010303080c030606070210090326040b0304050309030d020a02010e060408 85
    0x4070244001c00c20011601034018006244806c030816415003950040c0c007900400c1d0003203e0394040c1488840096082c0c846449601d40084c95031141046540d07000b2002d141c01081140001480c103c00102194040005807002c0e24640d000c08819034040c9007a6402e000500140d28004c140c4503002c221084001c001141c0050902c6800305848145520900316600101040802404035080020300603009500165030769800c00313883d14000c01001414000c250107140d040c0c1d2003000201964503078010041d40988401889a1074501c034201c45040c0b0a040d900401c00596041801c1c0a4142018034108041401d980580030500c0100080794100d2006540160350354020b07541c2c1c3c1d8400d0001002e9100d091002580b002100c2ea6440d81a0381c000400c00c1643d2254104080551000c03410482c0c640ba5a03842451524003048180f10000301000a03680061080080303030f080441010010b418051003616103801a8030410f26841950f078404000e5201c141c06035a00c2c2c1c0b505040c030465a0b03d4402c600e1194 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 291495656 1250 291494406 291494419
    0xc061409071a131206230106022109040b040f2306010206010515031e0103050a0b0a020405060922020403140c0d0c0509090f010e01060504050a0c020d230313020429 72
    0xe000c5c2940040c1a401450181894030074051110044490401c1c0a1100140715090303881810310041c51562541980d44a602070030320002504200140082c0d4044d990815240d10414a841c81c45000e40f07800c2110301205802d44ca070b56080c140394202c1e401450b403030441d801903004115580f211010518440ba03540e1005540b0341c0d0304100c07a4545e481042c030110750007184000000c01d0100109603c10303001d2240ca0304492070f803a03811868081c0d004a00400350300100810510200780303804070101c00004510b40c0104807600040701c0b1700003260459030040c0d61b004280060101079900601c413040042600329072a61850250b0f403101001040503001d190700581a4001041d8800700c200000c0904840e0b0100070f2184000d1485c000b030186c0300e10b2203164003950901c000306030314811502441d0f10354030071540101f01101800c4002c07214205054120307003c0c18503c02c0455000c000e0140214400c0c0d00e40e03400408800d80303500c1480304980303060301d0030705010030701016403403100d40d1030a0581e442c0e140403100d5 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 291496906 1250 291495656 291495689
    0x903090132210c0a080703050906061e130b01110106030b010b0708070213020d140c0a0305060a03050d030209090a200a020102090d1101090501110d0c061409071a13 72
    0x21403004944480282046071584010801c03100f030000020600030301a40d81e5035003e078a0340a015402d6400a603496103003504404c001411a0a185264248000e000080c954001e102d42010030a07a4030680c039001800c58484645844d10b5030003040000711140c0d444002c0160381c0c6107840e06030142d10103008a1501c0703180005d80c03509000a200a8030b0009030002e001c05103d4040b04000d900a43c010800143d0450820f69483c007400202c2080c9407040700030100383c03443c2600a050480047c40e0040040364000304000c000b101280080100d0840078090391001a51404400300300122104000e0540c03c0d400d04149900098034070a5000400d18180740c007005440300005038041c0e004e4000e041c001d030781010042c0b10810a101d5100b07440b006090080c0c0303c2540007501d4038011a0360701300040c180c40c2c06510034115030300041d109404009200703010328000225030521404600041c14181c2d24842583d00c03102d030501c10b00301240040c5000c002d60a5219140c2940a00161110306461103814180c244402d003 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 291498156 1250 291496906 291496927
    0x17041b030b07080405060601020d02150714030c0c071a12061c0c090b0f030a030c03180303080901060626040212010207030206160e010c1212050903090132 68
    0x4100003540d8803440c41e4400d4540300b000200001421181aa814400c0002150701540081189079044820340e0140c141003080c6e8084200140303025100200308000310f84d08000c0c00045001a6020307440c2d0b102c480703a4415035054003031704d004040e0300300207001d8030b10800810b041455201102c043e04c0240304d20610599170000040c00a01c18442c00300240611203200404206001440d41d0a84246550402c01c1000003020700005101d07030004650560f00200400021074051a10301020900c246494a5032000018050800c8001903004801145000051051005003801fa40303012700381c9850640c03841c5400c00c0c002d4907490f0300d5003000d01d9081030680c04070381503446414100c0302810380c1130000e540e125210318000350341c0c030021038400724038518064610030360600c5800c0107904260140e50b082854041615213803880003102d04e01c4c0c0e083c04044420b40a0244aa0007081d10502ea200c1c0550303210402d141c00900401038181d900000135101d007000011610fa00702d4480c5401407086211038940840c01d0 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 291499406 1250 291498156 291498203
    0x91605271005031009030801080114190605040f1d0d050d0b06040b0406050919080c090c090405040b100f0b040b0307050c0a06050402010327120509040513121704 71
    0x400083d0540100e04ea85003081206030404410303684650f450000c140c0e612410f0500303c61003507410103903442101001c03400b00207100e144884c3c0440d1690000451303a80c1c550000d01111001c0311000351260b104d48210703152007900405041c2480c50f1001070400310b2801a0001c045201d031003810780f4481c3d40c941140315030340c4900050b5400342004020b141e6a5584504e4068003036080044024422404c405101c069400349172403030030413a154140100618100c0e40108616150000c0c0720181d004018005901941c1e0b0f02d001c0e06009070b016a080d1056810004062115216141c02121224843d90410001c0b003106004603421a42d40f40d0100f600d0f5192440100e440c0e1241d841b03107403424030403200d04d00305103c1c10741d00c1140120b100362030401c81715054064440c10a40210440c5d091039024600c00b00100d0064140f10b803410300741d13203051464003035603c0025049450031398411901c6850b405940c2d00b003241c01d80c209000d8000d182096030043c011561001c82820300100000d1a1007000c28000020b148000b = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 291500656 1250 291499406 291499409
    0x2031005060c0f010606091505181806040c020a03120c090e040b150d050c0436140f0a110a17060a060e06030d030b030a06050916052710 60
    0x20805a0342c1c040003400c0035607805101e0f01440309035180440000741c00340100c00710402c4071181051082000c0e409075055480d07030800308001c0007001002e180888203648445080307494411454100c2c1e924201042400110713188072089405552140c100080442e40141c40303210892000c010200304074041303c07011a00d00358294040c403140c4c120034050004124810702c41034890540500c40c0c00d0398003202d0381044484504100050603a8001c03020100389410150895011616071000070b141c0900050300c19112080202c440034841402c5c052024100a01d90b080d009100aa45c001401c429000d9070040ba2120404039005041d500078401d005060344490b400140104103c40480081c00090f019858a075030302100d45141c4645803100110f101584c00c541c02d400b404014000b07161400301014243c004028a8034419403503c203040400002854501a191061b540b640240c01e07404404009007854520581020b84210b00c0004840d105194141c1c418900d13141c01c050407051a01c0b10329580c000b1101e40e = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 291501906 1250 291500656 291500659
    0x81b150409140108120717030603010b060d1a060903071503140a050414060403080a09050c03161a03060603040204181a09100b060901111515120d021002031005 70
    0x2c141021040340c1020150a048811000554250031281450011507200c0c4540041404c00b40754440520100f0401c080d5900140282c0001208002040040c0043e0002e400c018015911020201402406414245423041d42034a0003410031082c08006510785419008080d039030200340040050041c800d811a1180302402d034100c0ca0700341891f299000c0a808200c0c2c00f550b20541d0512416811000010308070b101d103030103a441d800c7d15104d06400384040c2001040560380c1d40b00d82460400c2e41e9400348002116846040700107040941340045001d04420850941f01c4407403418010040d10703844140c00c5070390003076040f60005520305244281484220640b40082c11801032800c0b1032020349003940505000d02002e001300e42968402c2d9a0100580d2020a00c05030002014880320384154000da40c040c4030005480140d5100705a00021443c820f04220f612000d4035082c1c46100d201c0303040c01403100c66036000d5100039015030110008065603505a12102d4104182d0000020b42d1515040d00b0003c040c050 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 291503156 1250 291501906 291501911
    0x110706050112021e03070314030408101d150105010f05120a0507080907031e0606080609010b0f01051908250c06180201080703020a02030415021006081b150409 70
    0x31111542090500c00342c0d403c84c09003020300e042000000c00380c208010440c10081c000c001042c1561740c2c04181280c03000d04107003244000c0c003002ca480130b800e01a81c1c00a60304001c2c0080e81d5001416040c0c424224500c456010b604400b00208a400c0e443e0400d17410340700b0a0a043c8100380780100122818425011400024105a402c1c4060145a90481400784d49182e554000d25143c840c1c00c56241c9015100060940300447e42c4000c00b00c541031402071800c1d00541c0002602691280802c0c1011011100109a65512145021149040902c1c042116000c1ca0290f003451421a4200019030020001000f0b01240100040300340c422881450719003450301c40b4014154074680740103400c950b101c80c000c541c007505000c10104001c018509039a02c60303805035600d0b5090388a5410940c020740c4904170031704c1140001c000105a0018602510b08020031583c020510001610750550440c0e0a0341c01c04140ea801010f40e40114100034071a071510038034121440d4500e9903c812200301a40700381d9001000031030 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 291504406 1250 291503156 291503159
    0x903020a03240617010c0801082109040513050f03040e0109092f010e0f0105070b04060e120d0e0d120b060915070b010602030f1b0a050604120905041e1107060501 71
    0x84d0101d04103202c80400c80024400003030203943c107540700381c42402684256840400d0b080c0f05503400244242a14004240c600e2400c0300002c049016100304940341078100940d04000c2e402c01908001e184000c1400c50040d50620b030400c120901c000030103108284c1c80b04e40b01c503644024484080742100f83e00754150085c1c80010610ba0307060310300500c400d10f000d0206552151584150030022520020040140d56543ca0140c0302e42d142e90035414040c0095440c039690b02801e051000c02005030072109030100c02100d445403822180340c8283d46108002c034816410198610003040c1c0c11141220340d088100f04042802c000140108115000f402c1c0c103d503000728074400302c445641c404801030912a00408034980c0380d070b03290a000d82ea41d1190124030034a4913002c1242c18044600102a00c400b0b445a005465903031203982c654519100c2c06a800340e5801c1380b80260803103495000700e000f800608050b18103111001a6601d41c500000d040041c400d8030f1511807a80781d442c50424811181c03c140d10050401c100d5 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 291505656 1250 291504406 291504419
    0xe030d0e031218040c050c0708030301140d05280615030303060f06140d0f022101060c0201050706111e0d0c0c081c020405120606100903020a032406 65
    0x40c020000603009005990042140548a90880380d040841d044000c281804000901005202403520803041000502c40700d6002c8005000344401400a034006640365418542401c242c0c4136203400c006d02c0b034a4a840c08100040010031081010240d4007418005030019201c010703014941c07000010141c41c90000e08192481e031142c4200e0070340340a5a410442c82d41c40707441c004042107070782c00b800303021038540007415149da65030301e009090078400044049052081101d450050760001d01c04042405040786008048542507000340f0700610b5149811104000706400280c82d502c01c481d00034002e541c94291600c3c259051504a4407a40180004024156028070021059801c81c80000381d50b9070074804c240380703207520902201d8151030304021111b01d002e81c4404030391341604d02e44865200c1641c090100051680c1c6454a1230b0a00305414044c01040c60104200203410000e652850140b001281003031000d6112004820256503101500780b008040c2002c00d050b01010389615483d8090800707101040c807 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 291506906 1250 291505656 291505667
    0x204180b121006080601060206010b0d050a1b120b09190e0c1f03060801151502070801050a0e07080d020a030c0302150403030207050606011e050a180b070c0e0402011e0e030d 76
    0xc0700c0c03900b411713200a80d880c0c4c2400c82c3c441c1c00038071540e951080140716000782203003251f000c40d03005120204001100174458103200125640380c9080004296001103c20350300d1030901442e058800308440c1c0d010103207042c4104032074608050b480d050301c555a48400c040302d40d40c00c00c0410385010f4020b00361031410300b000704949a0b01620081e0320000a0803c400080d40e80300c1402482c221aa01500c1c500d6050f01300380d000b646154640e01460114820311100052002c428410030707002c1c0321034101c003285081020000303900e055510340c003044140d40200004504580d000c140d8000c030550521340304e20b803241c01d800d04901d42032080c0160003088600000340400c1580503070040c009184528280c0c0d07421360792180151050003440a450741100340366110050540d10a1005107034411840c00c2c6254a019101e00326050b28856420544403086c0001d450028040c0f0310030244005c098005040c00700c0d18250b0300081504041c039a030030b01c080c081501e0621110340101a400c0c0d0a05020301140d08407501070710003e06 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 291508156 1250 291506906 291506909
    0x803010b2b02210402031902040f0c0f0207050d0203060a090c0e0702031c050906060603100b0f0d05090706050d02131d060f01020d080103110604030206040e09060a0204180b121006 79
    0x50254402940b5082c03d6005058030307110300d400401610880104010440082c20900c5040342c0c0240d584500d150340301007070b2140a600c442990390b04000d08040d410040e14040744e580205101e2003000101b5001694005012a4400004440443da4103020b190507808040b243d009400b4000c00341e02085035842d4000081e00002c0c81c503d01041c240100c07030400700c1c21148107644411203a0040c00006a050030002c0c021340d00140444005103002d640d80008103010b03000320b0302c0a0310000340054a0021400346009040e00004088040c0041514001003c0c0651040a884042d01900402c0201002d44d10034405801071103022a040c145880b420f01e140c80d9070104546c250301c1440c4000045146520005266000380b21548411109074255229158940b134140256944104100808070040e12020301400080c11812442c16060901001c19410a00b00400c020742461040c841002481400404c0a410094440c0300290110302807021440004100c100c021083c0316135070b000008042c550f07000c41c0 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 291509406 1250 291508156 291508177
    0x260c07090203151c0303050c0c07030c1509080d0c11091302041a150306030a0f080a030c03090f32030405030f010b0906010f0c05010f0609050a090803010b2b02 70
    0xd1030301c00c52000c01c83d4210341c5018038504d0404500c41d52000901940c8444e8000181030325581c240380320032050615042c45600100e032902d10304a01005040501116111a00017509211040728105101d01c2d9452800525280030080310301446000d01026801c2e15440c140c1c003500000c414a0041c0900c01c1401d05140e049000780d180200d03030507010381001c0c1c0c2c0c44e0352001c0c0101065051113081d4072070002038002528450340b5006860700100051440000b0400d030030311400b0556164544a100034040311000c0c0e080000341070500074103800007100c403007003502211360154400940a5801c0e050f01c0301107080e9003003640c8460301000109013802e000009082161011401c40d0106041880224281c400318408260000b04110200f02a5805100450b007031400e01d145c00c0100600a40302d5509481462281c8540c0c50350fa20341c1407003041ca407400b03201d80c00340c0030303040c140400c49a641e01d14103c4d100c14410102800f030701007000e514100d403241e407503009800003083c20a14401000d00b0000294011034040 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 291510656 1250 291509406 291509431
    0x30d0c061401151d01020303071805060c0a14010b130908091e10020c0607140a1505040b180703080f04030602070b1005010c0807020f060c030a09050108070c260c07090203 75
    0x740301c4c944802080006010040e400740d030a40d1101c0da000c0d20070418000d0200c00e003000d28540402c103034032040c0184c0300003c0040b0040c070414025050007041c2d081c00205070581070f418803900041301d4860424000d130120344030720005410070b02814000000e00401c01000c1e8080d665406029003401810f00d100310120301251108100318100c00c05a0740c80c1007200c0003e0300100b080c0107400c08038841180f13003491501080300b901d00c0d0300925614041014042c1280100c0d44d40e8900500041c80400c2c40360651241d0020b800181d0302c141e04840c00d80d46c40d064400200f1504002038601c425130b5009060344d004503071041096449031754516152550f41400c444d800d040700c10240d000078166101c3c0414807801d6030401c40e2186040f0254080c0700c4106450b01400d50031203030030806880ea82000f0030061070908201e0741c03002081c41c00d080004290711800380c203440411140345504000304405012940746845001403400305051012100c0c28030b80144051542c42e40100305000602d4141a0000c40c443c10743d41400 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 291511906 1250 291510656 291510677
    0x906042a120f0503031008011b0507140115240e0114090402071e030e101205190501030803010e010605120406020304020d06020d1e060302030d0c06140115 68
    0x55044440c000c40c08400c440903801020090301c1400380700c0e540d52a00541031031915030072a446440c074591041c1c80b044031202c10000c0800240b4020b22514280c2ca04d0800060224403606100410b64041e06101615881c6541f0381c1e00b00190b000d42c030441105540c0380005403000d59515a841c6100c1c810014000d21818020100481030f201380010301d00d8520586070141b1410401c0c00c00007942c1c200d01400d0790020b50810074000800c281d001110341c12082d14410f804586158a0020720a004d98981540a0a07030000c040d00480c2c3c01800d1882c00e8a0124000034084d968480c0c500607211242c013243c1006803500340003000303100064000307606940a403495071015990364042100d1520880c26072540124680c00414002040e41d0000d580080c0010491211501c194490804070303401400c0300303805c0e00c0e9203040240c00d5801d148500b4100980150f82000903a1a50300800c2d164611034204408001c3c000a1120030800070b640712400446a50100c41410343e100c0ca20403419107490090440820b146060 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 291513156 1250 291511906 291511943
    0xa0b03070e07141b030304060608100c090b091f08180609030301090e1029010e0307060809150103110a080307050d0e06040801020f03060f0a060813060212090604 71
    0x1040e400b48180369140c50180c400344040c80700e0754200000310104c0b42806148001418020030255024501400001680c02d1078170048926001c07142c40c1041c5014149070a420106400a8182040750401c000880da142568000104d9804444880c0c5041c0f403030030150020030a51104015211380e400300c3c2070f1a00c204220010550380c1004452003034541c0d008000601900c0d036150040580e80031040200d40070121241a800152940702441c8159800400b0354001c44000100340c8010024083c286803840983c0358001c243c0720545d5000354824440a40089009000d0400c55012115605025560556100d00c0d00d02561000d0300d807203900c107000d50080422051404411136075203c4e403280082403164501c3e40140c03407507000e40b80099801141840f000455001c00c6c0010031550070190740041d928034222082101400c1c002d0549401100d80503401e010440d040480c540d048110300201c0c1c0742040c06440c00e68081d22403c03481d0708510b10324800340180450001045ca001c3d0b4840c14202c43c42c58070803030 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 291514406 1250 291513156 291513179
    0x412020405090f0c010f09051002010f0f090233070803040b010e09060601110c0307080322081506041107050c0312180f06040306110403030f1404032003060a0b0307 72
    0x2662403d041d081129101c0b1036600803a078019a03a12a4140300001d59602d0b80004c4031080f0f130601020140c0d4484031800c814100030b2189040d807502800c004c10001c4070756004600000d03807504100352a6450202881030000322b81400080501c1642e210954640303a0745414105e40d0002e40c4c0c200e414120110007c901e40000c0e480491194032150000d0a140d9075020044422f001c1030f440340c9080340982d00d012503440e182441103201402c609001160f03110f01807801d030000309401c0d41e01601c203512201000e21000501043d0002204181e50204103a500c41e00e00140003021071360341c0b180c240300c000901601045400b00e2054042101242622040c00d80a000b400a034820f00001030503000348010243d400e460700700c0342ca035000b52011307000c2820203031203036200d0084400c1c0c0070081c0460034002c00d0420030594401e40108410029280c00d1309110a641d0080c00d160142d40401070000c5002d908e141714400d040c13481100d511000070111851414400d50350001000f61800c40743c020301a80c1c1e17000c5102940c08 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 291515656 1250 291514406 291514423
    0x906020d0c0201120906061a121b03010b0c011812120504020f100309020406060305040507170615310b0a0b16081303080a0807031b120204050303041202040509 70
    0x10784035130005251810404000f4028100200c0d403180e50398201086032000030b40d0100411000d0344541ea505c521440104540060080c40340d07004a0801c0300c124044054078042d241101d03074a00200d46c41d60b256a51b414007400d5801d400d8040410821080d5042c08544000324100410341e4030b0b45261a444540322005071481103d001e07401c03518a0f4110007190400054140d41c0c40e000d0300d00001c41203040d45c001415030308640d21a0700020b403102c040c0020f2000510451000701001c010804511541380c804c01d840f040000c140200c2040440402e03d000d072900500640d010314201c240440c0f001e8142c07100003018602c0040503640e28607005003604241400724081e02520540e110144c00c0040005100c1d04080501c0c8048603094014003c50501d55044101074000c0c2d0700c117000c60768986610410080001e06c00408410805080c100396500d18040c02c54103040740f882c03910b404564040d0309440c00c00030788596444650188000200010442184007400070300c1c502c229070501c025100d1641c01550762012 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 291516906 1250 291515656 291515659
    0x70e0d030c03081f0f03020405010e0403080610050d0e251a070602070c0b030402011b0320031902060402120106060203030c07052d01050a0c05040306021c0c0906020d0c02 75
    0x11501007101080c0126901944410070000c0000d4581134006540c22040007584000049941014140304614240c002c20703024040340703210014a40341541f002000c031200a001240550600c00ca8012450710885c100c664a102c0104148015082d60b5401c65880c50046045002014101100016110280c0c5d00000715008640b802d980d2702d0864400001d960300001045070940ea0800401c40000c3c404148180101000c1041c1c5449181500001d402c1c98242070b0b0b04204600d102019000280d0890140003142d80204a800d454410502d4100d01d0741c03080d101d44145d284000300340e03440c655a00259441c031691098501d000e5803070140740158240d42003806414003582080c00000c07400d080d100040c0449500610032118034551012030081c41030100c00c102100404002140d000118007401040d811812441d01002503501442c2d00070030500440c04020b00341d90300000d445070003c40c401814910030b60801000c01c40008411405001c020712841150b002d03004802d00c0343e003184e029101b13141e06e40381c0 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 291518156 1250 291516906 291516917
    0x7080402090612150c070204140a0b0409080304121404080f070e041a0a0605190501080603070b03130204090b010602030c0609030310060e12160906090203090a02040e1212070e0d03 79
    0x4044c0d480d82c0e0007280c0209014043c0754140000ca0141c3d8440c06900511300c6110685005030074908101029100c00c80503e500650030003008400141592048940c041e400c02c804a2400c941c140c801c40b800b1842c50000c4400d20000316020806400100d40c1c0c003403120300c3c002295025565091401d221181c02c5070080d0010301d110007004114680d03090f089903c4103242e0790000d10180c4480c0022140d03104241c200b03880820900040c0503a503001b4034030035040b0004500800b9018030700000004144030050910300315000c4170b0620030440d03e860f0003491055612015420066854250083d0f903a008038416080c03520404000c2a80500f020003101d0240d9109540145030a05101c02940c000c2d0b4100140c503000b42c5001c80b1090a400b090011b042d11203601078007908240d1070401c022043c2c66454024445540c410800d21903410f00c0004c101a04540c140d03000701e1115150348400d41023141500c038a5408020014440d1030b00f51001c1455071286083d41c41d090144003c0105000202c007400f20010041341 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 291519406 1250 291518156 291518173
    0x20705030723100b090f06010203070c090c0e19050105090f04050109050603120a0c020120031306030c020d0903020d02120a05030a18051810050a06092d0b030408070b07080402090612 80
    0x84085035147c0d000b02d06004032483e1010503074500a20079129071001e2001030341c640c0d504600c0703603100300d03940000b070000c03551070551040c5c0110f60600741000340704443c103206001a821105407100c004144007142c005004000a40c0d692140a0113003601300c81c00c034803d01802201d1580c100d0300c4020b56001810565032901e403901039500550744961368000483c8480c1442c81c50000c102c50400c0100040b507140452200d9451901d0310150940d40e03818080010341d0089400c01241c00d43c804003060480342c04548280c10b089050001c01d16041d0704818110b42c42c011401038405200700000140310182083e0b444248411440c00480c03415811805400d07800041500e04411400c000c82030560080d806a6040b642c45030f0b644006205070322264050408210301039000c01c0300e082070a01c818030701003a00741081000d88804006030480d50141c01440350822020000c01d0520600e5015158003035442416040c01b420b0004002c0c084580803103003284503031204000501c05e414420005034119041c18000d04065 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 291520656 1250 291519406 291519421
    0xe1b0f01181413020a030b0315070219020f0306010e0f0c0a09090504030228350a0516030309050105090a171b06040b090f0304030503070204020705030723100b09 71
    0x80b40303440701254000101c1256000700c3e4100d200801140c034280e10b00060412005081c54142010100c02150b8018400100540b00382c010a03e0040101e403422011701c0d080080c0f001441090300b889440e0f8040c0b00f130000100708a400303401c90900450620341c08000d256035403041c40c00c03544100e040030000200508400c10001020b6082242c000e4070038010344507448040752004129180e56000c403017850b0a0070721a182408000800360300e51940d03c00d41e0300c04140c04083c45840030703a054050012112000516070620500c00c80944050119a044448040b0480e00f802809801520021b4495520b01008155035070000104180e070264049240301404082c90044007854018902c161280e448500c5603901d02070090109910852050f034000216043c0298002e00e41500f2003420000c5a20800050000c10340020a40d41400e078112000744e90b03184203180242c1180940c4000515109a00300690b11003400e02618024440c00d50044440350000d500c10003069039025100b1903044061070740410302c01c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 291521906 1250 291520656 291520679
    0x20d02220f1a090306042904050a020603133e030705060d090204020316020f120d051801020c010c020f01180807020103110a030902100e1e040e1b0f0118 67
    0x200103120014905000a240c08139050400464003220041c90f50744500c1182c48140400040c2518040d0b28543c0902e002d56030701d555080010b4001c0d10403070f40840025918100081740c850541c0c0d0001c030700108070310460382842c0703012545550500700b4200c18811189015010f0b514546a04d0010001c0120900d00300500c00d480e4464403e07540d0554480701c1c440056229400154001e024900303035603414200c0a40000d0030b00b80c2e04140002e4580058040d250881c6004090310000d1420140024042c2c452040c001e06840c010000d401cbc445d4004a1500da22045c1980000d01d804119020b99510010000e02c2170300302d0b800302004a050302000d2039054003107440080a00b408510604001400c004414601d070065008004a00c00090729009204d0441c01c00044070054100103040c90f4260903020320000780c07200524804080114450340540949940703d40000b251074050505541550101d0b9500e4400c0ca80c407400c3c21401000c010400d49902c4d4491240f43d5010302004100215260500b52482003 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 291523156 1250 291521906 291521939
    0x506010e04141923041b0302090103080309010f0606020c0a0614070f02040f0501030b0a0b0103110d02030403091e09051b0a0804030905091501080601030902010509100c06020d02220f 80
    0x81c85139035011035a101116400700070b1201c40e0703118a40d480c2c07458285062019001c02400c184042949614200016140c0a20b8035040d694000714207516540c403c14031a004100c005042c6202c5810b1000c0001c0391900801c0c0396001060550343ea030079842c1c50710000d482036030f441c448160070f00c2010488280894220f50070041424402440410b45415840b90305050f104203800648500d030300d900c04c1c00080303143c0e03101c0d510002e81d0a00302480034902242c00100c1c18012510f88201094000000500309407180f0300910140c202441e40461040c6008161510701c40c00b4020246900d2501000c150480c8801800007a1000342c400303410b02c0d007081150101c410030000380003201441004140455540c1c4e17441c00661007508a26585188012144001015168081e205605041c40c0c04228001350343e01030112503c0400941d02240190600380080340c0c40c0d510031402805a502c0414051850002d0b40c000380071104580c203036903400909035008060990210701c503000e003910510700e0820440440e5145c804 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 291524406 1250 291523156 291523201
    0x1302010302040e070905030d0f052505010515010e091501050a021207030203070b01060c031218020918070e010b07030e0604090212041506081b0319060506010e0414 72
    0x42c1401d95a02c006608058240e0b8414040388035a2014001814100f0038884111503603e800f40e4406002c050181441c483c20000d069005003100c0c40d54142d010324620041c0c03855210000700100e2a04000c010107032013810ba041d900140c080b07a80500280b41c41050366000b41403014441c03000c051f9241c01540c0642c0680402c80940c06604561290301c40e0080180200c2c0c0c2c0a0b8014540d01c08551074003200101c4142c00074014004040ba40a010980c00081414010a0300302c00180c504981c0704203502080d02048001c3d0f201c0009010040441070820211454030b1442085506003511824500740840c030900400e0603c45050200700c000c20300c90010216040c174040c3c812850280c07546043c1c030990f40005800702000c0e4280c424441080340b40103407950304904440d010000c282c14856029100d9694500c095041d031b000d450203942d50f54042c403a10a81020000110000414501c1d2070405444102c03184c60104a5903c0081c0450401d03024110314013a0941345c8400554801d6a07442001c41c514041c41d = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 291525656 1250 291524406 291524411
    0x9060302180601031b020606130e06190b0a0f0f060e01080c07020d0f0b1608090a15320a0c320a050903070f03020913030e0a241713020103 61
    0x4240070380c5c8841c0903a4007038101d901800e081d103440c03814010107010301c80c105540f20f440c3c100048000d20380810a250012004050140d203880c080c40c034080605481e01c100c5034007904c0700e84d002070351000090407001118000403150350020750324031741035964110303108007940419900701c005044480d1040041000502c000d200310310234035607510b900c03003210640c0b07070201e840582c20010300c5001c4114074000803041e80320345011071013454603080681c1c8608501000600505049941c1907401c0600d0300f06100c8070302c0321500314544058079100b1044075000d03403500c00c64140d140c002007190307c0c007940144510400f2a440d2442c2c013800b103040590007240d0410b686a00000040214071090081d0320042c0b000c4c04031550f400352540581810035091496a03807004210840c51319040005845890b82c10798842c5642c8040850810f25080035661240716841881c0c0c13010a502001c141c0019500c1c00c1090030000e07250f580561341c01c2c88010745000c00d0000c0c02c0300110440c140000c5201c0054802c90304501c0c41850702 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 291526906 1250 291525656 291525671
    0x10605040e041b23090603030a0309080d0f06030b09010c140c19030201060503070512071a0f0f0706060e0f0406020c0a06090c0e07080c12060a05060c010b0a0906030218060103 77
    0x103e418010030740e00184e188012220804203c010b011003e26822101102d2407a0300f0f0401100003590b921440108a00b0705450716910018000c0300002c2d0b0f0040f010030002400a56407a40360207000f0666800202c50b00c90118000c90f60030705052068a500035120384880400d95400c032500c0400390000c6080050620980c040511100000c610003018588a50008078181c1d00742020141010b056402150180d030301110800c031281d01c0000c82e0400c80e9950003c9202c003c00e0790b02466034030b200d502644000716900044038015000510000d20003540160000c00c100c0e5240c841481c0d103004140d40135602103212402141c04a45140e00403c0545200c0d412a491040c45035201010b64900e008141c9010500340c104000c1010750b409071a07844907c40c60301e000765241511000184e40a00700c071030091902c903040001e4664a5a0006202403c0c0041c002610340101003402400381c05680030040c0168054003000074101e845011f49000d695006280780301d012160086000b4078403006061504150b01c4155 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 291528156 1250 291526906 291526943
    0x429040b18030f0f1902030c06160501060501030902061c06090609020d06091803030b010203041a1902160b0702040912050703020f06010e1f030c0b090a08010203010605040e04 77
    0x80800186008811840c004000101400e00500c640903d00341d42040d0301c480120700020542a40705050b0b80343d59495000140042890072041480e46a0000701c009944695104140171070702d070140c440c2000703100702c545500044090f00d00080b40250480d01c03d00a0f6032a03012000b00080c45800240e40000e5451b54454404058410030742c00b6141030f07a4005072803c00303984240191400350062200034055942007400c081c60200c00307002c014081551326034080350310f6813084c001c0710300810b40c080140343c103031a4119481c00103a10021460101082c48007a40c1243d60010601d002400881d2040001003440c0c441c0c8940250700c00c00e030032a17020b1346d03130034040380020b20500c0702c101c4032007070303541d8031a120501880e02134a00500d0a1280f40c2d264418001080302440420a15034003840c100e200307175a48910003c04104548803600000d002001c0180c01080017411500504030303c980440700c000e0805e5403244021b00300e20080c02004005001000709015100600304000d03085445401d1054152a2084 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 291529406 1250 291528156 291528179
    0x913031707051b0607140a27080c0f06030c0c0f0114072303130203030d09210c1119081002030106080121060e010902181b042904 57
    0x7611440819008034500382c601000e10301407040c04201034010300e828204880c01806c0010280442035103018000f41c5d2458031132181c0215012060007042d21521042d16074601c406a0b41c890084a446101e5219100140e2400d1540d4242c040e00240c1041d186890b0301e00e06122a42c008050784509124100c0c61018901c000d100343e544100500d41d016286003003442c0014a80044d50316000407443e103007201c091024a001040b240c2009079680b65011440c6117101090031030207040c0900080c1884c1811001c07e100c46000c2c0c80d51303000c0d1165280301c0c80f081842c000350303205820030001411601e400c65041310395007000c044a84103040100d80c104c442c6a900e4681c40c0c40d110010103c0a40c464011004000c0e40d038200b8141809021034001c017101d0301620842e004d60103050010040d050507103405840800120a43c404617940e50050440c1903a50140c0147c894440015281d01011014424140c4008903c0ca01540e09907014403a989100e14003905088a411840b162480b2000c0d404100000c0e030110102c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 291530656 1250 291529406 291529411
    0x1709100e0d210e0109030804050409030c0f0501060e0615030604050c1209070e070306050f01030b04021306260106021b03010f1805070501081302060310080106030308090f0c09130317 80
    0xb51100c5080041c2064010b0031000428242810301030f5004060002803040c2d021354082e1102960006441c48850a045035900881031000d0414210a13804405203c41900a8010360f100c1d840d03000c94036218881804040000e503a05d0034001c50080c070208509240075008141c0003032004400d141000d40c03466491041e050300340d44008041d4400e9a0410845054000c116400040d90608006240c500f4010840ca0a00c4d420031504069a840c0d1514607656598181d581404400100c0030102c5c0e1580406004850a14010112076096028038584005102c034111b0603210558094030108160342400c0d0b0301511403ea000d035255480e40b1074a00303800502d12503606410f2054105080c0441c11781826414651543c100c40d04001041d42080016a980503031400101d0741519803075500d40e00e80800100c07522294020030300395401c0100010500d540030901c140251315034070941e01042c5240c03841c180e1b80c0181c07604142e0442170010001c1c001101c00c0c1d0405a031540a41001e007040d04450b480e807450324008 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 291531906 1250 291530656 291530693
    0x303010906050d080a030c0c1e1a01050d030818030d05161707050c010b0306040f031b0f0206030c0d05070503011a03090a08070206070f060204031709100e0d 69
    0x4401080038140038080e1400504041e10020300000080d180c299483c410307000e5001c141915840280c1304584215040c0d104c458000c00340b100243c0b040001d0316040000002e050360b0629242c4000c45106100388103c60480d40c000b45840850032055500b41c070301401c0184003c664009200303c0713424000d824802005003101c1510005100e00d44030808a44007803502140808000c0c0c1882d004124203064480b494011885007021500c8650403016140500160740c0721903010300030103060101f0060030b03500e00400302e13201c3d44900500c1007004810610381e014919010305402c0c03445001d0340150800c00004c5400006140c0d041c2c1c5480e8a62314450151a8241e4038400040c4001004214a070300009070001000d5401c00c902e0701d5420100c40190740d403082124060240f600000c0d04904540c2c0c0e50381120f940c1a881000561300c070590741040402500184015074a0f62144080c030541c402a0f0801c48400c01c0000305601c0e1541e8007000212908400741007596003000300188202d000c500c6106118164000e0b = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 291533156 1250 291531906 291531913
    0x4140303130f0f08011a120c030307060e01050618010918050f060612030a08190e0706080702070e0105130f0227190503060c070320160b031302120c060309 68
    0x1d840c02c04080310782944d0195000342d1401c07110440400500c0c0403450100022900001440041580c403824051044500341d40b5100000b40c0e0300400c440c6403c44440000488020012541c0f40c105005140000b50101c1c114144e00c1d034010f0140b00855403203512005c04d0500041d500c0105540d42034134010741d8110070121035102008001c420b243c1010072503000044100a181010a0224090200d460181c10224002d00200b40e68181591fa40c1c491740044800384100c510301651035001600c440f0085c0c41e600c0060048840c0801d02241901c0c61034103c0f60060a01d240202c4540900801400f516030003d801c0e540802030b504444241d00011080078088441c04000700d0414001c10900003140d00c0c4003403501e08103c008000a503004a181580610800b403415624102c40c5403c403140720801050009640c604c028115000b4800a00e8003014010000f1001910743c480c203080690340012502c0c00004909290284014188050800040344d8a007040701c005400141c0051483d4104640280690341b = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 291534406 1250 291533156 291533159
    0xc031b05030a05011a0a0809030d06060c030f030504080d0c02070e010609060e0307080601170703060c0507140705030717070b03010e0f07030902031203060f09090f011d0304140303130f 81
    0x8055100f1a03005042c480002c0781010184034001d02e01c0c0c052802c40c603090250000c00544125001e05c101d410782c41030203500300b0000e0f8072042d0150540b204d01d4000d0b030000721043d002c03540b031501a00c038440c0915000704056007090b901000792805491000c0c0604114041c90300005180c000d843d04060180149480d440406420080014850701459804c03520903880001c007000400740100d03045065079500070880900081c5a0580340c68a54668801010720303203000c8103c20b40a5004c0c1c05042e81c2c078809d00181d141c40310340014a41d034840081c080c0310f60540041d00100a815466154206030790600b0301074850340d40e980c2d2446c41e4150070907400140c44c080301d0810030401103214840a070313218145003420802d690198020a136644c102c08a1300c4096500000443c1c100e40e02d6002d28400f403c001059080c5034605454490780341d8840c5248900c582d801d00b00601c00440121192451103501400114105490f182c030b1501d070042c1000c040d40d01800308012a003c482061840e080150001d00448010316 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 291535656 1250 291534406 291534421
    0x421050627010204120b040f14010f110c1b21010b03010e150118090b1f050409020d0b0c1303030c03091413050a0b04021303060506120a060c031b0503 66
    0x1e4140062015990344100300522a2035400c1d55024002da070072021040b011b60b104d191a6400001000740600031341c0003070741c03241c41e12203054000703107801a401401404840c0c62024482c41e14065815004442c1d00f0000381b403041c3c46181140c0203580d010003040c408440105035078003814400001512100f994584403076103c20f007424002d803401c0d918a100200101045070307620002030362040c012030701078130b074014010511071071560061107546400c240126124101181c0d83d00f0480010008003520a00140d0001118500340c03185003401034000e07240c1d25004c5510794508900e174200034100a402c44050040401a503004002e0310055032007912430042c0380543e8100600303805c0c1c0503482070300c001d0b00105400d55213459140071760522015034031004c10941c440301402c00150000398a07190b0000c0c4081020003504001c160550116030051074200542d84440c41401800c0c003403110031480e154003a903280c0300080c0e01e0740e0125131698642d15001446100001c400b5180d00043c00c03490001500200c01c0c00001d = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 291536906 1250 291535656 291535711
    0x1b020c0a06050406050414010909020319140c0403110d12020f07080102031311040e0111040513020304080a081e0c0408010e0f0c0d23011401080105090304210506 71
    0x907104508001d81824600b8000411030701c1240620111013645070225001c1da4012180c64010700f01d00e11056403603181c1130211f0354650313540415070301609003010200321078181c244010718007401c0c0406c42d4070302c1c5c241035403105400059a040d402e40c0018030090000e0109600300440e1280b802694060031a892540304080d251004d035400115051740704000f4003000490110460072000e9201c0c01c5080c1030020300c0005001002e150f407041c0141d509005650040c4000107000b031080d28403c0398022031005482d01c0c0c50080f8002241c0081c43d1400401108014601230041c05078810000fa20400c0d1050525a20b240c400a007900e180800480104040c024000b0a000b24845515410010302007002c404c2c0d0081d030b42d452802c5144d070244200300510300c140500c9001e00f0000c4440140201d07016a844c404050007041e075054400001d0002500101d104581030103041d00844900000310305082c281945a40e0800000700140b50200301d200f40400000d40070b00030f10384200f00d00d500c002260340d1001c2d1359000 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 291538156 1250 291536906 291536909
    0xc04230a090b0907060c0201120f050c0301060908030f03060d021908030909130317090c1e010e0a03031d06041206090512070b012d080105060102151314011b020c0a 72
    0xf25401c114402d206056000c1c825905403502407074034921460003076240000900320300c070706031104501b0718007040511810040158104d501d10b40c3c032410700c6a9580501c03900ca000e40a0151507008040002c11070914002d51100340d02800107083d20082840140307100358072582a407181c0c500e5000031444042a107030503440d00e0360102c00035072000c00000f01356a00410054188191113002c0105c140803c0102d00100804c1410b400c0140500c0d60722407251125814414080c4c03074890003d040e00060b00c41508203000307503000b01c9500d034882030a61440c03020700751080c00842507050b1b002a020300c00024899617240d1003411250007107100103000341040c00d101d401c1010308003101e00441c100f0400032000a10780c8003194110b070302d40254403070380341617040c240030b0064240005010076070340b248004914400d0650089000c6c4400b40c00700e0b1449070b01c00603117440c008000c40b8003a14100c0f10301c1c0c41c040844c0b00c641501c03803903000400000170200c4000500320304045040c110400164080c40f40e840007400c01054040 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 291539406 1250 291538156 291538171
    0x90606180308030a0c0e10050d0c0201060e1b070209070521060f0103020c0c090c04090522060e160f050109170d110703050703030509041d0c04230a090b 67
    0x1581035481c0d42100c0e00c8068070130945030b5990504c4a244038811114200100f200400c1c074000b521402a0045c02034100c1072071708042901e0540498805401482a10119850f003c0c05102036a109a03031401510201c40040c40034050401134000140e03241c010951081f0070300e4880c075440381204e864500720401c40c50035914501c014502030001907030301c4122082c0c6040703091a000d6036581c420b119203420a84c1390200d451b007201050b02800070310300d24940a0003d80d040322504100664502c900b04850126244140300c6a45108400d074021904542061560031081c4003180c41d84031842d01103624880d441d91114140c000c04c900180b0007503a003c0003034002000e6185030024494001404d05460701c61500b5040d042c000d000b00d401c801c00e0410700c030450013590484240ca502e15941d003406401c80d4000540c286c461840c000b000d11a0002c0d1592070003103005038200400741c280304c407003d000044c80001400c03800b01d8070b011194084e03030119005603440b07803540d030741c0104100031246411300c001580502000e = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 291540656 1250 291539406 291539447
    0x30d1506170907170a0503040e0906070c0b0f2215060e240d080d020d0506100c240e0106030c05090f0a02070f14070602061b0919080601090606 63
    0xc1140c0100082e1082929007100b41480300949142c920703440c0001705000144540000f160003d10b184075500e84510a42159007038a010380d50301700d02201c40000314540181034009500100706255001840e56a201000d200720030680d20445c0c0c448c050700458200115000900122200390040f00c03402148018072a10490070441d041c4034181c0c00e40ca01c0307402003280505030fa03440703c103016070b680c40d500e00009500054a00d540d0825903900c800030f13600080180507001e05040200713884d802e002045c2901c1c00c0c569540d502c15005181e8a2010f070400000c480c0646070010455480ba20542c0d00c91010b5168002000040b0580355182000705080141e00c01880b8642040812056108a886140e030184115000507598a040e183c80210200c814201811040d10340d4000701c01d14100044d01400c0c0c800507000c4807110f9a500380c031003c03080e40040000b4082ca00901c0442c449041c6200c031052003610401d80d0f048290380720303079901c3e00c0c1003001d90110240310703102c04040140a40180c040f000c1c042186004 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 291541906 1250 291540656 291540661
    0xa0f08090109031b05240405060d0605090408041a07020d031d12070e09030306130504020406030f0b07030b0306130b06030304050334061407060b040c0203040602060a020c060612030d150617 83
    0x180428000c80c86001c9c0200d000103024010960039500c488060000104000130500341814105000d0b0410b0140150f160f52852105140441100aa0300c4948d80248441394052041c0d038122a6026040b404011940a07401003800c250340707950040f94958003107001000d0940c50811558495200a40f03502c00d00d410420505c000c5466086040c4800c40b003110011485403100d102241c001c0407560700180a00001520140800c040700d0b001d28011000c0369024408650100c08040c0ca4802c281c03803400d048800c41101030009040442d2403030b405200142528200740e9101d002c642044207029a00c40503208040301401110882c480380d400708030310040301038101410004050001810100d4a8000c00d2020031580d04001c4160807602c58001b01401c01e00c0100c0242902a5a94002e4091400540221340010300c0148140c402d07640504010802080551941070500102d0711442c0f803461140d0008004a04e500c0450b40104404814549054008280340c81d00040c0420140ca00031010180a60309 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 291543156 1250 291541906 291541969
    0xc05030d0512100605070b070e0604090902130b011d040912030603050601080a02010c030305190f02030115030e10021e180901170706120b0a090606080105030a0f08090109031b05 78
    0x86e40c0405621807041005910741c0c0e107055071744000c031103021a070001340000d0200324209550800000f0034030940d000070301a180a0559015101411101c0c0e0000d20000c4007080117901442000d100180060400502040c82c1c0e00c03881c08560010842c8070109480300010030420008111035801072010307402030540d5881da0760008142564022004c0c04264807038000c02c4407041081c00b041401e0b13056403020002e071034540d00f14074065042445654541d000c590307510030010740a13000300d1104580c03283c040c03c400040d1204c044004e410010003200340945000d8404031041a002c0100b80d0560780e0000c10380030b5460001007000d040030503000740d541c0301c2c010503e0400c0c03840002825816a5039504060412020141540008000041815034008148000003514040940c443d0f01513903410383c0d0300001a80c9071010705541d0035404400038080c00c1c104c45400d020031f88460190810301c8051400c1807040fa0b89440c3ca10103000d11200340303603115a000038200b1030307441c0c0410203e5041d02ca0003803001c0380000184 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 291544406 1250 291543156 291543167
    0x10142a3006180a05061503131110140a140301030503030a050a0902030307030c030216090b03120f0a08060a05090c0a08070e0d17040e090601090608070e060d0c05030d05121006 77
    0x4012030b0f412034850300032564594032060404030500380da041c515100d1811038101c401c03050312094103850101c20780c1008402c9007000c0359050640905038580e000c0c1c40c1500c4203140c030907900c603a80354810401c07500303100000e09a0f90401580214000c0000315242d0a000c07514104494018110400040c03502115600580740441950006601030501c00602401405d0583c204401a03106603803901c6900004660483e0395441800c0e01e10042e003c64a0011a0409000031486070444200c20490107101a00c0090700c9a41480c0e8045009006001695a20004228190300030340d072483d50f2090101300c15501d9948000da25070301c00c2c0b41c0c1c5840d4030120040408100700e001b51040140c80c81130f098608241c0400950211401042c0c07540c01d448a500c0c05000071511410280a00c000490800600150001d00000c6010944040a250ba001030300c40d00200808480310362001c8070899900c050021301680e060220041e9180140c84455840801079218056004000d10035134800d02d42100c00c0c0000c5a000 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 291545656 1250 291544406 291544411
    0x705190c1a0a0e0405070e09130605060f011e1b060f15050901180212090109050f160b030411040f020306010e04050405030a0311040e040510142a300618 67
    0x94500048903251b00404443c07403119081c2590b08a030354030081c81a2880082c0400b4005030140b901000b00751116820007103030401e5490310701e00041c440a51003010041ca01d01e0403c0d03540d041d00f8003030b503620031068990a03445031100003543c00e0b940d90500001600301d6809400e941c8084020a544180e08020016014203c180a10701c0320f001101d2108a50761820f0f0b0454215542c880385c400d1140c03030309161070780c06000403503c22101c0e800740c004180d810103000140000c50400d0101c0642c2400e0410000800907000200240c40000e0301d07501c3c100d40c6442c2c9204038408040d001d0009070752440c246c0c00150021a0030300803031340036a180004100c08030f100030043e24450005454042010101c009005400d030045802851051819000340010881e00203881c00e07407110301a00a02011000000c0c261214008440a820009121068000041c4458511202c648050400b20304000150103110305280d0120360500f859107054111501004e5002500756014208803030000c3d070084500610320440201 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 291546762 1106 291545656 291545659
    0x50105071208190504080a140c030306010c030c0609110405060f15070807021203070b13050d080603030c010f060302040b0d0218090319200105010b07080705190c1a0a0e 74
    0x6142900c0d40b038203110022b5411541d60b0380040d0b50503600a00c0440420044d280f8281c0000d04ca0711452401601072407003042070440c00c50a00080b284040d010a2281201c1040e08507146d4800300111420081405076903100c1c169454900b10364000c45400035030000382c550704220200d9001024000b16030045060400c142c54005511005010009000d82180c01285024801a0264000581009000d41141d1500b10000801d40c211159052000416a1604d40801c1585018090b0101b030250459100031888034590005100e440101c50009010f5042e50020b40c1e588014003e6441c403a0000401d034001550910000300501c0006c0422140b00404c02084030308080c0511440d8145c1e180c01d20014a031802c55110301d450f0707402c010f408441501c45c0c16560080d004026241d04034942c07140080c00002c90511040750b12400003e024200000414480b42125a6000e503e080c00c0d040c0 = true := by decide +kernel

theorem cover : BRFrame.Cov 291366906 291546762 := by
  have h0 := BRFrame.cov_init 291366906
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291366906 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291366906 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291366906 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291366906 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291366906 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291366906 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291366906 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291366906 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291366906 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291366906 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291366906 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291366906 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291366906 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291366906 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291366906 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291366906 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291366906 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291366906 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291366906 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291366906 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291366906 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291366906 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291366906 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291366906 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291366906 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291366906 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291366906 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291366906 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291366906 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291366906 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291366906 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291366906 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291366906 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291366906 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291366906 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291366906 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291366906 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291366906 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291366906 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291366906 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291366906 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291366906 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291366906 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291366906 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291366906 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291366906 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291366906 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291366906 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291366906 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291366906 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291366906 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291366906 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291366906 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291366906 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291366906 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291366906 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291366906 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291366906 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291366906 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291366906 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291366906 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291366906 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291366906 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291366906 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291366906 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291366906 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291366906 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291366906 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291366906 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291366906 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291366906 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291366906 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291366906 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291366906 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291366906 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291366906 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291366906 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291366906 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291366906 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291366906 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291366906 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291366906 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291366906 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291366906 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291366906 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291366906 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291366906 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291366906 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291366906 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291366906 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291366906 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291366906 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291366906 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291366906 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291366906 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291366906 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291366906 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291366906 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291366906 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291366906 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291366906 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291366906 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291366906 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291366906 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291366906 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291366906 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291366906 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291366906 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291366906 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291366906 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291366906 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291366906 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291366906 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291366906 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291366906 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291366906 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291366906 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291366906 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291366906 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291366906 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291366906 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291366906 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291366906 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291366906 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291366906 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291366906 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291366906 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291366906 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291366906 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291366906 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291366906 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291366906 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291366906 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291366906 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291366906 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291366906 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291366906 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291366906 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291366906 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291366906 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291366906 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291366906 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291366906 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291366906 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 291366906 ≤ n) (h2 : n < 291546762) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
