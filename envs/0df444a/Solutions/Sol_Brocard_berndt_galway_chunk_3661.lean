-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3661
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:19:00.642979+00:00
-- url     : https://prove2.me/submissions/a53cb924-3fb5-4687-bcc4-1e3086b975cf

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 658273381 ≤ n < 658453237 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 658274631 1250 658273381 658273417
    0x140d1205031006050408071802070f0b0405370615080115050303041508040807020901060309061b0e10090503060c030402010207090b060910020f0a08030604110c0c0d1403 75
    0xe610303a04000070070f07045070f010040240400c0007a01c400042d094191121503110a0925190704a84002801550300180c85120021118010701c43e0881c0c03507034010350250b02610041d40c41da00080c40b05032017135821540000c0c500a40c0f41449001807013605c0c1001d2140501040e244000c1002d000300c2c42450700711180c140d640760400b9059180f0980c00600905081c1c01075402c0901c3c000c90004149588605a02881588800901041490000c8450840c3d00800500e81541c490000600034500e4202c00c135078040c0340020000010010354564000f0750080d55071003201500000c00d0122030040206035405000c02e10b60b01291b1a038080c03065a00c030798032a50b0131a4591909000091030100164042440c0900e007400742003003030721000c04850340001d05a40300610b040115808905c0d08a201000c0c3d02d0070f00400010300c08100100f0000e40c000c105c2242c0a001400c81d580340e24140d442980b4900703030542c2c0801402581d6081240500f1a0075002d08000e4030b103040e915815500390791083d041194092001 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 658275881 1250 658274631 658274641
    0x1030503090f010c080307030e0f061510030e07140d0f050102030f1e010b2a0c0f0301060503030313050307081603030c0804050604060e010b06040f030209010e0c0301140d120503 78
    0x604800c45140b5024a0b00d1143c0e4462070300c43c00000c1c4000342c1960200b64440c03444007500002005001c1c000d82d40c1800310303000c502e00040840f4800ca11441080e11407000502e070307a44e111303200303015a00c0e404540e1405084d03694502807140704c00010208003640c01c0048070400c600401d0d5507090002ca498001c00003d43c0e64641881c0b000001000144200340c4c00c00d03000c4000e5070000c024101c50341903c044000843e81c40103400100d00c0078007018135008281081c50030350081030420110f40d151800328252040041054558200b50a8034602e0091f0764040c0c0c4180300054610f2040f0009044060050081c0ca140055584645009620a03038142982c10f07005d802510400d5418490450030640501c0e2902803810250b0f1260f032100c101400141995846406040340203000303600815200000074401e90344d803540c920141444401922040e0700c0b405401000056222190380024400e0f03803400345091441c0c1c201000e04000c440040003c580080d44a0504000079840c190a02d84807100f80d12016142e141c0 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 658277131 1250 658275881 658275889
    0xa060b030d17010e0910021b06010f14150d150f1d0a02071103060907242123010e13051e010912050a090602071401031e050103050309 59
    0x580781e100c1003044080c4065000c000d4828855a0568001400c4002a03859900302c951034500e03000171300711203244002568601601311690400070000c1742d10580381a42c1c0d03146680d1000d901284180303624040c00898101e41d83c5046122942000c1520702503e00b04100c2c4519241124081c60132010117003040c0710103102041c140c2c807107040284038a0342140c0c4140440d2504444904014003500c0b4516008505403041108090f02164003d0014081f1546440c001000554a21040c820800d48089107a00f03242030200b2208440c50302843c2c0e840300c9140305080301c24080034154048007000d09955441072960009090080e1502a500305807510300300c2c8d4104021460790300006050702d8948583c0d100002c1c0020b0000c603a4540c8501c04452500c0030151030303950715015007150340005110207541103041d5202c4e60000e014000f40300082d5581d203c281c1d11640241e030b90340c07010700400d0200c00c43d855a211750f43d0301c43e400004045800700c144030340d1f4101141014040d100300b13030030855840d0000310380c074650b03418 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 658278381 1250 658277131 658277143
    0x6040305100501051f020c0418210e011b02090c0c0115140303091e030a050303040602070c051212030a020c0a050c0103050a09031b03020c0d0803090c090115030c030e0a060b03 77
    0xc1a0211017107812036101079a80c90406081e18011030311441c079004400c40d9542140d488030380088140d094410440000c0c40005050300e460306c089940e001c0c0007400d80d4403c610022114544031403039001611540c00308220940002c1030724240741c80400440e8030010382802903060464107403004540c4079051031040d02807111403296060207940144480111070340c03003810300e03070329504e40340742d4000300d03824280119042c00308014000d0000c0c8000801e010820009034002d141c0103000e00ea403107070459100c00420460040b003d0344805154805400d0441000c070f01402141c22590544006140000103005607051030038881060b07030301e904078007003a46507948c0600800d540030101540c02c0262100665001e030805c505092803600b0318043d042da0b00105402041540346a01c4014219104110140b82c003080760390003144d484c00d01e402501c4006c0c2e05030401003180e9042ea118100400154050001c00b02d00a21003003080340c04041d192681010450703402e100600e5500c0c01280f012840840000074946810 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 658279631 1250 658278381 658278409
    0xc07030b01051f0e0103150324090804060503070e18180105011a090d0512030a0b030a080d050a150f0303092c09030d14010302090f07021b0604030510050105 69
    0x465030100c80f082c80032054900188009082c10042c03c40c03698030340103c0c0280750042400603003103000140842400002c41a8030040320b00c0c007240849586080c003001c8181c17602c2500003402c07081c00340300c18010540294055540014240341094101c2e00060008660005414820300070010040912000174003613426010f49901c0c180c000c0c0b24652400c140c03148490008003d40b50b03200390200d100304490f0b5454510503610341c0c2141c00c45200307540440c81501694000d440c2c4800f05803a04480901074100400d0441c8181d8005c0a02d074104080d00b1101005860010704540d0b070302d81d0302c9524400c804d8140e5610b6000d4800c0c0c4000400503030441c50050a4083c4e1074001411550141c0100d500500b910100010076902c2c0070141c0c03c0c0c80d00c1c1c80b0040c51031405041110a902e80c208042c050044408400c41c078101d074000c8038404d81c261200c040b803001c0d004042da40d030401030300041c41d12042c00140d04100440440d000c0c11311445c2540e20740710a07081802c0f600705515416240c0b0010000c40c98a503d91003541 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 658280881 1250 658279631 658279639
    0x812180c03070512030d050a02040602191505041a0901050a06080a08040501030905070911070b0115170712051311090723042d09060806010308030c0f0c07030b0105 72
    0x50112000075035441003441618804c1e207074008410303480d0b03105000b0354100c6110b44000f4055828185141c1029400c40d0103108010700c02e0752052064500c0400401090a0300410100c1ca4507050100c04409000300500544003001020340d100c0c0076010741011940315519034000000c50f4106401154151042c076403040c2c03001c0d4840c41da03200104036001d08940485100742000506c4140c03510b0000d017408051750009416514016842c01c245800303000400c0014401d450903101c580e214001c1c0e001c3c0201003908200000c01d00c003040c0c40e4124020034415080119402d101c82c0180c10842c0f850140c5404490300003020034a002107204016440c4161072412400700e842c1701d510701d40100014080100c08040d100c41e01c0700040580700d080184801c40b0301818080d070f4000b0a8401813500540b0203a200e0003458400c1e54407030b6000644903018415041a07610207000303480342e0f07403070341e207c00301290809020310300c24010410400000602e840001c1c804e02c15594003420804c0d2039802e00c2014030740c0581c482801 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 658282131 1250 658280881 658280893
    0x82a0309090a0203090c031204050a0603061223101b030603031b1a0403021e1207080705010b0621090c010909181b05040e0a0807080a0507081218 64
    0x4569804904980c8140b0240300161240d0f00e02e0110b07441c1c0070786d88100940500030070030760410b0070b6a000024800d86909862601d001e5668030f1045084440761b05c2550b01d40360700000e00e440000c8980c455034a5500f42910644140c801c0614114100444030103c2540e4990700c40050710030078003c4038400e0f072841203800c1c10041c4500c1e50714050940800079518904c40e2801c000f104040005200710946c40b0803402e03981c1c000600d401e04d40a1341d03c080f946400c080851008106146491001810138040c410800965041440c10b40e591080768000b03800442d02552504082081616020058041d0310100003d10070070b20f5240c00d090340c244c075000c0c041c8482c0b80c014000c1050284d030401d400ca422a44d07021b400242000d40e0300800d407003405180d1001052407a1340e0040d5800c42d03058062000544404550030001c0d40c25900c0d0741030390b807054040001d15604052050501160321a00600224589410090301e040040e07929960741d84d20a0a04403400001d8105100d446008003500c860400211802051 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 658283381 1250 658282131 658282147
    0x6031b0b03010506130305030403060b120c0a120c05060c07051f050f0a030b100f030c090e011502070f08150f2505070203060a060312020a0b0a0f020403082a03 70
    0x15601c41401842d010b01c60003d00d10070700140e805603010007590440c00303807a111034492801ca00078000c20100e044c840c9903646044110100c011464a80000c002413481200c0d5250030401041c88400d2881510040040c40d0000b6098503040000d000120100010303042c40381c101001c00c840c138103903c5440403143c014070460044103030304801216042c1502614040c0c5442d82d00d0b50442c09842035420319504412203095511030142c2082901c08a8556620140709604440f40308540d00b41c5503100c1e82c03009025110041150241400c8071700d003211194816030761402e80b14110820400d0a90348101c031b069003e40455090148100255604116805e0446010f4148003414580326403c0c180f0000c00c0c1d200ca0640d40341c5d030b64016401c50b00100e84c0903040d00c0d1545040c010401c000c040a1106a03500600121812000c030720106020204942c03164048c0e01e00c0d1680e40300d000c000c1c0701c080c110a510310340c20400403011500c40c10103482200000082c52190810758100c4541d20b04c0350101c1032210b0352051101e12 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 658284631 1250 658283381 658283399
    0xf100e030423010906050313021e030d0903120302090f28180b0618100318050609010e060402060403060b0d060f0506010f111b0d0212070801050906101814010906031b 73
    0x25282501190344081d00404c2c040d008035031710ac154000340d034142701d080c042c0c8060b140c120f00301104582c01010342c0c0011003140c000960680c4100811244c3c810f500b24200400c5181c043c044130304650044d4034003404159003489800c032850300741e0002c0540010076108102e0b040480e02801812900c00e48000d400c0500140c00084c4d50225810130b98403409035888502d14862103503200c0c910a808031036182d140112070781131154640c0402d94201000d542003c0c0300721f14190000030b003503003d184c0c040d007050b10345851516020300400088180d96800300c0366000020111f078050003501440d0304031030000203050074030100240c611038881c40301c40244030054a5419000e0804180c0c006664000148081c1d00218140003c54400da5100b000794440c81c1c10300c10b600e50f41000110001070f90305503002004591502003440d07a851004560186200943c10424060301503140c0c02c0603d4299409070100c0c0c41e509040b000440c01c40242c124210f01562080100b0610401c10352070b031548880340c05800c2569042c40d0742c1e5 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 658285881 1250 658284631 658284661
    0x6031401050405040627030e060a0c0f050a1b0504140705040b0903010b041d0d03060e0411030f0604120f1806050306220902040e0f100e0304230109060503 68
    0x307a01c80d0741d58030005405d00600d500021a009042e854002075a641400040703c0e520001c0800e60001380c00072301700316490411004403a807030f400a1b11500c0700c401c1d0a5541da08000349462003151140110b441c10400290200300801d4220743d5201d0443d402810314007400b0440e0004c150a0000c5404002888002c0f5040001c6800380c9400c84580c1c0e40d00d40c41c403400b00f4050205004259007207842c0120015103110a4101c81c0c040500e01000d0341c06a0007100d008a05450f40c030302442220325482404200020004003e400c500309000d004d1340c11010049100608008085034151192800703810908192a0b112241c500065450700308501c1200c218000381045000f40e0003944140400003000c039049660341180e00400c05510500c0084600801c44010042d00180383d003240101e00301005000700c1d100104400960420303060080c2251002c510038400070302031440c1d002d02c00c2e00040101041840307020036a940d8400051101d4107615000100051241d007440d4000410420240b0900828000180c14 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 658287131 1250 658285881 658285889
    0x70812070e1003141519120b060a033809070f12081e040f08010b0a0501091202040c030204050a14030d020d0f1206090501151106100308030408190c0c06031401 70
    0x1107044081004d5000c24610f00984c084c42407111621100080c0310761030180e05483e904e2080c40402d185031030325414054080d8150200900ccc0702c415802c1000b11020a400c2c031010310200e141c070b512400815040b005800300056641c01c0440c3c020742014001c0764000c01e289030003403611001410302400940c9602e11117005401c60a2421420b549141c8026881c54050350080c1600080d80c00e001a0f0b03c40f8150700030015148480e004a00689d00000c40c2d43c000d51001044130f40040402804200582c2004010400c3d081d0103020b01d0707424000401d454440c510035501a000d500da01c0c03041c100401c420980303400c8807040395008540c040125a022140e110200c400c60034500d061228501d07011036030000c080e00d01c540184102038a0540006904891010056000c4402d500d44075030501d10010040c0e210403040b100b0190001c4406c1c0b0400c00144290010341c0e009010792402401c00074004000011a0092248400015241c410800c10f010045003403200400c0b090408001200c0060341156071300105200e = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 658288381 1250 658287131 658287151
    0x204080c0307060f0903060504020f06210c0a0f0806030a050d031a09013f030801050f031612080702030f03040e0109020a0804060c1206060503071808060c070812070e100314 76
    0x3c01c9c00c5459036014105040c8006104c0c6403110b19000d00c0d000c0810302c18003d04c161194901c0420030042c40301040340c441c40743c10364440006159451301070352102006003520350507124244000c004580d0a0000b07481201190350041002034210100b51194034088a0051180a1400040128840da14444011003c00c0c512258120312024203110342d4243d8010800d40d038191b100350140405500000c1035040c2c503400c517019450309509000340356a0b0f500c80e8080c202c2104502005101c98140f1484050005102d01d18482c0b0340103a940c042401c3c503102e0007441416900c0480c081c800c4580110407180940300102c0c003103040c804040b100900d500000f80019220f1961001c402269920444907813803e0701c001501840801d94482c0014840da2040303610200203070800001010140c410700703083c0111342920f0300402994442c03405840b216400850111501c0008005501c140e250f680ca08910030706140e115011144005024007280221440c0b82d401050f240058845000f02d51489103508030045030 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 658289631 1250 658288381 658288391
    0xd060b030c09040b060706020313151406040522050705010311071e17131a07020a17071a03271f111210120209040f150204080c0307060f090306 63
    0x130000c2120f921032180c019004a000004000c146600e40c1f100c1c071007041c0300c0c03012011803c040100c803900700c42c0341200201c1c0010740403001c01c9041c90140c2056810280103140740003642182c1c00c8849509000403000c441e03c0c2c115113404c020b84e40e09032260a60182556094601c2c1c0f1a8581d1900781d0b01d810b00ca426007071660703407440e2032040c04080c13400c080200700c0c07582c0d01690310703d4000b030011040740840c801c4400c900e480c0740101503a00440401d55580d1070340900754105103824403415013002421118540d00307074400c071400014400b900280200b003004a2a51150b07881c00d24003001a40a840320880c08441162803900590006002441c08024090101d44120221000950074041c0c280eaa400454041e80822094a4080403403840c50154600d0032414944694a804401d084202c000703000c0d44c0050440001800703d14140a20707a510352207001c0008500c0b898840703100483c0c205800181d022340c4104182c2d58581030411807840034028074100402441402c44000300f00c500c1502008001039215 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 658290881 1250 658289631 658289651
    0x17060f160504030c0e040209071103040515091c0b060a03032a0c151209050a020909010b1012050f06060406051c090b06101d0d1e05030d060b030c0904 66
    0x104182c80146030300510070701c00c4917504c1043e000c1c03c540903107007039100388034060100340e582d0300901d1400f4581301014040c40c02e0a10300000c0204401c0c54592909c40014204201820359850340420081c0c07013101c0b039030b55060540701c0c1491448118000e101a02a00c0048002d01c046500601041480c100304000c5404807035410f00c144d19801d11116009005580b040c0c404200349001000b07407500141c49545525008109018131400d44109500142c011341002115401501b0000f440541c4124000c0000c1400c8044401103014540e00315040e0f030004103032030502041c6009078040c00b60080d1031240054412b0605000250a9104510549090143c0080e183e16400d5801550302031804401d40704004805032801c010103040801c0710030b94030032204800c040b01c0640c040d03000880c1503c0000d4a441135040d068051142348800c0b41c4081c1c0711841d182d041e0000368503c1a80c201e4159100b04059900c075880c900841080e2602c641100e0820942401000000039400e42580ca00b0041100c0104001d045 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 658292131 1250 658290881 658290887
    0xd030509040f020a0e0612041118010608070816080612070e24010c05070620030313120e30030703020304030209060409020915040f020a080117060f16 66
    0x1516800340d003090034840d00d00d41c030b010254054070340006161110300c01082070404200d1288141c82e0202d00311805400485d02281c0ea4801070782404001500720b108820f2500403c0080401c2603001d1000140d041c0100190558040009a00152000182a9543d40b0b00501801251005000501441c00084000e410141c10400100209400904080d55040690f03104100b00581040109090002488803030a940729260601c100d0340c104002e001c0f40c908103401250040c2c11910466210003980784078000c5040e06100440c000e0340d44951801110100c0c0c60700c18040030085400506002c07040003880ea15032108900503808440b6000c00c0840500a0008000c41da6080042c4000b14440455514201a0004010000d8034000c9510401e541d079403504200c140c45080c0c4009402814000124103d9840368500303a0410000420116003505403040300000c0740c0005500c4000220320000401c800c0b10318102a610404100c00a00441d18150854489268000d006a100112124010014184 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 658293381 1250 658292131 658292137
    0xe01260c042a020d0801090f0603060c080411030607051b071205031210051f020f100f0e010209030a02190b0f0703021e0c041e020708070c1e050d0305 66
    0x6000303000304001ca401c0842d00d040d9000b0519050341d88000596008200c900015040f094070150781d6443c50903a08004100015056050005585688615001c000215503020340700d0300c9100ca5171030403441c1c1b9081c14011034002c034070b1003403d0080d0041e40c1070100c40c90b0301c8000c46412410001c82096008848060680f07030100c41c2c0e01c20400140000000c0e4100040031000304029078400c00c5564850f103514a001903244254400e46a0009070401c800c20308803030031026030710301228600603203002e00c400403120313401d1000b111540c7c40d0b0903503601c02032404c00d80701c0d120f2030703066080210085041030403800110750740789140c01010344505060101e18005800c1d8a0140b00502260504592501141508001190001001280503024003082e002c0c0d002441543c1d0b030380c45241d507001840c24035088401c0c07100909c43e962903034240d508001d50008040400d40000c1031954403c0e85a244eaa000500303161140320182c0d003040048142000b2402104068009000c050b02c07005c03118002e10400504d801c1d25144 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 658294631 1250 658293381 658293403
    0x920151e0417061b04080705010e0d05011a1507020a09091b0602030a08060d03080c0f04080a0809010f0212040506090f090702070f0b04030203060a0c090f080d0201060e0126 76
    0x8403146801003005400400c03124020101c1134107601040c41181808521800340d405418000e522111003086590320404404a0409007c0c090807034a8045840c2c0300d003942d00d04140d59007001d82901d958603485c1080c101c0e500a242140b240035043c00300650005810702103030b100b1064075548507028601480909003070743c002c10302803041120700103070342e070001075143d0300f010040b60f000c608082c00160544c2807030100f5000c01541036a60500b580c0c2c4032030055090790880d00c81c0c5ca0f442e01007800007080e101800c005950405001b1000365880351030200005088a003001028411500200d8008031950050b8041e81c040d1001241c01c3c0f9180d00b90a00481c2c2020382d0407007000c2d031001c0804144011a0780208501d8240c52101541501190f250003030742000748218400250964016400103a00e0b44060788014580d00c1c1e5480c018242940d580b00d01600c800d4540c100400035080782c5c1601094580910480c0e00130310381c07821506425031400c281e00448248100b288010f11161005c401c10180b03007030242580c54 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 658295881 1250 658294631 658294649
    0x1c0e0102090d030c1b08030a080c0c0d0e1215160314010e0402130209010e0909010e160801060504060311040b041d0102090406120b06220920151e04 65
    0x1c14070a04004008440c0c0c50340650388441e060f07545c1802c90a400c4406400e07614404001c500d00031115030111040c0d400100b000c100c40a00b400f02041d40407050105d00a100f8043d500c0341700804c200410440b44900312401c642c42c0e035226041c0d0100e01e101442e03070568004c000040485900c10b1054040e006041040945920002c4a90000c920980e1204100f80594000d9440030305100c20760302100d040f44200d0000c0b6012412048107482d0515049002c1e550001d19000081a03801200c0a4189401803c0100741c1314000581d00a0022803024800d40004000860381031180d02c0c555212a5041039a10140c0ca0059403120607820312902d940e00140d020240070002d400c00340550300c410758000e4006140403403051341421400100c06c420404c90213501c5c0e0304a219004661501001c0000c00000b400070340130192100300d201a2241424070450442c2d42c0250300511200502900350251256410740b0a071092280c088581090305c0d508059a084810080405076921880d00c0034081700c0c000e40c0d0201c0d4403 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 658297131 1250 658295881 658295899
    0x2011719020f0a031a09150f060301030302031c051909030512070e01020c010206061f1e080103020120060408090a0f09020d0c09301a07080901021c0e010209 69
    0x240714600c2d004003a41e0b0000d90f07040021144070018412044440211540d0010300d82020a04020744003215206200d4003c1c04000126600004901150400d81c020380140e0404208120f005200100003a9038910341c00701000240ba1100f51850b0b550166040e0642c9507980d10071110802d8080d00c11100780705051210303002d8515201e80000c0110340b01110681c018000c0c1d442188240d40000381182c010310300102010942211703030244c03c4030107001c03d00610401131003022103035609603045800d0140c00810303981d1103010340c11070001400d1402c00405040f404c04090880350f00d02280451119045580002c0c902d42d20781d25000003425400c4607422202c00300200d010300003050455030b401026003200885081c0180c0d035042006581d460040d1081c8901300b424180300d143d40401040f4007403000d030028042c1e980c80030065180c04d0b020014049860105188403814450001c0e04a088a50b000314084003d62400341c002d80c8000c40000f001804d4004540c07982c4076442c80c01800c3d01580c4400e0805005a0702c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 658298381 1250 658297131 658297147
    0x50a1112250512032e05040e16030f0203031608030a0605090108030304020d140d020715050a090b09041119080c090607020f0303040306150e01080c0a0b0706060b0c0312130201171902 80
    0x10135902c0c41550310a40c9031100e08c03008404040b0b42e6201c007504410050004c42d01d1922001e0850724080c1040342d00d400304101c0e000607003074004004084e403070013103140070b403a8642030100c401198020780245205024043c01040314040c00030460707a100fa4140c1d0003c04d50b03001490304181e01002e44040881d035000d90000e07240555030010b41c04007107680118405c0f06043e04200c0544441c41a0b5800000113681d4a0f01480988041002801100d0000d000000d0b84c054080071100590820094614003a03242141040d8890384407800c1034000701c0300312003645400c0002c000140b003072150000090042c01c442c0b05026850386c0c24020b4038001c6030030401c2480104060403542c10710302c00c14010f098001c0c038004000b0400f5000080c0100b4072080180a0120460810701040256080100c04640d41da8595201040c003442d030801403c1542905001540c460008050400101c90010701560025465640c14800743c1c0e40302103242c801034404c0700d07220f07240e440c0c4080c411503040320801c66000190001400103 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 658299631 1250 658298381 658298461
    0x120606030203031b01140603060f04111329331305030f0616050d021b011b030b030330010e07090504020c0706050a111225051203 57
    0x144105031080d001b0484045950900003d1000507114550154400c00019008094034038403580c026009102c01240b03510714a00240113055400d11108055450301d01d0000c42d16550100f0860310046001c45e071240383d00d201c0c041417000004401110380c0c040800b02c1c03c100811100d1059642001000342c0942da6804040407007400f89480c803a9134041d2040007440e52110b00c010803424004c00c2c1403103030480301c131883d002d08492940051032a01c04c030f10303420460442c02039841d50141e904115407a001081f84440703c1d401c0158009001d0900043c5401c000c3d00c165a544c0c04030440e642c882c004158040700020403880c1203007035110024006400c4203071a00103e42020b20039440c0e4418102a69089c4146031124144000d9008680c0030142c254044101030050702c1c0200041c2207401304500c0c2110300d8040179081d0341d00d0141c05220b2400c0e690000981081c05030003090902c07a820b203003035051840502190356003e558103078284010010b0300021001c0342c40d21610b0b43d00890407020200c6801d0001005d08120 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 658300881 1250 658299631 658299667
    0x201141f0506040b221208070606080d03200a090e041b0b0c061302090604050402240903010f0603080f07110406060e01030b0f1008041a0c030103110a050a12060603020303 75
    0x141034200c917600c00c03202d00e04515400420945030542c2240c11060f846a4400810f500a288115041070b12404e0115038000708012401078020b095a01150000d000c0c03950f1802d1013020624000121402c22100301c00c103401c041c00c081207403441003000089035202c0c144024442e1019401258120080000158044903540036000c503903000419104a61640d044000d6035100104d0020341000d002400607182d80350691085500a00240c0250302d2030a403e540400782c1840d0043c0401c01d00c102003201c01860800344a17122010042c120200803850440d1a000c00d0790154140303030b150400c1c00040b5203040041c0015a121101805041880183e44504c0c014014a5042070003500003460203502010f181342508404461000c007400b0b020001d44810030899100314024025030b4280410800c1b00b4040c0e40c0c14400034412505507140c29203d5055181c08414000d20300c504070311845064506200c1c4d5580d40c5100402c035941c076610201c25450a140c031101400b11980081d5043c0004103c1c21505005a440 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 658302131 1250 658300881 658300897
    0x181401062417040201080609070c0501050a090309050a050d0b090a02060a0801050324010501030c05070b091e0f3403030914030318040b0d170403030f0201141f0506040b 74
    0x19540c04040e042841904030b5011a400303070010b4000c1c80410040d092009000350420894503001d10781600e076881d01400d49005545016405a80340388801c280340e03021184030040c140440d0701c0304405241400094800c0c0d06e520003e003101000a0201c1c403002000c02000107020b501600090311113040c4100600400001d200d040c0c028014003031180721034000e023065400e42c1810100046c90903420000110f00502407a80240e0501004003c1000444c502513f050310582c000c1c070040203896040941344e041c06010303440410060b0701c0184060016203010417448003903421200c01c80d102e040000444080071f5015540040c51814111002c810f0562145401040e41c0402c42070281801e62403085c10f969108004d40030003400c818441c2c0d01d00300e140c19001101c10400090402001201a0b00c1d0081c80000940400c010b0a01c0082c007001050f40159910250034140c0c0002c106e0188030b0380303506c40c0d05440184100354401c801e180550b141400320150030b000e4040640030984407610340380941d14590100030 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 658303381 1250 658302131 658302137
    0x506180906070e04360206130305010b060304110411120f101202060304110a0b0f0706230f091204080a050114190509070b0703031409011814010624 65
    0x50340f003c041c10b090142c840c072a080602c01d415808520012400d448485110305404018003a449502580d20f000140016400c0901d22120181c5549007042c00c490120303000a0003035a00303000b0000491000e07810f102080806450100c1c06c0901611490341074483c0368808a04e02185609000107a18100d52840c0b0883c0324541d0b0112054503030944065281c500200254001701c01c20010300040c030102284007007018042c11412000c0d07101d14a800094000903005014100080784401c103110b07860042d0044144000c071248516141c55503500883c24001307185a80450214001c160410410011106084604075596854070745130701e203803501c03600002c000b5501d17982041ca5900300200380a036420300a5000500415078101d0044202016000003030440e14a80101d890028030794500f18010091180300e581d00040841158920a2901501401c410000d038548000111880c000400894240380c10401e07071000c209900c1c40b802d001d0070300b94106418102c0700075146404003040369800b05100d0b0035a1 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 658304631 1250 658303381 658303397
    0x460f03020601360b030a1401140112120e031c0206090f1c0c0c060302030402040e0d05090616060e0304031202030315040207060905010c120f090503030703050618090607 74
    0x4080240101c0b100d81c042c0380c0728a0465140e100001c44654200043d0f160700e04042808404000041c0c103010340c01c07074103440110190803440f004280a1050344c107600c4600f840124a541081366903c400781b111036009103903000e5032111240c100d0155800ba00900001000c880e4000f5024105501e80902480350102510886c004100305500201ea0349a146c1d040c1c0c0002d10a81491040c040100340d0141142d90601ca1510080342c040307020601002c020b00190b03180503035281858410300080303c140302034010300d0760006130b443c04089500400b125045042111200c0c0c03101c0d071b25020502500703185e49000300090714001d40700344030600c00300141044070b000313107203000000240c0a01070362a40310865440740340450130b0603d400c9624096020b00100c038003500d00003525035080e903650b40c00c58000c0b100107c08960b0501900b00e8000f070300c0c000c03003031454524241030014071a2550748582c0c80c04045d02c5882410389400c0000d2054a071101c4002d0001e180d80c51a141e0381c2421201c460b1110303420b403002030002d0000 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 658305881 1250 658304631 658304639
    0xd090804050a0e0606070609141c14070b0106030203191404050f0303012103031b090f080a110f2d0f0406030503031f05040204030c050a0503460f03020601 68
    0x41240c4500c00e03480600f10b43e107460b40903966400141040c51040300e031600403600b480320025041111401d2b00d60480d8241c9008400a01d002d014440e0003c2e4901c0d42480401c20ba000284146150340d0450303240d03080142e200d84440303c13111405004542c81401c0d591074004101034a04c01d18654901690040d8240d0700620001018640c0780d10090040030500340483c2c1d04114180703903480c2c00c080305d14024034002a50340755106049541c0c07280001040c1c00a008210700f4000c0c1401c0744034410051061000911341c02205981e030001c840034074204a80b10b0800c51900b03408076250300b66284480c0215012083c0004484c004404440d45070344e0500b40103a05810718a030300c60409214000c203480d001030045042d5942c2000305070031100303404174240000b400700300005400c1e1111f0000e0009076100e00601c00d0043d003000103000011226520561007a8171901e4040c1001c140c0368a0004905031015500c0258041c0001200800b003440b441035104442c61800030007880010b1020110b031a11a50a0750300c141d81e6 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 658307131 1250 658305881 658305899
    0x160510060e1b340b091b0103090c0b1c050609010f1809120905090901020906040302011d060301060306050909010b011202090a030b0106020f0d05031501030b060d090804050a 76
    0x44600703505542d080ca11090460302c09030050004a803562803102010788810210000000d06055030340312080300002000200700301d000500e5400714100f401030070080e000340d5112941c0104055500d040c10360b0703920b44000f03100111401d41d02400c170340c5a0390b540d6074001000c80c0c64441c09000c000d0540300d103031101007045480c002c4005412a0046080b81d110907080c1302d905d480f00d400c542082000705541e20142e100058541d803255580340410f0b202c194000c2d18050601107a090002c0c03031090103901c1001115080d80d6031000b40e82c144da4082c41c8c00304d034840d500705076100d06280f64000b1960041f0080000103145030b040d0400001c0daa030545407080c0e20341f00c888589090364000300c88103010400001c520b000300c074038542c09081640d40003014180f00b260b136611001c07500d08080e0454401a045001034154400f03040002d0b20841c0850700d0100e11351b142500c0a4200c1401d48003079a410183c480300c00c145180e407803e007601c005000303460041108140d189003c5400340d2040c8160740c069695030780009442d02e4 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 658308381 1250 658307131 658307159
    0xc0e012102060f070b0f010510020f1213030b0112020f0415031401020f0d0b0117150607060f0e0f060106020a0c1a120c03040309050603161416051006 66
    0x5403800c85030003032026a40c2041003d03000150340207120a4140701620104005c0c84005006440c00e0720070004650602e0140f09021904055240c19036100210b4030008110000d2441c1c0b040c601035501c00c2e2100c0d0310503000042c8840c03039480a4103101007100007140c520b88040b504000380f407085540d40c4a82040e2024407040d07803010340c544107011849400070004a0ba11036000d56030010120700040c42c04041144410445d0803440c000c0340310344da48001c080326650308032204901c0f19480440c0d48982d0700e0f21001c0d83c1d441d0040e01601600940000c150300003000b480780c02604000c5041001884502c40440103613503112400b88070a13456106a00000806900104031445a180c21180b246a02130030b000d200704100385d10101c9131400e010f080245034030003c0c100012a0040035000d05450756810b150500520381c0b6207503005280700e50383c20030a104d100900840c0c48525600e50707040000c3c16108400302103100d4040d12942121480d2201541c6080220119038a00e000c0c00003641008510346501940c540d01c8 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 658309631 1250 658308381 658308419
    0x4060615080405031209070b0f070b01090227031006140a30020609031905010506030105190b210d1e090b0f04121a07170105011b020603040c0e01 64
    0x2d007040200c45d01804040c418107522000340b908841d4225941d00b03104080341e1000444024454001c00e003002000241101ca42c014507507000e081d400c0460710007020b050304030300b840c010505e5003104030500440c1d10140045440c0305031071002005032580e40c800d04a019101c000b8024460082030724082102c0400702203200b0b0002407420b503040d4000d40c4000740c0070030b000c0d100400c0e81d0009050200c4221540c003008103800750b050062603080034641e9490f0032402d44901400c042e100364108020041001a000c0e0313100c000c4258010081015811741c1c01054a1050241c405c040e94210a071100c4661640062018145d91195446058503640f0782000d440c1c40030441480f00010f00c89480400070080700001900c0b42d0030180c2c559501d4107035030303810f082a41d42040e42c08907038007140281181035150000500e03660100d6503040010500c24400802c2980702414094141031114080048240c0b8080e040c420b8a55035014143c26078034106824001d10000b241d00c201040416424004590719038019003103100e0b8 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 658310881 1250 658309631 658309633
    0xc03060f070507030306030c14031c020c090402060d11031f05060703050a120c03060311191a04080f03040306061a120a090f03030b040b010e0303040909140604060615080405 76
    0x180c441e850112482c2d4041c02d003d508040e110b400110210300c98030006c5004210010003200d04031104c1c81810304044120341d24a41076942d4071041c01c0516004903a016440e201117a180081e59103030710000c0d551b4003411030b11244003031410414240c001c49040040d401071104042c0c1c081e01d0001003801225410b02809011f8104800b8044d06001901400140c007500c46c650800c440d07000c01c0446542e01700d825001420700000d8840d4020400d00c42089051030700b8031019100070746000c45800181c450480036118a100d410809400800740024140907540540b80704010780390444400151940d5a40041c082501c05528201c000a40c0064084040110480c0712180505140d622849030300060303001840700c01310a4840502a0001d180003425614481c0704e0f4400080e41c008010500040710051540075061203048010101142d4001080d14107c4401d0040071413107400a1408401c2150403005c148854800d160078030041021a4001c5030507036844e01c0c0da4100003048a14100c0e0800d00c10f403409412 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 658312131 1250 658310881 658310911
    0x60b0a0503150c04210b0a02271201020a0e1215070c1a0406021815040905270d140a0512151e03060c040e0f04060f05070f020c0306 58
    0x201004115501e64010b8044856605080d503815960003038170140340020411654842070441006504001c180c0c00009108003142848101079040e100311041c07021500c0c0540c0000351011959650f2118030b541401000000d5450f1861280040c081b0540c4002052041007034a0310300101c444001a04007820035150b0b5401a641c0359500f06842450841c00162100d841c109105100c00030f0780032403a80940c0c40b86031700503a6503000b2010045c0c061480e42005d482100c460300000310164884003910151072180000041c2503c5504040341c480b0341c8034400d42c2d1200c01c1960303000781e07401c4049080e2000105075100e5421002010f00004243c1c862862103001140003400000b00b162440301d802c1b60701c800c5422501e9003c003858070002d904062543d500b0103103092513190800031824103110701a00f00b50036080d8507040500b03100221040750001002c01d030f02c0c001c0c50030018090141c0c5400104103021035640401890401c810018070f106800100c00c005481809113100c25804d0005240380f00705405944010 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 658313381 1250 658312131 658312153
    0xc0316050109120e0907030e07060518040c030b0108090a020a270504060213320102031905030403031a0d0b0703020d180209070207080d0f05070b040b04060b0a0503 72
    0x561006120a98003507588080d1040055148001c00058003030b03e40360001c5041da0f80d0100b0110020003070480e403c05061100307140030107200017079960a03640d442c1015902d40268101e0b174045030184241d0a40c1c460b0521403683c3e500d82e011340c01089603407001e03a11241c0540d60071118a42c4c41c0302104000350030590340d50040000b0750540c89805101205101c000c1c011a042c80507032016544150340690700d10350300242e110b4003402c1130351000b0014500100d040c01c02d8409101d00300681e00c12000780c2114806103503203030041030b8802e104032603110100040101c00411201d500503e50341044a04030086403512550359280114482c01d4007118000a1100001e20025555070304c0814025210200389a020301020f0b400302c038180103102002c3e4400c4443c1103002e200b401044144900501a5030035504203c0b014082100f0120300001a4007490900802d14500d800741106c40c0d100302c0d88050410b240c13100c14401001428147c0e540100d01a404c280141082e0504109040781c0612a682d45940320305003000c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 658314631 1250 658313381 658313407
    0xa02060c0a050715051503070311091803030117011104051c02010513031a0705130303030b0118091b0f0507060510050d0b1f0f0501180f08031c020c03 66
    0x490100202e203091070500728075a460041e9441031680e40380001d070720746082003081c0b60411284004118210000c19100340346441d00c003101c440c005e134841d0080d218140010951262114040c1032a030111080b01e0f0b681da904d41844040d42d040c120303050125400d285011000b00d424a09039015680010400e0b003c00c1040e020207030040f410344c030003241408803e0060076400d400400340711006500403800402c0350943c501c01c055080d48010084005d1040038442000381804600c0150b060f01d615080c009203442c502401030f100160082c0f508200900c02240c0410142c016800c481e130180303904031400b402540b484000341d880859620307051001079002e014640100b6a1600b1281c0c00c400501c030714000003500e90300499100b8507911000d441e408101d5041c030003200400244521052040c00d882c0341014249003900603800e03039034403d6604210650600d00d0b000c0d954214070900a140f601c4e0390300001c035075a0b0b80706030304c80d01f104402c0e2003864003409040030b80c50303024021a8140020b110180d85001d00e400180 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 658315881 1250 658314631 658314637
    0x3050d051b071a071113020a080901091e06060b070c03060e070501120b1309060606080f0c030f150d0318090207170705030d0f020409051302010c02010e18010b12010b0a02060c 77
    0x5450070000307030140101603203030410003108200010346c000d41c0e60036a104020704400780103049034100ea8500305050002c00d4107421404c850000203411600030403040d05161002d020240c01015100d080011660100050126045c4c2240c0c401c140038000f001200311200e03251007552140e0350200b06122042c1c0e07003803503007a40044008a4018190b92806078002220300c221040e100d001c941e40340d59510103100b0503820104e0030740d0001c0040c00410300f524081240b5180d501016040f4050000d813000801c0c4140750061400d110303514042c0081c2c00750000c600b8010300c6406100360954400700c50400c0400c1850a0b07000302c62000b5000009030700c680344266200388055205d00001d40c0c040c00705100b8100542543d001d10ba11004081101585030380c1030862210444a0292104281041c0e82d1100b00050740c0000d800001180c09090030030198400c207021030525503210762418110480100040f50900c0e041000e000c004d0085040540d190f030326440e0006080c802c5005440150388041c0020304000c41e00b01c01 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 658317131 1250 658315881 658315883
    0x601050a031104030f05070b0c0304060e1503091b03010207020303031b04050306011d06040207031e050904020d05270a110105120c0d1a06040b031003050d051b071a07 73
    0x842050315114101d9980041c0c00032212070002c42d2117002400700801c5000060144802102d141000d8008402d80e070303104510480f002c1c4480600719080f2555501c410103030b000407181a403940c038640032000070303110550b41441d0b1160314202d000501880c00c052080d16600c5034041c000b10301d9500e0b142c080215444809c5d03150000300074100000f147c146c5003884110b0003044001206040082c5030840382d102ca410042201e80528814400080407907032000d5036a0088a8106500602000512080b80c85116880c0038542150000134880c460a0507940024030480e160081e2100c1c0c1d1000d20b00c40211064849401d50841e4000100d05010981030f640c41c06a094050601030300c0c0078400c00c42e04421410031a01d03505021030115035400a43c455000d20403140c4030708907a0710341003411a400604180564040d1740000040400041c02c00c86c9010001c0e8003440e0880112030580e0031b49080100543e020400038210070410500d5004000f0000500c441038070160801c484c94544140c901307415070b030003481c0 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 658318381 1250 658317131 658317137
    0x602030c07060311182b060c1803061805010e162903180105160e01030c0f21050f041506030210110a0b0f090706020c0d0f05032709090609060601050a 66
    0x11b9172084000080100c2e48020300d80c044003180f20310609005e0201c5400b00900d005100700039000c030014140281000d816650700100006100c02140300d944800c00801e400203200c1e61900c0e490003031030744000500c07511000035100c91848207a220180700c2c0301415444c102c00409151510098240c0781090041d681c03141012407502c8007034042390855400e640054441d41040020905401c5445600c0307800080c0b10315082c20b041c06210402040140100000403003d0100003c140004090350725200da0b55818401181080c4518100110500074005050380c08446074182c0445c0031868030850302419040301c1c0c000f0503007505101c0c164002c2d5110782d03610841c0300c95030040170260000a00c513007490300d008994030388000c00c4610740000d03181e03d00f6069800200075948940d604951a036a0051600319595008e00800c1c3d20301000e20b002d80c5980a20190002201c07030600c402c3e581592861500c0490441c01c81700580d1a440c1d00e0000ca0b1136480a81c0c0480343e41d000800041d5203075000e00300912031280340345 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 658319631 1250 658318381 658318399
    0xc280303091e060606170f01050108090316080d05070c030e010302032d0901150e1b0705030307080402031c1b05030d0e0309090f0106051c0b0a0602030c0706031118 72
    0x280b0089049020301c02c11100c0a60320101171003003035400140b107145503490044195035828604169001d1100520683c1d042003405c00001c1e03090030b0280b096500903100c1c41c0310104920058a00400c4c50381003103440050340707460840065486441040706581d41600b6880b0800001c3c15940110041d6000a280d19009903c0424498214408904c2008100300c200700100281c01d003132403a103081d2200404484c4004654450038030207104c81e03240d400d4000140c1d51005400e821040350382d070307494042c5040180141c01b010040125068020030702901c076a100b10203036072803102040c2c180300b03440404910880000310400e007260913030201844540d8482d0f0080048a041c42c2c0c076205241c0603139646148c00c0110703800208024070141029000c0c660410f101e161040313955810071400828038014040f99003005101c01020103c4108640d018402c2c28034054030700880c454840314003944d2a8404100240c0a01c20450000744091080c40703a4002011601c69480c41d001d4101a03d0700e46920340c90440da4010134003 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 658320881 1250 658319631 658319663
    0x623100e0319030e0405010b0301050f040902030f0106030f170f0a0e0f030d0c0218090c090a0f0504080a080a110406030902030f01050711070807060806120a0203070801020c28030309 80
    0x2c1c070b61191150300c80c0e503500c1810b0b070b18002400140c1d14182e0020300700e60710600050001da62030b0b03081c0d0507021109480001e1a4501070000a161900352600b008055181120100920020346852088180141d84000048150300c405200340d114101c3c06044e540c1040c009620120310413440700c40d500400400c18048031003d40002401d0000d80718060000c640000607810450402541c4180c10112519461203186460128541c0780c500e0081c01520924001000030001407403540043c0076a032a030141000710785000c0c6894603c65002e101c143c00855455000699025110b010348285080341980c000e080038508036060303018003001c1a040741d06008000c1d01005d828002d04c1002d03c104055a50a00310141d94102d19080010f60b4000f024140c106610510650741c202001c3c0350800401e41c2c050900d41c64603100c0c41c1c140851244000c1d80350140351000111050150041c0103031f4890f803020782d645a00140300c88240007140344556200300804007080000b107400b81d84200d4240d07000300c2c05c1241140c18 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 658322131 1250 658320881 658320913
    0x1b030f07030e0c0a08250308040506090a080a030807110c030718110c03030a11040e13290405010b0d0201122c03121509370623100e03 59
    0x185e040300010b6031021264007400c0301c81c0548200205c00d0401c00c1070040b42541c4604119200d10301406000700030000d000941c584501200e44001c20394038044d02c04c59020743c6002001c00d10142c0c0e0800005440403900c04070b94401003075000d01d441e0010b0080c0748840c9000a0054040213000d148503100340e64481d169014845a0000d0031180001400745980380f03800d2000c20201c690041c0c6110490109000030700a070100440d42603041500f40d86090303c008800d103002400142e10b40007140300c2e01940007070114992500d012141c0980d11800090000b10010f6082c000e80322107a85019001070405404600021250f5000c0032559110b0b40a01c11041081c103914207501d0a03120034403485504c00200800403141d1100703a15005a610148a01d40c80a40d5000800960000d0200003015403010358100f545000c180c0309000d43e89554420000003000076400d60010012481411602d140d504080003000300034082000c04500300900c2c0b400c010744003490486502c600d004800c0d802d0b00c0f0f008114825400 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 658323381 1250 658322131 658322149
    0x4080604020f060f0a0801210c0b0d020405060412110909030a0c110a080f0d030b011416170408011506080c0a0c0828080603100e030f04030b1b030f07030e0c 69
    0x22007900c0b541101c2d403400c001d0441d004808c5c0c560007042180150110002010030010208403121640007544458465015000038440c56111a038441000100050390502c00703e08242c4181c0103c0014960300170310020300130080d108540c0315225030810412035055a000740c0b9002c4019000b920101800b0a10b500403a8001c08250404019544220602095a1030410699484000c203140601942e0b07521000609120b1030000c00350b10000d404600d20350b143e201425845d010682282140c212200c00341c8151525038010301920f0099402e00240d8248045204c01c100d0440da0682d03a100e039030307030307a503800c0d991450300085984800c21421010f004007184085014004030090908070242078048821039a0902c2140c0c40070505004843c02040702941c1c001c101400d200240340e6002c160b1101c080182411032080c017802c0341030303908003207000b0040c00328800c0303214407600030080031500104105115018a00080360300045e200b04c04000104c07440c1c400e8101c202c0cc403942d501212020030b8000001100c0072 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 658324631 1250 658323381 658323397
    0x71401020a0309200904021003021e040519031709060408070308120a0c020d050d020408060414190b01290a030c09150507080309030405031c030501060504080604020f060f 75
    0x10761660105401e22491009100459240342d5400c24003004c0c040c0458801c1d00e000300040c1c070885541181920540c02501100e0800151145000324039030702604061154001c0d02905000b8144034046141e44840d4962580c1035907000b4646820b48120075480030b80d0f5611004016812a40602002443c6403081100070007461142e145103032512100103100c0d451441c001c00d0804003a080a041c0200f4a4010540c50340c075a180703140080d515258502c8540c003912940e40619524410072040100344000d41000603030500c0070809668031241031042144500c6101c0c0d40207800b5840860040000e95002e094042d17291030710f07207044080d24030ac1514004850300041c0001000c1703604d03084c11030940c036480340784100500718840484c8002c4814010003409401090301c0103141c3c1600001094903e8810000c3c0da000741402000c6a0449481c00d03013600300704e03080380c1203200801c0c20306001080d25030080c0161403d0700c11407401001141c3e9541c08000c203080030600c6058108608004a83d140010600109055 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 658325881 1250 658324631 658324637
    0x411070b0406020702040f050105060d050a180308010f0b0301060f0c0302010603060614030601090c120b0409020a031b080c010e100c0615300b090f06010906140a050307050402071401020a 82
    0xb4030a00c5c0148400c2e241e01300d0400e00c00901c0c00e001804030b0b981c0c0b4015240b0700a00c03080002019135900011000411030300310000001030b451100002050b600180301c40c1610304c0b0a10209049070b65080c1001c66004c00e01070305000c03565171111a1100f0344242c448401c103d0281c40080b807c903949441e000103d4149410418800028828041c0c90b8102082a1801808940020400390003c890020406022032110000d4a0b4482582505980d1180c10642281d50014000420a9968500b8200c2099100040315415281050005418001107860a07000b001038442c0b0914100800420070150030841c40c000c140300d00c140505000c10030501c18004201c13451034841c4009130a1034500c003450000442028800f81040798401c8614582e01200a25254405603da1480e1160304919041104642c00000c09120b10f0000150812640d00a04100d6120f2800840c3c070402c19010b21268000c80e00802d601940245400c10690500394024010390780200b0700130803045d0302000d83c41d00fa41d00070701500b000 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 658327131 1250 658325881 658325887
    0x2090a05012d120c18090b04090618021c08120403021e0706020c0312070b0c0720040506090601170903090406081c2c04021b0d020705010c0804050411070b040602 71
    0x410fa0051086210307030041410080620055014500f41c012454050030706070507210207082d007250b01e4a4100346c3c107056102c60700348920315410a2000d02609030810036882034004c1c01701030702c09170400e9040c081030300e8112102a281560950201c0403143d4042d104404511414142c3c0324690f00280c0c0c04060404e804016007041441c203400285040110200c20b40b107500720b1401d006160300c183c42142c08e01a400400900b15a0b50205075800f140150031001c1c2588841040e4180000e002c482400861801140c0400141d05d41605101d0058030440d03010340894880308002c0840801013107144c1c1d00c61481c5045a1518200c1d0002c01c06803131042d40585020f0f40800300d041400680c10303800000d00d118a207800200c0381c0403500680e41c400c0a075a0404036a1f016a110b264068540e81c04a41403d800340b02803030083c00300540d4055461665110290041c012420042107a41c8a00419030406030003499941c2400c4c10003081100900d0041c0320b4406c03040d4104600000200c3d03108005201c0c40c090000162 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 658328381 1250 658327131 658327157
    0x7141303050f15090309011d0303070221010c050903101d1905010c03110a0302090307170a020a0608100303110a0506042001020102070812130b0c1c02090a05012d 71
    0x180d64103010f4815140c5810502c12003006923400b038000c03070f500e0114940c110071294401010a04500c510034000c1c0d04452140802c0c04000200307a5040a00398600c0001c110300c500040c3c08503082c0c080d4600c040c1d499008441460f4032400c05405c00b2800d409140c51821407544062420340c40c065030382034400035441d40213502c82c043c07000c00c0c800c0398245c034503500781400f4241401540c0c00c0e2911031045100145a40400e032184981c07401c001c001c018100170b000c2c00c4902c0340542c40070350341c604400384100e01ca42d4240c40041030a51081e00350718021221510491141804d607501540c0400c140104e0296510070405050042403081103c24011402111102074113011903141c03c0c01c010062a541d415603004001c16000504070300110b0f148403040382402051526580000c2c010b48594010142240e480701040c031818200000081c0b500c1d40e071079291424034802c4c0354440f0042e070040817103e80c0d00c503482400400495002c2d54000c03c145901942d4240f0f102020700c1064024101d004403000051480101c1320 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 658329631 1250 658328381 658328413
    0x621130b06102106090203070e09060f06041203020307080f1e030709060f0c020424060c08030406180605150f03011401090e0705090f0a0b0907141303050f 68
    0x107900880d007915042c2004000d99006803403200c18030051040392000d480540c40d420305075808000680340c03022065580c0e00b020b6030000d1900402e0400c26116032036070404100b80385000500410212809045d00d42460b1506039500c040303081010003582980820008280040e0340c40d4010321070000f8403800030742c50701605070300d00140880030070f14550006c2c1c08005105006400040c548100d0340c0500c0c0019141c04903140883e0500c0c4030b164000d410070f0401d4a42c1000708681c01c030110f14407640e08961510165500800c40c0d080b604100007401e880400c102080c0801c049401c0004024070302680c5145c103031510ba880c242100c030116074031100310300d02d00d100c100c040ca45101e008105000480003400f49100d49050207003820010f10680d02d03000d80e901c038003141ea203134148a034500801c8020050009894000d042040100085400c071030710f40d1074000c9401140c9013001c0814040c1c10580d807030040081300481411600c1e8441801c41c855459019000000144200501c0d0b1840f041300000d4020341e5940080a = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 658330881 1250 658329631 658329653
    0x15031014150319020607060b060304060c02010b1c0209090a1703010e06090403050d0b150705150c0705100203100f032003190b0a1409030c070f0b0306062113 69
    0x21502c03a4029100604822035400440c011890301114102e698400c40d00c5c25100500350700c00c036a41c100002200300003e020300c5600803e030b00942c0ea0028000c42d2000d5040104243d01c0d4002ca40c2107036002c41171034002d1f050403803400341d1101c1c211040301c0158074140ca071110014040c6981070b00b0400300000500c0900441d865031034206e8002da9042103642001d9401520502840f808016015640d02c103a02040e03442d809500484102c956500d0750b00c0226080141d140d030195003040412030548400700c0c00c0181c0c907100301c0d07846070341100c094680c49a2003400b00010b0360015240b0f0322940215540400d510b160103420a00640c0301d600040250b500c09190004101d6050080e280709402c560404419103900d2250000740316070101d502e1200d503490707011401c000c12f400003441d061140811304020400100100801b00201c0c04411950350a907584104089070307005006181e0b00c035205002082090078004003400e000c3c0140c05000d030403104d0a040d124140c54003241c0700c1194030002000340b0306004d094a11 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 658332131 1250 658330881 658330921
    0xe07120318140607020103060e0a02090909030301060819020d020406032301030b01050d23010e0601170309040e0a020d05101103010b0703050f0c160513020c0615031014 74
    0x140814180c03805074100c8290080082d05030040b500010314004580c4687d002901804c001c901594140c1081d540c0c1d0f8000b034120030440c0d8069141e2201040f00340b04000240c074100c40f120b42d40c0c2820b03a40c0c1d25091b08040700403c0c000142c0603800f070000110308a141d00141001d40400c0d1350020380c1310001c41031080540440500600c071900d0040050003c9020360b0343c0e203819103d0a882e01d1758007808500d800e040610382e480d00441e018423200000305800c1e206420140c21800310004039070756a42c80b5600307407421074807a01007101d090703100700089801c0d81010380003144428403210585103e800c080d00440c407000380b030f03c01c200d600e0b801800c02158804040e22640b404900d018032040d041d5810902213030358a104d400c001805001c0f01250b00a0b0b411001400c643d50703005160295000302d400c50760071604082040c01058070074001d0820360f003004200752003559013a4408000408140e01e0305c0c80b00c0600c1e078010780084c60300b46c060842c1c0d5802090b42c5015032454550f818100c10820b1801c1018558190080c0103 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 658333381 1250 658332131 658332167
    0xd080403150b220b0303160506071e020a02040504020d020607031101150602190804030507290304390b0d060b16060221090105041203060609090509010e071203 70
    0x2002c02c4801e81d03e421440410918000034041e6007101c00680740d80102517085070f40c04c43c0c511b00041081000f0400c60300442c40c948030030790015a2030102c06c0ca0030b00301003010380c01a4010b20408000d42341c642c00203038000f03002070605078180d02e86401040c40340d800b40d1003d8020580c2e101802c2e0030910244a20310082010204800a150604100a4540080304c03800d403d0310003240005002e001c0368a040b900150360040c1180c004903a910079a017114820f190196440403203001c2c0007900c0c2c9601e941142c2c840d075444074486c141031480840d4814802850510712100c3c0b2117150502c850400407a01c0c1501a1985090164135466030050300360a64559401c1150540c005005000703500703590032020540c00d40d000d00007588803080030f0071a5603200ba60415104203e040789084c032080c41819032045002d01c2c02609000100410001d081c1c0617140b2921441c0c0001d070b012101005081c5040d0b104079044840900040703083d01c11741c140c2910f8010303107800036501d18002254190401d42c02c4440c101074208110 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 658334631 1250 658333381 658333399
    0x312030702121c02040f090c08060d020909010b03030c0f120c07260105010303050304060e120d090303020408150601180e13020f03161806050303090105090d080403150b 74
    0x240c000e450b9008a4494201d00001040b02498440120034945401c1022102151195510103002d442c41c5103d20410000030710308040754611a00c40c54000c0d02c2984040c0c4200d41100aa60a02c0940080103102d4050f44d540c3e869420b03a540c0e81800207110340b070f04020040130030300d480c40000c0d41048080d01e20304490300801c000c0c440000c0c0c40490b0070401c49441c40100c1c00003681d080800f02c00c285460000390000c0d443c03e0004001c058019000c5c0d80200d00684081084102c0340344165941c00300d508989089038000e00c0303828507102a0b0303003000ca00544245005800c080c0e071040e50078501341c0b0210a90035042d0f0b045003001102d5910030b2075808501c3c08100b6a1002c80c1c81d20700c00505441000d401d040750003030160429010741d101c0b607200034001140a400c441450200740350414500701e0500a620110842a00700d15550ba403502400050b5400200654035110000e001503800d0713070100ca0110f8125481611a1000ca00f441c006040114091001601d650040c10150301c06c68070024107071489240a0307 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 658335881 1250 658334631 658334641
    0x30702010b03031812030c0105090616020109020f06090406120c051002150103121e080a0f060b0d0513050f01090c09091110110304080c0315190b06040b0a030506031203 74
    0x1348482e81464801c1d80c0f503005582002d00f036141944140d500344a507540c205030900610607400201207114510454002c1d0400c88080f00403820f880101c4d4001c1d6020000d00e102c3e98140c80c1c448001c00300300c80c0080000031869543c1410018020104c1015150310b0448101003106091001350b421441c00544080d208111806c0003481213080c041c0009080780c3d20750f00b1440c400b540141c07444c080c0d110f0310702542a02109100700062030088103e031401422402c00710383d400e642925003d64400c0e80d4203418030a0403c0c07502e85100c0000c04004103105082e81501c1c07407010110b801404081c001e0f421072400407c2c46861400c4c8100241100d42c08454000d00d000c07403280105140c0080b984000100300da91084031a15441c1c101c07033014981050b035803103000005001503803400014081400c020140e05440b0741c0403805400e503011213400c5070419020b12000041c1078414009500508154800500c4e81d070900392109101c10103500544c0d130040c04a40e84400740302c4540340400540201d0798600306018a14905 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 658337131 1250 658335881 658335907
    0x5120a1b0804050c040204090902012706030e1c050703110c010504060c1a100e15100c060905030406120f09240608030c0d142104020420030702010b0303 67
    0x22080918040050781d40200b01000002e0000304c115450090040d0b441e1521105c07001d000b070144540490200b007040d02441d0002e00b400301c0641c0a001c81e0f070301081e00d281c80d014069014001030400d240031400b0740240e900c940c40b1088659a0100304580e946911850307035140142180510714003c00b45684003120380e081581c0d104003220306991240c90b04140c0341d16140b9014800c2c095071102c8801c50b04214040028011812449408880c0300c40c10b041c1c030545803050040d00d600c100c03604141c0c1001d0b001c0c10b40e00a003070003580942082c51195000140e42001c2e41c8445065400541111001841180c52880c200219010341d64800c1d41005e030030002050582c1e1a0258151860001d0078a80e92440e5010b1032026550302c684001d01a80003a00d0391000d052064680399103400c8240c90100e2030041e8a108000110700c00ea80a51a0f40080010080e030a190010321403c00140b089a0250315500c2802e00030494017449400404040303891034403820701d198040d003035031003030403c15000e0303402401aa0300e0102 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 658338381 1250 658337131 658337171
    0x703060f060e010c0212210304170a020709020f03010f0b0c10050a0b03150406062412110c0706030b19030803180307030903030806010f080f151005120a 67
    0x1030609119802d0001c120040c0d656208601010754440f040c00174403030038078101044030030000d8400404050300b034031108240709050109440c06005040c03d030a00c007004692000c02024160311900480307688540d1400c442003641d110562401300d001c804001041035078080440b060180c148840e849083c81c0c90380c50305a55034005243d040754003c0e01c80f000300b42d003034040340c2c00110a003001400b5111401c200004030101d4074020b80b030450b91907103000c03000500c07581c03080440c0a01031021468207100c0308460348100c2e4411000c100d04e4410566071842d24182201d48001803990b4005100030b0302406107030560140807610324803002c0e4014000c7d410350042c440e00d0721840354240d95004030026220307194002060a8441c1c00103e1110300d2000155400070b150304070700c2c000c044070300c02d0b61400e4541d035038200111480e135005804d4102190240c80840c04006082c14190740c0124008840000d08076a080081c9138410442149404984001200140050071003042542320204071005c2c031043c04001c07203685000d9 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 658339631 1250 658338381 658338389
    0xa020f0114090904020f060a0201150510080106111005010816060e0d06110f0708030f0604060e0a2409060f120f1511030406050702010b01030504120e030a02090114090703060f 77
    0x2444510000703046580754421b455204502a00aa84845070550080d0082104141740028140d01d50400145441c0c132413075040c1c40c010b144c2d07144041c0ba46000c0080d1401c0c80090981070140c052401c0f0000707180f20341d00c51030717000b020044000d11305100014036001846800d90842420056442c002010340c0d107481a88403000b03640148001000f0002c040004514000c2000841d4407d00c0018544140817010707000c0c500858842091a4458a03414200030460302c4522460110440c0d500010740c0174180e0780d201d20b00c5a900c401811b00d2002041104911401c5160403031040355030b441c40d050200a10254803000941001c024041a00c1a80e03208e0b000f030300002d901d004040b180c030466800e2101409803c812030308103480a0103512030505140002c05808100c6041d0019813a10001d07410a610a001b1503001d560030100c01840000c004a003141c0364641c070100c0d0354240c404d4040840041c0c450602041c000c03c04401c0c800f0f4401c111104200314842c024044108150400e0b105100d05651030b00d031b400440f = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 658340881 1250 658339631 658339639
    0x90605042a1509080712020316080606060706140f15030c030303040b0709170c120c15030705071403192d0912031e1403010b030a1b020a020f011409 65
    0xc0c40d00003003c5441074599003003903001d4040c14100140d00180c83d02060a4184210142c070304c2400588100c0c2c5004000d03104110540e404000800c1d007a0074440000c0c01c0d15401604040b85000c0401f11990940c8070a4480e082a6400c00c0c04100c8041b486500c0c004038100210090041c169214001a60700d00014101030000c0d0412008501d0b507601403000d68005142c5c1000b10103800c0c6d40e18101035243d60205107500d000f0b01c0c00407590f858503040490300c0d4101110052030f0702440310480099603020b400003042e01e818030130108000c0011402244040c1049444080155a40c1c90140e035242e50b049000701b00d960030b100a04001e49c50740390511b40c25111010360308164101c03410f110381044072906d505602042d410186003c1160078194041c500501c02c100c0000394044484070040100d440310581d524030b0b00f1070b090034001800414603010045d40c04c400d10481c0070602e200071244189400380428006409a440305008c02c3c02c500380364884011440d42402c120608492141c016400341c402d0314496486 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 658342131 1250 658340881 658340909
    0x6030509010b031f0902030610061d0d0f0302070b160c0801020a1b02180f07020105060a0803040b0c011512050f0d091511031801020c0406050a06080c0c01090605042a 73
    0x414010750022817110b800504039195420000a40c01a100e468054840010841640c0c0a4030305c1e82c09070b110a41b004098004440c070180d0b9203440d21a010600800c80860007440b1000482c8020840601684040074081c88840442407518902004d010340c8102d600340d00502c000448650043d0150940c018600d0102c46c007850307240b00180408005061030001d0168a03401e00c4140c541352a02980f213001d0f542c000b080183ca40c4000c00c01d80a610b840b51032010b030300c100014418148074030090f04c6180d0352000085407540c0724a148140082c91038000001040c00607516800b4000e080200b45804210b4101a01c032444031604000c2c00701c4854024503c8118409403194261403142c07454046d226200d0041d41d45030820000c8d01200c100490b021075005200c1c050480c01e42c2d10303181c4545c60840384005c02c1c010500745000f07000d80e44031300010007003065000c1c10f01140c1c00f2500300380a140d00040c883c142c005114a4103103000009208100c103028099426010031451a00e0140d213110140d40014000d40c4c0 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 658343381 1250 658342131 658342183
    0x20c1507082202030703150b0d080405061e0a0c0203070b03040b0a020705031207050c0c03060f16120905030d050a05042f040f140c0c07060f050f1306030509010b03 72
    0x10320402902c0000b9058400e0f601d000081c803c1100c10b070b4540303500510b0207000311b0028504005403452411806800510f042104021a2a0440043c4016032905a215003484510300c2c8110880d00703c0e08480d004500d6240c0301c07404500d003e100480142004109090460419807100288420020684010190b00084070310601c4001c000f501d40c3c0d0380d101c000a83c03413032074030000c020016000070003208100d11541c65030390150b15010030014800e0a4180f5241c41e01d95441811040404d01e5285d803400340030001040d2814001c0a000e80d0314000e0085000395585d4208022030070031a14000c28040c01140b41c00107000002d120408544401c01e41c0c000300d5100141c0d01d8403c1c15905a40051290b407152800c07140342e0320150b00d600a100f0600c40130010012035519201c010400d4417918001d40e5013604010760520215028001c0130a04009500c0d01c24200b84914002d06240d1340103240c102c4260a0140702081801d03418081c65a0104c0c44000074000580c5040201c0e6540d184240c3d041a94220489100 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 658344631 1250 658343381 658343431
    0x230405091b0306042018090106030c1205062b0506070f0c20041a09070507050304090c1209051f1a010804060912081b0301030b010e04020d0605010801020c150708 71
    0xc0b1405c1c482c0e001d2079030744e2030070040d0221204800b0082c40e4020301d010400021514000e1141e02070800c544c0c0c85580880180d488200003d00d00204900d40c40008030f42c07144400f42d00c1c1a1071516a0b40d28103d1120203259a0030810300c0c202000b0802e0041181500d40705894075807044c4000002540f00401d0384541d080022001c6624900c4200242c1007854112500d40d43d510b84041082c500310141e9085e2420f0301c480c0d100701c505104800c4050310aa00400081000450942c00803640c42e00f9407030030001d0000b1008842e002c3d030308203a4050f606584241b04418080d41c1c2010b100c122440c5607401005a00380b11500c0c02203600d900081c1605200201000070103000d0b10ba00007040d01544810302c06101e5000400107880906d05450b003980b03400da078450b010100b80c044002c6905a0b50041c0b0310099680c41e0060503240c0140040c800c0b03801210540607d00003609a020345806460524009a216080351088030f02e40200c1940b43c1056080e118280419281c00c81d40254010303603003d04440001001118007 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 658345881 1250 658344631 658344671
    0x4020a170721031701051c140313060e010f12021308070e0f01120b04060509011803090515190507290117030306100f230405091b030604 60
    0x41502c00012401100c2039810346115010342a200b51603480398540820707110314440200340505078100981c4203a8484144c4880002c070141886640c062004218106d2668115040022958401c100060f41880741542140069852100a2034480103030002d2002c020100032801e24022242c07940016041d01206240800c9400b600f81b8004884080317070780701002d99000c0403c644403c40c04036070000126015108500651000ba08030844020341e0b1216103804000308005071043c1042d650302c1c0b40c4060683d02544452004070b010781c550188291408062040001020a110354030140800224040d014a101074040c03c030401c2c54181c3d00d0b040d0354540b000d20f910b007403800d203401c607146100c5c00111004100c8006041c1e80c00001812054006003600e16070304e00043c0c0700a54400410900f5480c9a0b1050150b14070020142c034024140c0143c0340007140040310343c2d0402c01d4051070001014000d03801c0a8040b0f50b0008003003120b9203840301494807003d510313000107040a4490f03600c1e507290600c05134002e03c0c9 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 658347131 1250 658345881 658345889
    0x20c130608060c0a0906020313030b060d02040513020a15021c091205030301080c0a0e1f0510050711010801060f0503060604031e11040e0a060e1e1005060904020a1707 73
    0x2201d20b54100020610b1040d0010314600300050040d980c081a41c51020080c0d580500120b0003400066045658180844400426083d002030800d00424003603546d90203083c0c0038134107801e290390500a080c01804103211090300501c624010002e041c403e61a40022032502c030842c04e144548440c90400412900009168000415034000aa10700144100800294101c5807810100c3c0c41c00c03071030b1000348020705406200b0a6424200040054000b003814241410308480900701103200980701d000103400909203c4103138001134000b00d5940104400c6402d41c00d1040004d0070310107929032410700d00416041014103980c081050220205450391503403819940519400140307904480d5102d0f0074481c0b0a820003a080e50b80e810b5a00796000c65007054801d01d0052000e0340050104089181c4602d40a0103000c10540114030604101541c4800d51007812f0545007038400140a080040c4810201a1000a41845e04c14a103200c140030069a0388040c01085529210014084e10705485510303090400c1d5501c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 658348381 1250 658347131 658347133
    0xd060506040902040c090f14060d2c16050a15050c0a02041803020d0807080c07050307060504060c0801090e061b1e0a110f0a230307150c030c020c130608 67
    0x703521203006d81011810090301c003540c0803205035540e2540d4030400c0c5034a444045400260030002d00052000c2d94000c4504500c5002500c05400c2240c0e02102c00506c0c04403030741d959500103070342700404043c0407a40c1000810003110031100181c01d00d080170102d1960b144214050200000310141d550000744030b01040e95030010001c1050340a41c001c604d0711002e00c29000c400500850f0744d1901054000d00507140141d0003603403100030f01d5481800903031b000d500081c006d94491200b03020300c8001a1090103014400c0f03104000214450054150140c818441a044030480030b0420303a03641400b1400141c000c0d4858040d00741301c502c10402c010300b07814901c02c1c1c00c03a081220b02d5800314110401400d07401003400c1600e07903407054011a410301c81541c48270641c05200b0419000103090f20007042c0c80e118401e502d12281101c00d030501101941a61a5074001c1004a54140040c54210a00c001e10310442d00c4500d2a4117041c000580d0840c0300035207621002107454031031190070111042c0e1900d50381c004030103020018 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 658349631 1250 658348381 658348391
    0x3801031a013207060b060c0c01261510020a0b06090402040e010e1e0309090f06040e0303070c0215210c090d0602070b0a090c18020f0301060c05060f060d06050604090204 74
    0x2d921011552000300300b0b803442801c00003503400310b081005c00c4503100d050702000f410001c5040e800444518604024900c070181e82407602000c1500c032105820300421034030604c1c100340c404030010b100c81e10300307002d035401d007590403640c0c1020200300f000034542d92040c41180c0d2581c890343d4a1001030300070b04c1100852a4075629241031902c10800000c0e64024410508000a15074000c1443ca01d6881c07080340c1445d9002202d00c00030800308503140e00304c507030401401440070074140000e400062840d0411280c0e100001e294814200660a0110510358038001c1c0c100840d20b02103412041d64140d086000c1201301020b07294000600c4150030009941c00940020940222504a4141180690450764003075504840c060302040c41c81c41c2030301c078071000340c6da0100c8014400761030011a4901c40c424400c6900900d43c080201903850742c0324100450103002c85844407842e21420f410220300e4144018924070503806000c0511402d959000c003443c5034540c3c4001e001c20999503d0700030601070100610b00a400505007 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 658350881 1250 658349631 658349717
    0x2071502030304050c12030a0c02060d0c020706090603090c330315050301021326190515010b0319020408031b06070c02010f080603013801031a01 64
    0x1c0001d60080c1e006400302d4050343c29010400200301c0c40c00420070362a50040011500003802000c2424825000410f000d003048880c07403218091b1070343c550603100140c0103000300b4441283c02c10154001b4140c140f03401c0029192031f54908034046c41c2402a02c001a402c070414000700484810440312402d10140d014984015401010340074004503045a00e40b140304000100300c5050501c280e03804107584048001002d403420b01e5030220a084400d00c00040e1603c0107681c02c800008210781d0501a030922410801e2200c0d40c1001414048404000da03d600400001041007a9130101940d130400d0b8003034280601500410b51100007032103103030300809440c0808285442c1c80c100e100004042c900401041d68002d5484240440b00c8840f5601c00a021451620540b01d90601c03500003954099030141c000541d02c3c00e10500300402d4062a0035424030344080030704a07001120852411000c605080c203062008022510741520980300c2c0302c0509040050501c030007105100c0107081512454040804e1541d02030740c0c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 658352131 1250 658350881 658350883
    0x2060c0a061a180f0402270f06030a20040e0f0c01090602031617090d0609150b01170a140c07020103061401080414070b0a02070e06030a08070b0702071502 68
    0x60707002180300340750380c0702030340b411810101116524926690384a0b41d941c1e8560141840c001c0010344140e17041101540300c1402c145800d213000c0880c5c0210b1000740040d02d4501e002d4039583c00001c101c54001d03000031010900050003840c0c6c6d0792402400840c038a40b915400700c082001882c1082d0240303120310a041a0180480002c2480e01c0c2020007030b031b80d90754515200e40007030380c2c0e034800c610030070800d0890f908250300441c00080d0880f01c03200070a1001450070740e5140020310f41500b2501309456559541440038100118240c2074211000b08882c1444a0002e84d000a41072200058110041c84202400269041001c0e400500d0035955034901d19441e08100710058040d0704054000c034040b910703001021690103041e10203030030f400e1416034403401c86598641c0c8040f80c0090b502e02c5500c0d41d10480c080400d130b407495030026040c4101c1d0395000b0800b0710314000c001c02040001500e524041c1d00026031820210b2040c50450b10302c16000710429825841d0403404071f2a103141d03039021242039003811100855250b8 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 658353381 1250 658352131 658352141
    0x10f030e0a1a0a0c02031b0703060c05030f0123040b030a05010908040602070618030609020a030605070518060301050d03050a090b0d05040312110412031202040b070308010e060a060c02060c0a06 85
    0x140302200e842d43c0d6141d000c520200c80802805002581c000e000345008008100b81c04045803550506035000281d503035995000340c494010320301d07001c10b40102c10410040d42c401c0f0710a005060140c000601e00020b002008070b00c45002c502d0600442d01c03001080c11984080103480c4030954441c00030410a480c50415042c0c0350020b008030001809a0640040d11071711860b60b0504410140c10040c0020f840c5039500c400810808000301d0b00055804000400300e1413a100e150710074019611111364502c03c10242620b20f088980800c0e1182d0300900040c0f0882d00e8441c00381c52256410f050940c2d0318144050159002d04050380320310301c0a03000054500c400403c68210350f010b0352081d202c5840009922422400350b41e0084903030045a2014402080300340c1c0f846104104d098006e060140500408503507040a80e801500a8804010001501c9040551100c151170041c4032a1210b030041d41444400100c400891344a41e0b410822061f28220130340d80e412040f10fa12010907812030300400c4152400c803001e01 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 658354631 1250 658353381 658353413
    0x1030b060708070f150507090612090507090209040c0903050706140417010c030e060f04022107120309050d1e080415030507030c020f06010b13170606030607050403020d02010f030e0a 80
    0x10a40341d6030517246400341d00805008610310b80f1100c0e600c40c2000310896070510b181e40160801601c5151001c0803890500142002c1e0080100160f41c99001c80706000942d07003900c03a64010003548000404c081040801c0b0202035421620b08051015102d4107518041d028582080750201ca0207440d02d503000105603c20340310800c5985051042c180c0320521a41c0700c1320101d1f01c11048840712000240107181040840001c100d100548400d4074952403078161815540e50401d03081a0f5040e4181d500741900480d4000c000c000880b103800e40d0007501e65400c007034002c544407941d40b0360640c40305c090100290307070082c2c0d00948483e0b0b064030790b401c42001006018183c140d502501092400742e011003d03601c041403000000c0000130041680364a00b6106a007158031118000007104011900415014107035070400282540703001c01032546080803410035051020203401c900074028100000c1005889582c952403545409080a628181c02403000b500035000100e00c46499000f002107420410032030003504242c0d5 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 658355881 1250 658354631 658354643
    0x224040e1305071404050a051510090f030b040c0e0601020703060e12030403031e02030114010c1106040b0a2703083a180f020d0f0606180b0a050f01030b060708070f 72
    0x58440942d40008c4034420f464000b1911814100c045c1141486541c1002c40b6189143c035940d96a40c0c0c104044150903281c004071186007142080c0070510105048030805400640e1010b0000e081c1140082c0d0382d200148001448552500840400808140070000c1886040300e041c50741c0345070a00d030040c01040c3c2440c403a180c10700040b40c0950442e4070352090f00d041c1c3e64003d0031038072040c11004c0107442c0d03000043d100f11b4231580c400c1080c40d07090700d80c0806000282404080103403a000c00c1c150141030000d03041100c2c80c10b0107074011600d03403d14203c80c8031801c81f504030940664685034900c5c3d01c45403a60f400c0094200c102c0c03485000c10780d000395480001110241c82003c1020051181c00b03402c0e996000c09015040c85000b881003030162402c02e01074100c051060152030b4000c003e03952600c042e05e07007036845002e115060f2181042849018080c164100c101114000b40c3c103400e1100050704c0304050000715040664620110605c0d894000488010507040030385152034003120f107000c60401d85142c1c070031120 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 658357131 1250 658355881 658355891
    0xa080c24121f0305100b0a050307120209010e07050a050c0f06010b04062307170c1002031005010507151805011109010f110304060c0201170a090224040e1305071404 72
    0x4229400b035141c1050300ea00001a04250121040c6040a8103140c0141c540c0541d00200c000364a50b0100b0860000380011284504805554010004d100c1c8050b030160414070400e0f400c0000842c1d010046500f843c01c0c50030300d00d4039103805200e014034000913105045080c1c40b4600001c54a412100090070440709141d54940e10440f210490050080f002c800303101e5850410710480f000146d010281440e0610b814045509091001c50301618080e5010924820103500000740b00d0b6586840c40c81d0006082700f828024500b500a03a94040000020140a501d50344d850043d6015104040100c0c020300380c012009200b807021680964072180e02501c0d100340400c0100703c024403242d0003982c41809000d1b903100a9814641780072025120700230700c480d0403410024500304643e41c3e403005003000d030f000380c00f60200001c540c046407050144081d0088410010f1004c041814030802080000315011341d01103a40b07130501c036250040950005490340d00014650300404001103245015200c1800303028008450500c4 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 658358381 1250 658357131 658357171
    0x510062703061a04062106020c010207120903110406150305090705060f12010f0f0b160206040b03090f0c030c012105070203120112020108011214010e07140a080c2412 73
    0x3c00c0d04032001007000e0488800d81e0070b00890000e60107030000185000015251034203683d80e04034410dc80760200004110282c40c140180004600ca080c800f6401b45d900b04140e900b8442040f400d460b2031711027502010f440f200020490441440200300500001e064151507080740031020030590022440e0310803003c0c400c1c000090349101441c0c00d008a80e0603a400705d03546130600c40c02c0c83e000d501210055040c14561142d040041c0c0302c15000308000c1018a15082d1241070000351181482409500302e04641d000c0c00d04250070b41e0700801c1c20610780301d003402d210f080d041c5100c4500b481c40340c814030050800b42c80c060400050701e8020008210120fa0090700307182c0d503a285c0c06a1810090100c6001e80050242d50044c00144e81d8410444002406105d85c6c1c2d840a2345501c0507130a45039224412007071600840030801c21044038200700034404408807214201c941c24590b12039610100a29000e01c9001c2070082101d0341c2512500c1440a100f40141d4103a1394040454140c0250800f5100c85406480c00078400d8 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 658359631 1250 658358381 658358399
    0x80613111804020904170a1707090303120b0f04111b03040f03120c1709010207090209060f03060120060114030d081501051c0b040510062703061a0406 66
    0x1800680c80344009a89640780c0f6004d1040820f0004c1044442141444c111000314030303900d011f040000b50a54030b040c07121380030182a0402c003d0140108043c41011300c030620000f50031a440c14546250500b0020704444d410300000d02d010240b00d00d030364005103004401b40e05005140c0041c90207204015003654041851030b042c035601d01c81c0d8420b480403c80380420910000c1c1c0f203140c441c1010f18103403610b000c0c944460b40f40c0390340d11654404010f10322080014046042d580500c0004010300500b04218145040000443c11920925100f1a020b800010000c1e4051380180d059018000245007011154440c181e0390940d034200038051154210b400a002d9041031400040c1e100742c108450362802204e071110322400044415180e03d0340d05101d0180325012101070041c00da290011511100410780100d28400d0000312580641a038940c102c00d0101807082c0f0b03030410099803909040302121807080e240b0300d521024090a070380004202c28148901c2c428407981f0190300c00796915007110100a1155a8402c1c0 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 658360881 1250 658359631 658359649
    0x2130f030b160c120c112805060c1c0201060b03160e0405070e010f090503030a08100b190807030216050109021e0312221203090e19050a0608061311 65
    0x524001d8104242d5050318850720a5401c000d02c01c40802c0300e102c00c01c03400107074031550a11400b41410301d031085040b0b02d0511f042d4140010325050382c04030300e03000c610105030391190310704940c1060154440e07401040303603813007540003d0040860305826038803414080c04041d12108112081c00000e1401c14056155240900c6014061542c0b03454006858502100550711200003204600c20b1195001000415440a10081020000550729000c5a26280c4103550080c0465042484445810311103400c00c0400194846600c0d0a2800d15001d9a034480c3c100720007074414201a1010b41213003109403010804150400005640b08940c1c1d00000c0484004000140881811459042d03100785480728071b8520301c80003002c010f210040e40c0c0c1c0f210359481817540c00003d90f81c2c3c86a42185400d00f101d90515500000e000301414000c5c0f49200e85007082508510000b000042d007955180c4e659004ca2199035096001c540180380034401c5d504c007403500f031980000f4090b010300191034803205040500b950349008004 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 658362131 1250 658360881 658360883
    0x709351b03010b0f040b0f100f030e0a0302070e180304090203011d060310020d0905010c080108151506090105210711010e120c1009051e160902130f030b160c 69
    0x1401511648040410010b040810100ca030000084070030112240c1b00d410380123100a40340d0700c07005a0075050150040c00c0310003890424203e900110302c0703c1d00082e8040f03256800c8400d00b11807020b0503112071103841c10b1143e103104410705611002030002445031054028504850354480394584500c1c44800500c940d0303404503225035154009102e4500f0664050f405031085030890540000c11018950b6281d085542c402c0303501e80803030848001003010710340130420600c0c49040c02d200244c060503c1502c084002845d5001c061040710701140e6120640d1042c81a907c0101c0e0030914001502c071609050300160900391b842000040601c03a003449944014040d0308500401d640c0200341003800e40b280b400094000250500103400343c0c9080780600c118500600501c14018400f41828020600c2d141003090850340f503117606500484000000d80c18071540c08812526940805039071400ea00c1300e81040b5400981024207281200d06020003031100140c00d45116095601100b41c0b00001900180d8100e000120 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 658363381 1250 658362131 658362139
    0x20a031e02101a09010305160b0a0509091302030303040605060102070603020f0f130b0a050c0114041a190204080c120a1205090d081813050709351b03010b 68
    0x8061207901c202a8801c001112401c2e2002103100a000f00166600c2c0e070a0f401543c0381d611468000b100354410020b44001002c202000c645442c1079082d0261040c020320801d46c4c400c0c1040030014406070f44005413124102d500605981d40c0380341902d8000e008001c1036507807030b0045c82003610220b1228020b1080b104583c0351103003040d04003800554241201d41c0080c1c6000e0307001444410016000f0329840c0071f02001503194072a55100c0741c08203010380c21503401404c44610a0000024040859503400d005074044686210f140c0340f950f50002c84001145801900072111031000a00099481000c47c138124400d038103c46030060544190003a0759603c0c01510060b114040d44070401c18158091401403080301000781000014183e00c0c0c9400c52240c2100b818181e031000f400320004042d2420340342d900c004040420013044a07081c4950000d203401c01a0044d080d640319480b241e040405002d00b8071482c4002680e00c1480c135540d86a65482e01c0e40407203910056103240980f6810903926040c081c00310700310000384c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 658364631 1250 658363381 658363393
    0x14070b070602091203070c060f0e15030703090c1409010b040305030a050d0605090c0703080615161b06110d0e010516060209090709080f06040b0609090f070303020a031e02 75
    0x1448810003944a5842c150b0301600c0058510903100c1c060000d446803900400f10300b81d00e58940100036000340c542704003101c10800c000c0c9504000faa207030705c00a21a43c1062034050f80700e696480c01a001042e0194000d0041640f807240003452040c0392040419402c0c040c0d805000503680c1d80710403201802280001440e94005105142e030360740c410009044105107644000c20102d0ba1031000c40c1c0180c9042d00c2294083c000050200e0500d90042192038014006940d2a032007850108482c0b411402174544525018004400380e60a20524040780031415040c464000d610039500c400c090003d00075080d402659001d403102c0f000c221401207017000e640031410385031a4584022a02c208109002e010f4084440d20360034000d4140a8031810511031080f849904c454180700d060803807052400c6001c203001001580034104120001d00300490190b04004280c0307005507586c4600800e03e040640b0441480890b1007a0074000040c986d001900900c254000c1d160141c10703040b80c0d0311181c12043d0440e6406e016134800 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 658365881 1250 658364631 658364633
    0x21020a021e03120c0d0f0506010323010b030a09080c0a05161202090c1902060108280605100503030f1804050708040b0714071407090b1507050a02041814070b07 70
    0x780d0784980c0139504c180c0341c1910040744104035400424074011451741c40e401c202580d41c042c030954654201021300120510b0381403158110408050140d400401c00102c0818038149480d00003030800da600c0f21000ba260320f1202061692410010000d441620501c80c418544940703104100d015a010345a48095007010b640034810950700c0584802056041040908a101551501103038481c5483e8042c020b194540f0015a02c1c200c0d61416400c40f04080b500c021203000c40c050b000d5a809903002a02045a9030354440d410124151a801541c00d400002002d0b104d001034480203240c4242c00008011040300c10105000c1200c034102c031070402050b001e50103e40410140f000240e8400c0040ca041103050040044200f01c81e00304075811950210f40c41446000803109124100150030701060400c6403803000400030f16000c40d91781586034081c00c001407407000c0c0002400f040c4601a0060024441c460002c140b6403802c80d002c0d442950704002c600b030f21000307500010611404a400b2005180c6c140350781 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 658367131 1250 658365881 658365907
    0x604140a050411130c0e0306190504110916090e070f0c020f040c0e0103051b070201121107140d0f021e0a0506070809121306080721020a021e03 63
    0x90020f807070300c0d600895954000d0392842980c0e4451811110302042e41d061070b0a000c0c065170b450800c13040c843d8005008014900c21b09000e10056010182804500d40d15181003403400180c1c07030440c942d00000300e1020004503061190707520780c110440b43d0310785002a031381d00d54004421000759403820000307190741000c10507144110034409031240005e00300000b6181540004049076101c0c1d0401c0081340746034661104543c3c25214403039010b130341c64a09140c803074601c1c085560240b05810001707040c0000d00c4a844100c40e02076012084122010400e10b0703841c4c100782080c820001a89402840d980300302c1034803510241c070034070586d407000e40542c00034043c801481d4441d01d40b06114854449a030b01c60490700d0f1000c100c04201c118081c1441d84c0314103615003006441c01c1d0401591000180785007404000c2c550000c04000c143d001165074929082d041a1924001154624040b803120344211050141da0440c05210354000d0101e020941c0071100c1d45160b0795003802c184040c2e60141c06007030700f081c00a41036500d1 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 658368381 1250 658367131 658367141
    0x6040302010f0e100806100206040512161b090e0d0e0918060c03070801050306070e10050c160f0807140607060603080a050a030c11100e010e0f010f050604140a 70
    0x14190410030004443c40000c54000c1c07000d80c442e440003c3d07244003408440c2c1404105100c0c000660320143c44145081d03110705079101d00d0050001800400003d02c00081d4100302c0407100744550007507803500e40e0424031001c8006110140a440c3c11a443c2005d010441640000c16643c298071030b490350700800942d80204074a00c00002c180c00a00e40400d2841d810001090148078882c040d04484c0707584034141000d00038008081604094000d50050b010310082e20307000664141c4070b0030203e80410110103440411a15401001040400d9204d1108058034207480c050742c00040d140f0404020813100e607a409407517603840b22845081c90300300e0215600c0545013400d01c000c16a150003001c1c0403490031341c0c80e6221101a03000403082e5000490120b4995003d40c0e0500500301000c06500c2d00c410b21100300c2c880740351590100e190300c540c40399942c0180d400c08103080d0001e412088002041c0c8e100a411114028041e003400412000000e140000144c001e240034812000c0c0c0818500f8586441c2d5100342e41c51000342 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 658369631 1250 658368381 658368407
    0x206100914151c0302070e060603010b030c030603101d06070815040e071a120112020907110a1203090b09010e0a0308070c0206030c04051e010516080c1606020708010207020604030201 80
    0xc143c460440d81c0300342c80300049492940c8a6070003010150f18020701c406042d000540050b109d282c04100411000140000b5241c1040c242d914080c0d50fa20359a000034500a818201c52240b0350802500f03070b82d050312113491030801c102c0300000c1d99203035030342d00c0000c5601010454020342c030040c20031200411814a0741c0b040c03030b0f40591203084a003242c0d224211442c500440b0344003882c00c5100058005403d2140c801014010b00c003401c01c82004449550001c0d00041009003403104010300c4107100d1b02c3c03c0f0000c110aa125607089280f92a121014260050241c068a00e080d13441c0141c900c013268030281c0510400072041c140300042c040c4c2a003143e50031141240090421010480d100014001580c2c07480010b5005440040810360b4661508003440010098014a50074020184c01c86c03c01e01c3c6d8001e0225458407021407001c400141040c50301c8500d6001d083d110070154840e488003455480314400c0c0c0c2e40c2c1030f18a15022143c039580c0d1002010300b80e20800d600250808000c1c401080154000c079107060b042 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 658370881 1250 658369631 658369639
    0xa0518070e01061b060f0501031b1214031303112107030f03110d0e0901080c011409040603060213030317040819030b03010c0210050112050a02150f0307020610091415 73
    0x1c229640c49031703419288400021079442e56120010800c000070102074205403002002c1c0c440c501c501d041d4210504849102d00034010b42000c5180c400091018004c0341c0880e50355401c1640216181d044c1003801c0c5264000071401800700303a0400d50a0b482c014640b10503404004010a5080c2c00c0d82c3c0d840c40f41c2001041300310140b00034100009400b440522500101c02c0c070980da4003800d1042c0c8400c110070303160182e01155076038002000e528000c5e40e21800741e04801e0f601c445090741d503107003400104000f001540d101504480c400f04080f405001d0096440045034043e55a0035034006811280649a25054030014111007041010603840000c1d0300286815030501d00300007409100c0040800c1c00d44d40108483c40058200210007100014940f084c903000d0b200b401c02a418003442c6a54490361031111b08406032040100001c00b00030301200904035040700c0e0400141f9034403803d2421010396580c000703603560154601d041d1804038038405544100262000314095001f040d4070303820b90810340c500c200e0b030707900b504 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 658372131 1250 658370881 658370927
    0x30201090b0103050d080c25030e030d0c120807210902060a0c26120c041a0a02070812030a051f0f1412120f120a0518070e0106 56
    0x801c0340460158021402840a0b08000c149568006c1082800810354130280c0c0c0c09004d620944002581c1d500710301401c850319908501094141500c10700148080d40341d05106428110284a80c403150056905105e942c0800aa80d6402030a03030b0361040032240b45001810741280908200c0c41c1030000196031400710303c0092101c419401080e201c0d8094a20390000c21040c90b100800c01080d64400b6055604000103e0583e80c094101c2081c94840c1003507046264120801049011106008850040c4554444400c20312819148034000c0c0c0c001880b95000760003115000106100003081c4040b6014420811b00d26591f40d01001400400e0098404661280009500c00e50b01d401040154068a0b8040f505800b240c500b650101440c42d4070b05072103008000700b107000354802d500014036080d21400032803e20303143d200c16441d90806001c0c0d0841c0140f100e810409000c8800d41c0d69001901035040b045a52152250303611010313586060707900c14204a003034490010802c00d80f0803000d501c2c076080250360040c0 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 658373381 1250 658372131 658372133
    0x70b04120b130f110108090c0109050409080d0c030c020d03140c0304111806040b032406061306030c09050409053304060614030f070510030212040516120c1203020109 73
    0x2200030840c20216441044e8044880456030410500c6600c0880034006220141707003000002c04802c500e202e241d018548965045007008200c0051703562007442c0d000104089102c500d0000c01420040f01d03080f0240c0200d60140400b14840c2c0200e08402c0c121380c403254903039203c0048906103613000400982e54902c00011b40b0603580d46680c840d82040e481c4640c0340c4c0c4142044810801101c484141e41e0b4803d0707000d80c101d02014245c10000980010900105803150f5031100e020a0252040040201c001000c0300e10109059801d40e01412003a001c0d6966101199194818070088a00038503004d003450b801400030b40c0303102c000d04900890031004500b034600d6180c0c00340000c03c02c82000703460403200c941d101c91003848201e00c56003086074150301c01c40080c40302011641000381c8138511401f5440c00b501351030113000484d502a804640340c0c95081e40340007006190038140503854110000042c0c0c1e0441c6143d00000324a8212590001c69940041e19034002070b161903407101c005442011308500b50754036260030304 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 658374631 1250 658373381 658373393
    0x903120702011e0804080d021c05040506090d020a111c030504030c05010c08120604060902040807030b0903030f1321030c1d0a180f1103250e0111010f1805070b04120b13 74
    0x2701041d16203140880c0c07609061804908042d001000c00d03101c1d03070140b002e1503040c95000400481e080e81010042c1c0700d03080c4200c0440e51880d00d42c1044000003c1c40c003103820070994048018811280201282070303600d0780303410045418090101020b80350540900009005e1100e40c40d1003500181b00400000b03c1d142d56481140690300b01350b00c0b901d000e802802c010003d00800460042d8800300e040065071462820040c500c201042c00f03403d8400517140f509001e401c2101e40200c042045082c0b815003040b5a00c060030007005400680078180004403034100b110f56414141c9120b188a0500500c00050320313040025440515113800982851180c403800300c014452224481d86901800d000e29865992501c200d02c52859444001c0340c541e039203034050200720782c0e5030b11204014088100340383c411448000310003514098040e41c00709100c450f00e04145004d04c03a070f2001698003030038410002d8400d2150b98006141090003180f2035004251401e039980000154016006544802e80460b00c200142883e2200 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 658375881 1250 658374631 658374667
    0x20f0d03090203010b06120f0403020f120c0d090302030601141f17011a0409050c0d29010c050c04230103081804020309100e030903120702011e0804080d02 68
    0x105011030303079808906066090a00030f8044802064803514071300003003113510300024000100088201e42c000310204007014824000b02814011082c120741e808554403101e070b4043e510000d5150043d04c5111055684d140c042c0c200c0904483c0c005001e41116882d05044c3d1043e64005440c05600c0240140018081c240003010400d00b610203a6510a5201c0800203102a000741a0002424406c0340c2400d180902d41100480d000c1d2801d00b0340124064844108070300c0b0901900911140031750900d0350040f00c8043c0c00e0725864070840e1101200c4200c840080056440c892948005000b0f500028054074050a003600700c40520544542d12050b070410040c000611600c081c0c0044840c2400001c249108000d10503000c00840c004030b0b421440c40c10000c1042c1d5860006500820009490b54072410000c181441a40c64509015083c0c911020245031108196841018100d0104d00003203c4696940850f4000e072640b580c0948858104da200d03600c03420f42d160095a070380c2107515020070804002d0004c0c0e07144 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 658377131 1250 658375881 658375903
    0x504050901120228180e0601050a12380601080a0b011b030507021002060720370309170303090a030c02040f0c0206040309090b0a0512070b03092a0109090c020f 70
    0x40091101b02c0228120300304001a407100384241ca41601c28011500c45103154089182d01c0301420480d040c8025184102110544100c20081c00341010711025000f9248810311a00c0d0999400b00e466490881c03150460b0081c010007400600e0505802000c41c0803c000b00c00114000c0c200700d13082003581d50002d03075426102c000d020016003052051014441c4c01c004c4080b280c0e2540300918000800d10040b096035440c0000c983c10845900040d181080e00103200f02da8803901c003151b078000504006007400340040200f446601201b61012a240d51560804800e40340109600000703004074051b1520304903061210b5070340c140d03031103683c440c2d00c00c4440b202d40c4900100c0d8a45900509494a02030070003400005140e1b0080c0b40d03e83c103026403014541c0e01d01c5103000680c4d1040307540c1002206441410f518000254104201c4480e002040c490244000510000390f002c54604403200b1400c09000042d8144000e45418085081150140300b02d0009800080004105204980e0204c00b1003019914042a580e070f = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 658378381 1250 658377131 658377179
    0x1412091c0519060b091b090f060a11060a09110d140307060c0e010206090d050a020109050f160f05010f2610050301112a030c0303070504050901120228 66
    0x541c000f040024000d600c002e04041314844c1151519908610100384158500303802070b000024801d065070f54180716103400c40400741c9456110f000e0f0840c05448100d182c0036030b040340e11488000032002d0407140100205544e01c40c0c03401044505900c1449000102d0510844040d030390001400303035001041010300301c214050b020214400a001700301500e000e0b001080f850464108104020701404001241c48810807180f40c81a694074440705c00720300400780c90600918502540e10302d50300c400e80c0095002005510154036840050b9554106e40091169214042c081903100b242000403900540301107446280d001c5e03008605d00300080c3c01202140007100c02c50418588010207000d503090901c50540c5004181d25001e1400f80c9145080c0582910250000d070b41068210500c8101281402a95119960a000c0729124280018040c02580090081038023460b00f84000203401072013211002d03100d035005491001029140d070040300540c601211000700c1c0c00d160000018000701004017000008171030304 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 658379631 1250 658378381 658378423
    0xb0a05040b13020d022107091a10090515090301050a0f0e03040e01030f0314030a051e01052206050a0e150f01020303401412091c05 58
    0x125180c0811000540b50110409503030140c0e50058840260030000302c1d4044038208100c12480c80210320790401c98200d800c8500441d440020303001c515800c410952041104028064000103040c003007101000031818002420310201049a4100300c000002440b06100c40c3d80d00e172a54010200307080d15010303124044019550800d50900f40014840d015810501c900550715080c0780607516443d5820600014085036881c141881c10140114030100c0020980c0040315100c3c5010003c1d0401041d040304c0400842c80b000c3e02803500748000000b03c6060f118000d1130041c25a03826040083d20540e000d0140740005d580ba28003040a0742c17500603810003054018050702003807901d00c003c0068113800181d4103008864181c40032407542e07004030542e0361041e19074185100e04201c5041c071510000400380c52a500c50260f101c001111303e146141042d0060003146140080c60034021150355400c1d410a044945031001d225504082c90030030000c1d03100b08100d240f072506400340c6881c0d80e801d11403021800305500c0800 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 658380881 1250 658379631 658379633
    0x518061005040f140f030106030506010303140a120f0b040e01270317070306030f0b09010516050412050a1e051218010c230102031009020414010e0d0b0a0504 69
    0x20002408030405a80750880c00c2924110001c22480f03154007a00021801d08a003401954550705e030858171144000300280b060a80ea0b00744151581c50a0205400240417100c469188003054800c035000308103a6a02c0c0710780a0781c030304000d200804c44103030007000041d01c42203080314950306c9004d18605a0300100c00001d42c504c000c03504c8098100382459079039008005083d010f02181d04610308600c1010014114001961000c80450040203203400090a0900001500782803200e00030100744030310100d0008100584420030801103d43c0b10761500000264108008e014140001e00b00032805d40c82202101c109003030310340e1003d03244c000e50351b2818405c850034034000e130500c44200800200302a0443c4914034040005243e040c110802c0316685040c4401111200d0400540181401d5400d800464a00c0f401458185503400b0b90300558106002100c0100701084510881c800c403000c0703810b15440806c040301000015501c0901030303201d09610001600b00300010035181d10300b0511031451200e0020312403400d = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 658382131 1250 658380881 658380889
    0x705041802030f062212050906040e0a050f180a02191703190f0e0108060f090403020a05060601090803040e070315141503060105030f100b07060615171609051806 71
    0x510f4101c1701903044484a20001c82c46c10114606031142c2d034a0314641e2000341c200450a540302d254840d200003c0410100000258280c3c052401030784044d074407a002e070311a241441c440d0003000b80d20a074950031003600d1000500d82030000c004000307480202140c54596600079592220301000b01031041d6000003030542e04045c0d5204810f408142e0904000c608070300d14105c010a20841e000e2000d0510440c0000304056554458050a0354030f4014404040d40c170b860318000303450b403490b61411505c52080202181a542c00b520506041c1c90301400114101032500f0300c0148103900103420f000a150f51841c0d0f205011034501e600e003024006a104242420400109002940b48081807190035900c060007440390300d82c0d00c0811a038000090001d850901d4642c0c40201c09190380e207901c815a02100040c1c400e007003180c503030009000c4818600440040c0b010b141402c1c1e40c00241000c80701c441c40c22a00000d51001c02500d03000394107001914000341031640ba40f01154296000030490001c100342441000314070f240c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 658383381 1250 658382131 658382161
    0x1030e1207140d0c150e1203040302011406040506030c151201060536060c1006141804170a02010605060f031906062a0204060906080708010e0705041802030f06 70
    0x4251030700481d1300d20f413502c0c0c03041c46820b558140c49400e500d5001000000104200c40305c281c107800b0700041c3e52400c0528000c0d0080c09486d0101e030708440c0703010014100349040d101c1e16210311005409040520b0b80c850800c005460214802c42d8032800c1401061120406800710602a151035180c00c1d40e10103c00031022508200750440e260032060184803041244a4034500c152101d0041d100c030b0380c5624007107a40c130b401c0c41741ea880d5002501d403400200142c503100a80d0004900c403815034050135000401010304500c00400c031030261a20450200c0c00490128075001466000941c0c070000803865119070024140e98401c01741181c2507600403060250712945000c041108140720381c420000c043c6030803400f602c501c001c05500b240410800d2108804125110303415030209030300030400c110a989840541d0001c0003180940c8003a4840c43c0070111761040c0510480c101300c000b10f40100002450101000003500b41d008643c8000e80046040c81c00580b010400e080e801010703500603080a280c03816035001194 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 658384631 1250 658383381 658383403
    0xc060a0905100506012f011407091703070b190204090b04061202090705030c09040213030b090706080c0f0702180403020105060a120602032e0302090604050f0601030e120714 76
    0x107454a018000d15a07008100c3c00c1c001c074030400c141b02c0302e4802c0c400300001c03102c052502c42186500b040c0c4004404140a80c040d8407400c199141c01c2686a00c48030030540c07180c04803100d480315902c00c1200d900481e41e150035280c2e10030440740303170f01c0761081115407940d040e038001d903020103c80c0e51500c041040d1842c1c40c1c002d07800586854660346040100743d03000070b04a0000604110148000000407a101e44042d0382265040400034009560700e003840085480300380b41c0351205071154501c40021424110020443d0f0303085600c20f56030750300f02d038440035481d441c981d2080d100240960001c110002c01030b190041000080762038082102c3c400d1803e410080c1c01d544009081c01e103c2c229841e400e012030100c03075400880e0f164022030300580702c0da960001c0c0c3c0c0c52940040704100410340d007000c441c0c4400740382c51000c0050364420790303c012150700d545041c0416128240e0b280c1c040d10300000006030507075129602124100b6551011114120204002c10085921000c8291040032005c51446000e502c00c00110403c1 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 658385881 1250 658384631 658384663
    0x9080c121e0a020d0c0507080f030c070801060b0316120f0f14090d05090406170d0207081615090b0f091206040c0333020901030b03010c05040603110c060a0905 70
    0x79100c840300a48680903941360b03409001c507558081c02801400c105c5400034150b42000c659000e206011880e80c0c9130070005d4041400e02c00e10304040349000e01030242c0d07001c40d2880747c03503c0d0441d1512076007003240101c071480e054100b1040c01032103503c1035400d000e40042000d00f41d07000200100003016000a4980710780c0c0b1540008602800c2c4646030f44001969048500e0500e42691641c00c2c090000300a40301551041d0800c801001001c8000b98000ca02c00311014466000c4480782a50b80c0782890325102d100440b0442d415009000f0042c00480703045200d91b440e2140780486080d40c480340d0100701a0010510b08030b8140001c1030400260a14120080c1d6030180400200038901d482d940d0761596816500000748121804114000381c5800701c20640700ca030300e14520221080d0700400c50303c8020b40181160500280c101442e9042c9414103109902d0f00311010f50318645000c1c149801a0050800d8011110074030008200480c0e80e01e1041c0b0600b80144034224001c83c6000550902e10f14204150b5001000 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 658387131 1250 658385881 658385887
    0xc120b0312031b090a080114071704143a090302061b070902030405010506040c2303070c020d1505010b27010c0602071109070c05070909080c121e 64
    0x60000e81200740d81d400703d94829012007202140c0300b100c81d540111840940c0281d0100d03804a02c4c40410f40004d1854510751280606580e11048121413401d420f00f15480700c0d10305103000c07901048405080c080700d480c4090803a50324080c00700c0381c6666401e0320415a800c1e19a0290381c0c7d40301c2c000003210280c5620591510000b05401c540014120b4801c0c4140510345102d000c4c59008941403d04c5207a000b44403150045407a450607003099406007004445185c03041d441d0042c0d0820081c0950402101c20448891720804e81400a032a81490351000c0d0081090107041003802c00140c0d10700d0041ea200700d200d8406503e0125009440d0003c2c1c0300c0c1a0801088501c0901291815a00f03194004020030416032415002160440c0140d49020301c3c188007529090000603200103009104402811400c0d041e600c2c0c2d1810307941c68600b03c4010f03800003001040307500300e5401049100c1168114454a030b000340b400301d160244851616141040c0060145c0c06040041230183d5000c0307800920213582c0c10303202c011501e = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 658388381 1250 658387131 658387153
    0x7020f070801150b0901030608070e04050709020a050901120b06040b13050d150209041401030b06030d08060a030b06180103030809120a0c200604060e040b03280302100c120b03 77
    0x44204024001c0401c03280e404140c85d0251b0388640c100310000e000780030540c0c40b401d81350352032030078866011681a6803d01c1840e0002030384c6103440c401c40d400035116548980c00c0c8561500115188207018801c4c2411940f9056901b02c05d03501c40004000602d41c00b10002e41e00c85105c48204040780540e03121500c03c0d002480c070100030840d40041c2c0500c812610740c0059890321104001801441e0b0018a00311003900c202c0080704100c0c00c5501240150703001c50071183c0c5800c4c2c2140894960700110341c0076400c0179641b0401c200140034480c6454002c2c01c01060941146180b81007000d04413026401940014a40e03001d211a42e041405411615101c02c02070518019400c003025180540031030008042d103c160b140210101030020b0f180000c40001849260741d00ea4488005020301c0e403492041c2d200c0c514161068005150010313610a462140040e2030440260620500c0c0c02c04905810036025401100200c543c0b41900d0f2150003c4145c80ea2901403500e00d02e0740c01c1c0021101301e002185d000c0d0b445490442 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 658389631 1250 658388381 658388411
    0xb1617070804080304210906170426161121031b030903070e060f06031003030e0117010603061d07080a0b030a05030c010b0f150f070c080607020f070801 67
    0x580c415040f011042ea0380d221803a01002055641d05030201298035920500c441942c02401401282d0350340d6680e4518005029120f8403d48042e203001704814018001da540c4409000d03a00303441011980754142c107005801110751450504420304407214220402e030140245031540065401540a0b4078007480d52520101c2d00d9074034490380755480b458881d406c880568800302042264401040034040d900d17256074511941c1085481600c2c09441442085014803c0e070602c9000e881c03041032001d6280c240c4900c0d43d24143c401001d0720310050304121201e00801c00001c080310790341b0700074040da650000c3c4030ba00d801400d2414181e1040d54a040e101c18405101810f5403003242c41c0d0300040c2c400e10024a4072041c20000b0700e400f050010040050001040d140021901940800c002e104c00343d820103060700001c0c003004140018003086901220007802805000a88440500145449646441c802a4682c4c10451506104403480030050388004011000c0c141e05001c2c40000300003c50007400708003030500c850 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 658390881 1250 658389631 658389647
    0x61002061308090d050d0c051b010212070515010f0501080115050910090f030c050f0d0f1209050a240f020a0b0901061a0a020115050d03110a0b161707 66
    0x2c0c20606020544924503564444001c005603403040840c4c994620580000d02115a03141040d200350054401403003039581110744808590360140d000d00b03140c0900e08181403558012001c10796051140c4510165414061000a4003070801943d06441440c41c1ca0001491040141c100d043e0b0745d5a900706424807984c204040e1101007800721240495500001b03c2102c1c0343c06123501207124011480c100105100c005444041070724016504151601c46050900555984245008001c8655061200081480c8640250501000c0d142c0344c843c040d510340028035a1601c0d0340040011264810320b800d10800007a40350701e0285494203204810300e20101e03019403503202002c2c4c00340c40c485103000007402104080d4030180107041c5040342d04d542d500ca1503400e20758641100000b030000d07610b4001003008915000c90349400b1101c00400a02c0b10361103652b411244a16000b594000790321480c5801400180b1075503019105841000c402c0c1d10031144003200800d1405000194118200e01d0820b12200c01c1d406456 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 658392131 1250 658390881 658390883
    0x901181a0c070b040b0702220f200406051213050d1d010311031503011503062315060f130602010b0f1801090b120f0a0c0b03060a170309180610020613 66
    0x911314501d00380c001c40030492032140d4a17084031480d2041a140c040c03041e070b022a80d8ac90341c1044000b62000304400600303403403285002e098041002403012500880c101c8481c10743c0460380c54119418801e2640d25585080004030008001c80d1941c1080c0f11b14045245c01c82d100728100340390511410321105642c14061002401d40b8003040b100125045c51a1001d40204c01c4c0780070704082c104407030340d5a0304000d001003404a03090005091103841c030081c0e22108001e100e0048503100742d950050f00101d810804150700280994904950078080d40c58010406490310b00180f64031380021465040c0b0100300020812403003c91403007410354111405910a00c04031040c1510208036001900340c6205001606840003941c140c0810b101e0ba06010b0034606022400114461140c0b904084140d100e07030118006020845d001900a4060303001000078440900c0400d0001c420300090300d01e80246280412044800700c14aa1030649094003801f01600b84540080c40a00503480a4900ca09100300007003a030040c1240 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 658393381 1250 658392131 658392139
    0x1014070e0f150315040606021f05220c0f05030a030e040908040b0412060c05070b04350304140102120109020705030409020d1514060901181a0c070b040b0702 69
    0x4650390180c2c0303900011009032481c21202d1034480c03400c0390380c241040c010681e070b0340c0c055400e002c0000380d920b000081039445078407603c100400c81e4000c500003c3c01464010705480b04982c18060401001c82c1c5401c031040450b021f0808028250304040c4219032900b0709500c04c1c2c0c066403000f0440303070100e0741c0107480c10f50000c0c00f10f901283c1a032190805c0b941a0003a0742041020b6440042c0010305a030340300b22041202c51103038806104144194609071080c0c02091005400b0388640c0780054000342400c0740c070054088210343c080b4021088000040c0340d210000b0050441d5000000501090200c040f1310011440d400e08000e61800d035685903420038050040c41400075080c1c000c54614100322003802500d006d082040b20071520340c00d1400143c0e0186c01030320f00c0040f80144803003000c54a008074100703400640b48003411851622100340c00440e005030380644000c10f41e80d0b40240220303418682c0c0244404c043c5026603090344030b0031800100d40c2010340c0e40d8003001c4500404c00041103418405005e941201d50121 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 658394631 1250 658393381 658393399
    0x613060e010b04020c030a030f02030c09121606030605030613082502130605041514060d02070b040812010608060a030602070807020d030809010b0111031b0f030a021014070e 76
    0xe804580504100410b0940c00303800855581c1c840c810000141c40200c401e03030341c02c0c07018480760300c501d4049110594801030b50b030300100700300c0e2514203100021892200010044030807140c007940040102001075040440001e4503408104541e1908001c203a8010074100c11500503c02c0c507654058091192100040b01c03c4124407500d403d604500e00410101034006c0d0800501c100005800c00040100b801030a11a52800241441201c0080b002c0030070340b05070700d422451155104082080075080145000360b082e07002c02513400011080800c10703004903c076104e0b0948030380c080c20041160b040b0503000242041082d508005280c1e8400d0355210840e6040400180d07258814242442d1900c290b1801035080341d48140030004043d809650284101e203010000c22409007400f00444d003010181c049050143e000340700000e945c80c801824503484075040002c45540d080c601084074155013142c0d403080007603001021220340e01c88080c05901c44419151500014516125a0180130003c3c4031000c18003a0240c0 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 658395881 1250 658394631 658394651
    0x1020f0d0e1e030d051e01031e06020403080a020d0221030c07050d110706031503140307020a15030515010f080a0608030d0b0301060e041e060209270603061306 70
    0x1800030300010148800124074400001c802c50b07951364460340d120820149407600068580d64014050443c00e0509030007101300d81d196440d803074503000145d04c03080c030704000c1c101002c0001007152004000462041030815155124680040d0030300c01041d00003020b40d0010312040c00140d58010381940d100d402004166100d4460402142580c000c8107001802403091000790668140c02108805043c10b003002242d10041e100e904c1103080e10325206a40340c00312100c40f0b0600c00103903030050410450540004407800c042e40c0e60001240102140c0c0002012180c690704150150350602440d9840018000402e001e070740c203640000e0010130030101c000c0420000c13074003203599446140c2242c8001c003c00c5c41100c2e2070303446110700b0300c00900d014049a0f00c41c0d0b180480000380011070218081c812500020104000810810310300c2024400d030314219101e550070460044c060313440010280c591018032912201180000c055191600b0000e405203120303070722000c10000c4d1214601c2000081b10343c0140e01160384135030 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 658397131 1250 658395881 658395883
    0x12010311061c2a03050609070201020a02120c010908070803041502040b0706380a0807050a050d05160b070b09122a0a081201060914060708130b13060201020f0d0e 71
    0xc501030f041e00c03281c690000241c51960580005003d0b0740100d807802c1d0b280c1c5a883c02a4200e03c80e036008400507030003088101030300300301807805064040b581a0010607410500e503603401c4280e2000c4400c4404040200512052181c002082c603802c0824010462400d800c104031200140941c0758002c4c245501d81ea030200c521200c20350000203032441e1039013122500501c1b9080f03a04500209216070b014002c201d2001503640e800043c03c4044400141194102030704000c14000000b00c1250141c8062166101b4103010f008004440e40003443c1c0d024205444080d1840c0860032008068502030140d440640110304512103032040302c0707207034480c4003050b81c101c400041384000040800411109a0044007a001e05114040e4000c049183d000c1010041036a00d409080d500e0403828001c1100400300303122034491a0800200070800303113001ea48040d080802005400b2850b140d150010b020b01d000104401400d4000042e0b0031003d42010300007035003060000c2d01d41c40035a006441d007100d00507850701c00100711800 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 658398381 1250 658397131 658397171
    0x804080912100b040e190b1305070806220c05062113120804050a080f0d0207060e010b0f06030f07090810091101080f15011412010311061c 61
    0x91400c0c02d44040c0107501c02040020080e980c28640101d0820711740707600c560130108060000040d441203483d41d1034040e84034040d040c58028000a02c0d01c1046c5c2203070000c100100440801060481c00808040c0f0f00010a001c440b00f000d0300c00b00c580201d0000c400002054501d01d101940d03401e807a003903250038a41d030080d1400b010b8490308900f000c002c0414441c000c54038170342c480c003c207010303805c01d07d0700342051002110190f0040b54054090f4000303440e140002000c1c40010180064843c020609007141b155100f81241d0000004442d0181d4440c42e0b481707076460a0080ba002c00700c0888603e1307500044540410f0503403100a002c01000841034001512850007203864102411070b141c12103a070a0400d07070003c0020302e658070f01996481c04a21041800f0740c030404015100c4c800c0702003856030b90b4a580d80e8607481e0400035130090f4184a02c54140b40841405500500032501200940614075451400d001ca0803101301034005000310020001e40c0f002e080907a50b1929150704c2451300080c024480009084020 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 658399631 1250 658398381 658398409
    0x12180c040e01200702090f25110f010203090a06090f050145120c0b0a060905241002010b090a0c1d030c0f0307090207080a0801080d08040809 62
    0x1071411600c0c0101000540c009808400c03151801c0c001595081440c1d10180100303400258042403c00019000d1050740c0c2059810200c3c401003810210102c0c154407650400003504c140000b49802ca00c4602280c08019645441c540030000710700d542400f030100342d00c074450484080c148540b01c240751000c020003000d41c0d1510580000080102000034043d4494003030008441c0c5403094045144a1548130480d59803000911200d4075003074040350569070f01010030740d118052000b44210440c0f50004078002000043c420050b4500c00101039050044107411100060505034072104108140070041c1851444d262195504070341e64104d860b10050708a0241c120880c0f0213400070800c0c0b062000e42022900010b28004c5141c6885001e072906804c2090403140040004c4d81c50352200d905c214480c140740001480c400800b8080c0c1d004a502d840d4104281d901030081224000350000d0278001e00d07940001d890b40504000c80250403102c0c10380740020024400a8405001c4101c0092440e816a0311a52052480 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 658400881 1250 658399631 658399639
    0x2a1703010605040f09050705030703050c090307031202210f1b010903020307120206190c0905060304050c030706020304061e050c01140115141204050c0d051b0612180c 73
    0x2968545800400a40240c841d02c42d048000c4840410104058000c140c4941d1650350703145d0039982c1380c06085001d010b010300441032820003002401e01d070341c500b8800403006d18050b51031103001c018507180c000e00d0702110419880c2d00c1d000c0320401c2c10812418508a80d20240034401d500e8a0782c4d00000341c0c1055001d00200c4a0440d8030b03080e182020980c020001e000c01d18010a000f070f85000d14424240e0300c501e8212000b10244105141010382400c03194030607030103940e2507d401481035450340c0214030b4550050300e05481a91005030001018982000740c4d501800311880a54141454004c0160031002c008828085c2d40388841124600c841c85681a1814410b414000340700c10115000c915030807400a000711580e207030342903c1c0d8007031042c0983c5a41036400d100c0c40c3c02ca80f0b0a0340e1061200114800600102c505003d0b2b002d403428103540c4d204000503520b00500140010780c0d9001280b0280c80108101039015200a02c06a03154000002240d0740c0b0003032410709280805a1040024107100007141c1050740 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 658402131 1250 658400881 658400887
    0x504150915022d1906020d060909050c0f090c0304020316030605040606090509250e041401051b090d1b06020f060604020c0309100309150e0606012a17 66
    0x241690003e08601401800c403091111001d002c106032a11441041d90700e0444e81c004220800041c08114840340114011040141413160b82e407c3c1c1d10a407005940014451501da401c80c0060086c1401418514841110084612001d110110b215030f0320050604085000c0400000c05544007481441c0425001c2000101c0d00d686034036026008060a5600b541c01c03a15040740403074050303d1842000d0044c41c250005100f00b079140c0b170900c94850990089602c0344030139030400148000710b50011a026a102e40f521181c1d805a601131b280c21240000c10043c690400038180d03003095680581219401c40007901d0031400d0b960a41011103554080e10664641425150070010b0700d580e0206040040159a50a50383e060312602c0400099010f035000d450050341003085117290601d80290141c2c8425080d082c0843c084c1d800761142e01c049906900c440d058a512504c00380a40d02c000d2000d250f10002c2401c1c0011429071aa26400c60307400f618402c1d46510041e40240d00521031028110015880c1c00720407160303 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 658403381 1250 658402131 658402169
    0x1b1617010e0d0c0f150f051b030a1a1002071d0717070c0212010b030c011404060e030a080a031e0513030e0105161b06110303190603080a090e0105040204030305041509 73
    0x3c010000b1b101d0805400b880e100c0070a41c540b076000c140c1c0602802e060491801c607118684072100a20305c2652141d0000c190b4028820a52a107006000300f2000d150054a8801c0c41e010900610300b006484040365614001d00f00182c00e60005202c082c0215804211139182d598814103032034001d07c08001a40c03042079004a5108140c0c1504401850340040d019181c1645489005582049203440c1603080035405100034414507214083c80e000411009080381c1070140281c48565560707200600180001c4e4330b841c40c903058890012030001070380c1360b21501040103150240b801050803400c820001c08000c000380180070b19030700c50420341d041c0d03102c1c2c8012a88102c1046c50400444070b03042d5449114070b040d80e0000540306004d800420024662240654507543c5da0940010b036800c50040c10308a135581d03070107020010403000c03000742c01c003940b160b292120003505207103400115040581c0080d21503401000140006680003065404403400003001203c5034852038400d6070b0424642e0840500c480e0305141c0b244c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 658404631 1250 658403381 658403423
    0x110409020d1a0a030f060207020a05090a0608010506060304050319090911041703070b041101121109010306050f030c060f0702091315050103020f061b1617010e0d0c0f 73
    0x181200035058080d07041102d400c10300109a00030311000c1c00e030307182001d8800e01040305034000b404c05130b08c0103054409e100c3c0c45500103400380700705071810030466599860501c2070329000d114a40e0083c0b001c4405909600e0300c0d941d02c40e9644030b0140c030f40c00d005003005c04c00340c10b09001d4003001e0041c0c28404000e111090788480c1020319508a4440c400b00c04031002c00c0d00c00c44080100c103c40080d070300b20303038014116030352500c0d81d00c0e214000701711031410000c00022020450143c1d2140c04000201d510480d40e4440003c4001030940ba4642c028900c00c0c4d0005035035059503034000603c82500c005c280c80c0c403a00e440384100f075850140940c0300e000e034126826404200000100000780415940326803861004000205141c60403100b090000a40003c44240350520038507010004d48103d001e0f0089914031600c200043c2070900d1428a0700c0001481040c20600206960700230741c01c0080d4504c03000f0800200501c00c03099039443c07070680023010300107400c114900340000c44040c18201c1c1d4101c9404114110128603230 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 658405881 1250 658404631 658404641
    0x409020c01060e04030e06030c040509040606030201020f0723010201230f010909081213061401060906020a0c050f3f1903080a02090901140109150909110409020d 71
    0x10380c5aa510700400880c0300428071250f075014540554422a5138041c0342c0900200381c0c4017908141d01e40c0e500b440300080750340d00e1010041c4101d120355070106015156100281ca072074000b29508055402c045814003001d008001141401076480307044078400111040140d0041040146010881803043c840c0302a50250000460040340c5155000e00203070380c0c0e1801c06007111584000144004000c0143e00c211140e010211500015041581000455a683e0301030440e407800d101c0200905140004000b00780d00414480000d2030280080e01310600951b41d404918401400343d2449450000ca5924080d11040451000303800190200142e1064141c56500351000c180070008007030b80790704d0301204880c3c00403a01f060b40b138814182030b8440031810b5030241c445640085c060819507900703101303091899075488c1d40c95000b071000c000c0d0014200700038400100b43ca46650082410b1001034882c0342d49040d0701045034021035000d280c2c0024080c0344075040c10064407455009061040c004620700050130099405 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 658407131 1250 658405881 658405897
    0x30e0c10140c1c0804050a0b37050108010b090112171201090501090905030d110f0a0e0f0105120c160c06200607020d03050a1104080604060b010e1003150b040902 71
    0x3a00480e214485821076100c135086900826039081068107800060421038295001a44038407403400e4685a494600188012105035800d18000080c114084200501c602409480e00400901c4000300060105500300010310a001524034807000600034840040707c000c602c001d91040050761500301450b01c06284600303001d00750076240307400d00000da82e280a101e081c28141d4050091414410a450071070010480018448040001003015400c150100c100070b05203100b4646480c032000405805110000384200740d11030600c0390030442d5601800c03c0101031940010203a9500b0342c7c48074181e40040807403a010000419242d0300d9200800c5180d017241c0600c0c030ba20f420440c80000c425510707202c00d80d01c05003035400f003015821003007100c0032039031103038000d107501c03c020110118506d80340c44440801a401a131080c801e0390400300c2808208546800303405500f00c0d0074038083e0701d104520400030b615240c090255200307055445450441d51104900948001c00104010030744803035498126002175888006 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 658408381 1250 658407131 658407163
    0x7080d060b0c1c0f0c0b13140f061b070807080d0f141b030a02130f06180801230402010c0b01080303180105130204110706052401030e0c10140c 63
    0x40e001551520942c1d200c005000c961792a4024544951141c400d82c2c0e070090080c00420042030360300c0700803d07444042c0780410f821613001080d132584589030103410500c1c06440036807200d52001d00c4c00300044004042e03583e40c1d900b00314403a0b51ba03281460042d956100d0010707040622030911050b0140c002c5660b00c1b0409150141c40e00310b08541d170725504010000070032050750644520900101785500f420b940030740f003001d03d041c0c0b064000c0d0380c4030030110408038842d81c899000161200c03d00d07641c4031940c3c0e0961000b42080002400000b00307902c5504116a02e1385581101160b401c00000c05681c4981200061103070050300d5012256120a405034403030f4002c40340b1a00c8029080c040d42c604450520400b0f104030003048500071032207a80e908000c060000840e9840b940c080c144004404981c0350b10403140200700c2040c00d010340411281c00044140c00c0b00f082d00d41410b00e002c2c90070582d0700000c540c3d4000c0038000c0751071034204111f5040584146800c1001200f15041c081500d88803000005122010240111 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 658409631 1250 658408381 658408423
    0xa08100b0a170703140d080403081503060c030109062702090112021801021b011b05012901090506040e060906220f051006020d0c030e101d060f07080d060b0c 69
    0x81c0005e0750744e0301944004000549034000041c042446036000c00e0300807458030100e004051203031000902d00003050340d461901c0b4800000410581c68548908c5008040d0034a500038040703500c606070105294400140714006400149003115170f841882c1d968504140030008544600700780c1c0001d0503101e0801001c6000d846100c0402202402c0d9a100c0d01c60294144d4581b004079078850088000c510460104440a42d240c200c454070040340c92118400b09003110203406480e8072124001040c0c14826844a4011041003206012a00701440780c00d91101d001d441c11030840e203500c00130559800031444100450b61008a280111b0340003a0003001100f554601c080c001500c0702c0740c0f9841c0d1050180709840c00f50b4000e0800d414110f020313440c84c035200340c0207041c000c0d411030030740300402d1303403240b040c0d101c83c0001e5814081103642c0c07a82c1942c0314100c000103803603a42c10301c0086545a1113a20420340040d010150104d92441c00c0603580d04540c1c09800303062400c0f40c84d9100e0002d6195140346002040a04060b24 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 658410881 1250 658409631 658409663
    0x6051e0f0f13020c01090804060825081315020d02070201030e1b0d0501140c07150615030f0207060c0903120e0306070507020d0b04050708010b0a08100b0a170703 71
    0x4981030200010000301800c0701000c030b80750340c6002944007142424242d501d070842e000100d03a004000d04002d08171512180d8440c80c102c0414203000b008880e5030400c0080f004020009140d02c1245190701424140320000820441d08081c2c070194840424030300752500000b240c40d0902026000b034030445100307880505c600030104a0891700c5141c0000d0b001c0c0d001009281070340003071030441c4150781c069000b5000001e40600c030208030705d00850104c645030000c6c040050304408110b0352960703040c030350048000304110071070038902082d19429035030702032408158403982c0308011400c41d50304644c0c00c290b12607010001d440c003084000c8c10329011840152005803200a1280c50f543c040c03400300000e0600100580b22960702c01d40256900c1c0c00541c0b050b80c1101c080392a80c3c000888484145010300d000b04000c5c6080391410440e2800d464003d080c19028034100e00080188280010311500c1d200c030011408105101400007044000e0107681c84038051300c0e4541e5043d00c2030300010400070296805850100b02589803 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 658412131 1250 658410881 658410889
    0x90c05041104030510090206070828020a02031f0e0105090a03020c090103080a080411030303240d0201050417031603052224210209100c020108160306051e0f 69
    0x20b244005415900700075102081c00311568071205155100800b441c1c18241d25488903000358106038140c1098481504030740d080101130101035419980c0610040081c0000c90340400e4880107941000195604d42c2d1210030f044405540200f0b000d481d00000030401860030105496071512001d0050f0f0142c0070b1302855001328100660414144c3c0e800003040ba1a29000110844620b0f030b004206071030078203000c003004a007541c0501c0114000d807004e216001026013a10301311031410880c0b074a41d901c26500e050101c00142d070003400b174400301c40900403a65000b607043c0392350034114072811003503140300b521881c1c19031704060b082006040350170588101c1985084003403800341c100c801c0305c2c0a1000d03000000b448112680c550389050303098010581c50300b8a068425404491055140d2050701ca042a0300440d107601b060500d005031300c0d4950501d10341030104160903000a000044040e015a400110030050280c0d0903001c0d410410050002810f010f0b09500700050310070000710404540ca110b465410110200d07898 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 658413381 1250 658412131 658412137
    0x30212181513060e0301021902060403090e0702070512160f170c21160b1b07031a130b0a02030106030f0c050d020702030106051c02010206090114010324090c050411 72
    0x564012440e10b0380c1054416101502c500488550540d0200b00e0035840e141c021011120b0303a50076030010596410a0f01c2c5c060b00040e010f4010301c0c001c0c00c480d003c10504590008204007207a0080d506210110544008582002124072441e0700c4519008000941d0750f42c001039100072a01d00c040140c1046002c2814681c840040e20500c42c2d00c41502a0003581b000d21460014658600c10320407103811403968040700c2035072503040d8803078a010b00c0045244001903985910801c0790400784005018014110798a1125100790210181c194400c0710000841d900391640b542c569590300001407050600d040302c0b51001940c024020000041e00f4603000105560303007401a43c0c008006900d5180c141000c840c100402504210360a99043d902c503c1d0008941e1910384828128000c9007400c1d0f11009441d00002e0728000b4040d0121110341c0c5000207201640003089500f9064035400f407030381c150240740d0070b4200407500f0110b8403034a416407504c880c91003000449501103086038000e60302400391415403458510140 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 658414631 1250 658413381 658413397
    0x1d040219030b0c03070c120e03010b010801030803130f0b091b010e0d030f0504050d060902100903210c0614070801050d0221071203080415060b0706090302121815 71
    0x80407804030f0004455040a141d204005203840841ca5606450751609030011031868004202d402440700b8035400d003130050071041e039006c0c2016010741d499903403003042c907202c010079200190b41d11901000c1004940c010080301140c00520300c800c1818100181900c8405000c0d0780100040c41c41c1655070b655000d00400c000d03290340201604040b0b0010384043e03904e1000e03400f0490800c90300300000f1519541d42503040740400d00408001442c028140306105506040000754014441c1c1402c080000400aa21510b8030b10712600007100d418184031405e0741c0b0442c003984003c10080c05d01c451346100c00c0c001f56115105181c0c0303a46122807a641c601c1071200d070b2820101c003e0b40107007035100b08108010310b00c0d03000b081101010b0708582503559030302c000c02c0071412001c4044002554020a00c01844005038008d403881300c1600081200d80d250680710280d1740700b00340c0000d2209031680c10340300c20716000307211b0188843c1c07001c00d043c1da4900a2180c01780760800069a40d611a45880503007003c0da8580c8800d444070742d = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 658415881 1250 658414631 658414643
    0x1b05120d201e010c020303100b1806180f2413030f12020c0405071d03100e0106030218040807030c08040b0703030b041a0f01181d04021903 61
    0x605400c10049915030000440e01110368000348850741e14910421401d9550060001204149840b048441c0c0c20748121440070300071035005006003c00b020380c06650301c0444170713078a5041d540d401e1800d8407901b60700388525403158001350100710842003030030400d40f0b0090a00125107429900c40c061040000600c1c1c1c6403c610210300111660311f0108070550020304002118943d0604596a2513480790b246002c13041044940400b00808109441c0d010440303840380e081d0403613062186143c155401032140401d41c031440c1100d100c860b102c5100d030b00c0510080c1ea002251083c284210145900300303902810481c8812402500e203d04410240f64141403103500443c1d12031015031510f215031310100d808030a00001503401280403c400600700035a01c00400e199840391300c0c0411804000320404c000c03200b0ba20102e0741a140c4c0c00d100139200d5900c06600e074000c1202400c0062508401040440103203045802c5030300c150b0800c089042c0f250150529040c442c138801c481207a2141310309551604061120321008181e = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 658417131 1250 658415881 658415893
    0xe072616090e180c060c1c0f120f0e1b010212031905040215120103020a170d03020c010216060b0a0b0c0c010503060402071b0f090603031d1c1b0512 65
    0x80c4000540903501e5207401408580c0101c4c0181c001801540c840103c800856128800e040308100741d9138000002170420b07060001ca1645d52000c007400602d50004441580c50341d412000d2031443c0f0360351100109414903001c4600740c45400744200c40ca610b001078030902603c10142c3c851941001d42c002c0b244904484014003041c1d40c50103a41e6005400040c00890b400282d0210801d203204460340508008018410013000c103501d0350042c4070840d6640d801614a00609403020b0300d240c1400900384100d2240b928005989408100d102030081c019590b2103c0440070142050f000d00090703130494403034400101d4861141c20354400b1601102e2107101c01c000d00507013080e4890911903000380c4c09036a220002400161628100742d5403001a03a4010140c0407044058402c28425400005034210280458800401c25039003551009003959022549140e181152405410500d8655080d40c020421305205c243c864240d240c54a190840811f84803921840845980000d203803810020346565019100c015110f = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 658418381 1250 658417131 658417141
    0x105031e0c060a0e10120b04020c1f0e10060306110301050a0e0702030403060e030c0c06030723070f05100f020f0307030902040b1507050c04050708010e072616090e 72
    0x78480d080f440115042c0072018201da101612121a1851040490b58074504100d000c46401c41c210b40f06404030b107020345d205200d4034402500004403503c4001180c505009101c2c0d1900484020345144185041c0900a1881c8071060040301c0d007185040d40d20490381403040c0010f4040b00c6204d80400d1041d5584030300e0701d1ba010001c01c2503142c00c0d10781283c00361060340e01e441c0d2241c554100740d940346e00035942d2035031000405090882042c8803d040300e60040318103600d50708040b84014069541850100c00c0c0e0340b12440c03010b420081d402c046490b01584020203042e1018142083c81d00c8140d0007618101d0705042c4041c1c032141144a10840c0c44880402550f00e0564550600071001440845070890708550348410b8048545c1c1c682201e500540784c4410312503a01c10a6181260a000460117000c0c029401c01c0103100300304e03070001e15003410740d405917400301d000e40e035008022211210610000d00d000d0704649640708194000600d039612540e03411082c1c0c0d040c1140a103048443e81074034810b68100d0540540490f07 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 658419631 1250 658418381 658418389
    0x6040c050a050c100903090e1605090418020d030f021e0a200a08030301180605090606160b160e0108090c0f040b04050109060306051b09040f0212040b0105031e0c 71
    0x204030a460f00882d0b041d1518a9060030813a1031010f01500031070f40c007110403c5581d01201c01c81340e0240300d1401402c030140e510394010740a4020318150610540e21429024030720302d031310514100e190b80c004194907070000c000e042c0940004041c42030f42e00140102d801d903003141100c1e00048201c2d2010301e001000c5c82c111030784038500700040c2c040d070380444000410403030141551005c080401a241c03401c0955600d515118650000440f20740082c000030f030414404000e181d442c0703030308a984540180c440c581d840003101c0c0309148846403500700070b120301e40c0e210901c0700e40040c3c0f440c03001c0506160303180d000400c8801401500c0344402280c2e40790aa500c61250f00e01da0b410f09103000e507490200600041011001400001d055501c03d8002d100b20581d603003000c10034000c036030140e00e030401a104015154201c1000c50000184500030ba0369029580301e590048032003900e54100c82206141206518981c206450441444182881070310320a03c80d40e448244202c0c0c4200740403000944042c01010111002c50900c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 658420881 1250 658419631 658419637
    0x12c060106020d120b061b0705011803060903180308070203060f270313090b100315030813030c03081c06080a0b0405030f0f0d0c0e0108190f1b030506040c050a05 71
    0x11403025120685c541e0780341c8070a4050200c82028555044030030b601d5100480c0760a66560203141003010320420303604014140380c1b0110550382c00c100c020642049600b020342e010545502d281d026050200b00c008244a00940680300240c400c805031486502e03404003419005106981d41703039400b0282c4030000d4078954020030803420514a50309403820980c030f041c000200c269450b031002080e5a03c0f8030200f142484c0c0707604121020711050404101285100305001040c000500004081180010b218188951580108401954041060315009449140000294006035840103010004015100d000140382c060101511030280042c01200c020340c489081c0f1402c00b500aa4072404104020b190b81000f08000709041401d41682a0f551100e20140c8800c0394142d402c0712040140c1700e04d41911981c0c1c00501280c100104408114070241c00c501c00c0b01c000d05541b030f82500704925040300002c074102c0c1d030840090388400340e8800300800d079034040c05d01085d500342c143c00d140091802c1040360b4800c0d00410103 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 658422131 1250 658420881 658420907
    0xd11070c17100507020f060c030708011e030c030f0501181e15060e0717010b0f072a060e091e0c0717030a1b020a0204020f0c012c060106020d 62
    0x31144410419403042d000c0307900c240e4100c1c006030821038800a00c11801c024081c3c01ca0b0111042c241795250440713005081000600500341a05800e10704201008002d07a840009035401c040100d042c1c640d0b03071810085442e850801120380c1d500b001c00c50721820640b40c2224a80d00d0300400f06040c004544007110030303400790a400c100c0302041b0300c510342c082401c07040c8109400352444a910910030300305400007518074041c440080551610304c6005100605214064074040080d00d811241c845086103415860134404041d42e006048801c402107180c1032540c0d804404440075900d030800c4040d038040038404507210460320702d802020706402402d055460040c0c0540c3c444c98401e0283c2c10440103586102d038802401281c0440c23808040207120042880b489580e280080d16080f0f20320315058000040d440d40c1485201a104071740c085000030b1003105003011216a81e85c102c0c02080070b40c201712a5084040d03010b103156103204610400c1c4515200d80000e11905a940d20780041c41101c0f54210b00b11341034150b80072 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 658423381 1250 658422131 658422133
    0x201030903172410300501090c030e0a03050a0309020f0d03030c03060504060b0412140708010506090a0e060402010e0a0f06110d0e0117090a060c03020309060604051506181002030d11070c17 83
    0x10180d171103115229880c0a0014450040341441039403c00030140d80d044a81414690000542800000e4214003150901d42083c2000300e40c0320036a0001400c1c01806038070341500310070380d400e0702d0017015450307840780002c0110381d24100111034542041c4021038800d030040302d80341e0408020600c141c180035440c440480e0710414514034020042c4030743c6406c107000b82d4810920b03603443e5401e0103141c0c6060341c51598080d01140e4100491444004080d9842e030300540301034103102055010138501e459903260080a01049116136100643d0381400030a600c03000004200603000350740e4207403221407117801c00380700c160b80595030b248121510703c1c98601c204d072020340219114031800d0154000034080780500080b5540b152070040e22482c14203009400e0900c010315480c49035107000c0030020800d00600e1791250000003541c0d0240c03a03a050841c0640307400392402101394009030403855008607503400002803d000300d42c41d4041c071034141d60154881c06401040001020b043c0342d10003d1051207842c60382884100d101034 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 658424631 1250 658423381 658423457
    0x30c1e031905041406130512010f05090d12050f1603020c0601030602070312060e150103090c080a1202030a080c0a170403081b160201030903172410 65
    0x40062800703a8005405440480c40204003040030303a02914103070455100a13117030301d40ba10800c802460319901040c001c0500c03809045003010100b02e42540710a02e0050000710422590038030b0428141d485a00110600c0024400781d04105101030900a0600801c484c4541452907140e12010481d07089420404904142d400e100f82c0004440401c00c0f14002c6001d04001661030f5030380d08004121040c4014071900c85030800b0b00030030070801c050030115405000c502001018911500c012030282c9100f000c060704041075150042240f00002c5a9505403a2107004141300c1613202e0700b000d90716402880312680200d010800000ea00c0c01843e002800e00360603601c0c0c018183d403100d010f59800c203a42503c0650006446804102c0c0ea011960385000742070311b08482071410700c10301203010060500740c071500138100741d2281041030402d4010b031078044101c0d02c0311010084130700d49012400c28020713007005616850300280d401141c5504107035004807a100000d41c0d81d4010340161340b080003425082c44041b020801681 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 658425881 1250 658424631 658424647
    0xa1401020f01020304030915170613110310330513030803090c0102010b0d1104150b030903030402011b030203030f1008161e1d100306020d020d0509030c1e03 69
    0x3e20045200700d1180d02c8400c0803504205080c070703000788131030f51010502c1410441d003104000e600008981c081022a404848094003c00c1c00b4098800824408650310020007400301d0003071071200030b60945915580c00030681c0b29100c20899121032941510954084250441c01d440784500020104440d15000011506503a9620050a0380c0221032501c00c0b50082403130390b2525079083c06140b51590040342c0c5207400e40d00c1b80d00c03a0a03101d51041d240a200f29554924140840380046039940286020591141c0720300d080340400f0f4407a80102c0303040703001501925020b6203420003c00300440641e090350041d4210b507102d07e60b44502c2100074100c1461000301c0c00c00010110340030800d0000036560600c240d50103d1800b81c80d203906148044180c502404d420f4403d01c181070600841a8107110189a0f100c6580c40c3c400d00e845444c202b07600003400490001495420381c0d104e5030002c012250354200c1c1000a9510031482c26100e02072121100310941008580e010900c00c0d0203220440c000c05007090b2498500b003 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 658427131 1250 658425881 658425883
    0xf04021303060f02090d210203040f050d0f0b090a0c05040912030e0a0606080c041d0a0f0c050414150111030f0c011103091507090b0901050c030715051602010b0a1401020f 75
    0x80081c08849480c0d0660205005d41f40801110650b400315000031414a130910b0a617100f841e0a034001e00b03005003aaa1013600078081d40742004143c00c0d030000134080e198185210610380740d060444064a81076075180700010329042030b11481000542001c0c0362002c41c3d2640004801034800c003503d03140b01d489801c5107040030945610541c0002d04010300180b01c100161010702040c0c50014100203001c52441810085210001c5845a043c5034014840441c001d82880d02030f8282d003c40e04625006485c080c50002d000c18501080c40c000c20070f0000a82c0c54403088401150948400c3e0105207103500300380030071a07403943e0590190003414420400030504d103800854040d86d5800481d001c5119501403007000d2100803003103440e00e401036030a2030404401d40c1440840d00e480d205180c0924104040000d0a80901d40705105941000d80d20289440d290b0442030041c0c0e019281c1a1035041d01c1ca0f03902502e00c2e001c0d0f8014810000c1e08440503001e9840603241c107100c0088524041c1c9442e0660040e212a5024140 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 658428381 1250 658427131 658427149
    0x30705060c2a030306010f08060d0305070f0803070f110303070903030e0406031e0309121e1a04050a02040f0c080a0c0212120f06090402091b091c020f04021303060f0209 74
    0x30442c00554992800700d000400c10500300144c1c2003800014401d0141a490f001601401c841d054105990744015610740490b9182805002030514007010041c85051940090b0749119403150b5a41c1c817900c4c0c084c00032503a03100c3c402aa80c5001094443d101000024020345c0555080c1b100100f00094465907074460384d006e00f6a1079106603d155484001c281055002003400300a4801c21404400c20344140e9140c030b80c009280c42c2c80c00010b10100707d142042084c07030f100785140381280d201480c0751800c1902e041940d6007140b1008034850390405070158000302e018407441c44510f00c0399866000d1925141c031100010405880150118083d014030a81043c149200603c0080c0c902400301c0542c0c0341003900c00c12902809416240714241b02c00038000507036901500c580d0000d035889840d116403080c510941881d4890700c1c0d03245c1e403c02e81c04030140a40320148243e0f00400380c006d548101e000b00b400d0040208a00c0b913841c4058000b16024014004100c45902c900584207110000501d0001120001a5040307 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 658429631 1250 658428381 658428457
    0x1110c0a02122a0409061406180601050708090411031807090504020d020906010306030c09150e01030519060f0515030d180611030d2309030705060c 65
    0x10340400302010031814034410a80308a07031108042c01d100748489a1169401c441c580b9002d641128001a0480582d5150301801446070311903010011003020604440004400b2118140b00b05011400c00003000c050040b40741c0b252505035201882c0518949e103034201900104241c03508180d550303404220203401c01c0700841c09010b06004104800c000032003140e28181094114200c030702e08180500c00182c86e210750040620780c1c11241c440c00c0f035507030a00407001052140e00141500391403420001344070380542c1c40000d082840c005488071040d195a00101c0041c4284002040c45d84134110075019807840c00700f07074160b0300d01c251404507114500d15035040640d035080d07a11301c91602c03000d80303443c82a18040000703010089540c2851285510342c01c02d0504084158440c020500036540409205044203004558007600011300802c8182d9903440c0441c84204640e020420300080d800119000d214008252442c01341e0080080000e90303140c032400d1910b900b1200d2100001428203007024141c4020703038121070000c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 658430881 1250 658429631 658429633
    0x11e0507140d030e100b03030406111f020c1e0a02090702032206120903090e090307050312010e0105060f04150e1f030506040605031e0a02060705070812280201110c 72
    0x4c2550510250070010b8002060030641c1c54503800000a44020007645d04480e500d0403d405a0400e1140450410359410040024020045142044231125501410384c40c200b080840ba41840c0c0c104e18101034452802040340300390f200c80007200040c64407601041c3d00003118030589051034405090203403400003560361040303480c004d00010b00485034000c4010007104681c01003032080131115100a00103440a024031110b2406110000c0c4141d4400c204031111030b0740c01001c6a988540031100d03400640403e0040c0c000c94000b10b4000105450550141c518803448000900c0c5028540074501420409190180302440600d807880da1065a43c0f101a440c81410815140d0510381446c80041c21110010090f902c030350314020090019460000b20070410705420310b5810480e0940403580c43c6480c0624070700a60010380001e48200b045008504c500841c0e8035242242c400d26500d91888501c2d010b00032804508800060301000300030f00200d40c048050031a070000142d11680c08112000a81c0511021009 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 658432131 1250 658430881 658430891
    0x80403030212030708130314040902030406050c0c100e1c170603120403030c110415030b061f0c020a03080309070e0a1103040b0a020906070c05040506011e0507140d03 73
    0x500d6018040006520035075000e603491490200c9000e07014180103440b181043d242440000101802341d4811011120b019450588440d95440c460006e940f04403801c8030202e0a0001140103088003005440d03d031000d58000d000b4803990b803190a0700800c0d014503c520b0070311849020403041e8446c5681124a01c06d40d03641c040d00c107100d00320603612108000d408280030340d2081d001407840b000e406060342d0a40e5494038080c00b45c665039003449100c1c82c0014080c59841440c101ca044400c80030070300040100c03031141007048800d546610070803299514421200101c0324520342c000741894451800601d440b4030042c41e001da081e46a40350200c4903041101d00144660000506018505070621a04d900c00d01601c1709100480020600b90500c2c00007030801071101c0f1174031010a0342c01034150107a40c0d2024020304810307240c507210304180380307400c0d018070400307014500d0540400e403c1d511882104561041160342c82c102141ca01e00c0c1200d803980088070540ea44035804e40071051851050101241c0403c943d41d002c54 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 658433381 1250 658432131 658432133
    0xc07021c0803042012030d0c2c0a060306030b0105060904020d0c1211090a03140715030b091f032a030506090c03070e060f0f04050703060609120510090f020d080403 72
    0x4141100c4d8030030548258001910f40c960400c0000031070303040c1c42813190f01080350841d019055072890100024908698000c00080707448140c80c00074207440c00000c80d07408200c40d580340c00540403659103000103031500b09850300520440c1414001070452400c00f400041c0307030518030000c103012141841007540020707000c10010f01d04031b070345400703603d10089030b00f20620315248100002402500321342c0300052890040040e240b0780c40400b4007030034004062800b003a204107545220000c00a00300d0410481c8188070700c80104143c1080e140c03100354a4100c000000046900311380b200c803064041440c0e4401000885d400d24646940320301410302c000c6100714000c2c034035400c002503524203022900c1d5190b4020350280d43c0802c0038088601c0c045800000644002c03540c80c10300d0000c60f03080041002c0381034010b4204424420b1450740347d40042e0840306969a072021a40d101c03a03e4580c07209454130f020b88039520009100003100d00d550701603c03c02e0b00c507580a03e40b1482caa40880d041424040099480d00c0010400308 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 658434631 1250 658433381 658433423
    0x50915040e0d080a051b030a0e070b0304050c010804050c120f0106050613030b0c070c0e1b0f070602031807030c0815040b07200115080f01050c07021c080304 69
    0x998880c1c4450081d14080840d81d030020040c01000748003400090b1034401162010520401254003080c1d12640341d40e49181184107140581040260034030188106003000030841d8510090304c0c003d960140183c00d00030010401185c2c640c0c0060030646d02d0f405074980303001c86a070b250104e0f4a0482064006408400354000d452401c50702c06074000c90144608114010f40386025902d2801520703488100c03907500303844045a41c6614001d800d402414104801c0d0085012407091020710310071240c6000e80b041c044580d00c450022805482415640c55500f48110030005007a40c014542c440b85c00c41e6032000c000c080c00020361800c00d0342d520a4484207501030080c003482c18140b02d80180500226054800350400da91691302c84200140000704004e825811440150410884003440300005c0009000303490b00405107454140712403150050621610301e0000e540041070040340c0c4101d100083d0141082e08540a01c0400044031084480c2c25540e12200c40000e400400558040ca00610300001d5558000440b5 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 658435881 1250 658434631 658434641
    0x1504050a0f1b09151e05030412171602010e150402090a0207150e032a0709061401030903050c01020a05070b090a050a030336020a0f0e01031b05091504 66
    0x118200c005140d214501d02d504032042c00704a03070090500026410040404407540c12024076030741c2d0324042e24550000c5043d4000040c0d40164050f8000c8000010082c1c0162a000020307440d0140c1c0c0518180081d440f904210702d0821500011b00022581c64854840c40782000031000004882e604040140010b41c28a0301c50182e12242164045260410307540342e805903510106281d080b1742c1d45480c555681030718180250b8a09000700a05059800900300050800304480065209503226060000888000a026800071110b0300403d05080810300c000440242115178010340c18081c0401c202d1100010034401820a044140d0315251a81a5454807000e0300001070452911035119281500100340c3c0030504d00043c55040c00d001840035442d02120716500c1c000613000384108001e4100082500003d000a2502031084400c15081a282c20342c01c815150741c0d00451680040503001031000601e8440c0d201092a258505580c1690740c5000040151404440032401c0700604009075420341414061 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 658437131 1250 658435881 658435901
    0xf05210f0723121017060a0e010902010914030f0d050c06010f03021003050411060c07080105062d0303040f08030a0f050c0a02060306190b0a09060f0e091504050a0f 72
    0x702010300b1459800e008140c1c014500711001c0351030720354003240c0a0f0381200300310401004103001e26111805c0306034496445190440702c284101d4207001528520850621640c08082d505860b02038681d8105524808640d1000700544e0701803080d440c890210361010041c00b562001c245c3c0d0b460f55508150321a15045c5035040e032028504042c2c1e43c20a00040c0c2d502022255058160b1500242c255514104a607540f100311403041d4008030300003202c1511020114171403050310641c0c0000d000a0303d4440c1840701d030b207420100404400c89010480058540750b83d0142c00845001070480e402d1946a8800300910842517002110039480001c862881e42d030408c80401840b410307420180d04004001c0e5107180c84400c00c240003845139a00100003003459680e1041300d0f404034440d41700c200e06180c84000c0018142c1c4a0103c03d00800c2c03d5140000c0c0c03451107070384415910b030050350384c207070200b84072205000348140c024094807050748204015165640300c501c115031180b680c241010540d007264903c920125080c000e8 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 658438381 1250 658437131 658437167
    0x12031807060f0903120c080406030e0105060f0f060c0a1505011d0c0a05130806090105010303140309070603050405010207050a1b0f050a030f032c1f0f05210f07 70
    0x100b4005900031602800312038200c292154541d00d82c41c0c0444059884c040000d003404004140030418592550018212540c40390007004152507030001c0141c50301145041650142c4081e0b00c0508508005000d01002900102124114440390b5110740e00100b010301d0051300e16507298010004600350300100782884c6000c02c8565a1400e20075071214262040001c00010301400089280c1150f40c0440040001c080d10816918030381004c003840c502030030007807100b500004c850785480c0791060405400c80340503d00d56801015130038039058040d40034000080041d0f449550900213100400c2052003c680020b10414510a540d40d050314840e20951203074200c1488800301c0d000c18840740d01c885d1031000a603600320444008400c824901100c50005a0300c1000c08075042e01d04032442201100080705c2c8181c8100c6a50074000800d203002144488800c0c1c0500005030740d25030200d5100e0003170009109513001c10042c44030003402c017907004c01721450030354880c6071201c0c24104101e05181c0c0070141040e0025191 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 658439631 1250 658438381 658438397
    0x910050106031a100903020d0c05120f10090f050f0a031202041437060e04050c0d0f021308060f010e01080a1b0521010506041107080304051203180706 66
    0x140c2c0c60903035490311003c0d0003545400303600f0900301e00070f0b010b000055500034803401080490345422907010005214071170090140c81403001001c44003040c12603582c181680100766064101c4030303d002034882190242d981210005204000ca0707414000c15403001c10150090059808501e0010721001101d01589030301881800144440500c840e441b200448c03048591041c550a0420721b401c4042c191004e41c070381040d03040d07142c1e01c0790040c06005034111507040c0c84540e120760b00401804165003040703450a400c0e1000b00401020b410250780b041c0040d880031080103040880b011701940d50745585820008003035001004020b0241d0401c4c24841c013418550162000c1545005217244e620411a40c00400034503d4101e203e0310006000c144034001c110043c41000030742d9070600c50140c40000200345140320b500b00400101d180c00c05004030710604140d140007502d000c2490301c07860700075040900212050b025911002c01000c00e00000303140280e0200c09a61214018404647d140c54065842081400142c0c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 658440881 1250 658439631 658439651
    0x20a0905130b0f1e060702120a2103090803010608090a1b140604030503030c1c09030e01080717011e03050d030203161b080a0e030a060e010e161e0e091005010603 71
    0x120f480c03401014130a8455585800ca988006450702a4212821034140308249018042c407110561809200c0501c07220048000c401000c11015518070b860040c00512080004100312882280705941c0300c030305401541d140b41c400d941c6001c0740c00301c0203c00a2102101d032800340300e0340d0300d1500a402403580445d255880c0500d1661810b0b201c6c00024242022010302052991074140d448071092641c400f22030302040401118540a40044420208240001e240c10001400c190040521054504500b500103089a103800304440342d030001e98400c400c2941c240071000000036010000200c01d8000c6441c0540c84c0e03e0803c2141c424000485490020002c030311001c0c0b2904813200051500860300000301e580e4601c1e42010940311040750881150301031087c261102e00784803c59010b240c1c44201d11000380315035454541a19542c801020300404030410544081162254441c10010320b400106024100a9035400f00703601012411112402c2e150042c0507071842190b0144a900e002d0710f00390508000001380 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 658442131 1250 658440881 658440919
    0x33302031501031802060a0912060903110c010804150212131a1501080a02041809120f0509040906110c01090b0601260601021e0a0c0e040f06020a0905130b0f 69
    0x403c1901a0041b0030004020000d80e120316541e5010301901400c1964035001440c0c0b4000a10000c0d00940004510225144940b140413500b1050070780d05950b40052a243c5440d44c0000342d0101034054200340d030800c901d065242103110401c3c800c021038100c20300d40008506007004100d43d606280360415202d8000c020841504102c400340f84242880c0074542c6d99615100e00c030081c0309a40003440c901907080c070044503c4449800000c2410320802c0050039502c102e0505482044c120100080480d00510a1405a00380360780980e444501402c1c0200b510324001080c10840e502010bc1ca04840c3d44a60504007801340c0034030080e4110000380381c40c11401d454400400c000c404060352002c5110400c002041940c0c1c401c000d03c0600f1401c1c0416540d0307600480b0001982c8818500302114100c0c0030b49800901c4220741c0d681d0354415500000c400301e041c107103950340a0003903000c9024102804200100400d65031500f90700d15200042c0c00b200083c0401e1400104026050010345491154032640160202e80070 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 658443381 1250 658442131 658442171
    0x2c011407030903050a110a0206030a0f1104060e041e0c08012301081603200702040b09061f11030f120f15100207030b0a0617150103330203150103 64
    0x5610706212086e400040842c206940350402a500050200c18040e41e807080750b000c0011507045000030804806032501580841c0107500c18840800c404680307180351428143c02c0020040450f11100020700701081c103c0c4104c806020454001441e84030062110844010070001849405540c4a01c0101000002004203a00828121801144107101700503603004c3e42140d00130070024005143e01c1050500700284070342292000b60312035428051030078050304140d0f0303003580140d1001e048000c0d16084003915880c2d010680b0401010400c00c010042c40701d400c240040c0084050264200e581d403100c2c04056800c000025110b1a402c03641b200038000c200c00b038560420440c5100340d070000003c002452069041800650001d0118080c0104126800e01c055102c0fa080d10f072044d804440c148180c2c050642d45401d1344030300b8006058100010310200303c02c8030f82c050298040100c418884114484000a0052490000c10901c0e401205010060603151000d1300001006c1c64104040c4107840352500301c40c8 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 658444631 1250 658443381 658443397
    0x303031e060e0103140a1203150e090303060d151e0c030e060a1104090203100603230a02250f02030f0a02061207020309030f030903061015032c01140703090305 70
    0x1417407070215134101120034003249411680000c1c91202c0c49444000c090050502d954440890100c410b00c003090301005403500390b016044001c003c1d0305641c3d0305c000303004501550304400c0c4e03900c45a03141050180d22641c0104040e100c9115000b04e030b8546030741d01003800c0d04c508885040c185828214002d0309010b00259a56110280010104150080c0da0b50325080b80f055400c0602d040c1c0c0000300b001900291030282808440703030f540c0c0801903003580211a00e511042c452000d0255400600400e041d28141d40203064020316400075105014405440394640c528882c03011070785040080302500540c541408031005440b4290054144601d013030b400036015103c1e494000c07000001243c0072030f41041c42082076600e152409400c8411081c1c01d40382c180c0e1742e5084040c115100340305507400242d2500707112130501c0898030f251401c0b502030b040d100816405802c81d0181040152001c402e102d5580340f01c40c1e58070401d01d0460307000003007840d0a503c0b441c0d08007200410180a01d070070b010841d0000b80d404801c03103680c1 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 658445881 1250 658444631 658444643
    0x20a06050601030e01091b0b040b0f0c1f09060c02060c070303180b04240b0105040b160c150e060f1603090b070303050a0506030a0b070507020d06060303031e060e0103 73
    0x10759076140040c2c0081030104060140c41d840d1003210002c12000c105c80c40241c0a00d0104168030301d9a6500c450000e12590044812021040c003101176282c2c05400a0078509084c4030039680da140510800071203201071035010007100c5884080000c10300600f1310420b04400751610240005280c414411200b92140078030003820943d0b1070480030f180c14503070038bd8094a00d42c003054494442c142424000781e000900c2046664600d1706044008106050380b090010b29041a11060b080c2803601e01c4942d03054004d40c0007100707c405c4030540100010094400d450142040380c503001d03512014004004c0000004505090013000100300000e010340941043d1798003c408440d51a8034840d5920702212085250743c884985840c1c0883ca010402d41c158000358407a10340441d00b0046941c8020806a5407200311101500003045400810025846400105481c90011300201c080034050341e118812140039900540009a603000300411007040074035401c002c40c043d00d20a0000905050140342c010034180300003400 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 658447131 1250 658445881 658445891
    0x110d0206160f05060408090a060e030a02330d0605030604150c05070605070905040b0d0210050c010b06040f26061612051f06090602030913020f0309071a040501020a06 73
    0x20460000081c0042d2540982030320402d00b00ba20f0304941d242c000e050268422100488041000d501c50180710020b003100600400c400300b01c640901503907074100c418907035100f14464005099140b4499502d0000072594124654445251450720211a5160410740c0709030400030a00c4042250b403180d00802041d948400203d090b003080b020364561144120091505007444108960b064202c90980b0403a0702c140c0f401e002001a42082003031069807410029400810302158012481c42100034000c0c42012100002e1002c04174000100c16070003070f03404860803551000c41403100116031070090111030f04448101c24100d05a83c441c83e100e40c401881c1d607403a0000300041685052003401d0421880d8401c10303042055040180132510b03070000703644601005c2c891907000003030600e03c1141c20340d00722070099016504080000041000300f0b81c072a085100c0c1d00d5000d0146290030102903000b140100c00700e10041c80b19610b0701d1083d0440010003201000300030820f0108121a07600460f42c0104254031850001d2 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 658448381 1250 658447131 658447133
    0x60f010203120c030604051e130627140f07210209040602181504120507030b0903120106050702131d030c0d08090c0d0308091c0903110d020616 63
    0x45075000720704041d03001500030000d11580b550303030400560060005540511056480c0303c0031b01440c48089003442c0490440c4800502402045c2d0300040c0d00900c900004a0f82448444e8542e44046c0c0598034404005004180013003000004d20315901d4401051780540040c1c0a240e0216440b42000c0c4a2100c42000020300038546114090390400303045e80c000c040d03031200e080900b4800300a4210142907102c2002004950445142920240174442003034102e441c40e01e4100050240561004002210248907640000c000507684d2420f451054800710b0045440b07660a0085094401041c0e2194090150400498000da25456604180c06401010110700040720256a0b0303c40c040142041030f441c0030102e03003481d48210115402d905c43d016a0741d0b10f60b45e40ca42103031590304c520481003c2503100000e075403c400060f00400071682d002d142403064a50b402103600c0042142e140d0410150005030440009004100b41e05141c28403a900a6444402c2c8211070390100da5540f1403402014602840010750030 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 658449631 1250 658448381 658448383
    0x3080c0304080601150e1504051c0803070c12050304080a0509010c05250501050309060a18150c110102030f0118020702040204140f0603103003090923060f0102 70
    0x20002e2825104a403425a0758181841d1408035411070b0400107139403a0203400003443c161205049000d5001340c0c0e140b13450300d003a0820441c00700310f861305a032503481000c0400200d0406405035214402e00c2e00c0b072019260407854006000080000f075001032140c140103200200da070280035115900118101196103d00220050380c5001080c0c4000b4402e2141c8070340e0020b4004140004004d202c608031611498680f40e00c01943c0780d0000715503161407a8060703800220501050380001c0c402024900e0b0b91400c015942d241e61102541403107825400c1515202c01c01c6489502110002d44c2ca00248021400d6090000b600c600ca08018422000d04182c010160501d00c2c50550498014903070041003156100c1c0c0d01c4070b60140071501c850794188a0380602c0c0c0012030342e0800c0000c40744600c2c1d48400240d010303801c14034001d21203442c4010310301c2001d18031103012200a14844510710028046c2d200c01c074099251424000984002d41240010b60f42c08203140365049080752001900190b040f40e15040d000c80c40c800413 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 658450881 1250 658449631 658449637
    0x703030512150913060f0b1e010c0c240c1e02013b0a030b04080f070b010939050309010f02120106020d14160c081c030e060c030103080c03 61
    0x1103030b018007400e00744204407107850401a800b034801d002c1131150700c2c94848108107c80c03208001c0c2c0e800000240c000300c11540c2d4080701c0f10540405050040f800c4145441d21a20049aa086000070200028104542c5d5014060800c4a11079500c2c0800310220303955994180001201030403c0c11041d001410411a1b0095011004804802c44155600c122444944000c2c159409000e4060550381c3c000541d0340c1041c10390442500c0e00f00784540c420361031f196a81e90155011030310141c0714080500106001551106a460082088000202e01403044c01d2405000ca004d000c42e1075008150031100d4003092070b1219114800d002c00d805e2071b03902c6c3c1c3e80d4183e42d213001d0b01180d860142020710000780820801004800e950580b01d05608840045a40d403000740c510f450080441e4078580024040003124400016441d00c21500c50f040d10803045540c0c2030881c0c03800182c8041301d00c00c0c07210b01003140f036940d60620500b01042d000100901d074504200b4a420b40d10300c418003018040d03080018030312448020400031 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 658452131 1250 658450881 658450921
    0x1a0711030a030b1c1a09010b06040306060501030b0f0f0103020c0a140a050709090305040b030402010e030d0206072705060906040f14010807020f0706120e070b030105090601020703030512 82
    0x103403a07a80100190081c000e2800c0540c5920034a2400c182001241c0304080340c540070b541c4600d0501440328415101d299030500180b041d0241d64880c1c0401c03a144c0c40301e1000d880110700c5500080743e01c50a160015040e6089201200d01840c403c00c801e01860381c80d4050078045e004282030042c0c0c0d49441740c028604000c40c1c0c0e14007a104900040360041c44220010305282c1309800740003500c950315243c80240d01994659040a80002c0061009002c0404504000e64105105041c1070b15050000340109050085011054000d60000803c000240f50041c122003584210b21400211590703100946405800103401030768000c1c1c4d40415040213980301d036000c8130081c10007202140102e41c0d80d16102c2000000d02894030b4001500039020035140c600014407510310600000103019110300b4403e045404201c4100c0b20124903466101d000b040d07180901154001c2d01c14408450f135258104400e02292610141c080c90455000c20010000709a0104c243c40d0001d101c0d6242c1034898440c8007203a03003200380c80c40c1 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 658453237 1106 658452131 658452133
    0xb0612030301030204150806190c050a0909052205060109110304050c0f04020f0a031b050405030307060b0f0a08010b12010c02070306020c160f06080f041a0711 70
    0xf001806c00d40c203850b04995100045440c03c0c0c02560040000d808610a005500b0460301810400c800355007001850803070030600040808003c1d02c50740062542c0c91002c2044140322000400c2c0c20700034280312403c1d0140508025496000038400c58101c18078101c5c28078500c0c0568000d4138410340c0c002c0d005d0004226007800b4060940540030816900c15400c100e079048062001010341500e0000c4c2e5030018000c1c024809145945142001c4a410711000380410882ca540000032981039692107400801c0c1022080c02146991601071007903a44211450f5010404400540c00803001090849280304001e8003408501d088a40c0750004e0401230300308100a0001c00c0c201d40050a01c040c10300204d031100c01002c01e2001130000c0780e0b00030405540d400c1d40100a0582d00240070b50f0030180040650b503c83c202a660201400ba04d0040d08a12868410018280c50700410440310141060300c = true := by decide +kernel

theorem cover : BRFrame.Cov 658273381 658453237 := by
  have h0 := BRFrame.cov_init 658273381
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658273381 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658273381 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658273381 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658273381 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658273381 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658273381 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658273381 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658273381 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658273381 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658273381 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658273381 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658273381 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658273381 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658273381 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658273381 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658273381 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658273381 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658273381 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658273381 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658273381 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658273381 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658273381 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658273381 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658273381 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658273381 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658273381 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658273381 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658273381 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658273381 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658273381 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658273381 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658273381 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658273381 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658273381 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658273381 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658273381 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658273381 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658273381 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658273381 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658273381 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658273381 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658273381 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658273381 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658273381 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658273381 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658273381 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658273381 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658273381 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658273381 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658273381 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658273381 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658273381 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658273381 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658273381 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658273381 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658273381 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658273381 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658273381 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658273381 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658273381 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658273381 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658273381 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658273381 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658273381 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658273381 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658273381 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658273381 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658273381 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658273381 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658273381 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658273381 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658273381 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658273381 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658273381 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658273381 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658273381 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658273381 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658273381 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658273381 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658273381 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658273381 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658273381 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658273381 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658273381 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658273381 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658273381 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658273381 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658273381 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658273381 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658273381 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658273381 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658273381 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658273381 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658273381 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658273381 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658273381 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658273381 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658273381 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658273381 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658273381 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658273381 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658273381 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658273381 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658273381 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658273381 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658273381 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658273381 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658273381 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658273381 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658273381 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658273381 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658273381 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658273381 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658273381 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658273381 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658273381 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658273381 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658273381 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658273381 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658273381 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658273381 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658273381 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658273381 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658273381 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658273381 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658273381 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658273381 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658273381 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658273381 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658273381 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658273381 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658273381 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658273381 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658273381 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658273381 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658273381 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658273381 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658273381 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658273381 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658273381 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658273381 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658273381 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658273381 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658273381 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 658273381 ≤ n) (h2 : n < 658453237) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
