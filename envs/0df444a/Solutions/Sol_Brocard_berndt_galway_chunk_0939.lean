-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0939
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T00:16:37.801983+00:00
-- url     : https://prove2.me/submissions/0351eb15-2650-47fd-9d73-233ee5ceae46

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 168705035 ≤ n < 168884892 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 168706285 1250 168705035 168705049
    0x1502010219031b0302090a1202040b03010e0c10020609100b01120203090a03080c13060f02160e0612160b13030614160e01020a02190b03010603020d0614030a02090a0209 74
    0x50400300361110841e580080e5080001052102c43e4903046041403a10400941c08941500c9812044201c4103c40c00565803240e000c2180440002d0003004122040000a0b07282c00c00caa140f00e2107062846c503650f514900205c0d8a6214074802e9010303264000d0241031002c000d0800c40c01d601c3c100301d880074000041810070b10055000c2c0d10718800811285200e1320300101040701c01000d9000a8500340400c18128030a10b268006440c3d80381049030201c126807500724501011507075800e00103803c5d000b0020701d041210840b680a09000e6514640340f0415100007503071020170784240b4440780c00c3d03144200200300819000c0d0809021410250340c030701e55a5100d440c00e955241402a1445e0b0510042c00b0802c2603440441b1240c00c0603080c030000c146000c0c80080c1d111495071001174058003e00d000304907a1860218800054212182000d0710381d61100001002034115035080224103240c17400c0415010001501d030341c15904010300400c5040456402d0096412001e452001ca440d02030244503074a54840b2 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 168707535 1250 168706285 168706327
    0x1202030c041a060307080603070b0f0d05070e21060709150521010602061009051005060306040e0703050d110604080a1101060e07020c0108060d02010c0b0c0918060111070f15020102 79
    0x16950081e50b040c070008150a200065222508a41c000c00c440d00d024001c210a0b0cc680c4105040000f5840c0d56045084e04e0143c40c4114179940581c1041300c1c1e80100303201e00d41680f421030181046038160b948480c0c003914034280d07074068142024400111804c3c4140b084000388014040518032000b0f810500c414103020690a0304141c1c05030b0084410401c0a441214111f001004074450611007424002c40e592100340d0580038150050b0310002c00241c1c13585454001020700780034001200c2400e40d4a040c05920b5210740e0314030000140f0618a030302440b0000003003040c0a990003448551400040c11010350b022440301c450b0540c02e540f41c1400280715aa90b05006114162903005800f000300042c000601c403c0000300700714440c100b400304100150340d102d11061415070340040b0b400c44c5529490f201d50824000c1013400c03980300038407842400400c2c404c0c01489000b014280c0780c80c88800e82d00c0b0b01c29606e9410030f01400e00d0403035088108101d000280101c0080807410b6000040c68140260a2951034140321 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 168708785 1250 168707535 168707537
    0x60c0c04050709030227060f010c0b090601210201200a02040c111612030e010507060501030804030605090a02091515040902030403140a090501230d0b0306011202030c041a060307 78
    0x480001c1082d0b062860b01c07a580b18215080c44d018413940d41d5140c6c2403a45007c1c1117140262074000140080b6401000005001600000541c0982c40c21000403603807101c003400781018410307850110403601c140c404d02c060304603035058445000945130824074411a408400305100907104281030540941c8a07846010b180401030785e03d05143c86d43c0c1f142c405140c0144110b14201748180c00c01c04200f920982c289036040150f0515207801d8155003000100c8172400f4820b0094282c0713203800000010896203100901c01c49100740300a1100307a8910080a44a02c100c44000c0d40240070440000e0141d00302800340888000c00900c000c85440180d45904181c1d00150003a480c40e82c0d000091000b4036400601840380f0b20710407080c1c03900e0700c100b40c10300070803680245c41260b0500c01c54080240c121020600f110840e1503d4064854035401d00421007000780840b000014001c0c00f440002180c2c600c0240c00402d00c154000c0c00600100c540c0304140320040003400342c01c2c505101040410305442c0c1d14900118014007032 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 168710035 1250 168708785 168708797
    0x4080403150f15120206090a0f0603050405010c080424061701021b0c030a120e04020c0a03030e190803060406050913050d0c03120e07080d0903150501050f060c0c040507 74
    0x700700010b0111012801c240c103140340002c0c07040010442d105800016070f581035035030688900f142c0300401d2403126560000702281741280408115168107a00281c80785000b40000d000c070701995601950001d4060318080d20705d80c030b800b029820300069000f10540020481c94000750150b5114040b000d1405003550989450350002030a0350f1000b0801c001e45c4038065200080e04180160400080e691526084010401c118840507050881c1c0900340e01441990064415580d8444030300c0101d0721004e140508a02003860300070809404000005c4c0b40000350b404010301c42040c402c1e51201001600001e12150f4060349890011915440f14002e00f402180618a200c8046032149411404d00198640c901d040103190802c11000c80d5114050048200c451000050719035540d0650909184058104d000c2e02d12400b5040140c450f405070741c0c84200e0b4007641120081c0da1401c04404240d640038070409078072000034004042945001d01c000c0800405081c00c990351a031041000c64150f0310202d038840301041d0 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 168711285 1250 168710035 168710051
    0xb0a0c141510050603010611010b0d080306100f05040501053006090109020f070f02030a0b04140d0801050a050405060121091509021f110a050606041d060606030408040315 75
    0x815002540101d140300091038024182404138490303000511603802000348405800100caa000c3d40011400000075040c4c11a100c030500703203068170394130944811340140906d0464205003845012045110700c0681d882070300e01445c10004484542052401034083c1014401218088151000c5407074a2016500b44020740d2405008002c00742405900c500f403980c0c01008108108a402402c4428031544044400040d9410340042490181c2550006000f50716040070f100910030b650040d90007221140080343e03a1158468030480b6803013021312402e9006440090b041c001741c5010f420080d840501031401d917010044060b100412624440d0301c0d8006c0f5690354a418041c400e20201c075200c0c01c041920244030000c26540031402165008449145044050248c540701e1481030b03200e141c00240c0c0720100e03841c108003420115101c0d442900c0c0d40f8401d5103400444030704901064120601541c0c40400740281d45d40c1c40b000d0003030560009004494024080001200082030031038240c180003810000001c12030 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 168712535 1250 168711285 168711313
    0x1201030212030f1c0e0307060b040b010c170a051c02040501090b040308220b07031205181b01020c0d03050307030f0b03071206020708071209060302040303090b0a0c14 73
    0x30300c5404550101d508200503100034203101c90100c60740a204d181581c40520601d107a03520007001c610900d84400d000001b503c2c03090205030340240e50300040844082103c403000c40b0040d1600c1c804690002c00d200180250f000062300b840c03001d002c00030f030a81011860f2160050a1502200c04d01403105042540814240100e5a00a0000c000b80400200d01c0e86801c0c110749500219004564070030100c9802c291020342040c151465900007045c910012648500052038003038400900030740d2080c0707541e180c1000981a0040c502c0c5415001f00700d0b0000e42040640c2c5101d0550840c9400281410351003141d0300305070306403a00c10f420020517000340d80d41612030404010003400c1d06d4401d000030f40710307034185aa03110076aa0040740b201d040310b110f10105010008a0320700710000e402440800340c950b0390080340000600c06d900040d0400e0a1581d95004122a1500c40c20347c100d010303d0202600045440f070741406010700800081c05010300e6803d00c03642454142d9240720060840301c02d56038080d00400f030101840d03 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 168713785 1250 168712535 168712549
    0x1303080403060f020313080714240f0c0a050a030e060a0e0c0901030302030a0f020705060d06030b18030301030201080402030c090117070b120f1003152007020a050f0a0b12010302 78
    0x84000f00410362841c1840b10200302e0941c140070026080d81d17030000f99081000300c00d400502020802d28241c0d10f4840c40d0705134894084c4400001032383c050b4540c40c00100ad508050764014880c02400503410700785084000b080300c0cad40c1c0080c10150207155440081c00706e015010031046108003108000802c0e00d40c00c210303119080040c42c1d9161401400302a0050000a8010094808146071490114040044030754201d00d00701d0b4640c13026400c00c1001502000b030103202d40225055074000c640b00440ca440f80e229008011103082d08072203440e0020b000500041d071041389606d4210340000c0448040014810008803c2002030f840306c2404850a40d412078051400e100010041940c87e0159091010807800741c0303a10308000301940800c0d001c5600040b0501c44032004903000e140c2190304c1001106120134810014240038003040410300c52030b9130499903080c1050441d00360b15070103400d5609180c42c15060081c40520718100c5079001c28000e83c00314001600b28050424010248040001035166005100309 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 168715035 1250 168713785 168713801
    0x180a09060606170402040f11030a0902030d02070e15120d0c110a0807090c031508031c02162012010b0a0b1e0715050c090f10021908130308040306 64
    0x1030118004a4030244031110f072841380d0050f01514041110303040352441400408036036140c403c0c203400c04020300c040800d483d446101c4251095044a030340302540282070ba942c40c058482e0003401a0003000040520411217007664140700081e0007070182c404044041800d2120000340752001482c1840ea40091009006013a00010400d0342d9110429062010150300d810aa001c1d042c88141c860350001c550341d1083c0c0c405600d07079210041d051441078540c4030b180d4882e4400e50f114108071400980440d4007524602c2103404500c0d0a0000010018171640d0705100380d1200b044200c7d074802c080c2d20448244e02c4000002e03688200c65000010103c1c2044108000151150800c055034a424030902d80001500c4050200310b1003000c4095072914403529008910084150002030341134100401d0010103401c0c4030142c0003182c0200d07084c0c1000d126000501403400c00702171403500181e1282c200803008407100c1d1040580d031070046240520f00107401c0d00041c00c01d21103a104072181c03100000d042061190034460700c80 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 168716285 1250 168715035 168715037
    0x5010806010f03021b070f030b0105010201060510030504110a090b1203121b0f040603061809080301060e010e0307060801031b03030806060f120108030a180503060a0b180a09060606 79
    0x201a0800c1030000b0000c1d0a400c07060014550b001440e100001c0012071110500c3c40d540d011100702c0c1c1d44501a10b2000c0740c0034403080710301503074450010400d0f60040c010541a560003030700d042c445203041c0344124088d01d00038000366103402021381e070f108503611a4a00d01024161040700881da07011800705000c02c101201200740107680003403060a8500f202c208c07c440c1c000202c0c0b030760030703101c240104407001c00c503c02c98000c5011100c1c0060001841501504004100c03210300c1c55000032100a40f500f002521083c0074001c05600c1c007040140603860168508a00c00101031410041d00d40382040482c2c540880341d0042004218040010410821503000c48540d0340007985071403071400e2031982e000c0c2a4910280c850703131282d440401c4008908802905076007030f802d028032030081c00e941d450300155266480302901000041800c902c41c06036540304a191070440d03030060f0042c4140ea40e00881c0ca00100010030b10715a125903500da001d10741020360000c0a000301e04a0301c00180d000403603c0d000b000c035640cae80d00c240c3c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 168717535 1250 168716285 168716297
    0x30b0409051c0903080d05100803180f030d1e020703080409051609030519110418030207080706020601150306120b07090e090d0809030d110417060108100b0619030b09010501 76
    0x132000520101c02e83c3c1d8030000100001c10705072100c40c0d1412100503103820807900c0c2d200104d100c0d0f082120155000300c1458042d00c008a07020281024140c45255046408020500300440da1665840140201d0b02801d0703240706540c0190384941e190300d500da11650040640d2503e80052000504420a02203002c003c541000c03140c50340307140d403800d44901540c00600c0804010000c0d0105025050240b01805c01000300304200362400e80c03111071024040140e0903401481200400700c6e09500024950b001d48189400078100c40e131804503402401030032410202c041507201c400c00a5455440610182c3d03d5108061408551600c200020310034155580040000f02e120f01c14022000c10102d00240d00c074089190421040d59a101d4040c90b61050711292400070303150402e44071103032040501030020341e90440600d0b0b04245000054030b6540030203000e504c1071034100a1007a0f503202c440d98003042541c500580102c2c2422100001c1d0380d07810510301200d0740882d445003c11031207468004000c034098803007402d00b4 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 168718785 1250 168717535 168717539
    0x1218081e0d050a1407020409061805060a0c021b0d0c0e0106081e0c1318021c0b1f090305070e01170d05030c07060618090203100513080a030b0409051c09 67
    0x10404d02d11225150182d5200240c0038040d500c9941040c40000d402c18004d21100d0101c4890520314010240180da05006490100b80c1070301c2c081c000c0f103a4103207296005242c2c0042c80004516800074014150b07504c4403041ca10701d400070703e40141e404020100c0d400c103404c084d072402801420541780102a4680f1800c440300c00d20407a021040700c0c907040b50f4074101c015221403c00301c800c10048442d400c400c901d041c440c071442d011703920703a03030001c10500110840c1880800011a90901075406203610726507c00f002c074020440c0c80302140303800e03c1031100350324180e000c0075501c1d19a80d04010040d0000d00d80c040706000144801c0c41d02002030f4040000c2c0741c00800c50541c54110040c1140005420380482040010740b40f401d12603160800e002070403142000e81c401c1c1c510500141c00800c0c9000089009010f90244a5040d03540c078400e4520500c00710007004090344181c0c0c1c80b412664410207186c02810303610103c0d0a8140c07103d12542011501c5000109003d082003c00100c0c015401e04c550b05c100b00a02e401 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 168720035 1250 168718785 168718787
    0x12080702010212090a0611030c0f0105071202070c12020102120d0c090806090d080a0204170601090e03070507031220060603060a0b06090d08070f0f0b0a0501031218081e0d050a 77
    0x8178103d038000d1800c5805103400508060645c41840000c000901c03500d508404c407113006504c003600803c21900d40101118401040e00180e006100b8003821052040d0401c10601041c0d1007509111841481035071200000e500118900d5003290340703c10103440d034400b41003415541003400354019140d644002d0500e0302d00001c040360b81e20003041d00329042046041c0420410f0000e88c0580740913000d04000c420703900b40d03660001542c0ea1424405d034050030b41811100c00c0b041c90040100d40350a0b8110340505a064207603154a0100c9030403001c1442049139000740c00d805a0360103542081c810204401429150130082c041501e003000c0900a19440b500d8a00030303108a41d903400c200d0b05000c00030743d540300c8002441d0030700d410309000b0407070040e01589400100c40100301c2888002c00140b482000303424411307200c1c4000d0f0710846200b4000241101020100820400d0040c021181d8407034056466030065a1034640f510f060030041080d8030050880005c030f240800c0c509002c21010150302d46000c500b000c0c48510 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 168721285 1250 168720035 168720049
    0x60c0f01050717240a1707120302030301060f0905040207120e0a3614010603060b0708030406090203010608030a050a0206090c0108062413050103150311060904061208070201021209 79
    0x41e5419588186035070000310000c00c0c40d000701308500103041c0216241e0360150075501200c0c440c1040b4075402003803004a003070100502c04c8007000b0f405500541c01e50f0b0034500c06455020300e04031100700380304000e0800a0b1544d19400104000d5101d9961091941782e200c0000c0c04015442c2c207440d20405440c0c3c0117221701982518007142d01d029242032200036150040c0e030703090451910351717100c82200c2c140788d5032526048141c903596049544c07507a406c014140e596010320405001d00f843c000c007a50402c00118001c10015000311075054001030001035019514411070b031869001d1804d203004a00c0125614141940610605a1010b4146e024041090304403000905412004111034400d150b051401c102038140618946100c0c041d001300e05595000023028000c0300101381c4240da0000b410040040382400400015074102c1e9801880403124424100c2000030981059500b81c1d001aa180d000140c500070040c1c0001e4440e00400c8440c0c0c4d105a18000241050101d450f0358001d190100402c0003d034803840 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 168722535 1250 168721285 168721291
    0x7050d08041101200109051c020703110d06021909060e0a080709150e0106090333110702090408040801050601081605130b03100932070e060c0f01050717 67
    0x11034007130740c05401228098480c18025000700801d62902001c0000c04c5000680c0171000c180d0004084464500c402040741c1da11041c0c04010202d14000c1c04e480c0c080e0508181811200c1d110390000b42c14090095a10480d8807511b480203800252071034020010141c0100e14022500020341c0c18a110504101a0980d1000c0301e00c41d9500e0165a90101250006a0b42254001d84aa0f03c4c01d5452560340300c1e0024440100b6010580c0c1400ea04900105c1300e080104030280400030310000718000d1042c108c2c4a1005201e11000a03800500c10004000103a94a1701c0603071149204443c929259400c240070340b42180d10080515050020706001d00c07a19441c480b84400c2600000c1c80c2c201d42da18040d44507410b05e41400e84c4003c4100c040070003403011300403c040400080d01c4550408002450a4001c1596840c8290003c03500000c04d1142c940c46450f054020039600c00d800d401d1100500c4406008260365030b10403400c409094109122400c0d080c20f0a00916802c80410b181464040a50315403420102d00c0203 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 168723785 1250 168722535 168722537
    0xd1a010803040b160314040807030203010c03020a0f0e04020f0408012007080304060b060904050a020901020c10050904020304320105060105030103381f080601060c1e020409060207050d08041101 85
    0x3a04d0440d0800d0712400c5900e28901c00010341545641d9521101551070710349010892082d400d115111600c0c03882882507900740b801c0c640e03a055400c00640c5081c2c8208000081170f541003a001c000103500122010018001840980000101303417980400c0b0a2900e040c400440304840420050785002c66098826203130070507003100c00061403000c0000096080d00c101a00181c02070300341400c1108082c0640d001d04144002a000c0d0385920f540e000030090b0b12004103014402064043c846140d107400c0c540d015507401841003a865042c641600c001440c8a07131070031110302c40000904102c0800300000e001b4241c0100d000e003001c90965045988885603503081c080e00c0d051602e0001e9901d00d085150011040c2d0214403c411040306042110405003c40c4501003440307a41e5051010004241a0004000d070480b02c0c0c50380c441c0031041c040d41d08c254a400f80f800391003442c4002e0340c50483c050703500c0384241c0003841e22034100160b49942915040d03003001030b800d00d0103092114002c20000490240ea141480090003 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 168725035 1250 168723785 168723817
    0x304030f05130503070b030612060c04150c021801180b01050406050a120c110705180406020310081615021f02130315050a2a1d0d1a010803040b 63
    0x30780c0c00782c9240b12400c1c0d44910f9052240b140c0006044120800441c00b4400c2a5a0703845415103035120b0540e07034141914228446181040100203010309510440500e15581ca40410b12000035000101c485040182d1194404e984800401400201c050020100ca90641051107900b0004e40041c03c40d005a224660178440e0009440300384a03c50a1b01e81150f03030611030f0820425904200007454400200f1049407581305180001c280d5150503640b01c0842d419040f2958040d58450f500c0300d0207504040c0c00c05c1200080c030140400c0804090002d105458104101480f9691606c1c400301c42d0000f243d500310056401c28044400324905586041b20046100c0c20050b03641d10030b0305580b0a5400d09075001901c3d049c0c14584900410340e0b540c001034042d90034440140940c540c5810b601d801103144040088600b8440b6001c0e02e503d50003840000c0344001255034002c10008003201060030109903000840c3c1d50540d0070280013584041d030111601600704180118209400e0862111092042030003035401550 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 168726285 1250 168725035 168725047
    0x60c110d0806150f0d091e200a170609010f0e1e10020a03020405090903040b19050d14270a0308090c19080d0305150105030402030f010c0f080c0304030f05 68
    0x1001011504c40b0641a0043d44d43c84408001c650000c0c03c015100f01d8040c0c0c421191020b121284060742218103402000b0200c1c411610244074065404003c91282c0000210500041034682a5004101105983c0251140385800c2a0840c21200f4800d05040310300e240000b010103420740096110781a000083c41450804402513106203070079001c441303000a1900005040c00d0260340b54003d0400c035030081d140508192140c241054485c00b850148152061041c002c0030b00f8134801e400c41c840c02000c0c40c10038602d8082541b6401051355034403000c001c0d10340c1d42e2005202c0440300400d011000305e140d20b1654040700006c1c4034595110741d9080740140411110001013008200d0038004643c26100040941d854035001e0041100c1c070100a11403100c0c58000c240c0221902400303801880d00c25500d00c0c18015045414100641e60380d000500240c0c2c1600c20229942d0000100b44100204410284c4070905c0c01c18410034001d008480c010100b251890f418414080007a802540400ba000644e003006a1240 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 168727535 1250 168726285 168726319
    0x1060c02040b150901080a020309190c0801091a0601020c0108150a050310050405070e040f02060d0f060b0301050a0b0c150612030a09140d11090a090206030103060c110d0806 76
    0x14428002580f100f5842010500e40412a005080c24103013030300d99212903034072034034880d007240012205103600d40c0050100001b000146011048414407840170b03400103a80f42c007421403c5410b84c40e411141e0505804881c140c1400784041e00740d200c8000d100a16012070801e000820091028004500c40b1440312410718603603640720501c0d8098500076086500c280e03484110711010380410303141a40c44d40a02500404d8500303000e001c04c0d22a58000000d4409007081c0c0c4d081c082a91f00c44c3d9a40d00101d595401203440300d40780360042c50002d1040c2b003101038581d4100000c0154141c1150b00c036503410780c820004510500c4c00810180003503510300c500c00d00b90b651100017040d0548041a0110b2913808005050b00d40c0f40c2c0c002490300182c900c80b6940580c080d0690f414080c04118000e00a040d00d03458030440301a52401c00ca40c1640318440c0c40011410b04219400310364903810a800031500140c550b42c01c00d103200e5010315900c000d050307a8801086443d00d2400c1c060409200070705034a00400709074000c2c030b50803 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 168728785 1250 168727535 168727541
    0x1305060d0206030a020d050f070530090c09130c14011e030c03150602151b040b0702030c042003130c151103030702100b0f03060c0a03050a090b01060c0204 68
    0x1141c001d400c0c181e0302d16113820150000d50203989025101458800441c200c11504030100e072040c3c00b40d44940b0710b0546a0142e00c16a20181e030303008074400b5040c0400c55803090700c601d9400c0c09520b400000b004103c009504201051342c0c001c0074500c2d0350072255010305c00f00310f0ba4001746e01214503492030b4102d0310151100488190145d400e800f580c0c0d0f850040e41c010010b81c158003000040705da641e020080001010003c0d090642c60b4410032005034401440720710b51002d8000e4054000180c040c0c07a4001066022480c69203030401e50003807400450102d511300950405002400d4804402ca400700409007a603c1c0d00c480350a80c9508601e807255000c07000440d402c5014280e02d620540040311041503540e01c41c1c10091a5402e0300c0300c403000800002c0b84021401001064a004d040c003500609021409069106c0c01080081e0110398050019148100c81740c03000d000c8640107660382403c041da5841c40402c041c007940c2014210034455071420420034089210840344505503035292401d4155055503000042c09 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 168730035 1250 168728785 168728809
    0xf07060c1b0605040f05030a0b0604020310030c060f02010506060a0512040f0b0f04060b010201110904180204150e0705070503030601050306130c1d090103051207030c0506010810060b09130506 84
    0x9040c1c01c0090114040f60810040d10480700d55035000c4400984500c01e15466070003c0314011300007904100840c0580c6840c0e0082d56111007100041ea11450317a81c0c43d028580c400c2035000ea000318109000c0381c00c400d40d0a0082507800402590164504200841c0c0104035200300004210340d9114100800c0820400000c0200207035080021640c40b400c0c81c51803102804416102121000e1a250003030b030b0320b54010700800345840030030148181058090300c00d001c06840e0003007221404860b90500c150050741e462040c050b0b80d845418610b40c80c5030030009800c2d21101c1c0a00360310b007809018000c82e00020300000440c1e44c0a40d003840c1c80d64407511402e0102c0c448c0c418031000013252030b0a00d1502e10380107601611142040c80100c0c0b9105540f440c42c0e090083c2580203010251036070700001e580b4a54029101c0013045824424540340f001101c0540744c003402c2103000e03040803642d0b40113240806100c420380d002d8140030702018a510b43c0740a4600300040d0a11201d0300c0c0c0140300a4803a00040d0a966070b80010b80b074 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 168731285 1250 168730035 168730073
    0x160b07081e04090501060f0801050405071110050610090e07030b0406170d120605130b0607050307060b0312121303030209150306041401060906030f180b04050106080f07060c 76
    0xc4030307002a90509909070014041d41e84082d10b0400001a0103100f019031899051050710b80d0480d5900b404140f04c050b0100411800034450710110048031440c00300020758924140c02000030b92030030305004008027410401c0005080002c495810b0100b101035101594102d40513040004988554002042c0689095440b800003000d805485407000c00000c14480d110390410f644181140f0304090035141283d0702805500e4200d441041c41e02100300007940000c02b07150008140c82d0901510313990301031071035100501c01c80e6010340312082c5410710b0a0170003068802091681a0a04149400855041c40400140b10801001500c0211400e00d40690f04480e00e5000c003034000000c0050140c1c840c0d1540c2e20594821b801076180948010a12500b6200c05050720310f00d0b5144001c851405604501400200c40840d020b1039844040003a040010300580c4a81403180c2194441c0740b4050601d00d0842c0e807580e02042603504001c402101da903001141e08403d41ea40e40c2094140c10303c060400724001565060380ca0 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 168732535 1250 168731285 168731317
    0xc030403020712050a0b0a0204083f1b0a0308040209071206060e0a050415121406040b0a0b0d1707030201020f0f03010819050a03030f090b0a051602160b0708 69
    0x14090140204032098103071b00a000400480d1500c50124089100f01d1181c00010307001040703c0100a107154a5041800010385c1c0a490101400c0c0d001c1d1507811058400d2070348580c80040c5030450030000000d40300b070000c60800505001841610050302216000704024401c40c1000000b03a140c2d07000b400e0003400102c1e00c680400429031203040207422081164401d9100f81d50084000840f0b00e031500851500c00c0451101c0080ca81ca03200a806070380c201c40004072039901031289040785280741004060710a501901c46480941008512601201e903a8080da60040b8007030034414000c11804240d00ca806400c400580d40e480e00142003c07070082c001c20200600481c030015500e012002e580c0701542c180c41c5090180c1c0d5000da194813000c040c112040c0001040d541050400b940070901941c4280030214145101041e82c044940e81c200f0001e500711500402c1c203a5034001d00140301c45510741c01090055500040c5030a0488000c91180c10190b0300c10038a8a54000a1176410000c0a00c2030f0754030040d2001c055 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 168733785 1250 168732535 168732569
    0x60c1e03060503070506070c0b090d050d051c0203060a03030f031d071401021b150702031005070e100203090f0619020303061003061202040f11130f0e0408030c0304030207 75
    0x20302030655403080510a22a0210100381490020102d94802c5e0780041c41c1c1880e14a0700c854000e868001c84025984107010010510101c2d0b000e1042c0000d0140b140e507100e9413540646e00761055460800d2030611100d105104000c4140c6070300c3c0704003040d2030300750901030189001e9880c100c0c00342400506200d0300d140710181d004001a000507841c8143e0714841c024040300005000126070350508078903000d0300d60300b1034000105581030850901c04640310481c0014035000030ba8010a1a007010075541d115503940d81c2082250803684420103202400044030450307240d041a0400942d64002d00780380c07a101d541c0300740141080366125000c452180c22051001c0165203003035a07029490780c0044403103900459800d03a403000d0b103a1103480368605840c0c403a40b120550110580074007009010501035180c040b5074030425500d07100c81800c0645104e030700800c0c00c42445400c015612002c1d003910760101e20b0f00c100402c140b0000031070490503070303070b014640004003912070351603040481c6090103981c80010200700350f02e00 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 168735035 1250 168733785 168733787
    0x5031e1b03071104020306100c0c090501150e19051c1718010305010e130f0803090c0109140a060810120b06121c030207060204050915031009020607060c1e 68
    0x140140c50f0203045248601c0c5641014042030b848100d9085500032000021800d000d40900c866103400383c042c1c401c06212548490402084440a810141004004524517400503501508180500c8402e45507501c8031950402c6082c11000c060003107902c25851f1321030140b01f94111a021030840da40246003d520300075007204180440d401840a0702d1085545603402145501a001d02070403a02070000440c0b05980d2051102c080300d4908008403078050084403640003054261001e1405629104058024040d141c00054a00200f030b030b00c401d040c0409503040c07013407940e0780281c002c003161050300300489103aa8144016802c00d80603048078500711080321000e01404003c12a003485007006440100d051003140e4819542c49910000d0240c0c140f0002c0240420307284a9006401380da44921000742c00d0640340c900140b044001100c1080a00b0907085210b940c0345001c01ca40755040d001e40504108001c1690086440343c814401d001e44410307125030300303030162903c103051a004003403005005c0070380040c0c4404 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 168736285 1250 168735035 168735037
    0xc1b031b1006140d080d0f05100f08030409110d0c080609010803130303050a030b090c03040201020d111009020a09090b0603100e0c04050702160e100605040305031e1b03 74
    0x1240d40024801c40c0340c0003040c002103109070300503a1229825459050750702c01c10082d1282180c00d00701c03070707403a424018504400c038540941c85619141810204140ca0848000c10841c1c407182c1c0a94000c1103000810030607040c0103c00c81c1c0640d024068003051240c1e802c0da103e43e192090340c0034180300c40d2031b10580500066104003803d009000c00c59510303265076610f80c800341d030306d024025050900304290002000080d010310020060705040e030801240d031030f11040000e915032000721414584680d0000c1008215a0b0601c11100110403d08010f00d00ad10030841181e030f2010f0407200040f0143e5214618404c0d595502040b0004200344074040c07201003400c3c0ba0101d00e940003038828034003a210381c925449000035240641d442c20410f00300104050500d1204000180401070000b4081d4041c0341090306446a02081c1070014001e01607980700a41800c135044907402007141c2c03099007001014001400011000700c1151a24490040c0352104069401410001803050465120b10840c6001a0b2030b84e000006c0 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 168737535 1250 168736285 168736327
    0x9090313090608190210030b0f0618090c07031d040f0e011a0306130318030611030910050c040303111e0c090a02030402150706020f03040b010305010e0a08030c1b03 72
    0x344e401031030311410003007400301100c0d500179803044210300c042005600c030380e200690b05c400c001d0005041201c03980c045005640079808440c0d011103888001d00e003d06100b500d0741d401503020021646803044540300100b044444040360038070b02c803a07080c04054030b0741c0b686c202e030303e528070b03905400c102d001c98482e16a4020302075241c0c05022141043d0005d044c078540443c10a11810b040501840100c00d07658048480c0c1d12500401d4a91071810400440456806d00c100c408148003c0d0400741e40b41003280c1c046180030b61002050119906181c00c0080310000c16003035400f102c0d40760038209041c5031840c41d00d5041445000d03006000501c42a80e26201d400c00041804190000b0740d5051100d440e11501902079105c102c40107500a402d003512000d4800d9910f00030b204440c05010018185125a4645801d9074829039050701c510928500501c00e022081c8190f011301400d6800500c034030001030b078070403080b4000245001c627600d0000ca07180403405806440641d0964402055035900c03007440d0800c01d1a40504 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 168738785 1250 168737535 168737549
    0x180d0914100503060d0c09050c070309080304080a02010c060b150d0f0509030403030c1403070602030a0e031c0209010c14010c030510060203070f0206070f0f06050901020703090302090903130906 85
    0x1030034400001d04004959006040345940c4580c03440d50350600740040c0607025441140c4014810f20001960b28844c4075540c0102c00303c4103c590303151540e040052004510390801266a08104401c01448100160b100005a8282400f6202c40f0b1300d0305062000b050041c003102c2c0c00645c840f9400002c00303402c00007401070106070842044a01030032207052084410407214107079654010002440464041d038900140d01e442110410b0a59091061031400c2d40c118a104840440e008400d01400c55214010042001d40c0c0100550501d02464558100d00b010b00b8044a4071a50000700c286490340304812a5211903040b203849481540000c480078001c0c540d01540200283c0b400c004a04064403c000041c00c940c6598002d5050140c00e481c2c0c0c0317510340641c1000300d80c801001c2280c400051840c6a0341c80801740115030240708114107007002c50940d00c00030305505059204114a0300042d410418520940c3d070142d840014580d1100110380c070b544101c0442e030780202440380c030015904005400c810140c1e044 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 168740035 1250 168738785 168738809
    0x3050103030f0c2a0f09060f051c0609080d0204030f050c04051303050d0b0909100f06060903081305120a05070b0901140d0b04061205010b190e180d09 66
    0x35440440d0b682c100d85500034140000c0301c254003482c00c00b804c0602402c2010001503402c480c3e44800d10560404e8075800300d0782554482000f00141d40388015854010142901e40d4410034003100540c1a001e0006030000341803554841c10314040c0034140c0700b55815400c03c071808560b0b843d2642800403064202d60421200c6201e186021880703802c1c54040c545c090202e0340c980d255a010542d83c00d481d10b07040501680105640c070003a1100643c0c80c54000c0d8041d8041001502c1c0541c41c011090042d074403100600c50159050200070000396a0081c1c40b00201c903000f41030261035611420598079000740ba540600d40c0200b0306150013540c01c2012030408a4148a2021502c43c103aa40392110b00030b0003025101c80c08100211740030f0300025241e000901e03607010025800107103131541c4800a001c5031501e400802e0b200c41020f0b214402c0040903ca072401c021005c0301c000c0c0425503e00408880c110395030083c030f03040407845404200050f04103034540140c0001c19042e00d1454540080042c0340c40d001740700d20400c04007 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 168741285 1250 168740035 168740057
    0x50c0a020303030123030a111002010207060c0f230d0f020f0f03061008011d040201030b0d030207180902132c160603021c1e1506020123060f06070204020a0305010303 73
    0x146c0020104400d541c01450403103400707103a00400090b40148070b08001035540030821000010240e03c9444682c1003207849141d2480680c0b0f000900c05940106070b45000c0710020b5205450403064402d64144045101010031510a450164006030050b030003107030907034200401c0d0400700824840145201e40300580300b81e03d910341418070842d503013103003032140c51190003101c048156210040d0340e06507445401030402248001c49040402d60310214a54181c0050704404001e00443c03441d013550f6115411400b4086c4038080454002a441c00525210130102030741e0790080740b0a280c1d182003500b0b4107268004087c054410b6824200f40c031181c01c400380820040c900718004c14401c0c02442a21900f480003000ca401506807805e46100904040c1040300c10f030340b0f1810084410070814015245004d1041401ea041d4524210010b400c0d00d401c2e5182010142c1d41030b0070000b0790b1003561102c503848803084449044180741035011030101d03c039000d0065002800010a03c042c1d0340c06403c054100d0344280d0311009150b07 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 168742535 1250 168741285 168741289
    0x60f040e030c030a03152106020705191407030b240a0306020d05010b0f030a0c03110c030c06070c0b0f0703060321270e0405010219230a0906050c0a020303030123 71
    0x8059402140e10140e5076000205420210703e1040303002034414a0010314100307880c0c0311540b811039030302d1820145030240600c840c01c0048801441c00c0704e00dc0d860091204508680d291b44101100400200c50036403082464030300000e8641000c0f04c2101c0151502d1000c680743c4c10218003951080d986403403c14240000024460260400c0302d400500443c0c02d0782c150740302c05404102420f50413885078101a121a88000000b90480082c041d2001c810021740d0303582841d408142c10818020200010300546050202c0440e0302e14a0542d80224400045491a50f4680d0190010012504041d00c440003100e50b00c188011440c084031101040380e19041089032002c100d111140441190760800b0b5582c14400300300b03441048100a03002485a80058142802c1001c074203926801ca5000e98001140c0045503001c58609210700c0007840403980c080ba281c125200c2000e0110b4540d44501e00410400140c1c40290350424410007448590080c00d9a80d00c1d40d5440f0341202c00b5103624200302d0009054a0811824 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 168743785 1250 168742535 168742571
    0x3040608010506070203011b0908060915060105030a140a020406110f0c0d060b0913120f0e010804030c0506010b0306120304150f12020c01140603010209010206060f040e030c030a03 79
    0x650140e40c0d021032aa003000706000c50350700041c400700c1c0c00d503480350740038406407004203408991502a0b81d034140c41149000481032a000000e0030300180c54000e082204007444080b41020b03400882800c006540b9220905010018031b980c480c04040528101e09008a1040fa42c00900840e0880d80d102c1d180c440e006510b294a401c40800c0d214102d038407054251241c1d0500e2001c28203214001c41001913030003004400304100780030845500101e0ba101c083c1c40810068186540f0351250b0251401601d404107840e0060048080d41111038140180100000c0402d803003058102051b6902c241514003559441140c100e05410540318141301d250800040d015407076000054904a6284c14880012007007245025600910202c42d54020001241406900c101c5e07540000c000c01400d070301c000505a1100d00020650300703000f5017420711903401040310051507a40065100d4100508984000c46203503100001001014406d0900215000c0803402141011002c0007515000f08903490900031608a031000100c9 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 168745035 1250 168743785 168743789
    0x80105030606010906030c0e0d1202120f0706050a0906090b160e060706050604021908040204050117100b06090a03030801051201050403081f05180703110c0a062a020304030506090304 80
    0x244444d8030401ca060700c03982107016140c00f2030078500c000c1002103000c20382c0d01e40100c009807059514042002c40f1141c0c1008501b0280a07013403426800d203000d4061804a500c58440082c200c251903001182c810744250780440d1401d43d0041040106041d54542850400001c80e18205100c50001003400054001c0800308031500b80140680d1416103d5500d10008100140c41150801d9080c4504038031746590850364511080c49440e820035529151040009450307050304a10000d1000c4800c800310b04200050803402d18800c2c2e60041109a901c0000c00c80390b0048040d22a030101038804000141908645958161f56040d0740d20305120202c1ca0007036081e43c000303640040003d000e05001403003441d401c400d442110704032408188685540e880010b44141a040992243d801e554800c0c042025094801c111680f10301ca829103041182c00402036464135a00f4070003a003507940b100c80c0e108901da91407030220000348020001c54160b018901000350340e6001400102ea2030f110f40c0000c81d82d944000001d841c2 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 168746285 1250 168745035 168745037
    0x50102191502070f02040c081905041e050307060f0912110a0611040509010503010515011b0c03080424020c01180e0708041a01081b01110114061e060304020d0c080102040b0a08010503060601 83
    0x3c1c0103009c2c4030f2040080a004000340c809044818840c0171014030400c1d040040c50040e0002c5031260b00e141003e80c22142000041003545140102e100c002940a81054020803503e0071701e81209a02c6060040c00c141036880700a0030075261810702200d007030000002d00240c2e501615104600e03a01c400505081751803d403080d122460b50400f544c610b0350f01c1111a46041382024285900c401d055070382c1c04070a4090f40e00b04540007640803400f4402649540d11310083c203c40d1942c04070300e0550104000e903c43d00549002410054040c80000f400501101f00100800d10540c50717003990702d05160010b043d81015034084030750000d0000700840c01c0d19a06a030a040e2011007010b441d0002c0c1c1402c0c001c100c41841714841d8140400c1000a60310f500c0c00b8842d0140d603003104240002240740850801c0a00e42007100c1d203414202080414441d1074a03060143d0754020350540d540300c460203944c1480001449107030b22101c455800000e001c074512100300003500c841c019588035080700e80d807203104140d112503088442c64 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 168747535 1250 168746285 168746311
    0xc0603040b0a0207020a0e040f030809190b0a020f0711150c030d0506011e0201090510110f2203030504031a070e010315171e010501050102191502070f02040c08 70
    0x21610392a581c000c0084d07510080c0009000356840c1c1c072001010700120723000e07601c01d40040c90100a05401402040d07020110354040e0144d029100d85c410042c1024040181c804d484000002303207281c5044d411501c044d0b4810342c60359140c45541c5050b1a0070004c81010368003e414400280110030503541c1622021480c00016500300a407007003a40c3e000b00030082c107150400903100c0341c00d406041c01403401d9486c00f0490780003040d4400141842c41c6060342899030b0003121031608420610411480b004e0766180040d6209081d03841e00000c2c0d071850a696030790101c260015240400104043e00140100212407003034002041004004440d400680b104550b4100814181034226a0750361181d84200401e01d0049951440c4503151001e904110514400400b00c1c1e601201c1c3c1e8a4000b0035030a05000700703403d100000c0c0015818071000030f40300c0d0018120f01d48980c0c4503030301e031404001901c50710a40940c420013046494400f18180000c990600420030307405580b4180c460302400d4427820300d02c1c2c40307450be6840c40 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 168748785 1250 168747535 168747541
    0xc03152e0303050702040603020409120f050c030a0e03030f04150306050f011409040917040501140717030a0609050c03160806090c0c1903020f07080a0f0204110903010c110c0603040b 80
    0x20f907010340c08540120380c403980d5a00084011780e540c0c4508000b85000e07000240c0e280780d401001801e1448042d454070705008081c0030700b8a150600004413640c0000d40e1608003002c840460100b407035401234408080041f40d020601080350301030303405e40d80d00391600c2d5541840200e50729028441c0c1c09017528101400245000c94030414802d01c4001030036801c5000c0d00019030b11280d41c4641d23241c6c601a11095004810001c1d04000d15a40180100070110090003190700c2c080845c0d0703c07100101201600c0000c941d902000203411000e081c3d06ca44020107801a081c0b01d90300c2c100304950314541c0102c4101404046000301c411260380718601107032254402801010f000e403100580001250041a078203030390352196482403001c0e408480581a04c1c28403a0b0000d046840141008504003081c58110480503030000c900c00000c20482401c89400d15010b840c00115035803070314698007241c4207044109800d98240b1080d10324155200032480d110308850070981c0d002c6150ba81c100480c510041d140503041c80c0000003c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 168750035 1250 168748785 168748787
    0x14060711121633050621030d05040f1a1006050304111309020d0c030b090a03020a0b060a090e250602030409110c060703020301031703040b040f02030c03152e0303 71
    0x3d0050a8440e059025018120146a540a0440441500403415110030500056082520307581a60007600e0151030341e55460140c0040c1d8034060b40d222110425110030100d0144081880413401c003a8000420329800c4403050840e0404103170136521a06400e15108002514502c10f41c1070b203010300d0317111245000441701d2104000c1400c1c1000c811420301d0390354510300b1005036200455403072501e05c40c20b002e8000360310758207100802840042428585800c40c5c02008000b99010454080003580002641565201d04000c00c4141030f042c0c001d210014640310821403414000282c036500481e403040c1401804420400d00f10300083d09103d1600981d000b444103100c14401d54200302004179040b40c010f42801164104a85406426565030b000300e9800070041c0103000c024150680c11212988003d45103040dc1d6440049560b0014400340c04a0b501003441405c5580030322291903001001811900030b03504c3d0396400300d88440f003911f0345004072a4881d2038000390041c41101103819410082c00010540c03660724 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 168751285 1250 168750035 168750053
    0x3121b081e0904020c01060e0601020304060f080717010608090f01060f0e0c070803010f03030f020d0c03030b220e06060a05060301030201120e1f1802060301050607140607111216 78
    0xc0c0780d100c0441d00b403150355202d44452020f00990074103a80081015446c2802d0341480d480090105d604640003008180030320394110383c0704000f4504515000d019556441001c8850341074101070104045d1980c030000940e507500120300c600540042c001c0c0e800d002c02d030300e0700c4070300320390f003612070186500300441c0c04100d001424400b8583c805810030281e80340841c03030f5541603041da209030000444104240414401e0652056007540658228001404050b00100d40a0881e8180500017410562200c01d07a40c41f0303450740030342402c00200000281c8841c0003550000d0000d40300b00580d05015126240001d50345d031410901c000e040b500040c084510b964295001154040da4002d540303121039840b064a1003005034204440d84800e80751088007110340050b00d0307802c0241c4980c240503403103141d1020300c03d10159903407000b10380c11900111080c682d2034030783d0b24281580381039000c12402d0780e0040401b00b003200c0746c112115a0420f880042641c011754000040c8040340d000301c101c1a8419102014180000b80c0552 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 168752535 1250 168751285 168751327
    0x91306020c010e07080d030203100509060102010b030d020304050111010519090f050a0308040c09020306031c020708010203100801060f0303020d03020a0905060703021513051b180103121b08 83
    0x500036152a450303501041c25500b103600e03040d0060b8070a03c0c0c200004c0c002404007480040452805601e14107101d0902e600c422041e00940d071066082c4008140568001d62007035880400282c00d48400303e000f0000691690082c2c0305803804149161420340070460188683d078030070340801e804a1380e1004041071920040205460440d0503541c524a00004a43e0802501c62003034826500c2803098505403070442e080600542c0003800d000e0045c000d0010b90b9501195198a010300512100010407001314104e103040101d5100c41608c3d4400003e00520714000012001036801000007800f46696991075000312080622000d00140c01482ca20903c030f6110350020011a01c1c41e107041d100f504d8031800002c00c25804100304501580c801c0303c1c2905103c071603240c12517201c1d49601104012800c15202c031600c400e105100c01e0301d0041d030000400615070f03a00780390380200d031107541218180e076031030b443e0150000030350480000103c2c0c07109100d080e8402003001e880729a55407080161741082200c1c0800c280049601c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 168753785 1250 168752535 168752543
    0x3100207020f090a0b0315070c03080403021006170705011103070803060d0b0f041a0105030d2d0203070614060d06020304020301140a0204050a0e0f0103080d09121706040b0913 77
    0x7600e40000c0f0f0703070341e1030300710740210900d0030002801c151010405141000d08081803155404110800642c2c940103a004074500b505810450b10b1540c40e464200d00301040b00c0b00032a1300515001c03001c9100c40b070341030303004400c2e5a10404070342c462078580005495507501114804140d6104000200000b5819005950000c0d409001d010303e51a00b582e82145090b01162103481c44907502d800c02c000d100c3c469603003940607214000003444030b506040c0842c3c0c84520507a03100701802a50545400001002c44204040110340d11a00c0c0f12004441c200940341d41c0702c2c04c1d054400340c2c28040035105904240e402c6d40d01641008284011102e286e64580019420050059070305558071590f040d404810400b65600c2001c400200690300c80c241010040e49124a400c2801100804405c0003200508024001c0c1035036000000305440300c08094030080a0300d4a0309006041a07256110700b105030790050f98081010030780c0d11095020307965000c00e00c4200c075000440250b21041990100d458280b15000400c0c1c10340c06 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 168755035 1250 168753785 168753799
    0x6060a1a1803060106050901080f04030e04151a09100807020d0c021c1103010c0201050103080901230a0305040b06030a111504030f05060907051c030305190f0e06060f0310020702 78
    0x1c09000a81011000d92020010a000040705043c035139100e00055808221410108510700b0b207030f00c0080064040d10390711030007143c0d942d02d0105034804c9182d8243c014642c56802c1001c00e00700103901c2c40d8580040301c1007030140d803a00d40400c40700d6006550b80ca00c2104180c1c01044c01c42c00c0c034042151100040001a03805c0b11003072040b18000c2c0708611500c0c1d400c1d40955074202c6209150803e1608540c0c44401100440e450300f401030000034403000c00c0310103910007442c1040c00c0d005001c1401c4c00110b0240d840032136544d40090020307089078050308500d204a0158100303d9442d520001415102c070b200d0780d402000380b401e8080e644581d03d000024000740c03403010b544c0a070030107071241e03a0001c1c0c0901e00d00b001c1d6040c1d40701d0300400502d00002c001da807020701001d81c3c00130b012801031005590320b481010801010b16441e03500007110f50030042c0c0b0020000c3d58120082c8282d0250940c480001c2000810a8400e07018601c0010b26908002041c1822030201400610000c0c0b043c00e00c0300c0094016903c200e81c0564 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 168756285 1250 168755035 168755077
    0x3120f050406080408130b0c1c0c020d02040b03010b06070b100f0308030f18010e01061e0b03340c0b0108120f18101206061d040b21010b0306060a1a 65
    0x1700c1000a0425029000300410000008203449c2d0741440d51036240c0303000c200740e0071170030381c010b0311070300b00300414154180d8010401c98010b00000e4090600c100c0015003107a00032840d002484a50b00b0706500032084071010004103525900c1412190040d0f00001d8050202000410144030406881a0380039145050b503064001e4074980075400d59604011a02d441da44900040c001c1440c0358041104010000b007150007580c1c507080d010103050000600c1882c41c2d428408908030181900c40403c0c0070403141e103010f039199124a410180035208203400c1501c40b07000c100000701c0c00c1c2c0b0000981114145004a00c02d041100400101e8650f40c070100700303941c22041d00214500b80352903c02490040c0c00c941d86510464901f1918442c040b01e0040d4415400c0204c9120040c45900f0792511010a509060740c021894071140c9012030461005400380d07841807800c07000320346202c140640c46500c24100c118103854041d1202400c01001ca8100d0042d04401c00c070101d0000c00404054004114001e00d410088002e21 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 168757535 1250 168756285 168756299
    0x150403120905070b12160c080a030f151d0103081b01090c2603041a0904090212100f110d05091c0801060306270c1101020403120f05040608040813 64
    0xc90348590884c03603022802c44240140703e4451036201000c10015401c4200c10000100000ca07081400b80002074002002c0304207038802d0300200c40e003090004e0f05000d118550b07407a040600000e403282c0f0388018122580701c0d400c01c40c3d4803152812a40c00c003a1182c2000200743c00c0ca41d49800844c1c0401036590fa607a04000000d40181aa0008001c441c8003031074001794881680020a040741c1d43e214094004000a0041d003130010347c0118407400342d128998446132180c0104006051200010303512136000e00b5810407000000441150030303e0002c0090025420202a00f02503405140040b502c40f407003030010501d540c0840c2d0006500184580440f40c2c02d02007c4440c51482c10300310107500c002000340005000554041c055440201903030419001114201c40d0010203094034103000e0944075032141d0f08825041d11403004a0050080b21008554460b03882c80c140a140340005c2d000b602040180c0900800140180207aa0482c0c0c903c0d1a00c0c41c00e42d5541e0f070f034582103501001c655118500b0914002c82c1030 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 168758785 1250 168757535 168757543
    0x3060604050915120f0703060518100b010e060a09050d170706020d0501061103033c0103020f0108010e0a0f15060c0209010527062103130503150403120905 68
    0x44403c20003200c0c014403c0801c0c0002c0380d01c000036800c41c1da44242c940c031003000307030000d0248201c0b50031003000180c58456601c1c900c0c80110020b50a81c00744a104040c10010303e055101e40788040d402d80320900c6448864061100c103025244030003004c2601490100450300f40301c0c01250b0f2440c803c403070130b07000001c0858010006421a4109076800c81e80414248001c2041c2c0c8109800340441e801d0240c1c142000c41140c654911004001c09401803100c5c000d02d048201d40e03d900c1d4511020542d0641204d07066110030000c00b0340c24401a0304c100c03408120814594001e40c49141a144150000c0c2040c1d550624140003510801c103014011541c2c0f030030356244d15050802a8400780c0019510300e00401e42030700400c95410750607000710344505440244140820076043c03580c20603c0300c0c040b11581503a42c2c00000f40c0c2c05100681d04201c02034a030145182c0c3c0302c40100c01440c48000301500c0d018460740350b90906030b03030300b000c2c1302ca44004d480303401e011a0101e402a41caa28850b0020340d0003040060700c03541da031828 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 168760035 1250 168758785 168758791
    0x6020f180a0302060d180803430f0909050c07230c040c09080102030403030605010f030606020d0c020d0c09050108010b061905070f120f120c0e010302030606040509 72
    0x105582400c0c2980c0c045606104004031400c03440141075400144042c4605080e0305541c40e5500c00071041e41e0000c0c0001006503070042c9505403646000760403002c00c44404280040542d0059840901c5108581d110144550720301400302211081c1020546103880c3d001d504034180107040c0d50004440350700d40100c40c494a02000102e460341032610309040c00a040b401506103035441c6088000c0c10000005211000c41c4080f503010541c290340c030006032201c80b2030782c10203662540008200410b26406401c44401c488081c0da502d1603c2ca9046401c82c100c40c0e1380c0c014900103030040078021108902c034103152000030740010b0018004046a58405402c15040e40c4075403501ca0700d031401080200420311030581c1983c42990554039103003500a5a5500514102c1e500003031000100d9084180000900d81085141e4080703004c5582c6105d888014103109000c9080d40001446450401c04d041c00b1070140c015002080d84400040005980040d0060b4000900c40d98002205100010301965a6005180 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 168761285 1250 168760035 168760057
    0x5060f040e0a0b011205060d1b080f0708060c0301032a0801090303050126030405061b0307240c05030609191104030213050f13031b050d0809010501080c060c03070602 73
    0x42c100c1c840b100003401e04c150003504000750303a02d0441000000e440c8c0013850400c4903444070780c0707800116664007000140040303a0403220f00c1c2d10800b440036489010020704901901c0d070381011111140c0c0c482e54039484034031090000804900180780d4101d141d0420031060710004101030040198151690041c1e421214031013030071380000c3d450700300402c622036681010000c0d084110b250b1902c005254030032103a40384034034401c0038040d41d00050341c041c00884004141003061603180980c0e544812a0800d501a08034551a00709850000d01c10f42040b082c840c0704401c1c40034a0340e25058190354804003081541c280041c00e8506104054805051a0400b8803e050380380e1202c41255403940e0840c014000c4020701c085401c2c40844c503240500c01c0010200031039a61020b51102c00054614981c40d00301ea034000821044c1000b800019107400c00c001020a040080d00c2c0d041d564a005075560004040c280e94081c072402c2070f00d4112414592407810044000c2401420780d0341100e290a103140d507070780101d0b480700700044 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 168762535 1250 168761285 168761291
    0x17061c0303090b0105012619021c050c030618070e090a02040f08070b031306020c0d09030b060108071b030c0b1303120905061518010806060f01140405060f040e0a 71
    0xb50421004000c0640904801e10f4160103020016072506800591100403c5001c182440000c0000c003070286400ca40f10500c0c041991a41c91213031040d45410350f9001c0c44003c1d40d00703200016a18148042c2600d00c1001c2c028501c2e110300e48a480f0400008402620020400c980ca880d0707001c981d00d480f50418042c1c50800f50040c0e6592425000b2141010f1a41044074150404807082000f40961029281c12082c0415400d5502200c0d1502400910400114650b9070289480740620310360081120003c8a0040c41c01205c944e880800444444c4411950103011914412442212080000c10300c00304612034107000c0035180903501d942001c1501101c0039a032501c8600c590b9002c01da0b01000d00c03401d00c000070700203011120b0141c1d602910303040d00908421032003103166049203842e900d03844841c1103241300007109002c558603200e0762522484200e0714a4015699185030a010394441e0041011120140f42054105402c3c001003001543c0840b50391440c0340000d10010689a0104032154010b002d01c82d000 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 168763785 1250 168762535 168762551
    0x2030d0e07060306080304050904230709090c062111091c050f060708070e0117040b100503030421050a020a0b09091506030a0b01050c0a0b0402090903090117061c0303 73
    0x3400e0f10041d030042e401a802c14003040103991641112070b40c00543c05132491000c43d90841c0040b10481d02f5118180d07052048071000a50750f002a40b05090507805084050100781d140c0e541595610780030704c64606500034448035441c10309001d6102d40ea004900040302882d01e0b0300e120010301d02d81d2241f1081c1e6007496101d810b00f010014100207940d40644500044c21544c54559030280041070014090810721402c4000203103030340e00c100c00d116145000300082c80d405040c181000f0041c4801120b0701d0100509411005ca481c1c0380c00411f440c103c0e10304034100d0a2240c0a17506c03a0b0031303000380070104031030342c3c4200f411801c0140c0da801e60a2002e0b04003114269164200071040100040b0054510504040300845412031a00c0f03d030100c1e03501c07802c6aa801300348510a003004903614403940142d0019406440903070800c003d49a40c03e94003890007140d800200d51101401161a40300390b90000b0701040983c4000030200e49200b8070542d0180004240000e1400401051066510500c0003140026034034205 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 168765035 1250 168763785 168763787
    0x8060613090615020a02090414071706100801060b0703030b0a030803040b0a0b01050406170712151a031018200d0c02010c090504020d0b030109030504051003020708030a050702030d0e0706 82
    0x60014840f045100500907a449030300450300700c0c040a44041c0498a080e100c005481004000790001003102c6c0d0041401d128501e9200782d00c1c0e00c01030b111012051754800d4001100c0f0760500400c0255001c0c01c082900d00750065400350300400540b10324a07004041d00c800000803c180d0006507101e07a000300c1c0720103a149131044d512000c940da8090542e051180c20b00060240d0380c0e2000549403143e0101c090035000c0c1e190400142e07480180000020a0300741086181074407101426542d6003291008bc050600b80d1211644c590030314001140c0c0000d104454282c00c110310b041142c00304180b0b04101400241c40c8620360b090806146286a1100800030300103120121340d00d0720f1141c01c0c0c8402e5584002c000c090501c18004084028910510340b18940214407030360301075038651000d0741d81c4100400801c0000f0301464044c2643c1c11600c29903100c0c2c001a08014a5203001307000f101c02d039503885810355146594445010000f080b0107024ac03000c42c0f1051000000c2e110491081c101000c0c80d110041c0006864884 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 168766285 1250 168765035 168765059
    0x130e19050a0c06170403030903022b020c0409120302090a0801060801020901080117060703270f0204060b030721060b2107020106080a020f030a050712030e0105031501080606130906 79
    0x100c07160404c10b80e10450911801d072490007035041681441c0c0800d89210905040785040ca20740c1004180c0410110505c80e0a83c2c09000c10010481c25025110040c1d00c120070402140c8010b4070181c94006840001027500303200354020014040e009011010340d64441c1055401c5420319000310140c0d81d0f0018540c000307507030810703c0140140307860b107288810118182181c64440c000940560140344d01c0b0b1304603071042140b810ba032191080040709507a03203c2e00a4240100c0003021404280e000764586980811101c66200c2141c3c0b2840b03980e00c804018049074500c14440c0580520b045600b20b42d226000b01e058032043c0c000341032203d85000581c038040304031120842035a401401d0301003913a1501e030042002c10000b040850010390121660001205c80300d001c241482030300c0800411900501c2e002050301c1e50944504402d85020340d0b82c05c1e00c1030ba0040c0c01903d8511003030300c940a0500e10864042202d40c40b400e80e0540c840006040d81d402d2120800c0750300e81442d090340040b41143e4454600748040f101c501 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 168767535 1250 168766285 168766289
    0x1110d0503010f0506210403050c120d14010e04080c010609050f160e010e0d05150c0c0705090106080406090c05040f06032a03140705100309120806130e19050a0c 71
    0x364007074036006c00003080c0d0f81c0807082983d4100080603480000303400d150044090f10300580d0b008003665504a070380c01c21080c2d070b5172020301c01d2429a841d2100a40c80e95007500c078040d05807003580d00322000e0394640e07440d61440354200b14041c2c9034941d00c0748004514a0000c1c002c440c051130f0381c18a021003c0c241401407050300f0b00741d400300d5010001021810f88050ba40b000794040720744000e80d414100f84140b400e0003401c1400c07444808201d400c4490a00101400c06001008410034100680350010b03101d20800504020070300c540b400080076100840e01248103640a03261683c0308582001c0007d54940108090341c052601201c01d070b6a0f250410011301000040d0f80040c249024008400c4003959403429201d0803da001c064413007040341c404c0c000c42c0b007401c000810180a0041c4005444502c1110003009000f02c040304540e5429156002c0c6001805200214015032008200b01c0c20401501017178001064042010281485400a400b0180310f180d81200281d6015030050a550092403d09440d0880c0c1a = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 168768785 1250 168767535 168767539
    0x1e030f1205070e040e0703080f040e010b0c0d0e120601060e031509030304080c0709062304022113021302030702011503033203090f010501080c091501110d0503010f05 73
    0x442004a030b140d01c14041100e901d000c0310002544c018042900741307003d55075000105940340026603036681000c000c01400484801c6014900c0c160780b1100010080c1c01541300d05103644d0300c42800407206e40d0082d8221380c0a40c0f4068110031401c0329035586a03141160a074821004220f03205030303041d45400d00b030200502405400d181101917003404a02d1964a04c001030014050410100758805984000d20040c030080a80e49030900100d5220510324554a504000d070300c9081403103480707601c1c03075061500a0304c10000340c0303980405640c1800203080342001001071000d0b12482c15540c806005035150352402c1401e00342c0c0100103840c1e00d0300090103401c40701c012024121841c242001000080d0344102102150f1040b0b0000d204c41c00b0312403032890708039605071a4401e40a6000300420540c038100040d0031030b8104115000f4022640e1302d0803a2520760a1001010390061555030001345080404001070700b492006142001c411044c0d070b4001814070043c01910f400240d000801007082c0b000d882014000b0b4041 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 168770035 1250 168768785 168768791
    0x3021917150d0f05010905031207030c0314070806062a0f0f0d050f0d05010902070204060f05010903020411300c0405180a0f1d0601170303040b041e030f12 68
    0x101d20300003901038403a400000c11403080301035040d040003420b410200300b0035400400c8940311103c0da004a0810036080b6021000a894041c40884040c80780c0104100040000030007403a40e00c072030408481403080102515046981003004000d180285d020f981d207101903040410345046100049182010080c040041065101d808154145603001c140300c01c5594041c10103e03980d4803030008242140c000d019614000c50700d030034000600c511041d0000c2020b68401c880400c0800c1d11020751440190f81e50241030b001414010080c0010304060740b00650b50109515481d04003010f42c0c4103c01e060344d681444032001040540c00d0050403101100050f00101900c0100382002d00704808140c6151402c001d840c0b850340384102250100072a170b40440483c4480041c1800074150002414401d002c4220f021892841004c00000d291070588040300c2d00c0a0001d4040c51840c0c40d151280420400c0241c0245e03640c01205505150080208204004d4035200e9101c00e29040c1c107d400c040c02e0b640b034401d844114142 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 168771285 1250 168770035 168770071
    0x60f1f02240108070b03040f05070f060f0207060801180209031b1002010c0e040203130c090510120c0b0c15280504020f121906050609060303070c0605070303021917 72
    0x10002c036502d4152040703521100d4a035070b00e50800003c400c88c3c0b503001034010f004903140401c00100340c1e4010815031711141c9820102c814601c2049a882545204284c000382401006000341d4150303501c40008100c4869001d1b06140310440000d0030b02c00b003414505107148511210004609064142c4a14418603000030081180ba20001070122140000c030700d40300d190f001000400c001c680e403c40b03a0354690004000f18840c2d481d0030150f40188000d41f00e0740040081c0030f02c001038011000c2c42d4600c0466200a45a1181745011026a42ca400c00310864503140138502041000c19400c3c19002c1c03054048030301da000d1100a52a28866144403181c10502da1400c2108200c096140c082c1d42c210840004c0d9617401021407840006800c0c808402b00714841d4040c819070356814000540c00040c001c000c1100c000d822610b8100815640c1d12a14500030040311641104100c0da90180001d81502400b90801525000c41021300c990209402542e07040403d5040c202d64512280d1080d00540c0722621040410001e9 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 168772535 1250 168771285 168771299
    0x507050d08040e0414010920030708210405060d0b010305010f1215020f07030509031507080a05130206071b05042706020c0706021c03050c03060f1f022401 68
    0x440b6038020014121211400300b020000116513440d90078030404000c201d2402585002000342e514401c500d00045034407840c840903884e004c140c1d4811202d244000301442c04130244110400c2c40901c803200b030340c0718040c4400601501c40c0001022000b01c070300c90009520201c480003400f25001a0498a0958600031043c46031200e00c442401140d6040b0140003400750b10110309070061b10810a8502c1c80d1400411a0b104158212015001c0c12000720281c408261849446034500f140031503042e0000380303c140100d50791012950149400c91400270400389800c6994011542c0c5a1040e1b00c11a00e2081103501207004141c0c60b40840c019082c2100c0a00c45400425905c2c1015601d45a60318071142201d4241810042c0550484800d41920000d0324490360b84c070803001c1d444220307414800151241d210130454000d4400e1158172301c501c0005a0707560075030f1207440900014903244078010b5045400013008032480314400604918010704c44e030060198110000c03021084600070004ea880f10080b1f800140300003 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 168773785 1250 168772535 168772537
    0xc08060609040f092a09020c19030e0603012309060a06030c0c061d12030907090902010e131506050702030709090f0606080105150f09011401091805040507050d08 71
    0x150811030740411583d041110030380c0100301c00d65000388101c480c1c0d50408521031140b031200f4402c03100d420500d40c8259030390a0b40c005906c00d52801c8952600410420a500e200090911028074000d01e8405810880c80c40490340551003030b0081c107034001c0700d0442001c03503d00072100c03240121016100400d035818001c000c507108ca43c0a0060700240f50322019020721907803207094510042a0001b05c00e05c40185110340900d801161801c0da2280e80c011140010342c078940000072070340a07580b0f040c020310481c0e00d4241c2000003081803000407030400820012101c801c1d41d030b50401031590000c0400000382c0e1852075403815250b0000d42c0c008000d00c40207010300c40160360007040030381c100c03104490046229100c1d450100d070003041440000f00907070320b49140031542e44015805544569021000318610b961441c00b040b0701d1502043d2025804032640300107100e544c0c604600e88816a40c1810401a015250014443c021902c1c2d21040fa03480c0e81c40c020001400703410481032006280a40d80c0c00104080d44d00ca251075 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 168775035 1250 168773785 168773797
    0x816090b0f10030e01050103060b030d050a0503060603040212010e16150207180603020a03050a02010206100302031f020c01060e06090f010e0a02070f080406080a14061c050307050f070305010c080606 87
    0x1c51500b010511090354001d07005000f203400414020003030307580c50b840c000303004100e040300c6180240b08010a5200d000e02850888142031076644500b42075036151010410a81d100502c2280c02950003501303d0513000d401d0242e100145d603001c0180c015030403030890000d90960590300c0b9400c0b2440ca0041141c180750041500c005841c0440480c0382200310703898181c0d0242c10f03107510080d08604914800000d00c080484c1e00d04415100b6030071b4500c40d85172070848030121020f40c00060351503048103c03083e00c00888000d40000303081308950054209141c505000342100c80c90b030712a101e010040020814a464800e507010b9001c2c440c40507010142d414003902c001c00e040f004000514403980080e21509001001049004256200c15a1603403141c0b1828010b000d04400d035581d000c860308018083c01030007813004400e0321405024140c0266880d0680c50701d031150001045c01e59040c0400c0041c240421810321205580311600382c01002c0442c03130351900d2400c4601100e0a0340400a8080511030140d60340000c0741c070 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 168776285 1250 168775035 168775039
    0x308070501050609150405040f0203120a030c0302071a090a061805010e0a0c0e0912030403110c0d1218090e0309090a09050d0f1206090509070f14060c0f03040816090b0f 74
    0xc0c42369650f107011000a4100900a5418484c1414034800b9520f010020030080742681c1e000d118107941030740c0540c06d900414000802010107685000c05009120b041160300100c50411212004030503203c01085409400d203220841880704200c1d01070190902501442170340100081072118070a0302c03458415102c0f03000784074000c0d17880c0e0042001d110080214900c100c00c003064203903403810f2510b000303050200110200030791400b5080d010031080c60105c254103031441c4c02070021510342c0da60460403140500d00c44c829981160050a002c110094644140701400001e40000c641e1072400808000e19420000e2071842507038203040284000034000b00f003104c8a40b401d1b0400521052000074182d480000080ca40b01084d45400e000003801d10060704100e0040e03004d402a2802103407292003035420700c0341b54050415034840901c0c200016007406401411a114903800f9246203000c20b00e011070840c0d103d540101c049030712200340006014560000c90300101600c0c0d208203c4000c01c2000301d0004080110418 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 168777535 1250 168776285 168776291
    0x6140702090601090e07020705040506010c020307031112031920030703200a05161a0906030a02070b040305030a110a020d0809010e1504051c020703060b0301020f0403080705010506091504 82
    0x900c503a4094035910003d4518045c4803a00c0d071500c50300c02940e40a6a1240d148100e007003d001c0703011540281509405c0c1c54016020300315642c00c41d11011402c41140614a400031000c0848070504442070000d8645905040c060b6011044503030b100510750b9050140303a00c0704400c0c0c40e0b99807003a50f27000401c44400c590f141c1001c0d0b50902901e007019240c400f10041c880d44d6802582450310410101007003c5400d941e1400030250702c0d60300c45205c05041d0440c01c0410350850000c10501140d1710b0403001071a80402c0d2480b002d13242051a50382c000054000b41c0e811004594003009000c006002401001411700c80c40c0f010f1418038030700b400002c0d40e95006000d40805c0c4a40d00001c1940341400390840c17030030306401804444003503c00071046141904100c03002e6909002c5c1c10340a142c3c880220900500c1c9071882d0307004144003425038031058000c10709020b600e5410766003000a507a107000c030130025100540c0034140c00ca8a07043c113410684d0030f4038001004c4921801940c02000344500c0706146803141008255400 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 168778785 1250 168777535 168777541
    0x28170106050108013609240b0d02010c170a120b041404060b130204080c040e0a030e061612090303030f090209150307030503030f06130908161a090f070614070209 71
    0x100c080210182844400c2c6424100d8a0040c045000d5208032072504600501c451011000d540f03200f124100c1c0c043d527520101c882c0303158000d90b00c030310b14010a46004a08000004070b01c0403074040641d100f451100042101d5a07600c10600b011442004000c4800381d60501103407880d903c03204944e06004100034046562141c90090759282c0c819180151410400119511034441d0b192035075484094181a202e28100201c010340890003180140040d9403581755410b550740c809003000301c0340e0020b05018040d02c030b0009400c0045540c01008001c10b0059031100700031b01d819400c0040c00d903002150903001080c00c4c041e000005031920503035690f0014001c01e00d440404201c0b400241000c0c034540c8090001e21001c414803217407001e001c030868054001210f40d4162450100007030015580c0204000e000d1001c280040440c008100c0c1c0c402c3c00a03807040d800b42c507501038400403c860b004800e451f595465804846040c00c00f07102045000081e003134900f48081c6004020741e00c00f40b203204400000380900b144c8004 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 168780035 1250 168778785 168778859
    0x90302090414010b0a140a0902041206090302030d06030b070801080114010b0f0409050108060f06150708090d0609030807020d02032817040f020a06030c020303062817010605010801 79
    0x130400c041c14004200c5601141d443ea42c0900441030019100d00c206000140000c0f002c2813842143c00301ea228840000700d0124540301c050040c210f80c2025010350108024003441c07075540c1d10461300514400c032014802401d000340024034001c41600000071070380c9070060000d00c44038005481411102103d0903195681c60846c650503441c0525484281c01900301800801d1081001c07074254450786010401d6055a0340300400c00402c07500110746034503903200c00c000300d101261070b50b030007844045006085030721140c14503680c4500721840810140c000501060922480760342c140a0a01811030920085040050121010315040d040c55043c100700c00c0c0d003501da0f40c2c03564090b4481d03051020380018002c4451a0904114286900444c022485820090130100b5000d0080c0f294400700240c9500860441d5100b00511900c7c1b400406180e110312117601c0c3c0d4008100103187e094004c1c103000b0403100319030307001004003078203544450300043c0c14000050014011642444800c40000c0d400340c0c0c0c02c0003000c2c480c2c01d03 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 168781285 1250 168780035 168780041
    0x40e07081509010c0507030906180b0c010c02010b0a1a0c010603050d051903050c0d05100302060a02101b0c0b250905030606030d1d130e1c09030209041401 68
    0x3000c000d0034080e440052042140d581e0441d031081070103030000d20450910100884103841410001030200c0c000d0718050002922807c1d24020440e2080058400c20752500001b250359008028401c059a441c0c00f00000c4d00e44e821301941c88907020542d122000c203030a1901c64811074810802c01e001030140230a0b0205044800d42003940117641000c01c2e684184040c0400a0495000c008200109040317201d140c04100c0c420310905201d170f420100058204640c08a020001d8a00603200d0905a0202c4c3d4011001d82e9402d401003040c1401900180404003045500405030740f01d0724410584c503540c0c0e12f0b949101c144c100c482c400c00242c1c04049900300359100c2250840b010451410131036440200d102d4240b11503000520901901ca0032011162036560b910101a0707942a01200c2c00d000460604100f00311691040466600c4280100703a03c00c0184c82c20540003c5405401001c4c00f69481070018a50f11050082021007074009460320180c0c007030550b004103040d018080e0005000142a8001400e00e1000f94 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 168782535 1250 168781285 168781289
    0x1003180b09070f0e01030317151210110309060403080709120b040b1f03020f060903030f0301030c05010804050d0f090e04030f020106060318020f040212040b1b07080702040e07 77
    0xd8840d03400d034203091101598a20550081100450300c9120114031502e840e803699040701e0745070742d8404000a81000300d9480000141c52508004422007550389180d0310700110030468240c550087c4001c032290888002902d05003255039040000800603c0303c0d00e00e012514951280e0141004c00254503007a0f0300702c030003892981c0503400d011480d4601c0c0c0c00308510f10044a0050b0300131380d00704e051511a00c0b075502c9084045c020600328000340601c200010300b020340002445100085c446c80c02c10000703001090a55018000c4003041c42d600000600c00c03c1152828040984801e03c0c1820007403400d17a6459598258807031000c010f10211444840030103118550380b0000e8118042200440e05107440c0140c1401d1080764100050750034480c0102d4100d00c01e2003071103480310000e1510319158980b5001d102f80c10304921500343d00180c08006060300d246042000500a51040700c0300d503000d01d000052040b001c814400c0d4100c05020412100f0f020802d08401c0d90380c0c0756012180060521400100103250042c65 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 168783785 1250 168782535 168782543
    0x3020705120306190f080c060306030c1002010e010e0105010911090a1a09150a030c030509150408090a080d1b020117130210030c03110702150a03060b040906080c040b100318 76
    0x50000b04034944042c40c0d170402c485491040711024240042009003034002141c6c080d805070b00040e010700c100d06c1c0440744042604901c4c000010a0541c2710032050a686542201d8803682c1c0d1510700422201d0500e110b2800744a2036003422a0030100201c000840718160703031081d007054041001607013440c661303068100c1d440c010005110802d95081024100d038141c004040a44c04207283c03480e100e103114028002c15125000b440050000340c082d80040c0400d03104050011384410006000e40034642c1c803003920000c040d00d208801099400d840c900028209c0d5411a6a101d210440c114210010b0740c201006c40000000414030313003a41d5641d81c01658180700340e010040d50054104030390705256a0150300c004403107141b40d541400711900494091120b071144681c000d4004460040c8000407806e03420107414042003034900410384590303a4144003890b800070703006442d006036030714010004603a08110129852000b035900340501d550b8040005d8034024494030b030300d061548540c15200d091002d010042e0030300340d00c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 168785035 1250 168783785 168783829
    0x21503070e0607030521042a0b070501020d06080a05070b0f070618060903030f1a060a0302030916030819020d0903060c05070813090c020f06010614040504020304060e06010603020705120306 83
    0x9000e54203d808147c03000d5488101602c20110606404040c59030301000d861a001082c0c1e00d8540c4500c501d41c0401002c1e01c0c103541c20b120381c0480004502401c002880350b00001d0007201643d082c610b080c1400d55010b211100c20400c0802015411901500d0070b8540080740019000d001c24008081c00361841c0300248514604003103d800c2540542c404400450000e9040007010103208111500140c4105202da00c590213004e0302204178866001950b10202440c15501e003043c9006504040401e150022115030b00d0108644040101d01c803154100b80d07010b813001300080341007090090448200c600001d055180c6542c1e6407840035010740202d9000591101078150744000792640c880403400c0394015901d5140c01c0640c08900341c3c2c0f0016220004a2000c0040c006c0c0380d10f4404140c512200f2032014044c4401c0c180800035007691284040c51103103004590216146880070142c500f08101600b101003410701c14041003002c21400141100390540b41c0003015640e0726680c00080c0000008035160800c0f0326 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 168786285 1250 168785035 168785077
    0xc050d02250e0f04050c09010305151003020f0909071806050406080a0206190c06020a02010c0e0603010b1e19090f060518040f090209070903021503070e06070305 71
    0x190009071030001c16500c0241181e050000c00c150914005684035040148410700b0104400000e02410b00f40c005114a00b1962400c00d000c01203a07410409034070540325a0000440750182c4558034801942c042c00316562581480e0441d400600e0310f150b0312042c0c80c05a0547c100091658500300b09500107040060f07140c03e9482d45103408000605028000e0308c0c003841c10010b0014040c0c0c03000038501222039008000a0611269255140428009040f02420450641c882c5404105140b004000851303240d800420516403580c40030f411101c01c0c0d409039000d00400c000411559170150702380d60096850780e540698541901103010014064004c3c0b865152000800c9041c0042d000200c1c101210303500110091001c0d41c443c41681d0b50701860b40c44408084080c800f980c414a040d500000800c40009000030f010030035038000c00e0b00c01c01c00311420000316804440510a41c80e02021243c0190070002840d4a14903140700c000b0240800d1510403801140080380c4841010300a1054803480c130700080f51401c07003071 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 168787535 1250 168786285 168786287
    0x311070515070c0b091f030609020f0301092307030207020103110c0105101e151803050609010f23040302070e0405010605010e0d0201020d1407140102040519060905010f0c050d 77
    0x10b0b00510085800301440d80002400300034140a803501c01074010101c5110407440c011184c40c09100441c202d0030588e070341d00c3c00b10320309505101a1a4010021804070381700d41c10080e07518101e500442c002c4501410340c403c5280c0300903440d40d5180e030281c128030700981c40b40f800748010303400341106003144d03409001d01041ca07041c0380300d056111f68031503036802c46c4407020603a4861000745540c04003d1682114190700400307016814400c0003080d96110240b070240420850700f150604c21032507642048507141c000c80d060024443c0d0074010006612010a4100241d402c89111700001c0c0c19101e4050160720742c424000740500d40284152401070449400b00c0080d0f01c0c1514001c5e00038505400b4030344c00b04075040781c0004c1e2800c112074004238495068006040694100600f0368080044040c0e400c0c10031000c1041800103291501203200d2800510009602d0794140307010440f0421465103203010600640c00d04000159006541c00c00301d0b4005e080c92000408a144c04a13608810150083d190b803280d150360441103 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 168788785 1250 168787535 168787537
    0x6080601030b060324070315180c0e010e0f0d02030a080309030a080f010522020f07080d0b0616080a120615020609030319050612070609031505070503040311070515 72
    0x10340c3c1c0c200c0959000140400d0300c1c000c0b902c039610a074941c2585d00300008942501035880425000002542c0d06c02481e44d0342405001500400603c40ca503e4403110207849543d0880c4648140d030700e007420a01407000483c404103c0ac00d90401c0c2d40c0b0b100d444020242c0c0259242480ac01aa09400202080e42c0c0d10b009a6103550b680d20a285050015000d1800103030907031800b5106030b059400051820300c0d00243c100c0d9480409a000d070341040301e20b500300415040d40a60100500302d4510a02000d40c4407070103060020304581400300c810340079a07010448059284c0046494101e001e50210407540c44c0c030b0745600c040b91032507103003024842581d26020000c81d007408840c0380b61801110740e6088070420780c1d0300c5601c66282c1c0004d481c4a03c000d100720300c20400403000ea4111551000f0003414682852010100382850203031a0352258000c20800c41060090102e41c582d0b425a004c01103006201c18180310030001d01500c00204003900b041403524040360000001e02c0f200005041c018074134401074801d1003c0d0038203 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 168790035 1250 168788785 168788791
    0x80309041a060307200a11040203071707020106060e0906060f0307050f04030606080c040c020c1203070210091502010b010903081b060a1b08040203060f040c08010510031101020a12110106080601030b 87
    0x4417030040c40440c2c6494a00080c0a101554022200c4040d03208900601004c0c6d0000342080e4148400c200c4081a4400e4518000b44600595070011600c61700c1e0100180c2079018661240d4064144e9901708450341d1100c00440d95000b91a643c442d81d640d442d034008480c94054288000c1c01014006030002c00d100d015000307013003507034400030944044071650300410040700c650f031040c44d0240c0c02482034003181d8900283c10a000d000c10500f502d1509840d640050b058880c104c40d4200415407201040c80900e005001c40f644031131890000700224072070840003808100042c88020400480010384852048501c07100d500c4100302c0300119000b904001101d607000e0503e100da90320b208840a0111850f0520541100b800303140c028028007102c0e2241d8007010482080184162a108095140001c1442c000d11440f0300c01c40e076803800c0482007410340c5000c0d5110b1061207103640c1154040405840452004028041351840320708050951043c0501e03071902600940d44040211701540d0000030910002514440c4 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 168791285 1250 168790035 168790067
    0x40314070f0c0e0f0406050601020f06040b15011815090909030e03060c0403110d030c0f0c06090504090803070e0f03191401060303021902310510080309041a060307 72
    0x500b41e6116a03c5180003003048900407403040c12040801c020810680c0202d40120043c41a928080d1001c2d01c5945045000e99040303070030104280800006000c80d40703615000c14030900e407412022041d4458001d0280d41800b0f95501c0c4c070540d042c1040401d00071100d40c4000d000c42e48080c041683c050802601964544107403070300a0080c00b001510290661f42120107070390344002e074085011250800e10044484682045082c804001c5000700814a258030040325940310b486e8404199052802c003c9c0044580d602c0030380610b01b004400390020741220140e82d8441e11902c2c04140b00306040c000107500c107100d2052940c06001d0141c0045280c5501a138004100303000d00a420b20348250b22409034221400e51101074010381200b03540e1429102d034050030ba16600d00003001e20203842c58600c404180400c2c840d403030b4918880b032130b02c107207201011500031294070a04100c0d22514041c42c1c02941764480c403c0c4040b15102d941d84134111450f40243c00d1304101c442d28050009a22807a190101406840c15806030310 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 168792535 1250 168791285 168791303
    0xf120302040b220306051003050d0e0d020d11040e0c0103061d0402010c111903031b030207061b05160810020702030a140309030f1c02060618040314070f 67
    0x1405150180c000c650448080394a09441c0948400c08050300c51200784104030350040b00080040481c81d60700906010314500e8000d0101e103880d600e8040d00d420000010481070001c05c01e10030032155221703000102441e4043d584590048041c1c909191010743e4441100c7e48546844500c44da0f0100000705200c8106003030301c00b0400702e41c99440b0540d03c21240d00c02203020090400000f00154403031008843e003e44680c503104010421040011a500c90710802c001c521101c00d14100f06140c0d1000c403c03c05101d40c140402e04003640ca840c001d440f6180b90260900b0b015444100c04020303c920805000350baa0420262007058407141704080034040d00348a1201ca91155048080741c1ea0054801c03280c40f9640140100205d00d13003a41c860303010010014482c0d000340424810101079407030500c103003c09000084050110307040010485c6148088580180c01107521140400200782c40d01c501c01c000c10500030010082d42d0b0348178602200e20009a0100000407403003c2440c1c41000b080790000c04100f4401c0c5540 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 168793785 1250 168792535 168792563
    0x1911010b01020a020d060b03030d0905030715090c15050d050a061e0605040e060406080f01051f0315020c071508071d03031c20090a0b040803030a0203060109030b040f 73
    0x490b83d07541c0c40703540698001e840d000b607200003441c241c4c4018031001d0090142d9040801c160100c3e0b007100d04240c0203583c2504009050300c10003200d035030b180b0044144440304002552142d2600c102000c0b00c4c1c0540d003511071100f8001d0348410300403800ea41800a11080c140f001e07280024104d00600354500c65044031240d01a0040c140140c108042070644802d680d0342e60030f0618241030b88400841c042d002c2138015a8425002c0ad00050a2010001150114001081b0b03030605210f40356980115450204150440820520002d0031b400c00d072079204080c1c4d10303015884070b248441d03031070804005601ca8032071000e4150709240400d0b0410306040c0b20342629140ca043e52040159000131f4a02071025107a4544c0040112a0038032285140c02c8c400b100b501017000074201e0261021000030040d5400031008008042403402c414030306100700c07001926106d0100ca040501c2c00d01c02d50769034000076110004141d004030006803240d20600c500c40c021341e0408011252403c050504c020712a038050702c1a28402c3e00300d048 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 168795035 1250 168793785 168793787
    0xe04060906090f0605060a02030a030504020d0b0f07020c3106090203010e010612090c06081b180a0f050a06081f0308180f060406030c11070b0a020609071d07051911010b01 75
    0x151f0f0301c000a1900038510b05100355808134014200104103c2e4040e0300d803001d9a0105072941c0181d480b880f200310119107141007041c03010381341204042c402407080c2e42840303241480c0035040006d140c1101c24000c060b6240f00c1c004280d50080d000c41d402110340984040000505420708441c5107040b80c1854841108020400c0c20000a544008101500c101d04001c0104480f82c802e1000310b034003082c0c4202501d03014804d1141030079141e102c950003000003060a00d0002152400c07152400040032410420b5124500e0140428031008242c4075900031321001c00001031030400d502690015254078403400001e0180c492505012a80081d002c054415898217070403040390611000203000c0301c1d030080c011030500349080411000742c0540c0700c2d00410403860000030071040c0002c02010001e490300e000c403107464000c04c2130300a20b86007005003a0b44c000c2d440301104101d450fa06405d01511a41300409000490f62030400558440c0300c1c8450030b4004283c13011080d03415642c00410060301d0082100280064440c0d080 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 168796285 1250 168795035 168795037
    0x200307030f0c020603241f0e01020a0b011205190b1503060f150111160e0c132303060a060e0702010b010203090904020f0303070305071209080d0e04060906090f060506 73
    0x80000e40002041000c0f80c001103c0743c400500011011900c1d07803038031180c0c0010840c108007601d107546460b0b0038014140005900070388e43e460034803030a100800e2015032546958040720018480c003c00c2d401e03014079a03024000280240d11768410300400c007080b52581c07450040002e2004643c1c0c14090717003800e00b008549160114880340148809245500030f030716010100ea80c019841c14601d4107001c8100d80072200044148550a0000c0a001d1132485040c50080141124440200504071020041200d40c40c401c580e05405810f45600030124180000c40d08440f4002c141b0144001d54148605400c1003071002d000d8010f01c0645084103014035060312000da081e820f98421001c0c040c003580080c03013208001d05100e0001d030303070041c0000c12121101c1e010802080c155405034000740d0000704001600750070b0103011100c1100c22079652500401d941e181a2603907446048440c2c040040108010100c42280c0d200d4000f4405000700c2c1c1410460347d50780b214600014003000081418660505200194615040e0 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 168797535 1250 168796285 168796307
    0xa0507140a021501061b0b07110a0302010603050d050c1506043902070602030403240e0f0c09040f08030a0e010e10060504020a05092205040602030a05100305120a200307030f 76
    0x194041030203047d9482c0714405c0c000826480c10001100070301c06860404010741801d042c0203800020340d490550038500d04010050b00400140300013004464150040015022401c1c0944480310300c40c0d846100019000d03103440815000c0f6181110160100c0b002400c04252624400316111003400b0340b4000c2c142d071501514441d400250f007060008101054003003072030904080f0b00309680c681407500034510f40c044a4104080300301b1170348069601140088104400308803e40101c441d2042464103999002d40c0a030030445c0204450004030203d40030702000d802c614591a0f002e030007482403150940c01140c0e80c481d00d12a1031015420305500240504107482254051031055803000c0c58078010005102400e640740b44201030501040c441c6140e06003ca1140d20302451142c1809a5207040c40091001541c00c040c00c903a9600307805d07500030000135a0014000c42c0c00700003640c50a0b25180c80a0080e40d2910000825154898051000d001440d1010006080e554030a8440c1c5588132500034044605c20500 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 168798785 1250 168797535 168797567
    0xc020606010c0803070e18130b010e0c030c0711100e0102100509060a0905120a030b0906040c0f2604080301060801060c05070501080c070213060e01080c090a0507140a02150106 77
    0x400204460358424a0700d91078000b00a022102140347c40010481e10b402c08880d0900d0381c0d103031509038400f0007800900d098018401c400000101e420480c040b840d05102c0900121358031500014507804202e0010704040c400c00005014003403041e80240003802c1c0c0d00c1d010741441c3c014020140d44006c0010385110303150103114600300400003540d03144200340060414690a461900c00c040460285207907440c010b0890b00032598010a902504a0501c100703c01d0185c403c0c1d200300c4c1071050070303080385500110749211002c86180452100d071841130300c004000c003074081000501610030708100038007a004005504331039150f1b03620aa6a0303602c000480d101445540001d0071500180d004204540c407038480c0682080d10301c0c80461401406500040c6d207601c00201d03070503a07551901401c218480000c01010300401d1032101416a606642000800e9094000d0540141541e94408207000e244503a402c00d00110b003000352141e81c2d0120040103503075801c058980308480c545040002c13075500d02c102c400310300000f42 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 168800035 1250 168798785 168798787
    0x8010c03290a1a0c010c0806090f250305060a120b0a15121202070828060b09040804030606140a172107030e04060f050904051c030c020606010c08 64
    0xe0351008402901010040d80e07031140c0c0b00a004070b845481a0a9032001481e0103603601e603202815070340e0ba821344842200c8071051188180400895844401c911588019061040241680c610008030b14900d499139000313440d001440c03900010150180c1c48a401200f08a420781c2c03d450780c89804c4c0102ca40800300090151180c2404114030941c90340017003401c0b54030303014405041c0780c44016a241442600c03000b51000c0d540c43c815075102c141c05005600141c140030b0040c0c00310384d401010402824000034a6400054600854407003807120652010008880c01010305003d4100703414040c4980d046404140e071102d03c0c200000410f861004400e81995034040d00d07a002d140d24142c40c580d50181d05c075500c41007500622040d101c265401ca00c0c08a1079010740b942d05e980b01c03003480c100181070800c1400304034022890810b0901668020720754500071500d04940c403a295658a01e0007a080c50100103850b45030307480c030641010190350190087e20320390400e5804c507451961a0750044400f0f10791480080c2003190 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 168801285 1250 168800035 168800081
    0x50c0910080a2304230304060c0302070510030504170703120209030c09010b0c1605031b0a0e09061e040210081305070e1f0b040b0a0309080c010608010c03 68
    0x4010480700e940a4a00000000d4403808884045404806880142443c030451010802000000705c0009850301100c1100300d5034a594100b00c6980e80b00314003403642400480d149103003c15208001c02c1020f060f010341100e80000c94054041c010304802c0d00d04880c0f080841d81ca90b0904a01d09040c1d480080d0581c1d10200c0d10140102c0c400020752013400e00640500460200c0580c0303881381c1050500800f03400e41c2071a40c2d00d0b00c2c00e00d19401c0041081c1c00c2c800ba0031150604000c280d400280a2039941c0190340c03020002c4d04e08070009804090154800c01c421044c4408100001c6004960781f446110403841c41040380713081205900380710408503002580140704400e030a44492140007000d070b1200b4044440c0172100c1c5940c03946031401d4040c0e4441c038084c0e010401000701e014a0403480c01d0380e905d844840404164246140501503005070300a00300a07070400300340c0840c07080c8030740c010103162500181e91550701d07488010346501800341c9005e2001e1540c200503c0d0042c081c840c0c480e01089041d00c6c4c0e482d0119031 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 168802535 1250 168801285 168801287
    0x2030a0512060d020d031e0e0604090c170403030c03050106090b0d0e01110c060406060602150f06031f02030a270206092107030308010f06090e040f0b0c04030204050c0910 75
    0x84809080c094005a001d2010303070043c1c039142200800e0f1400f03030f250000710190a00c1d038040d00c030310900250350030010890b202c5105509c4800c184c0c0c2c02e031780c0c0c001008518502d49070003c641c061f215206a2000e41110428007091540682c8a1000345169903800e02c46680c0300c3c0c0c4180d40b070074514854015a40d40030400e458002c6041c0d4841c0358209407650001ca080282c3c00c1c013041081d0007552520405030071150034401000105d00c960300c020074481c005040b140309030102214001c88000c1812101c1c52143c0001003040e074062003a49681c0109880300c8058001004103400250002c803441c50105103000e0b5031074401c0c815001010248802000c1141c0d00b40e9640c0d007805540d421962075550402e10700c582101c0040c001d001c1141600c0f84110080c071587d0301d1802c00400b81c0d90181e2000c40e0307200700b03400d0521030340d680010800b0035581400b50b4440c03907031a0344c500100307010348801015282c0500c1400340840543c0c00d400900c2280d008031021301c500c0d2640040d0034503034840da030324a0354403020b01110b9094103 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 168803785 1250 168802535 168802567
    0x50613020a1202041d010909020105030720030d0c021506031018060501080c0102100e031207051e0c0f070e0a110d05090604021201021801050c10021605070602030a05 73
    0x1c1c0c00c28940304610b440720300301242c1070340c0085d04602580381550340c043c030414505034615401844540c000744410900d54001820520000c2e00700d0080004482c24008544c1400d12002038100741401140c1e59882200c0384d040082060140141c0140120a501c1d4501e9580b03811060041c9001030151644002032140380000303095550f00d039a4010000420b4801040b040e2145070300034081280030349409843d05000a082140707201d06984210f282008120a42c0d0b0300100303039404440b100c01c0d411881c0e210382c2c03815100b40c001c1c11640040300c0c8d0f209001c0c116084401001c0d00c101c402c14002c1700d481394070304003803242c17582d4260007898940c010710701c0005c8000e8802d03040780031184a8258514a0013110180c803405440f401c0b56007005e01d60100043c0400c42c140803070411117102d485002141050b0600511003d49001500100c0c1040004506030701d180c0c0d0288004805c07103411150855548258401880a1211084007035038107001c0c1c03080000b0b030540003004444445d01c0603a40e05292180c1d5507550b96031 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 168805035 1250 168803785 168803797
    0x90601090e18010203090f15010303050d0207020402040305010f0e5a01020a0e0904020906010e0312180a0915170106090603030302030f010504060609030305030c160305070501050a05061302 83
    0x4003042c0200209141c41082c4021400f980c1c000000e020240504030f07501e860700c0d2850aa000310749814000400129a1143c15204450b802c0107000d0380c1c418041c00050080d0140750000781c00c0c2d51801c20725680900c030551103c0c0034007800c8815120301c007010a520300300004490226410760004400442010300e50a0480360007800e26000c0500035910441c1611203403042031049031507a0b07500041c0c09032410341181e24410001c0003115910303201d01e010f0f408a010201d0181507141881010804140700d517900f808484000b01125512684901144415607040164030400da40142d54402006c07a10701e1031030003106036051912038a910b444d40742050285403c1c107a402d801489550703400740480e100c0d02034060780c0e004500a40e409601e9040c62405030b24500010b900c00d0b441245850810414540c00c5046a01201c2d0141405a00da50301c100c90f9001e00d02c5581513104d14940e48454040405810202500c0070b00c0c0a030000300016a15011800212081035802c070b6403140c020100314590824980044c00 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 168806285 1250 168805035 168805051
    0xd0b19050123270702030d0b060f0a030e0c090c04060e03030c0304030f050307120509013b060f03040507060807020307030804020f030115090614030111070204020903030f07030206070806090601090e 87
    0x1891103c0881240c9080c0064a0610040c2c10000d46c0441c500050701031021180c804460451804514801284807032040300c4c0d001d0305040d0ac070024140d60610034000c0c0510000060f00504030340c42c14809040040e4821301800022800030b4503080151306001050394440100d00009528103030035a1101c44901103e28000c682610040000d10005440010300d4003a003001a21019110030f8044005841e500a40007440d1031140001c4890b4000e5a032046000b0040c100d00c80d841048100c56004201244a8141581e90648001090004100000070180212002039840c000c0613203c920703080740c0300e1003000409000261142e010a0151034441c1e8811031440c00280005682e43c2c14003030710964010207a211000b010b64035502045003402c036005080f0402d038110001c018107903941c890041103008000c80030b0f015550201d080303040750f00e0801c01c64040711b540002c000d40714045468002d5942804940c0c60002550f4040415000c2c100b00786400d005440503101d40800c1d5080601c40070040c40300a01e0a0 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 168807535 1250 168806285 168806329
    0x180b070f140d05090a050d050607051309110c010c0809030a0813140c01080105121c030207150207150203010510030906060f0e040c1d0c07020d0b19050123 68
    0x81c0192204001940c03550b04580c80d0503031181922410020702101a501080c09918085003840000e1004076050703034807040e00c0c20312070f07251400c1c100320783c0c5d00c90550f4004180031807400510003003405007034001d0403020409600901c2502c1821000f210b486c1341c10380b20300c103050380188a1941402d005241c010740c01280d1401c5441d5548040d11a44400104201c940817103030007001d1804020f5920103440c4c1d01510b020303a55040a1003d02e40d1150b03650074110040005034881403000c80419219804030707100650400c0042c0712130400104100c0003540440c004813841340803c4a112100070844c001e0301c0c121840201103a05c000f9507140260302606d01c4550855120303544480c00324864a080010001414010304600e0712882d10386400d958030708807500034002c0c249449090060000074071010503401942d850009445021500c04100c02038441c01c40207025203a2101080400d049000d8008041c3d468010240000d0340e032100034649012807110036940c0400c0302c0401091908240c0d038510154a0005184 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 168808785 1250 168807535 168807563
    0x20105192102030a0b0102030a09030f11060316080604060302060901051303051906051003050c12030d110c101a011b1e120e0102031b0f010501060f180b070f 69
    0xe007a100c0c461015000190b804400d00450007024810b244019100780001c5140081d600809080d500644c440106090110b42400003044914400010f1500300a002c45899080070110140d0060340c610f2114002140880007404d2032400b80101c000700e0f40c0141c13800e49400214001150150f100c148100c40c0d9403004003000001800811600d248d80b0018213a80800c0800d0b885c1c44c03419190040e00504003024a15024004a034010810a881c0c0e00120360440d04010110580c5086024990b4600315035480e10310400f91103052840200001102c1e4000e4503c42d10703180c00180c0490b05240c07200c1010103041e071021507007540500112401c410040d000c80c50541c1e01c0e659419a028404c1c03260340c0c070360401d41d65180200000388210035060300c018141640f842c010480003e581307020309032800e80d00d110403050482c0990820311046540e00c80ccc0700002e000c07d60b111640581080704020078440091081400445441035103000c14055907200d2900c186060400d03120080d0300f0156a40a43d4603103109030403 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 168810035 1250 168808785 168808817
    0x3090203070b04091515050c0a081306200c040c0504050d111203032a0c1912140f131d0105040506120d080403020c06070c0e09030702010519 62
    0x64a0010b10109010680d03960600c0915000d0f01c04501c4d680301c250010400038041c2d2520641d41001030744882c60b0281e01d5034108041d140c68100c41c2100030f03000c070a0004040582454400d0035000790b98030780d22680c4015141d14401d4039a0004203403a0395032038104071002c41e0b40c4e1400d500150089000e0b80740c02d50405444000141c5405081a0b048801000a12aa80490600d6004a030041d9407020280d0304502d04080a030805039506d54001d0310051185201000d0119580e0135680c0c000441005c513280801484103103e040c15a00e101624010002c1d4907401c41d951280391400102d941002219082c116480709407803d90300101c20083c0c180302c902001040d501845144039144c1040c220400c40154501400e0208480006c4c0c2683e004d601c11a05a85410b00001101300030303841546024155940e41d42000c030f0130080210030716584810000b62100c20b110b0500b16100c10707142001d0961103191202d4402560720b11607580020b0200d601032028142c0700034800c00b22003080145050101c2410103d0103 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 168811285 1250 168810035 168810043
    0x9100902040603051f0303050307050706060e0a1a1f080c07140313150507030e03070803040801021309090302060c070813030305040305010b0316090c1e020601060809150a0c03090203 80
    0x440b4001036924810060a60b80344004084002c1c0503031a41a281400c584008000b4403008019609200780013420204100f52580078400800103090003200c18103004285c2c5010340450091811511700e840380001c01c51800c1204444050400400203440f500a080140c0340c4400082c10700084100c14050f24022070001c180111800b0013220107540e40e0704280d509490241d81f150040b4040e050351a000c01d001c2d68001c01280c66264050515807110900f07500017920749181c07078202607118080885c00080c0d003603054024080d00214880c0001e0070f1510740c0f044e001280d419000103401a44000301141d521b18410700148541030003245e20526010855030361002034855540203e0024374009030070018803400384113060036000124064901ca00c0801541203485070349001c0c0d5005281d69100350f6001c1c43c0100018207080c8250307100c03440c1c05401d114010b0b48500b024410132000c2409100000c03028074010500145e00e40001d4802c1c90180c48141c011002864000020000e140d80c501320207001d1b80d0100 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 168812535 1250 168811285 168811289
    0xa210e1c1e0b01030302060c040602120c2a04060506030f04061e0e06070909050f010512010b04060905060f09160309020a0e0a05040311070b04090e1e0312060d03020c0910090204 78
    0x1070a07000b954911700e4002d1034158005c1c40c8000300d041c1400140301d802d0b40413582520440d03a0003440b64980d9986500a401c124207d404403481c00c883c400f0041d004907149080c1c1d0441402190304110aa0340da8052003007070303c0b049400990030104200002c0c0019000e92100c941d04522303007580644e070350740382c04000100d03403415200a00035070095041081403503110b07880b6001790031310f0700c0103101904145216501031501030240b544075604144210403d02425480084000d0000b0b2083c0150b50382d42d22000028101591924001c003005e0700c40d06018205180885c1c02004084807404170418101030481c0200180c22049900065500c0001205440100520700540b0f003800c00142034141841e0107089245030f48503030740494000c120300308489680700d0280c0e030854680c0b000c0818401515245c0d14109203807038494030000d64040303141c40d03002c210000180005000314003442203651240c1003088040100300364010016400b1000f40c0d607560405403440ea80003110520389098480d220b42443d01a0f03006a = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 168813785 1250 168812535 168812543
    0x2907050d0804050c0406050d02010804081c0207020f01050c030301140f061b071509090510090915050906040804030f051c03090506010f0509010b0307090302030a210e1c1e 75
    0x808107200c28001c0511080204e00e03c100c40c10459685040040341c40c100c10f680300030781803051500001d0103002101c02164007900306440c81c4031462414030b001800a421004017a400f07001058080c42140d4062400c407801c5424120055040d6841d10140b03c4440d080761264a400441d034a1171603009443d0076010307008180c4126030b40c648004130845d0340c6180c600207a00406500d65035020011000c1e40048500042c3e4030302550114071039845500100e100c0c2d04651042482d949801045403d2107081c0c0c881101c0f40034800800d1006480d080d14490b0382c0c100a9038085c00e21101000104001280e40089030741142c89401600c800061000354414200c1131900e0400101c1e8481ea800810080148103c07405004d0700307840d50302c3d800e09100205003810303014041c02c03900400000214243d00d009000174802941c2c01030840d44110700620b052504019008040c061040e5508a4801658010b41c900410000c02401d00607003202e10228181303144d00800c0302564100c1c54058010f9600910541c015459802 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 168815035 1250 168813785 168813797
    0x17060c04032f09010b090909010b24040f150906090f17010b0301050426160209040516030305040906060f020c092d07080601080903031b0f18030d092907050d 69
    0xc0705d087c85203405c0014080c1e49164948129039000da40d5207002007004a129180d824131040708008410424400c541000000901c000c100090040d81d54081050b9402c01d03903620401507648403402c1e901090b490140f85200550000c0900564200c7c00d12888110791250000c02d0b0481c0c04c101080c210b85065505540803001c5041d14419561400766600c0c1e600d00240c03040d8502041e084402c10003540395040248035030351880c045814420308100f0b05269440d02425100100d550307107030242081d031052042c445007609102d03001608138000c14a13201443c3c1c081c0c014280e0301a0801c03c001708120010035400401508290815500b904030800b41000b0040e507809041901b0310b160064030305a0014480c03810001c001e03040044004002c41502c2d08083c084403104007102015181c5100340c003500144012007030010a6000011a0310b041c0030403186000c1e4180e5140790741c110002c4030903088500941c00403801c1d039010030303440c840d40d045800f0503080744030f0ba02070400030a55584e508102d012407202c030001740 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 168816285 1250 168815035 168815047
    0x305030406091202061005100509060d020702130b18040302100e01061203030f05010519090203040314070b0a0b1f051c0c09030308060108040c0509060f0a17060c04032f09010b 77
    0x4100c0d55104050242150f10100c95523142e40c00605910a6220b0b450050f000403680d0319041009406a4162690080c2641c00d04d42400300c04a000b890300070b03915403080f10b02801e26541c6600c0188003d00458060f405090215811000c41c409007842820400e880e42d80e6002c0000c2c4030109511308500148a5540400c02032108550342d0141d0340107070804c5200350341e003c18000141c6003150600c0c04441c1154009600c070350716400c0940b5040312a51418844000c00607800d82009002040705118514414080200d600e240d000e00c0106403402d050314124500c541d005100003801600a800c00203000061007407004800c1404109844113401c03401d010803414401441015004443d02d81d00034020300e03041c42503103403603214000780031407911400e40144c8841010070002d440d02640c2401c6c0d80e00140c04001c2681d0b598902880720b03003890100004e0f82c01148041441049034408880840b0741000420b40d444640402051246410000003075500014207400d070307255103414409900070000801c010f51285 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 168817535 1250 168816285 168816301
    0x3060a050a06051c0c050a180b0f1209010c050d18081303170307020d05070336050102060903030a0c050d0e07090b0102010b03060406181e050114070c030503040609120206 75
    0x54900345100c44c03031410502c8102107a0782c0081541d101c1099440d25207507100c459485405201c0168000350f070318060005d404810511194002d03c0c0f50700d0790f21025041555000c000500300e600b803003801c4000490401036214000403d8015196403152011000d00b46051980d4802c0d0740d6121081c80414014040c0c420001d121540c40e50388142c41c1210b111034910f00e031080c0020b454101100e103c405010010030301e101494890482e07a03007034204000415140899400d400300c0512612940307803500e941590b001003400c0d480030a545002d003e00300d00841c01c5488812072103001d0510b031403040c0100507061003601064000c9000b4015403028440242440605010158080c1c500c200350390350546e07040076191201c5450000b2084d44c0241c012400042c0c94107081034541c2101c490400142800c086036000340a04140e001041c1d15030391251000b00082d9080700f00c503501c0e50304101e84442c04120303994915804a8003550095a0180c860000050002d400d69241d90944c2c0002e812100140e120303c04020446d = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 168818785 1250 168817535 168817567
    0x1d011b0816050d091505040f050c03010204030807110424032010030e010f02280e13110f0705061e010b0f1c020418140c070803060a050a0605 62
    0x4428103403500181c0200480c40500240700707001104211550307031080d004c11302c102d80604060b80003040405101c0d070b00f40350421403400d0790703801c80070760302d40c090701c1210411450f051085400300d99000c0c074070b54148071042d00c624038007860440304c2640140d126400b0400051205509846004098074020340b81821400e1014002545002d410234882200040c3d1009035500d0103111600b5a45240c00b003411000403039041d014001078040d0381040743c0085409003e850900c0346108401c2c480303402020894035500ca0840340d813820080496001603007008000341410b900e0300009080d076403114529103000d001c7e169045940e03000ca103003600d60390407500601484074106111051f04041030024500700e941450190000b0f4890f0500098065400083c41c6034a02001042c074070348001003410454855907911a500d07580d2000c003000340f0449140c02460507640a501c000280501c54100284d41084080d03a03079101107074000741c00c1c5588011140e400084566440340b00c603000d04001d0382e80f241c44e40d40499500c500 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 168820035 1250 168818785 168818791
    0x9090323090d0f020102010603080301090f0b0405040f1b030b010902070201081b09042c0312090f0c09060409051b0111010207021c172802011b031d011b08 68
    0x481030400460000350749041c1c0507400b4940102c210b1009141920041c0e004140951000b0038100b0048000200e10446a000c4044510742c0e4034144160000e940070042250401c40300104002d00c1c1080500c003141c05e000c10071307401d80212035401800c29101d4a5902c480c003002d91003c52100c2d0000340300c20031540d10040d45a0083c248010702125006e2814490002d4060215a1805559680401602c8a0240c092510741e40d090b4828203401401010b4007603160391011240c0b40004501601103103114200150003001d82e0303001d00c0030341445241c03041001000b410103020154801e4640b214100400d800f440841c2400c040c0d900f440782c80e1800d400024009100584110300c5591051003e900035807541c407403520814100304800c049200c2c0c18501108443c4a1201794510100c3c086404015005029807542701c198414046500010344030b08102d00362411403400e50380303803d10340420205290007600809110918140030015406810400c03c0c21180212590504040c02480c8040d80c9030b0040001d40e0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 168821285 1250 168820035 168820097
    0x6150602011505100306170a020102010b060a1710050301020a020a1b140f0301090510050411120c010c0c081015050a03020a1a04030f0506071d15070c090903 69
    0x1c0e200c20b4031101d41e0519018450f240c002e083d0600e070345080070b210f0351101c000703854101250381a82d001c4805a036560303095030000300c4c003640c03030104084241e2401c6c0054401110b4199203982124058415105071060054661030060401c810701040540d82030026142c82d075455402000000c096040608420b8401e04490030b0100701101c060000c8900101e00b400707000815144028080041400300380145100b82000d000b0b8040c02e800900b80d908603410850140740511141c15100110004001c03000c0000842c000b000d074840c40304a20745502503024126091f0040c2c1468000fa643c030050903080c001d8060000c0c7d481992804820f66500c01814a407001d044244c07032241c0441d05542c0030035480c00180c01555400a07a5020b1080713000e59000c102d07005903900c0714814814065515205075075074015285000420a00001c01403032603a4245038004c1158010079400c4005501d21049040341e000d01802d07501404956004102d40c0c03098000d500b41c00f88241d035201c0e500200760755207054402228440c00 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 168822535 1250 168821285 168821291
    0xb03011d031921020304050307020a03050d030c03020a0903110d02040509160b0906040e0c04121a0604050405070501051e0c031306090305030904020d180506090d02120a050304051501030615060201 86
    0xc20500e030f41c0c90b50b40341c034045407402c01a602e0f15075040491031800b030304600950001220001004120003c541d034900340c21551400d00044031804d00c00e0742a03004400b1048000360010078104081a0320303014080188101500008201c013440d00854150364046400c1d004580c00740c0d040b080d44203441280c038801003040700401402c0c4103d001c0001c7c1c052203035204483c9460224408101408030590845008088440408906103458601a10311004092242546100314400140581402e018441c407540c0d01a0140c2885802c0c01c0054885030450400c6c40b1400041507103000b5021181401456880c01003402151070b107441c1d00740e100e078080d00342d00f01e5010040034603001c0001138800001d94580401c03c65002d40c5402c000c04941e4010042055128100c5554003890b01c01d001d40440c41c24000d100f0001a01c02d10410900241d1f920300c0d0a00381d414042c0c1c020000360102a100308095a0070074410806c1e501411802066a8000813081e0400c0c0c0c2d2003662800b007039400b4144601c00c94000c03d9240024 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 168823785 1250 168822535 168822557
    0x20606060304060509160303020705040f0b09010b0a03021b07050a080a0b0106030507110a03090306150503150403020f15060901060f0f030c02011b0327080d0b03011d0319 75
    0xc50031500010784000d22490700d64021800c062000d04c8600040c4400314440c00410b03644e0b00b4029601c0910f841064007562400b1880c0c80c400030603003d0503007180c0d0701814541d210391a02a0704525a801a0803036002c05600380b0005419040070804101d00d00104001001040c2c14001045a40b21250b84000d040c0d0340000c0d40500002c0104040c10304451044c2070000e4155113070740007074981460000c3e81c5c0303100307000c0c41440c441056003050032a01524054001000b0b0400c40d820000b22001003805181da0503801000355a10241c1d110002607070081c032a2060f290009810b0408a01e0401e285502c8942040000300700045410241b141038014010342c90000caa010710214040e0410344d1340c0b104007007019101c08825009500035040060110301140703074078001da091404014010724a18040180034000300b10f035007480c10700080030104426082069549018016248400203000040d900381e0503549494046102440000350350f4183d1150101641d81c468031900102d1081c04040384c94014440b80c2c2c0a0 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 168825035 1250 168823785 168823789
    0x210090b3004030f0c020f090403120c090f0902090d05010510080f07051f02011407020d020111030f0f0901060308120604050f0106230c070617010f050108060904060207210f020606 79
    0x4c94407682c9400c4c20051001c0005002003006074145d0b07101030f6003006000c424041003685c06510038400c0500c0da007080014200700a4101e0350b4021522401208521807041070020750020740c0102000301c00203000c0c00c4000320035a178603400d4410403504d90354020b0000400f00701451090058101c0c00003000007130519903050200041003d112040c10107003c403089402c51441c1c1c1c0c000d500081e500c07031085810f183c5034900104025640d1446032004001542032a00030710910910300c2c1520702071043d9a035410056655400100822000100540350700d64a61500002003441040208110080040d1254039803030208140002e698018050250076041040104841540028126441e064804c2d42030220440d549481d4514000c0c403006600c94005d59a0000d02e0320303000629080301441d0a41e50380f98a0781d9807804c89401902e107219140c04181e15a001030b055107080c071502035119200c0e080c01820140030ba1515605404807803010082d44800d42c036058003403030300708040c07090741c1049100a000f03525000700 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 168826285 1250 168825035 168825047
    0x90203010e070e031e0705010e0607080d050907030f050705010e0d0213050c04030c080a030f02070602030304021c0605101e06021b0109180603060f0504050a0210090b300403 76
    0x31203420414048690b0409940c103200d2108001d05c0041c90285100f0013809113a1103074100c0c0300719400306502c03801e520310a00b0100c040d651403603005201107041ca099154000068000144418005e015650011000841d60994201c2150003180248461800e140c0090711718000c02070481d100350a12740002005980d4120300e4510443c01c00d80101d12038482c200e068200d8080d40d0070050a49075001c0e400703d40e43d0310001d411120140250758a130003041c80141d099860709803c3c05102d00503041000044d01606114981603221100c00c02140c0c0c08042a4550804482c800e54012084404c001001c000800784860b00c00840440030841c1c0210303500c0c0c200081c1d583e00b100b480c0e03404440340082031400c05a0040307078098003c1044017a24205920320a0018005100a0008844051900500c03030b44098840c480c0912440d8807030014070404038144c081020501807110074800304110403030041081d115510180010282c0050000408451207034241d00410403200b038000b00a01c11400c010202c1d512007 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 168827535 1250 168826285 168826291
    0x150d06080c0402180f010311070818010c1e0318060309060c0315060c0501111209060108160e1503010f0903080115050412050c04050f1501020601050102070b09040e010e0c030601090203010e 83
    0xc45c5411580300c0d10703005134007520202d8641191003030040b840030280100c5000a05e80c800c4103603d802039860305a0010355250f40e142002600f00820320342c03105c45500f0005502d4010a01a00380035018042444500318000010340040d40041d07100d1810100300501400b40b00e1000541341010301c840781891800750002b140301d12682e4100710071440c10109100c42940048914510100002d544140c0210741d03090452043c3c803000440d100e81000005c00d0706020800140d4840d100791800784651400410f80c101c517130054214200115138010303241440c2c3c0c092080800381860380c100401c01d800e403802c0143c601c900581c083c07214420300540d90032a166029088400380c500c4900006180b20080c185030786007184000a060300070f8540401d001100a0b8100715511481409070003c550f01d100c04d0049032501000c0c480c55000da40080414411000c01c01c0280103001c3c00508006080035401640c5425180080c80000144e00001021304807810117101c0540541071002c029481c5516103e00104610340c02 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 168828785 1250 168827535 168827539
    0x102041d1003051f0e0115050a08030c03040501200d02060910050c070f030909050708190e0616020a02030a080a08070807021002030a242301021b150d06080c040218 72
    0x15034003413100c6414550085e000024820000c05c1280c0c6801c0b50985180c0060080f01c6c400c591005d000903415070008110349016540340d01942c03c3c6882c00005407111408403e108a0505059a4460500314100100b0b400240c0c03541c010101820b2429149040034915081c01501c1c5092104200348096a10212401603030300843c40300d40181d16040c1207440c04581d4020301ca0980c1002d0621513200c1d80120b0341c0e8020880f0040100d0700100410859080314400444294030340c0001000030044000c0340342001103965039005640d00c40200742e000034140001c4003011500f200010600720540c50340125020340c003141d20b0500c005070b8201100040d41d560b0302031400c0c8110b030f6000000500344c0e20460300700980d5045907400111800b54a40c01007402e203003445c010300251544003c1d40d464007404402d014080e80906070003a15003072810f00350100032800c484d1882600070303078500f070080c0100051900405041a85900c000b4445044c000110304004160300424856401401100140b002c0103060305c87e42001 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 168830035 1250 168828785 168828823
    0x50f0603041703010905010302040f0203011413020408070803180a03030503040f031e0507261606111201030605011e140301090503040621061a030a0207050102041d100305 75
    0x6910781040b0000300142407100280d00800001804903079500258107a910844080c0503609505451504901091203150000804007010021368142046045a07461a510000d440c194944000c0ca00c3c2032100c0d40051230030b610000303140b503a42030b041c0c032040d2103400211900002c40786943c80c014142d00000c1e0014000101c2b90282c0401c05014a00342c0c0244044042e020b003283c0b884000207010340e004034030700340c44003803018076141e18111981d020145582100580c0b00e0900880c02108008405409030803a041550707103002c02c9c20b0641e204050441c0c201d258800703030040c2d81103241c40b4041c0c2d10f060741f083c1907048400c5100c40703816000b4404001590361a607072840008600c6c8001034003502042401030700601000402082190784200e0118a03c0222584400c0052040c10032100312001482840c0c0e01102d05842a00300d055110019600702d00b0190015041c414592a042c0c02c90340240d01050444909401a000a99503840120390140c1040c41c1400010701c0e6486458a44070303541391007640032003 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 168831285 1250 168830035 168830041
    0x3030402060f041a030106080f060907112103190207120e040b0a2301090b1b07030b011508060f01080f060a080319020106080a050a030c0312090303140907050f0603 72
    0x300d1600390f0740180800c40c400c0900282c01301840350150b10a0180000080900002400503902c058103940101030140071400c2650f143d5508940301003060401c41030b030703000350041d0300c4208549100241c3c0513112040c0c1595242030050b4001d87d040c0346800c6410320030780144a0100464829a030041c0a0f00160070070584440405c0002001084a030500303a520180f070000101c4c41090f0890508144400405844901d200c2c0c1801560054414458803940000421000c0c0846d040001095045010744046802d056140d07a60043c151809801c80308000e40d0364445c1c1000581c0c4115902d03008081560450715034909480020100500103100c9450125058080707039281c2c40f100103100003001c003d000c2e02d0311140c13502d0341001d4103074510203d80d005600380030300844c4203640401c44281c0e03154050001c00300c5855503079094583d03a02e0300b85d00754140326154004800d1440c05000d000c404a100b44d6000902c40856840010701100c003070f0100341540d101003400d00c00303510b07041c0d46d4408100d8104d0b485a00c0307507 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 168832535 1250 168831285 168831307
    0x9051e0f0d0614040204050709050306010314030f0408030d11072112140a06080705130b0105041d0415060f0e0c07020402190915080a0c120204080703020a0b030402030303040206 78
    0x8a01c1200401080ca042c1c2c6803000c4080c6030100c0c50045100300e40510003501c13500e804072440d0341203004031589034210400400c000f444010b030300d01401d41c01c2000d4130b04000d0070100d60042500176074007100182d0000120302648007114803034003034034090b10020705090603075944421114800d0081000d511800d0466200c0206004030654031b40301c1c944d40d20a201141c103a118250b015442666044c5007141890400b240304040881c4444c190b84001c1c1c0340200101680480a001c2d003002c501d1345050240400010074408600b1840004a00d00c03d031100d2400e08191424091a042801034814103914041042c0315080c001c0c16160700b00c40d00c80c0039408090310341d200d241440e81314082009501a10018040c12a0b1240b600c03003694030580d81d03c5079101980d45040c0303081c880c07401c0c4c008600040c26400000b43c04c005250b0111a52000907d8000c1c440c9580240807003ca90054100240c1d650044404100314508404aa00a0840c6111450031800c0a502180e503d01014100921601020407006404 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 168833785 1250 168832535 168832549
    0x1103150f0112020301170705030c0f061e03270a231f09140d09230901240e0310020306150a090905070216060807050c1002030709051e0f 60
    0x1c1c4182c0030308541e2540c0d1034108094440c0440b008118a0084d01c40c000f038145001300e8640712461000c1c08030b000c0700c0803020402c1041c2d032007212036035103504c20010340130108545140a94425187c4c26402c0c85e0300080b10013881d6483d514880c109180790302500100c00000c455009c85080e0000c00300700401205c0341c2d031402508040030400e40030311801c12517044108400d20350f00710b507084500500711196071030070358a4195201c9000700050300100d010004100846482160101b00040f00c12201c42a0310702080e0004030340b104280d010501d5141107690458070a440c00740b0000c11030009092248100e011080440d0701c42234030340908841c00b40e002c030014201da102c50a11206203240c041c5102d548407028071000d80300c00944e001c2e000c0381c0c0f440c15000400c00c40c00002c03611600d005031000e900c0c2e0b0300e25040b01141c079810001d00440800c1401d021000c2210002c00040c015004242005a180d15110b5001000e130304c1c0300e52040e446040484840c1800d00d2201101c15a40c14003a54142c5445480c103010540c0 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 168835035 1250 168833785 168833807
    0x2412050a060c031d010204140607030503060607060207051c08011418090304030f05010c080106211a030706020c090a0203070807030b010513060f0e040c0509040e07150504091103150f01 81
    0x2000300f0368658043c80c000e046d40144142e4082c6242c000c1d101c154203003408094007032094014041003040001c0751aa142c14409045445d1155030050310302501e540e0703058107180c0c0c0e001c482c40c1064803022402c020340c2d411000ea035014104200350b180100c0ea0100025801400c00d05041a1590003100400d521482c00c1c811034014581000c0704241400440c50144d00802d841c0c11000002004600041145481110240319907402d1054980701a48442512001003e0386d80c0e81c80351a54007250800540e84051004800419a070740250886140120078004100802085460321520400402072043e81003032846400c040d0601d070000c0c0c440328010040e113091098405000e41c410207100001103c035803001c59070314150480d640e001010880da10520069441d04240200850001e004801d035508003584011083c0c1c1d0303080111031400e44d4a240090355071241e00740031000a20002030500c0703844464040e4802c01000356800030b156141228420945082c0244841d200b1100c11524001c5684600d250150b = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 168836285 1250 168835035 168835061
    0x60f0e25030b010e09070816090b030703021314010b1323040207060c03150b0a210c0c030212040302010e06070212150106030c0e13050c0d2412050a060c03 68
    0xba0301c2d40c42e4000328000030f40480c0c2c500000e02c162100480c44100104083c00d640c40724440ea94000f5044c0081c0001a00d03180000385d0300340c854000004090f985030001c8070091b000751000007400076022110702d02c03d0007050b00501c0e042c4a080100a014042c7d010341001100c1d0450f050540c0500390260b07038501c80c02c1074600b00707038420300108400e018055150301c94a50002f0580341084600d21a600d00409807000c1e01c90101b00000c180b015181c0d0601882d40503003561201510113603010809040b01b4225691440d1140c005010a0f001108164040140b804403120884405040070b02c0d5500003030019000c4140c59025a0b0b002c40c0d200300b19210248003005070081e02d01900d181c0c80c1604440c4a1405017403203401c001138203011001c01280e014070360000b0405009444400c100e00a5025030010701801f0b800943d5100081148480f03000035441034102c0408082d0070004551301e050503601105034a43c003e20300e039143d4109241d00144000921001c21030788a07401144c00a5594420f50003841c500414030 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 168837535 1250 168836285 168836303
    0x1603050d05040b15030604051213180b09010501110705131407020a0203120a080606030c0910050711090705070605090c0406060504081005011503091518060f0e2503 72
    0x200102c402145118150034428504c0d100300400426580b4501918082c109400402000190807212001000c000c84d5035014199800e6940e100b0581e1540540c1000c101240d80701620f050b50704e0043d030207500429003464a40f04107007101c400b05c0e0321004c0602c41c003481035132554190304110010b81c01498240041000311007a0340f07400c000103511286050301c201c1c800d01440c1c900c81381810082084d680c0003590f60350b801c075095940405000b1640c0c000f400c103200180052011195907070741c001c001400410350790303136540e140e00b864a4010b9440020b80ca50500c01c64984003080b00585c1c0c05402e89080b150882c101080d651200300c5000e05012206600076009410401d002c200c940e00a0003c20440e0030040c1111920304a562003174007200d40c00c0c0070708101c080200b41c4030704c031442c07080d0004600240900340103a00c0780e0705942440308481c07c40301d0075100d081e840404401840228410341c500900260018041c0e4003c1440c1c9985540004101200ca541c85c1072a0004951000341c400000d968815419 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 168838785 1250 168837535 168837541
    0xc150909090f030306051c0221010905030a08010503120f130803040b0711030c011e03020d0216030f18060c050106050303030a15080c1507063305030109081603050d05 73
    0x110b200101d07000c00a0700464104480001c090604020b000000d0050b16061010b044240c1c3c20011401e0190304403c3c4191501407018050200a00c03403108264424001156030340c05a04000e408207205901039807080d003103016020070700603481088406501d00c0f1055a40c1d1070361607a5000503207001641000d04244400b20340420090b00c0c84000700541401001d2440c0003107816410150b81d030103403889950004100c2c080c4540e00c00e100c422804000700300c6040140c10540c121440300101c2c0c1052580e90b90403130381c204850017890307044400d51429003024900b1351300002d10620940c000d40caa83c413911080112000041081c4202940484050306004003601ea89007452929000a0152010200e1044504440c002a101c07000140c006c07440700060071680c102c2d01a4a120070254000e01ea06840d15a11280c2c079900e120754004594807140007140d0740c550103400310b010424105246801680c00b076890000f1fa1400300c2e07005000e41c1c020b4802c89080101e405400d16040318140036a00403a8001803e00c828 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 168840035 1250 168838785 168838793
    0x123040f0c050c0712020f0f0d050105070c03080105030105070807080c070215030406050f16030c0e0909101a0102062202150309060c0702010c020427081c06030c15090909 75
    0x1e042c100c074003d08580680e900c811039007480d44003107600250f001041481c01615424080d84071451050000c00c04507203494103403a5113007555422210600000d04250031030082540001d005400b408042d0002c000e94942080090038185001c2c2c034890502c801c4500143c44c801d11017040f80c005682c09011204024155954503106030820341e0100e034510b007000000b0f03070103200b0041903c0c450014100c105484607465602030740141f0500d08240c4c04c000b115021300006440c0c88040340c1c0280d840c04000d00f0b02800d0b03143c0b140129101e0840c1318104d402c050300e4131580760380d001a1140d04564501c01030846c1c09021015280804a004002500106040d0340c062400d41c00d82c0140d4814100c41d001e0307440f03541d20305401c0130320703403094460090214402250303c0015052076440f115070103540024640308800c10307007140c1f4200b80c192002107450306000030300340044c8000100100e40b414043c540c2072102c14150354038440403642c5405030300307200607030102125160307445140618000d10400004128480003414 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 168841285 1250 168840035 168840037
    0x30303050a0c020307030c03260f040b07030506101214090321040308070324090c0210060b090607060f020a030903020c0901031509020d05010c050a14030123040f0c05 73
    0x350000c0d031034a4841000c0d0014000b1088603c0300340d25940387c0d00c401c19255010744080c060711208050000022214541c40549031014a000308125038500255103800e10b882005410002c2c040c1007058204010f00030191107000301000300704498208405120700501200d00100040590742044031306880504c030090101200509488074540358030a5441001036100800540550340100080d81c080f00264440d4800d520044d0380b0944105000280c00c8002c0158803000a81c0d005000ca80341d8450703003c14116010071140000003221001840f20a150810024007030145041031406402c0001c0d12404102056104103401e80500c5000c42d1203044d01c0d0302c02801448005800ca001d445040161012407906200007070480b648002803440900d801003000000d4600610101d0f08424140d0361040094030030b0041045114459807840c0d122082008000e140d07090b502c05485451380100300500c1985140394031107581e020250600502c0c0501c0c400810000c0030144548001c3c2c2e450441c5134004154090 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 168842535 1250 168841285 168841291
    0x120203120301060921021504050f030705060306010807020a05010509060601030c030509120d0204081005040b010f0e13030e130906050105010323060a031b05030d050307021905030c0703030305 84
    0x602120009050038804030038a110a0003801c000c0b40f2949400c104100540a580c40c0c0780a400000380300640403039012079800c1c03441855032410f00801180c240600d0070000041c403182c9104030010900103191401045c858400900310034100201a000124942e00801400c81e401d41d005e00200200d05c0c02421154480c0c1054401c240060b0400400b0540075119001d002d0040c0d440101030049025240d011030910b501443c88081e00f03d80030f00001515650a200030641040038003c040707910700e01490a4020700405802071000f280c045402480303076610b141031040c0d000418024100c0e5860300741c102a56026500036400740d0080444240341c14a0402d50071041c5890b100314024401640ca81d001501a2490482c510680c40d020301d00a0080c1c0030515496500800007510741c952103522038a9441040290000d07103408909550380800050808104824103240140707055030844c2040c5c1002500c1d24545020700c580c100800400c8020302c0400c0c400c0f1a207901902048504940d50b918020700506011 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 168843785 1250 168842535 168842539
    0x1f0e01021608061513060e04060b0d03050304080c03040f06030c0e01021c0c0606090c17100302090c072a21050d120603020d1103010507031e0b0103090204061202 71
    0x9403009072014146403503404240e0b1240409000d03269078580480e84e0b00714005088961101d0030f840526509050380c828040a45202d1690844070b01d4103040100c10380341e00301c0c81d0780e00a140220000012a5002003a01d03045603200b503400c0e9440580d00001031850186402140c0080d1110704d002070000d402d07511102456080741c0358002e07080440c500581c0c540c3e080700d00e01e4001d5811002c40a168611071400c04800600c00e800000f07c00c3d4030341c10090700b10303040300c407205001c2890303866550709044180030707020f5200c9040d86e036003c00c2074196030101d060700b0005008003203101e00104001040055003580c94089d403944690300d010f403282e00c0c0c20310f500804142c42201000c41d5040341c101090180c592500c4d083c103800100a03e040b08105034101c907241d144003440c064040c1e4882e030100060b40d0b03d590807e200c501403401340b40e4980c499020142103c501902c1c02c0141813a1601d0702201c1c000155160120405880e40000d201013400010790280605440096000e45021004555500c08038042d505107802 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 168845035 1250 168843785 168843793
    0x306060f06120e1c110d0825020304030206070203031909050a23060c0708060a02030103061103040f03030c121409070806131b08030c0c0108060102071406091f0e0102 73
    0x2030914a00304444a040b010611034100c2c4541d07507001d15082410780800813062805d1524001010717051401c040e1511b9424002600c01401d03c41d070410480d900c0c1007503482003a488a0103214042000c0d60700d202e00e00c4001c0c056400802c0d100e081d56428420340d014034070541c10741007207900d103004003c1100486028480c440c0551400100342a040307044c0d015000d080070000641d0fa80c2900e820099142c210a0841e21903200b00303800461058420b00902c0e0081e800ba980c0941c480d410b40c500f400c1074035089969060502d50600800011a8210440c2045103416050000e00c0b4980d05404840b0541601e00180c811401c012401169a00b1403800030300c640844015142c503240c581001b2600c4400940e40000b10368508401c21001c0303010340c8095810003585806103603907141d07110b811a0031a041401c000301c403908595180784070707941c11807000c2d40d2042c0244041c051369410701242e8040d00000300e4115004c1e0802184030348641e1508485404954a00c120f000c00100055000500070740c140d22200d40103002d = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 168846285 1250 168845035 168845057
    0xf05070f02120408070905040204020c0a240b01200f0304060909270b0703020403140102030a050702061902180a0b0c150c03070e0f060313021c21020102040306060f06 73
    0x11841c00783c5040d10011030241c0106454041e64101810300501b080e64419420840f10b106c0c4201040040c59851080306440441691140001420303944044c00001c3c0905101c200c0b000c0e6a0701c031003014605205a002940e89090444c0c1c0f40b481c250074007030341480d1840300042c08183e10743c00c12500c00c1240c007000003e0100c0c00e520100181306142c00c00c00110361020f60f60107000014190070346158001451701d401402e143d500d40b1a501400c070003100c0000c899600106001c0c80b14151301840b640801c40f070000300b1b41c0d030400e0403401c120002c205080f41c00c01c99000c190545200815040c0b5a02000d00600c3c0300503c039110810350546500c8030300f070700c200c51041c250801d5107507641c50302081c425061480c80a040d66291481a00c0901442011590089031050745030103581d22100914021010391130350f900c103c4500d20500036044492050300c0c65603910810000b00181030301070500040c2071002c42e440c190380704448050f4003a0003103800050000303083c10008070700b01e0380c03105426040320310175a1a182291 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 168847535 1250 168846285 168846313
    0x12020f011104051f090b180312030103060b011706040b0a030212150a060302010f050901020a0b010f0f060c080405010f0207030506090102030f0705340204050a020901110607210f05070f02 82
    0x8413450b410704041040380404001e2107800001030303c80000b417071403900b101d0007100000a082c0180210210402c1c1408001401030100d103225070207004400303080201d0390025400484040b804020b11080c812612004c04400c684c03150044000155405050f503c10644615445612801c400901041200c10003000450b2429580034203012603806848010b1103108940085800c0d03840801254194405e115180300010000e0200f01d000b400c410b0700402001d41030500c640c4004e0704550011042114840108021520044c2100c1c1160f03003d00303266010080015059040041a510280450003920104803240740306400461180044000307408032903890388000d888a000381040284c0d06d812aa0411002c00071703480c1411100360203030b24460f80036540f0743c0c0040c0076a5422180c049116801160407909541c10180c2041c1c0d1800300340c0070304014a8020801040f10020401c1c403405808802c200d10448030725035100c400600741040040c0054900000c02400502000858400600c030341286503201c4 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 168848785 1250 168847535 168847579
    0x1e0901090602070f0b1e07140405030d0905010906030209062713060501090b0304030c0311030c010612120302040506120c09060408010b030607051306080a1112190b0d12020f01110405 80
    0x6a90562010b01068441340707422a280c1c00c5000c0a03400c48d980c01c1101080d82c0d917080003003885505130b80c1e40b2400403034205000103000022076071002040c10300622101c00382e0703611402500e85501036001032018181242405440c8030759a000100d0300100021031041c0134080700d40000d000c1e25000c1c1c03604002e9513a10320024101c0c1c8400c680140c001044982c031200068030a4101d01c01200c0400d088038107211054800c180bc44009a000399288040703503000d24200b00412882c22800c0206003001c600b803a1500c004102c1901c00c0c0407901c645c2480c2100041c08a04440c8140c8030310710000b4201c6034680c0d4407a802e807402040003c83c3c0234800d00c901380006215034030400842e131303000c01d2055003e00541d03e040d105542031325019202c040100d80340c2051650f0340300c010300580422001020420f0090070a20013003444c021095031a150070300d0528068544544400e102d0600304c0d64060100d000813005918201c1c20261103050784506c2d9401c00c1481100182184080c3c01900c104940110311460400e20365103d07 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 168850035 1250 168848785 168848821
    0xf0d2105070308180a140f0709020c120708120109020703021c320f03010f2405070812090601050411090d11010504091407171e0901090602070f0b 64
    0x3d905540061100c078180d14090380c8643c1000c0440f004400c0e01e507030340c070003410102d40b02090560061a403a2003c02c0708110000003008002c0c002c5203000290300f04c03a070303c41d444072541880010740041c0e4102040700d503508075007071840601c00071000384d40c5511280b0040d51100c202600180b082c0d444c06209107000c3e0100c2c0401d01c015441d805d803a48001c00544490032044031003000300c4a024038003102c414403000300030310141404054495482d03041c500320b010100321a406c4036a2440c0700d90251103040c0800780d51401944201d0520945804440c6000b21861040340608011110002c09200c8038420002c1d1050503508212814003441004031840c04007400346a4200b40e12003501c0e0150f0000c200c550480c10305c0f1000616002c0d180c1a20746072a081034031200d49544000460780000c0140300c1d170344101000180c009440c0c030034401c0d007040c03081d2032202507541a0905801c4525404187c10200c00d45c01180650f50006056445400c5803c0544618050190070350b103481e01c903800241902d60100c070000d2 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 168851285 1250 168850035 168850037
    0xb12010e0a020409020c070501020601150203070618062d0e07090b0402190804110114090f012102071e03090b031317090a0e10050f0f0d21050703 64
    0x416840c25054000800015000880040c0c0c2040003040b1062039000400e001640300000b03152507443c11000a00d481c0059100b01440c1007565007103e00b040c0d01001300d4800780d4200001040e52450848604068841d001c03000b4043c3d490402c0b450003046a0400c4050340300c81c11591208100d0014100505075043c000d401051504023071000d004092a40d03120b0b820051010300f0048c14080042c1203086102c000f4160700300400c80d08010402005031900d01c2c482002c0e002e10300f1800d2503d81e415010814028a00481e115034000789921006910604c2c03078041100404180d1481020b8041c400002980241c00544071054110600e11811684d52041c85800782d0655404241c07034075080c0a0720071600042c00701002c0303201d42c04600002c103074000704000c510340210790403e036605440401c0180d501015070104400d50000310070001c0c18140030380d00c07004480c015244400d90801e50f03000140c4000a0140791607111254600010070710001e0b02d050b0b04040140d11000401e100003a10542d690b020703c01c0024 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 168852535 1250 168851285 168851317
    0x80d0e0a050d0b0405071a180103020708071421090a050414130305130303090503060f0f0106050901181e06020105040519150504030206090c0906030c04020c031308030909010b 77
    0x340004007560f1200e80d1084c01a001c1d0352055885000c489045004500b00341c12084001c65850aa45441308007004012801d003000c619144071780c1e490b00b0301030181c01806440000e0458828210a4091107030181c642c1d040080744801e148407603c101c1098020711071140c00f400c0c1c0800d003c01c043c2031500c01d0706683d00d032a203080c1441742d6650440545003054100d0803030801c8004d00040a00040200403000a9486a1900a01213042c41d09051a202e0000c100b4500030031024240301d02290780580d4207064407034500d02203a5807103640f00140c9100600c00038899041014075400034500002030102803448801c40c5660a0080c3d80720012426900c080d01d0241c03080e0000080a99180d2480400c80c22461050201170122128140b0090844030f04a40039005a002003007044480350090103580060001103644540c2400c1440202c0c0d81c1e02580c5002e58012503000403000641102003080d10209401a04090056602c69820580b2078210b0448607029148010021030035641b4a030550704030341c03c419881 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 168853785 1250 168852535 168852559
    0x70e0f010b092d040c0c0209041202010b060301080a140601031703100b1314030a1a0a15030c0503060708090307020d020631120305030403030207031701080d0e0a05 72
    0x1c070420390b0201d0022903101c4901407110940450305400d40d806440c0d0002d2100301d40c030f204401e0000740c54007038070b030b40c420451110084001681e40001003600039030031000c041c0100e503502005900411100b20001e510072404000090b40c62400104206400c3c8505500102c0b42a0384410f26039400302030100074404120454000c81c851031040145602640030404002d50f5036541c148800d0640c00010038207000352684030103203c904044009000309000c140c0c02054124107945500445610005804131759211903408517208083c0e5400032021000741d021b0074a281d43ea2480d222130030b01140d00c11603000317000d502c1c000b41401e8000c103a414030a440b2140614074000081d402c2160358588070b0f00403a4002c80501254030050fa00b280d420005400b0749040021550300d041c0720744400300702c030340c000042100f440d070035040083d0340b040689801030750500300982c41d602c1518080d0f4125148200c0c0305501251000000380b45400060030505078140d5072210340704440301c0811b10018241038042e49407c410110f0709 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 168855035 1250 168853785 168853799
    0x6140403020a0605060f060c0309040605150d0504020d020307080a0b09010501030b04020910080708010b12060c04050d081204080a0f030e0c011110060b040e010806281806020c070e0f01 81
    0x4140c5e0300c044000c0440304101041d400080203a04020760b6403165a1012400320750b10f080038803e14000d041c0c202c404000a1b506100100001c2c410b40041e4040640c985001c54110345460400f07828990f030050645403403546607040c041d82c500c80c50b40c060320441c0711103021480002040c41a18140c942000c1c035450503a90755002d000e8040005880a9400304800c5c0c400180c100003071000d42c0180150b01c00108010387c1000c100190025102c403404400c0c1c10410a10804081c000112021907400344c400d408828580c0c2400f040c14001c0c0440d2031050a0880c0070042002111401071400d810b003a2621208800c3c070000131012210384c00e84c034a00c3e135400344550952540c0a000c00303040004a1404450b103010b800b05d00c200c203a605a9000000a0750041414407400599100c5e042c094404803004210301c0c49d01c075903460030140a070341c5131620341071041041c81d02d91a4036411802d00700c8844004d4915032500b83c07600c0c07002548044141141c5003e001c40111f00d0284c280f4015003e0020b55480115690800c04 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 168856285 1250 168855035 168855041
    0x607030203190206150a0b04090b031e0c18061e0402040f030c05010206012111010e180108012712180e01030605010501050307051806091c06140403020a06 68
    0x40640651005202c803a20040001c02c0c1001c030801c01ea4003803d403906080a031488681c211100031841051a000d050141c0c51642007030300c049a2a406000c11410310700c00100b4140001c034968141d003140c43d0b11960224082c0012030b40c0d0b00300c405560104c4090405000440c0340c90040d5150ba034440150130300881003078090b0200c02c2c10074400420061905036034002c14469000d4540c02207030841040303031003048030390707014080180148844203a4001041008001c4458500300c100010903c801601ca60445030f4405c00000802d03d0020781441401c412040214090740404d1242000d59800c081c42c5203664200d03290320184406407d980490710455581c0c442c200c0003100c1c0e030018100680c240403000460401c0101c44005c042a1250040c19411401c2407c150b88058200505001c0c0800034000000e6204c0101d030001e034003070160804600381010020f8120b1055a06440d400001020b00380b51424070f001c010000303e84900c80812100d1030500b91518000c0044034080d01580081c601c040100f07480c0e0b0 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 168857535 1250 168856285 168856297
    0x50d0f020a0b07030c290403050f0d0212060451030f2f042a03230708010b0a0504090c090311090108030f090a1701140a051506 56
    0x41192007101e40340c402d5240c071604808419800520700d40c0100044c0711003640055440c5080104480e0040038464800c010107001a000404102c070004440c1000d24080f005d45014810008040d966003242e00c00768a20000c06541c241d21072450404402e580c0006030f40a01000c0901c1c4e000640c03000d0500751249250042880d11000c3c421103c03d418014031851403110780510310032006050b01c83d07a10305000c11456010003804003d078007640109182c10708104080603821008640104030b0103010301d82d0341c403100749200c0c1c0d4840d4421840500c08656800d17801441e059402100f148412408000740b1144c1d01b03a080e510040411242e000600c00031000000074283c1440605055161682e1011020102c0310000500c1e4001400c4072400c2c81009581d5041d07031403a00088030303200007a50400e6212a10391160031010300000000045800c541d80390002c601d001060100d0f50389140c0c03406a64903501802400107906481210301000502c0c0e02d10b5031040c41d0249003201411091a4081d1f0309012043d4044 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 168858785 1250 168857535 168857539
    0x30d02070b09040f050403031d070303080a0c050d0c08190b0603010512190c14040903020d1b050f010606030e0303090a030804170310030506130807020415030b0906070810050d0f02 79
    0x40d144d104004540d030042c180154441d5400244400310f00c01c42d020603120101089100e0342007204100301099100002d29044404070700b0000d0140c5800d40d0036280c51040c4090000d12a041c802c0301501030b0b4000c85840d2084c20900c0b2240c82e8580090700500460b2907159110b80d10000c184014132050a1400360071000c4841d81c0100c03042914083c984508045001c08105c0d20403400c01e105203c0c412504901e0100c00034240c9003400342c41100d0340c0194960b43c04079051410850a07071024a00c1c00d40100d1101e05164120b010717940380c3d00340c42c1d1a59002e44001c0c0184000700f41450313200000500c00208880c800c14120024044055003a90129032090b0040e10503100002d1500e50303600741d12099001103004a036042c4000e46284c0c510b240190400c50024a00e014241c076184c14580031408500440d01c21a60440e400a516081d07064101070056080c0c00250602468000300a00e0441c0020028000d0406449640440c1c1d0b885a1045180244d4002d0b80c0d04984035903101c00003e841707905408095840 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 168860035 1250 168858785 168858791
    0xb130203031c06050a0b0301030201021b19090f060512060a0e1216050c09010f1406220608090d0c031b050f0a0b0a0b060403020120070905070e030d02070b0904 70
    0xb585902001d4410220b030100156684010001854100a030700024450a0300aa066615540010f926410039100c01c50002d00a000940a0360b51150200c400840c6103440130340d126500c1e01540d4004016119660600600d000c81c0824a4035210210f074101e0a00c0000601c0d4940c4c0c0c1408103005481340c03001d623040c05d00c289429820070740c0c4064007419040249501c002d001c29031a080c114907101c800b030b888a010303200e480c0050201502291504044d90030601e8200e941807000d402180e641e05c580e45001180011100301000100500502c20080f500d00703a4840040d41c0f5a1000c0c144c072042c007100d564003c81e101412a400280c015480a68004400100004a440305032115801c001081c00030800e69001001008104080034800726003105480c001040071904100c0891814480ca000c0a8144650070782c601c2d6040b25044030b407810000000091341c01c5a540da4816070050070058070b81002181a04801c60072908001030791210b041e680d0f074002d2464503c1e059100a080e0f108440741900161 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 168861285 1250 168860035 168860047
    0x51b07031202040906030b160801050a1401020709020d050103020312040509062b0602030106020d1d09100306020c0604020a14092403030f030106030c050703080606030c0c1609050703090b13020303 86
    0x12091003002c0045002c0c032400d006034035108c0c50a424880c1060400c50074061084e005000c2ca803158510304098483d1030b011811020100c00040c2e142030056804000401c0c00010300d80c1200c2c1e030b03075040305040328030075001c0380c1124458050780c00c094000d81c05250b800920900001c0d0b1280b030540254110144035806085503c42c4007880c0002a0510321020390312240c00000401000e81e04109410f2191850310300002d0382ca855000700802c0c010400100380c440c00c0d008001ca101000d944498600035a031081c400c5544a04030443d9a032203580440f03080c0c2c4281650000044e00f05a0a142c0b1140020000e00211171030342c0b10441c260754082c030340d0b2201504e00d0200b21030301e0b0242c40800040004403261362003542c40398134100c0014140c41581820108000c0241306850000e45c001280c96081001100c040b0380740d946000300e014907800780f9010400d6511070f001049004600300e0304d1510030f0307a480700003e012075030703803241d0560685046a00041001605100217042005101802c69440f44018162441d0030 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 168862535 1250 168861285 168861299
    0x2070f0b04060b0a080a0804090207061104120b01050604030b0f0411030d020a06050903093312040203010506120c011115010608160f21090204060803070204051b0703120204 76
    0xd2003110100c03001c5540c0c91040400c2d1400e010540d004108140080a04d51050364424103507001b0b92283c808150f03000b040303044c01c11074035800054401c4081c13175030142c607541e5604100c0000365141900795280e08076200085800d00f005c0302210283c03604008035008a80380c64940c00740d0403900070700c10b4440d4807954406941da681c050041e40181c1499a00a1082642a041410440f02d006d00070f02215803080040d0041c58480d03000c2a1a10444a4003080146403540104c00085034510200085043c002603201031500e452091203018138001e0b40208901da030707183c060040300b81c1107518010203548881d031400c40d05d600c04c0340400c202c00112030030b60728034038004904181000801c1c0c11007000326464600300800d102d6031216204000303126281c8101000c1140c400504000801a506000c6c070f603042c001e0b081d143d9020740102054940c050010050030b40e4403652aa1203400c00e1000b244170707908120114101094408400c00c0c0942e00710821031510340b05950980f0302d0300d030791030340141c0c05038013071100007180 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 168863785 1250 168862535 168862553
    0x10f02031009060f030f030503040309080a080d0b0d080f070203011e05043008060f030d0809010c02071a07020d060509030703081e07050a091809030e030a0807020402070f 75
    0x1e044884404000e260038210078006603101d6401c135900700d2035021420008102c144111a04098160820551380e46031401c003191103040c2070300060724521482c064481046070070001403a45a00083c801c100000e0b05801b00280780c0050900503003600b0041c407500e542000ca200040181c203200400000d0340410f09181030860100c42c0041c2410f160755041000284094040320303244641d03004099034022501542c640300120425030400042141040000344140c84a00702c5506421000f0100c0e402c1c000340080040c08510225a00303040c55003012002ca2066000290b05003d980d03283d00503030010721000702e40c0b20072030f00701c803a050740e100000f2000303440407411a129150040c40800051565000c05041c003070300e8858003800491011128210f883c6175500030200140d000540b03441c0041d075034800414119900d011681092500b01010850001c020100354000c4600c00d1107602c4407610a4101401c26460780701c0984060410725042220400610b040d03401800c846220355010808014552140703050303 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 168865035 1250 168863785 168863791
    0xc04090e0a030e010c0b04080f040305030c0105010f05030c060d0b0f060406020715050412030c02041e0501050a0f0f0e062106070809031e160f050706030c08100611010f0203 76
    0x1040d00706a01900a055020034648901d800a0801c0710300a0380f999218106804014400f40c610200880e584402c080750400301d400550b0010b045940740c001040049009140c20300c104144400e0b01e0358009860304000c2450203203a00000c0c01e4900f0600d91401901c082e240c0f44549030b83c040a02c0c891801543d80c1d0b40c0103030026268030390080441e40d08000c12082400da10604650500000740020840201c40080e40c104440c0d1603c0d01000c881c0d840d1001c10050705803080c00039403040c0313909030100c000411544094103d80d07044503514480b550744c0040d1000099079025010300300148200a000030381021038483d401030360180c40c5510100400c1c1d0302d600c4d1042c4886101035607811480900c03803041ea201c501d0641103030b48080910f01d070034034500250300061610601002c1d480c00c003007100300400411141e82c042c81500221880c0c07904071903140054949542c0c2c0075000100b41b43c41e0132221480d208040b003500c214040440c114440741400e005844041c084409405039648074501031030104441d001540c0 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 168866285 1250 168865035 168865061
    0x2130f06020f12031006030b0310060b09010e100903030807020c0d0605090609150115030902100c05150f0601050304021306080105010603110f03010b030c07062a030917030c0409 78
    0x403019a22403215410038080c03c010030316040c3e003070080c0310107151030840d03a0046500606001804103842c10200b410400d084030300038140c5141401c0000e45116080042c41071400c00d90304d5003c0d0f4959035040159030f95035840c0c1180098100c04003807000a0183c00160b400c2200d50044420540c070b80c9000070300c03112034580220348460304c80e000c0c8070412070300f0400030740c110342c01c54040c10030216240c1d000090600c0500c1079041c800303030f0310303100900031070280e44442111500074280c0d200d079a108400180603103c0658007118203101e2100e00b59281c250f410052400b80100c0c440c200600c0e11110b004540c16040500160b0344154030300e03803c020302d0881b8072500b4001c040d09000030403190707d4404082c00b01e0382d0040042940c00c008000d00c0c0289920442201d040d601001425500c0b0344070190310040c503001d002d00040c580d500d0b11514400700141c3d040140e5420004603e58195030346d10050803401c2c3e50750403000502e000205016440000c1c00d9802440d030244259001605140d03880c440d00b000d80d00340d0601c640c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 168867535 1250 168866285 168866293
    0x204031515271407141b07030b0106080606180907031805010915020406020309040f151d060d02090601200d050903062203030902010306050a090e0f0705060d02130f0602 74
    0x44208102c03400381c40200b403940541c510040c6061400a0907015200700c0440340c0100000c1d5a00103800070b0140081e038180b0b044216032140ea103a10700351120342000c3c0603540c00302d111100000d000d4038011003100c0003041003500320852000c044081c0f0034554405030900c0141501e541429051480319210802c03154041c40020450604505048100c0300f43c84441c580301d5801000240034007a00041100e07580d040503100000e10911902c2008018041c20b0481c45034140e002000150240d0500300d603804042c251141c411a07a00c3e40420400c0310004000000d41100014001a2556018204550134000740246810000400d82802c0741080011f034000ca000c035002107103d034000d041c1040841e5009120010303580d0710807180b4200d601c181c4a04031004080503281c000394011a40729070801001454080c1a400c14a5180c03145000a0710056000c0820b501c95100c00c1b180c034a1000607800704990b03010b8996403401c04801030810203584400200c00d4006c1e111000002e0001c4001203040003032207164050 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 168868785 1250 168867535 168867599
    0x50c04110a08220f2315040c030b010609091a011e0c050f0102070b06040606020601051c050115180b15070804030503070503030f010e04030206070c05011404110a090204031515 77
    0x40c00007029171503421703049003100c46842400c2040c00104000445040441d84101e41d0755031a1070030301509541c00061200f03011320000034089030840100c00948800c1d500c1881019541100007110680700d100440c005a40610074500d0f501000e4000350111400c0e24103032040c28a551201480d0010b0b26084184982d0f002508034240300e82c201d612500203904650a01c0111b03c1c05030000e6480ca01809102c2c0f1400000760004030264402822207415607101c07000b8414810503044901418815102d460030f40342054503025014040ca1240102c400d40083c143c24840b500c480503000a5000000d04940782c141c10000400800c6040000d01142481b50000b0b565030701c1e051a200d0440c12040c0e0042c40913441c08810b02c00080d801082c655807090750362500d00408401410581d016219110101101c0c02a00052100384081700500a407a20015640030701103aaa0304804001c0b441684406000c02c81080f400980390200342d0000442c0a101032000104503464035502e00d00e07244001051300c000c828142c41c07 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 168870035 1250 168868785 168868793
    0x1006060f0905010801080703080313140a030f05030906011505130e07031d1b280609170703080a05190e090a0902180603010e07080703050c04110a08220f 67
    0x70703440c00742000b842e085056515040040e90396a80750b0100a2081d04040002803409100c403200f0b40c009500080844000e40780885007030786804d41c1d8039068000503000c221491109011b4012a40100019001000d2903840d12204101060a61010400704071041010030305401c1d0810307200c00a8030094461094504081c0c0d000303000c03a00e42a03000c034102c040b03258480c0b940100105508a40603044240c0c01191020500020540317101c05241e20f040444208182e880010f0b2000ba840c190341e841d840e50f0803c3c644421000a86580d60042a040390348084404e00001d10000081d00500183d03041140c142000102c07465003644641c50540c0c0001c105c0c030340039915851300452982d08550b1075042004181da0a801088962031009035040809451001144080c2c509510401c1810a0a001ea48250f40ca071210720b51260354500c01500c4a00c20200800b2440c9030610071040c6650003151440d02c0e24051820039640094010b000d81c00442c2c841c041c2d0400703a08150740150543d846080e0301000c4d0081498 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 168871285 1250 168870035 168870047
    0x303020d0b040902060f09010c06060602030c100203161808010e030c1605060d02090307030c1d060301060f03030c060b03030a0507030f0905010806220c11060106140301171006060f 79
    0x5071003841941466140400f41c1c0301d020868641110700d240480e0b8a0b0034400068032031a42d0301100030007251908900250203540071010b031400403042c9049d0761064000f4803409090703001c10340781e44290b0349090085070726444c040d03020310028480b03a024140302c20340e4500b21142141d69101c4809050f410014803013581e2001440bc90b0600010038075018040c41c10200480c1c1c031401400c42c1c9043c0203600062014041c1c0d01000094011944201900030729612400c1c202000344140d001141c11035281c201052883c50180542c0c810740303c001c15402c4910389181c070201c520300d08109090310200d40da901189080e442c02c0c0018115508143c88140ea1041103185c01070041805000900810803404d03c00d00c06030b81c0c03040f060780d00f0410842e20700080c00070b003152409480b504074088941851500000074170107a04000c006c02c0717880080095548030783c0c0e1844182d171203c0e00304500522247c0c04000500204071210340e03071f030b45641c1c0c00e004580fa50144442e0581c22682d10b900880045000305c807001d81116030000c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 168872535 1250 168871285 168871301
    0x30905010906050618070e06070201021e0304061d101b0606060e090106030b030a1104240e01051804060504110306100801062907080f030109050f011203021b1306030303020d 76
    0x55421485c0800004001c7d03100b8202c3c0c103100d5040010701800350f80c0b0802126200541c040c1c00404001e04040026503242e000d0b00ca044081080405072010400d280b05441c6c14444000d0914000c02c400d48174210340b0f500c0c940050780300700300c401c54404011821520070740d8090041c03510b80c000c003444550304000c618841680004201820001e10036010384001c20b0000a02c1d60143c005622180d0800001d0060324140074094180c040001d2103006002d4480030880889590b0300901c08140d889000b440b42d20b120101c403d070300706514180071400044035948119031250150000000307036a17010380041c1c1812030944500a054800d5981404102401e11a0000400c44c401c0c5044c1441410000d42d10309840c600c611525042d00422008140480081207440c4500300c0110260740e50703100e80395a8000c00c1c040c0c13040824054a10004926084c20091092807150035800800a03c0340b10a42103048030031042d81e494002d102100d0b81d0b4180e0740c4900440000e10b109480150700c500e441850035040352000 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 168873785 1250 168872535 168872569
    0x31107050f120c0a0b070504170307021f0c030809070b030f090105010e0702070506180303280302180603060f060c010c0e06071a4b160c02010309050109060506 70
    0x10840407520f00800159543c0855110002c82640d9452000036626402181d1158501c42c2c0d03250074559200d08044003c0c00102d20888603203444030402c0541000c1344101e00c083e000445e4140c6442c1c1d01081c0210f031042d44c09813661007111801c0d42c0741d51114003140c005540b000146203801c000e10140500078081d15001d00100002c06041b450001002903a4091038460a03000b5038001546400ed20070400b1b00035200c4502608503690742c0301d03841e2041c040029424104062071a20300c0420310b80d42c400e0080700c42442d003216141c10a900d40300100065503101a118660214520f0f03d0310384c0320780b83d0340e01500031009210b00024140440c0200078105c503030741d6500d1601c43e180800814002030116480003000c0300381002c02c903c036a0388410383ca10700031115945070402c0d000340e144044010b034003407a50026520244114441450044100c120903107800751049441c02c00442c1490340690b10a8450904041c01490301240c05081c50b00c445086a25007002603401c2501e902c20801c01e81070800d407141440d441 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 168875035 1250 168873785 168873787
    0x60c08090d0e060702010c020405040f020111010b01020c1e04060b0d060608060603130302070806012903060117060f19050108010501020a05060a09030e0402121909081603031107050f12 81
    0x301c1008152044401d0344a118000210381602564490f402c2c3e050100c0d809070040200341400e08088075000101001240052081c4080e218018418041c6404010040e002800e9915a510400041c0500c5401d42c0c4900c500b010103180b800d5686002e182c000f0202c2e00880e550b82c0713165800110070740700c20b500700034240310030711007800065161601100c0d4041041d080701080410a440c00324186000ca6014880c584210303000400c03242840100001e082c072600300080007010358142c00c02e9803800708440e01c5000c03545000a40d5020061111143d50040000706010701710214140050700d0790b6a0303c0ca00c6021100402414030055030800d462602418090004008848480c0d03141c540c0d541d401090402810b0312900820300305401140b83d124020300c0200250b4079500d8281150072103500071140380c03240200c1c181030301c9005144e600c1290441508411400e1510700302c0c41c1c4900c0302100240040341007641d218070507449014000080d2003202c0c410f001810303100b5030f010100d41c5040110101c28940c1d00c0 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 168876285 1250 168875035 168875053
    0x32004030206120a06030f0809010306061b12121109031002130b0d020f070f03230a0806031c09031b0e01030f030e1c05060109020f03061c050703060c0809 68
    0x107194000d4415407803e8410001a6603a4615810050728032136000070001142e90411030304104032140a410700c2c880031790b010840c00c0c0d5a0300089440b14130601c604174a05182610520109900d80450590042a030900c02c10901900500008a0b0725018030344000b80404600e07a0380300c1c5024019080c0c03c0107003200560070404400000c0b1005490b9200e10704080c0c2001031503880c0802250161124042032013052a2a43e001e1b050414001c000a401100002c4004080742c0b44d80000c04540020980400240c43c14110703441d0060307c41c04070203016164940b041c41c003010409030040803030b015400d500742d40300c4480b51b00e5440d0070784400d60380e0804440c0c411400c1c0800c1c000b621400e8103690440390400c146050303c00050900703840c00410080c0042d0040764200c5160348080f500241018103e100b482120010780e80d0340c0700d14049014407041d21a040c001000441e202e2b1601e42c1180103031290400750500c40c03e03a16601c0300e1501105034401c0b11100e8a80710304d4034203607030404802c5520030702031005030503414 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 168877535 1250 168876285 168876289
    0x60f02010e0715120b060a03020403060b0a0806060112090c06090f08030306150d1d07180510060f1b0c06030e03071101030c09080102030c040504110c06010b16060c0320040302 77
    0x2079851109101046690708521000a010b178002e40d50302070300a00f51543d12075540c44011b0196019000681e8980c1c2808544112401e160411800303c403100c00152155403648001107806418a80c60081e101c5d40b159240d0000c54007030306100300146903d03142d5103603052500700103a900324019800308480360003e00400c02292034096040c0c0903011100340d003550300d042c0031f0318020007800d9003410600392103902c00c800c1c901c2c038030001081c00517101c010b41010f103000c074503807000340a946c4119100c01540b01c0c460020003205002c0c01d07000003002490304110a440c003501400c0c0c110b10b4240300d002c0e51117408942003000429014400e8009651000000e0b524002082e02c60740a80700c10000342904140d41c03260280f050301c2c03150004002800000000355906d080140804201e9005805454071503494140b254041c03a0039202111071804848000c0d1109a203400c40710545500425501c40c01000b950741710348005403d41c41180c511074295180040c0d2440403a0a68440c228007910720040803004020600141e = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 168878785 1250 168877535 168877559
    0x610030803060d0305120a0f180201090b0705011b0e0a0b03091518010617100b130513020418124805031804090b0c0a031401060f02010e07 61
    0x1080c0141c840f112001903903d8203d0780d038499200305150002c03090080c0710071400301c0d070041105142101000e002c01c4010423101c81d0000b0707800300024003080210b0400c000c0454150301030700b04680100000030b0049001128030f500086421a2030380060701041100d0814a86011104e0140c400080f0150540c54645e05140d43e030700e40101b4200c4696803000000b2141030000d820f00d11807481140c020b010807656000f40b4920011801840411801181e07040b0304010700521403685401402461118540700404c8010020704028141e492140d0444040b000580c41390b01131000301034000c0c26400e2080b901030401a001e01c0c841140349081000448244d03a000f140c0c0c00301c405903e00d1f102d01d52742500300116140e1000e20b4410051010484004407200d05101001c4080c202c400c0341003000c00b001d190a1020842151141000140715070860004100580b840102402982d55030341000541406001403280311440300368814000034640200d00034030964280200307008055500020310683e810844e0300500 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 168880035 1250 168878785 168878791
    0x180307030806120109051c12090f03050a050706060e07030b0414070e120601080609061303050a050d02120a020d0c0e030c24030c040f1410031a03100209030610030803 73
    0x403c07295264450341040007944409103040d80072049411041d01825140003800345400302c4070124444490101c0714010314000c0e5402d00354020360b0a4007400d0607960030b803100d4002d00c1903002080024031800e800201c1034428100503051800d00843c16107055400102070300d4001802c0d5000fa410000000160f050080c20340d500444a400d0051000036940c1c04070700c10262008502035140b15030800000c1d030070008541c0500401a01007624007a91340c4180200e0300d1a1900402400603804000c0b074411507200b44098140c211243c0d102514100040c0c02d00100380000b594080c10035540041d1250107a001b0b0300ca100711414050034407070708004921000a4403000780e00c078280e01a1001f00d02042c80009104004145e21403003148054803818080d42c0c803801038000307009001040c800440c010500e102006040345417054000c0c0711101d80d085e0464200c01038000c0707a11040009a00422903102558241301e15900050150340040c0c9402030403042601e08178002c1d051141e10aa29001403020601001c12a58 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 168881285 1250 168880035 168880039
    0x150402060d0207062c0303010602030711010306030210080a0b04062108120a061d0c0a110316110f090c0307081e070509030709020901020c0d05070f030b180307030806 73
    0x3444a0014802070041c0c8609000189011724004041c0c0c1481c4664000c1610a41c4290700008202c0d40307041066074a10080c051180540e0060040a000a40c48e03209041d00726818500800d5460f526804110440d0b128203601c80800c42d01c2d0100720408050b03110318813500000312414048140742414400420b94414200350030039040403211424800b1800440c0c80c10b86034014605450710b0320300062001007040707008007213624028619800401150409a03405021030101403813911410340404c4e04d55102119084015010038001d48402108650891503414018240e90101e406003408120769030040b000350910540441007031203d070650380000d0742d030701c102ca5081c080e40700c1c0c070b40345e03101420600361010316043d4400ca4010001030303036880006444954001c7d001c890515840d080d62101b640500d0070814010f900c404074500480c03614902d00160079002d5400d40c5e10440e1603c20b0400c100149800035521428a401841205807580000705207076030786107000e58103101440e90020428000035180c58 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 168882535 1250 168881285 168881287
    0xf020d08010b160614090a11040b1c050c040608030a09080a0b011503140703140f040201020c130204080714120102040506030105010804150518010b041808030403140d060e060315040206 81
    0x8020448a0b62019501c4407150090740114640801280d5581f0418541203812201e004140d01142c105402104c00306200200303400c1008070040d2070240c0142514000355140d00c50100340c42d10340c3d2101e2250350082d18a074005580c0e6a08034050107850920660b11004d00383d448488000007003080d426000e4151801d0b44070754180580c985100300c01825491107030020f101d0b40c0105102101703030541e0000d804850b40b00500140713a44c2d10070320ba410200e01200c02038056040004580101e02e81121003070307070101c0c00940c0141050b440340903141c500311103030300700300c9015150f5400e8031100d1420320300091274445940000d500c2c00741000082466804123100f41418007805c50046010403035071000302003280304a12020815850f10881c00c034240403000d000100c40c2d520303080866801e81001e00803054001103003095103080048030ba039400b00613030000b1b02c1a01000503041040100c40000c8004050400307002c14085a2141048262206914080d001c0d9100f0b62040440350074004500c00050380c00340d01202d00c0c03 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 168883785 1250 168882535 168882577
    0xe121303120504150905012604060209031504051b03030403030e0d031101150504050a0c020c06070804080703080703031103090a060f021e0301080105060a081b1c030f020d08010b 78
    0x6031107500403604035901c603044482c148203104e503002d002d4400700d810980c1c0d202003c3c01200e40d15070ba440e826038400782d07819110780000b5000c940250014885400b01608540300c4207030049140400500950b4225800c2c0c1140300405d0b06259031030034461040d0070480c041e40c5841d28659000d00f60b41010b4210f240619109500d441c2410701401000070351106200080c48014000b00e8800817801c082e00400d0304c00c0d40791101140f40d91580744102c85a8121540081c12401114020032078181c10201003200d00c550204800b051844c0c0c140440d400a41c802e0752201d072200a07901d0050103980c1c0c00407410b00528410b0080001035000003c01d0811140c200d840013450894440b4850081d10686e00d0241c0114a80524001c20b1550328004504039508500204855203520741081903000030751003034820540c0310348002602c014900500001c3d2202c0280341c1e500300c08420070452f100c0300280000350041660718101c1c402c0c040e01404444c5a043d17140c034000c0070560600c03000c80258060400220f010045800007 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 168884892 1107 168883785 168883787
    0x2121902090a030320010e100e0303160c170c070609091103010506030a0603061d100605060d09050114090c010f020c0f060c0a150e12130312 62
    0x18900b8440e2a588088551010b20101100a01c240703645004031610240300f01d6441017a000003903c0300e039606145003030031100803201c01e000c1900100100110010100440502c221050414003040049420302c1840c00b01c00c046415800240020243d4003a0130010f0484c088a1140c0e4441090079143c5407454107030385081002c45c010040c01d00040c03003140b512001a6601510007180040d006580352151421b88404070040724050070401043c00400c0818003080c002021229400d2110528007004180e152084810348441e8940d5602d401d41040001c2d08034088030a02c018015556007003602003940c41d0b1541111013404291001448110300740007040c0032800f0700e8014440c000d0f03842035209006081d0310804030000d1a0041412103070002d0310505451641a86480002a56074038412000746800000700c84690101e4003400300000040c019040c103401e49034440034280d908569444 = true := by decide +kernel

theorem cover : BRFrame.Cov 168705035 168884892 := by
  have h0 := BRFrame.cov_init 168705035
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168705035 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168705035 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168705035 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168705035 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168705035 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168705035 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168705035 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168705035 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168705035 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168705035 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168705035 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168705035 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168705035 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168705035 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168705035 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168705035 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168705035 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168705035 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168705035 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168705035 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168705035 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168705035 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168705035 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168705035 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168705035 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168705035 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168705035 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168705035 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168705035 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168705035 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168705035 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168705035 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168705035 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168705035 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168705035 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168705035 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168705035 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168705035 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168705035 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168705035 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168705035 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168705035 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168705035 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168705035 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168705035 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168705035 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168705035 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168705035 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168705035 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168705035 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168705035 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168705035 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168705035 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168705035 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168705035 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168705035 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168705035 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168705035 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168705035 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168705035 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168705035 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168705035 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168705035 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168705035 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168705035 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168705035 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168705035 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168705035 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168705035 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168705035 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168705035 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168705035 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168705035 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168705035 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168705035 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168705035 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168705035 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168705035 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168705035 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168705035 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168705035 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168705035 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168705035 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168705035 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168705035 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168705035 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168705035 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168705035 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168705035 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168705035 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168705035 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168705035 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168705035 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168705035 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168705035 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168705035 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168705035 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168705035 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168705035 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168705035 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168705035 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168705035 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168705035 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168705035 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168705035 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168705035 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168705035 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168705035 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168705035 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168705035 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168705035 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168705035 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168705035 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168705035 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168705035 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168705035 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168705035 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168705035 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168705035 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168705035 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168705035 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168705035 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168705035 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168705035 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168705035 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168705035 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168705035 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168705035 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168705035 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168705035 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168705035 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168705035 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168705035 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168705035 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168705035 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168705035 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168705035 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168705035 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168705035 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168705035 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168705035 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168705035 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168705035 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168705035 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 168705035 ≤ n) (h2 : n < 168884892) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
