-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2060
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:34:07.264982+00:00
-- url     : https://prove2.me/submissions/0be2571b-2fbb-4af7-b6a8-34830a47d948

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 370323741 ≤ n < 370503597 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 370324991 1250 370323741 370323757
    0x504060f11191812051c1e0e0303220f12260906190305060a0303090b0307020f15041703070507200607140d0c05060708040c031202010c17060d06050c 66
    0x10f4401913030000380600061040003003500801a0400001c44c40012980c5211040104400508203e0040c0c0030302d11603240301d8014000101981c0c600b900002d40040c2d0710100c6852210100c0e1003010412240510340700c444010042d042c03002180510941c0c40300390f00040b040c45850310203203000c6420101516281034528100001c0c0c2500c0e91406c0c5c01820f0684042e00340841d0001a040034005030746420041000c40440c0d5241d202d1098107410411615000d800c020208011031041d441c2d1915403460070041c0440600c0c802c0b117045d105003014140403110752500c0c016122201d8082044c492826808012104001e03041085400c0314075159020044030341d030451041d540644040b40d000107121600d802c0b80f009030380d44021a23138400807507241680c0030340d80c821015005820480025102b2409496001c0d482841040318005590309e903651404107900b06444040141c0d580c00b82113042541000c101031280b030210340106180e20b450000038011812400c00284200e8903600400c00031002481910502c03 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 370326241 1250 370324991 370325009
    0x18021e0d1b1701150906050f130f181403090114070309030b2403010603020901050d1106030a020a08060a0302090a0905010b120f100b1e030c040504060f111918 70
    0x40c4030030441a60282800804e40d550443c00b110000079540f4841c0f003010100e40f009007520140c074240904118071000c2d0802c580f060240c6840c003d0031040c0d440e1240e89100640b0500407051224241094850001401e42940e5071350f1080280402c1a030b00200a040e0f000e40b070b00825a034601e4285000c80f208082c0c0d0344003c021000310300038040000e042c51100385142524410400c5c1800344e03481014240c400501c4040d4004a587d00180074a00b0164403620f115170003048500003903210a004100d09030700c11601d4200b50713a400710328112500c1d400755055411940441e075001c1005d0035600080c0c2d0401010300401c5066940c1d00c1c142007000400e4110420006d00104216400580650f1503500c40c40c100741e0540480c05100c440d003a003c00c071171045068520014004403400c5007280812042c40a4850906501d8868103c0320032107541c1d24001d803481548200404a0140c030380e03800392b10130b9444440317100b080f412041c4140c0c0840402c0c1251220a61154030300303813181d998045002411007030940c12441403 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 370327491 1250 370326241 370326269
    0x1206040b060321040501050f0f041409010512101d070312020601080601140d02041b03200703020307081303080a02060702100203061f090918021e0d1b 66
    0x40c0816208030910449055058072003c007140d422456598600c940020010340e0b00b48801c1c40ba9510400103412450f4900303080c03e00e0f0594005003180150030903444140c3d4032030000b03150f16003030034800341d06401088151030710344d05030343e800b10101e0315100e0680a0864907039550343c100f642c90f414008107280d6070390741405460075903031282400c8460300d690008180161003054000252200c0004646048401000002a2210080080003d009402d19040c3d90094031402c1201c403080c0110100c0003d20949d440008821909800c10310309101d420243e01600c4009001b1440865004822907100981c00b40001e5603490852000e85408082ca40002e805d040c400300f0381002c00383d00010107600940540e000c860700381d91511043d0090b4407044400a13002902620350b4443d041080c400405031070b1040c20140519a1140c60107421195850012240127021000850035803c1500390100c1e1680070104d0544860300801c0461074560032000000c0601e40003001c0152070001c3c500c00790000c0c0030711880c074a030 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 370328741 1250 370327491 370327493
    0x9051b010320040e0603190312021b0c03010c02030a0917012309060105090402010c0213110a0c060b030303130b07050906030c373e10020c03030a0b120604 68
    0x10035400c603009141c1350408400203d405850b0002d2410350400c031f215902680c4000680e030845860201450764100703690280f010002c10b907008842207a600c0705640060400c0561300c0101400e50f0600e40404d000c1d074008002c200610f980c000e005005947c0b6030b188082d080ca140014690061407151002c64112030030300c0e00ea01100240d240741901941242c4c8c01c6a24990325202000480b010641300203005c50508802c500040c01c01c421540c0c0b544805190008000305010703401c05c9151300c940114000200700b0515041001442d1041c00d041580590043d0300714649111190014611100f0240200c411000059011886070003256a0a0741c0a0592926801c3c100c1088100d9040000e030000c0c240714041483e039421860461000b500078100d01c1120b4a20a50801a995200e03d02d01c001209481200060511031004000421001020301940c64910107032003414240041c401c820f18445004100590740c000b40041640c0e04000541000180348442d6000031300e45400c0403804510b240a6901040 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 370329991 1250 370328741 370328801
    0x20a08010f020720060d0903051e0a030c020303160c0c092a020120030901060515180307030507050103180605100f1a040e040c0308180a0909051b0103 66
    0x424030611a03000c00d12002c41c4c04851940802000341259041942400f00909401841e0050708825000742051803404003601d011b202c111500e1103004140d00d000150214045034507119803034101c1a648051410f50411036000740c0780c7e81d1912202e40130402c254690506000780c0c42541001000c0c00e00c002c211207484800459511a111100c100c070585110840303010641c0180510094078440d8106d80d0b070204503a1543d0742d056040909440e4042d903960030f0100f6035488036024902d5564000300c1082c1c865002d41c070141c580364803160403a80a80c005a000b040000d0000594405844003400d0105002d407407074035402004810200f01411090806d001e0100b141e0b841040041565202e030700d0540e000b901c6822030f1021280240040e0b001c800304200c10055680b81102881c0c01c24800c005482816a898503100c0960300403844144816140000c0d1200300d02d48150000c0060003100c1003406004029101c007130326400c2442007000350f40740c4040250100c0e8400d0b404601001c200010715041d03000c8404850b = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 370331241 1250 370329991 370329997
    0x102030f0a1d010314061513060e040b01180603090503120106180b0f12090a0f03050a0e0904080406030b0f10030e10020328110d0e060f010e06010c020a08010f02 71
    0x1032a404496288501182d4480e02807100e24401c581720803002d40c1c603284140038502c02d04401e0307844a514244038092900e40350f08140d40042810f0380e50700d444c5610030000c202c01ca03901e400707076141405880081e407201602d800710008202c0d5410f04000030341003004d003485811031040e01d805000d0249a000041070f19900217591040c3c9100990550b0045034a4104d091007920402d5406004a2000d00c800c1038401c0c4440203849c0e12202031400d513000840503545d440c14004508030220040380c0041221a589588400b080c07906d294203da4181e40d03801c1644400b2428404d07030182c0e004140d110f03000740003107841c1d00880301d0034010003401aa1003001030690050003407259024150342070055050404440100d4020b0700e0084842d1480e9510012110051141c075412440780c515200d9152000c182107000391101501d18100b49090200b0390380c08010f0554140382d00203104041400b24440140400305e8010b090075807100084c280040801d805000185038200d05501800240d820907c10607104800313034000d = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 370332491 1250 370331241 370331267
    0x406050901060b030117030d0f0209030610060f0f020a05060f01060f1805010c02180c030a0b0102060412030e07050607080a031b0e09130503120105090606040e01050904020102030f0a 80
    0x1001540c40d203a10150aa0b80ea42c410340c190320700c00b40018170201074083c140118003201c610803686050114650b11061b114900302040e419580410100700e2418144005030384503028004015003a1308005000d0003612603000300e0070401c03245c034002110f030034000c02c100ca0001e40c000003107a842c3d241246080bc6809800d000c1e01001030350340311007004c00c02d0203413400a00d80c00c0364010b140101070a00004640346c1c0e07003000c410303603000c0110f8000c81410000035031158040c072074159100e0794031300d0464040350642d0b0566040c241103600410802010a04480c18040301111700c1c60041580809404290320745101a00840d07446031000900c1d01c02c10401c40018420b46e101524140310003002c08904503555581e00c400ca0000c200d210b009819649004103c0700c0d40400e031003001c118000302c00e864481c5160000500b100a0504030401400580341c01305940d540018203c400c02d00d86030921921018000040c13003818012049039011804580c003d0084d41e429107072441c1441d44941340248000c0a048131452 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 370333741 1250 370332491 370332503
    0x1c0207090605011b1110030e0c0604030809090402150c0c0a0503030408100e2b12061a0c01090f050a0308070507080f090103060308030115030509062710090b04 70
    0xa000200c101160240c1011150141c42d0350071801a80c1210a161030038000701111150503121003440503586089107228404000d40e4005080c03080910340603d841c4150040034445c581c24401000010a91011520094800c0e513150440707072264400301c3c00d0800780d034a00c041c050901143e419050200004c251b001010100c034041c20560740e1f801070586078400c0f40980f81d0150000c02081089885640080340178441c0d0341c048030b0780350311740071341e200401c1c140e125600e400403003108450100e0750b600c803211081004180b0f108001d01485c241c0d12a040042d0300d03191000312540896620700c002030079889080525080404195015118500b05880e504081b200703c0200d404207002c81d030141d01c81d00c180c1d03824030fa0100d9002e240400c1641180b801d90081002c080c1010b40303900000c0009904c10340554001e040600300d41301420903142000c0e0070f8500040c03500710f10782d200390100503028910446c2c000d028605100449000070107110f0190070214040d41105d44142440c078041e0400c030040e01064840d03070180c0 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 370334991 1250 370333741 370333753
    0x10f020f09041b20210a030c09260a0b04080403051203070801031722090f090c030b0c0d09230a02010f050306030106030b15030c010504080d080a0902031c02 69
    0x80010b42c3c042c1000c4120300155080d2a1035403525400c0e01d5041c1010018011680d0700c81d0f0170384c490032080001c840210b00b0b01d04046100c0c0341594141c01240c0585006082544609040407821402e810074802140d22007100b045042201d2030040c07010842458100244c13518a2909062003030712940140300480311403103180d003800c006010a10130b03a8062410391307070380c00e016034615150140c1c290400c07800010150001c015456617080d1400c0d00403029143c40c4603001c800751030101010200e5180142c614170040c1030900c02e10000718244c1001003074a42c881b54140d180c2d00d600e88074030041c0c00341d8000306a80514240f0358005010620380030445100c0d0003150040b41452482c20261110480c02c0c000340401c4026616901150113070000d10b0b81311101030000a4000d41d02e80b94056800b8081c0d40c4500c29844243c2c501a039401c040c0041440b210f428200b0318613051401601a0751000c20955043c108030f814404201d8002454100c05103283e0000c0844025036100c1c081c5d000e0300600da001c404058804e903 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 370336241 1250 370334991 370335011
    0xe22021b0d051c0b0103060b0706140702070e0109020a0e0a0807360f02190315050907020d050a031107030305070e1f030e010e1e151003021002010f020f0904 69
    0x40c030031034406030f043c56540c0d0154860f20460742d0141030903007051818140c6400d400308228000b0005032184502030341004c1004128446c2044101102030400c40c00c6403c1442c0c203100c0642072000d110304403030300b0030b50040e50761100440450ba184000c00f3700755485504e080c00040c0340f138000206c0c41e043d1204401085140c2c061503c6c0b0008061020002e0300c100524071103d0f031380c031500030742c0410008840c440b0007500d41100c419080c015a03d1603445c2c2404a42e64410300755082180c0c254190207010191200c03072103410a29000ba640d101c00510b01010041d001070701040440c825089500300315140c241064458101d071074098007801d4200c0304100010049070ba00300c1a842c05c01c0c0c040c600c2d92500310705861100d00f421812000703004142000c1c1c803030350b40f152807144120204100405180819590005a908854031000d08080381c0c8070300c24a80d2140c0074180494a9040400c3c482125411905411051042107080e1b015181e110b600d1120180f000c186241254080d60090942c840100c5d010019002d407 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 370337491 1250 370336241 370336247
    0x110601050d11061305040608010e010501080f0613050c0423070c320d050901021207020907110a1704060314010308090f0612010b18010f0e22021b0d 65
    0x200744001c0c0920340700a6240115041c81c40042c01e00d241250101020b039511800070400303a6443c4d9001e115981c0d526201450040c40138070440d0301514488010305140d0000345030041d9203040103400e6162200c0c8042d024020840100b09150021340003402c2070050803424001c60a803070711450059a52655440d002508052003218080c001540c030400d42c012514906000d0b03003900a1140c1100d016052401c242610800100304000341e80c0c45594581e075407152850002400d100748400d004140e003d05000740c5006a580b843c5d0541d0120262810b9440302801c2c090584c0340c448055009002c03000c41d490ba10040002c0140104280c404984050103a030b500b010781140c540c1030034880a000074205118441d12840c0c03c030000404464003d1086003401c33130a1101040c02c000a9200d0904100002680050302a06800e201c48483c42400e1212288802c124043d0903d0b100d0f0031054400d41d84084041c1d0020880c001c3c400e03510650740c0003191103c00384580c40c046007854416407200f51040284034400244 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 370338741 1250 370337491 370337509
    0x1a18060c0a03051302100f11030f03040c0509040b1303032702030607110c151c02030402091b0909040c170c09011509150302040e0708040c2103050d1b11060105 70
    0x5e80a443c0020141d1581012604081e0490b400020824050540e030003900d410070292941445012040c0d0307a0b41064640390104520903886140034030320f0300d030401007c40c0c413600490394000c40380d40f42d4881c28a074503d0f00321300800401c0010385079003141e280704481c2103e8210350060964800d41c1101e90b5520f5012040d01c04070008215820240d000303041d08036003070a10036010310080e00e0a4048a04103010004115030554490301c030f072646a07a012040200b9490070b491061340102c3e0820040a894644040f50350003031040620460040152a000c1820003c81c0d60b4014000c1004107885490342110280c1d070341d1030303a1264440f24130070300301c04002007401c040c0180c0114640145481c0c1080440c03800741c6040b0b8041c4240480d2080c15800d020004450b00b0702800301e4451440d0b50f407400d6203131038a880d01c2c10448030305801c9002104980d5071900d0340309520700402e14209406050403038a07802480c805d1406085041d0045a291403138000488007260030514012400401c0d0341030b81c44c81e0b81c0f11000e0100c81d50b = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 370339991 1250 370338741 370338743
    0x50705031003020f121203070201180206180f04020c010914070e01030b0415020a03020706150503100e030f0a02060f18060402040905190809030f0304031a18060c0a030513 75
    0x1100401d08200601e030510f02403116030340242004401c1500c036100c2c02d06002c4091000020040c0000810900c3e0341d080c4100080303600c25a410503640c000940211300e1501070315940080789010381c0e5444a40341d480807440001c08000910540d9102d100718a03d42c041c01e5580d9003101c0882001100d803002100101d01a0141c0d4241040000301c1d0386140c44c1c651820304060700a4401c00d80c428051010344080b80020300c000600c64501580e6a1410b180c0314007142c8a00000c511015074915050040360390100701e0605642c2e15042c0810b011000c000d810b0309610500d200b40c11844000180d8401c844d4000c200c0b10304c5004034090301c1ca5a507844940c450740b800801a80301a07560131480010b0014605a48005400c60080044580e0345450a881c4107001c0b035001e070266001940801e00a030140f0b420440d513000146910040c500f82403a59031203000742e400600190302e0801c801000201c1e607507081c0c4141c00c00301101c0340842c4c415041064901896a101d1192200040c0c10480002c034002c20082460b00340d2 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 370341241 1250 370339991 370340011
    0x31e050a0309060207141804140a03030504020901060302120a230a061a0313201215091f020a260103121d100e060c060921220906150305070503 63
    0x1f0031030100c030540d00d84c0c80c0103200302d841291051914180007020130995090621036180002c550901c0d00400c6510041640b04008150040200a200c542d031500b459400010456010600084020884880c00000c0d0000c4180c182a8000c05c40c01e0107007a0803100403030350b42002012001491118004280c031084614442e10b0506041c4800000c0e900320900482500003030500d0b4480702c520380020075040e4100000d0800c4e41c0680600f000848440c4c120a411000c3d860003000d00b541c01d8401c0e000c816071260000c40306544c4c08501055041d004240d03020306590174a01c1c100c1540c1081d0008460007074280070595540e1042d030000864180944041c050034200c40414500941d410740412a15007a02d04810082044045508203107807500800340102e00d40c00c002610700c40ca4071140d1645008080b02400d55030443e4403c003620325001001c1103500d07060b040c030810500824400f40f250b0407602d090703010f981502d1500074002101d00004404075a003d007031f40e80611441c1c5400f14100c5090005844000c09 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 370342491 1250 370341241 370341259
    0x150102030f09130f0b1503060f011b1b06110d08010e040f050106080a05060a1109100215040f030e0102010501030320010b1008010303090b0c07031e050a030906020714 73
    0x34600e0900c090103254070010300720f2000c040104401802c0e644454030359112a5101c01000c4030307502c0c000d440c0640000f01c0b090020b080d49400f00000b41c18158418031141844106540d1046458215003491070742034100401c04012400001044e41c80241403064200113100300d50346507c0e071500419181c0010b501551a42c88036420b003c40349803001c1000c0c000301e46508816440b00000343c1c3c203010f09002001600060302c2403038841e081c0f180c10464010909000390785456010074045101f0000d5442c081000d80740d8014014449800b41c0c9003030458038095941e010f880c000c000030408001480c80d0614400d43c0e07040c01041219006a090700c03401c3c000100480d80ca9050700507004070014071071502041100010038000a070101254040314081e0f100c0340050b91040050040c16000140700d001810000d003200e1034454800c032441c0d200c0c0318a020042c2420740d004071400d42280030b1001e132026075802105a6204502501c1c2c0504104013038400c54001d80900140015440e0f840ea450391000d080181105170 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 370343741 1250 370342491 370342507
    0x15010611030a0f0e06210a0b040209101b14030301032001020a060e120f091c1e0c2408011e030803070302040b042c042001020705040c0905040515010203 67
    0x58500b60307901040c1d00071209110380c0080c44c01e4900c0d5110180e00b1b0840d0001e890403d007500c6000d1b900c2c044c040c2c50040340100b280e817019845076611080c2800c454a000020111700c04104089002c80340406803290028072030128800078080000d604032441000050040201c9031341c1056a0314150341c0031030158204000368000300c0d02c0b0360000890303085202c0c01e071038100800c04003001c2d030b680003084618a411000305400301241000300340c2403186145070f50002c1000300556108460040b010141007000700045401e0410041c940c41c10002a103000c100d818601046400090358501c4507601b407400149804000203844401701d1541c14580350a26540e8140c2410768a68110703a900203400901090303404c01000404419a0780500007902159003c2c1440c1d0044455070030144a10503110078200860109010015000da086400c000e2202d4840c50050421080181c1c200b0120703901640d049802c00c1c91072080a0b5200000c6030603100b040300c0820081c1c4890300c0302000040e003a40b0030b60241e8400c0291403 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 370344991 1250 370343741 370343747
    0x140318180613110d020702030d030905120702030a0b190b101709030f070521120f04030210051305060903090d15090204020d061d0907060c050a0515010611030a0f 71
    0x1c0100b0080c420042100710340b401075180c0982c081000c20a0031a07002c00c03c3c104500d02803280451030000c070f203018003058902380c032015203e044042c10304000e25000143c0c001151000c0c00072100701034010792010220700d0480341030034840e900d490043e4421403034030007590038524141a2031080e5404965882807112000c05460544c03180c05011a07025110600a00f4443c0300040010f1041c18816030107040501400140205103501c00140d40081050500904807409004c204260380034015200580e00340d186c1381802e13030030143c008a941074800c1c285400c20400550450382642075a114504440150307991407001c0c1d44900900c14015030003080342c00a40c01140c400d0104550300005042d0020745004e00740c1c00501264410105410080c2d11144101b0041d116182030030b0001b41a20707803610480c500001300c00d40351042401907005100c140c1081340184903080041d1564554820216100d9002c500c0c0c0a84890340300748940360001d41540780f44c0040e280c0c04020b8503030003141501c1e1900b105421801c25 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 370346241 1250 370344991 370345009
    0xe160815060408060411010908010501050f1003020c0a0b010f050f0f0402031f0620030316080c160b010302030c12070918050a110111010b0d0f06091403181806 70
    0x480d0701050030301c00030401c1d0000b8003490780a1071044090501030700c1d69500140c54900d0036441450f86901d804010821501c84804005041c1c1d0100d0b190740300c0380007010b4183e00a014540e52501c1c207218a0307400c00c04014415420605071031032014643c41c0e0302d95071010020008004101940c2080382070f094040c01e824903401841e0040c840360350001c0b505840c01c2c1100750f001640d61000d00000c1c605505006244503201071010450101c1001c0e500e1850404803000420200c00050404c000245001400c9034080000750380c6405c403c10312110009245081c0088114020f00099119000380280002c1605c1d00000d61000a85080023918a051501c600319005202c01c001404543c140240b5650000b0014400807541070701c512508544888813200052240c610044c501e866a0715125000d200b9039120305001c0740c0300742d1106c40c1400f0000203191040241c00480c0000340403000700391102e010a000030000d806807100d211600c0e440c0c2d07080305007042040c0c0d440032480c490816240c4081440ca06244000c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 370347491 1250 370346241 370346281
    0x10e010c1d1c05012d1409030a0c080409061206060605042103020a12050c0705060405010207180b0d030c03030b0405060904060c0c020a2c010f18180b010e1608 70
    0x50200b0f0400c02c1c80521220914008042001d9103058035445d1203980b182101d0082082c0c6540c034117107003503400e1a81d24891424044103221030f001c1e00310104621481101e000d401013881c14400c1550310f030400110340840c50406c440007030600101140e018842c805880803a0f201004688030360010080e05080b268401d501a07085025803078175800440c2000d1a00b41011040c4c0c3d07221039440e071851058a0074030701660030040c4140c904100802950780d00080035402d640070302c1030300c80c0301c2d400c81c040b54002800d80700d00c40c940140d07400382c50405140c1c019002201d2070f806a1000e01c58074a8460804c8200c0b0400c82d1080c5d03020104901203800304145511149004e640c1c1d080c540d10101454001545030b00c0f42d58004c1418242101d030034406440c000ea180c0502103540706c1802031650600e1000000c108441c007944150684940e4084034900c45508802c0300c5805482201c1e4910350207060031400f00e4024028000c6040321100890300c1800e00d20b1a6482c4e981e0296140c3d0707801d4a5030110b0304070541c03d401e6 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 370348741 1250 370347491 370347493
    0x3040311030f03180f150a0b030a0b040602040f0e01080a15020d1103100501080c07020103110d02070507090507051303081e0d05090606010f090e04060e010e010c1d1c05 74
    0x20b0340031092403000c015401355000441600000c2285001a8585200105007009a801010305d01c480c840c4000c2c140c5e60031841d90f02c8046400d400d5000840d10300340070841d020b081e00350000c0a0005200f8544d000340151684071441032001c82d05c0700e05111900c00288034000e62680004202408541d0900d0491070403100c07400d01514000c01403142405540d500640100f40b404c6c00000d1094102c3d5000c5c1c4034009002c2820824101d01c0d008407859030710300585002070306040e19080c0419038480d640703003103615451144801710348400103410110782c1c0300180e0140000f1b1601d404049014580031358151014000d0050034000441d0850b520090f0680103c5074070900e8240c0b00300300590140007000600800780509400003040d15111440d60f00d4228050300580c18008044e0b08083c100d44d01c41e07000b03c150b490916411442d5261481c0900051004080c1d50001d5442c107100e99100700c0064004069039006940c03004034001050f86070039100b0340035905803030307002540b0704503030700c20000803000d4203406030043c8 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 370349991 1250 370348741 370348747
    0x60302030a241401030902150304080405030a0b0f0606030c181f110705091003080c0c0a0305010902033d111914030c032202030d090317030c0304031103 67
    0x40202c0c8411000300710b80458401d640c2005110880203580c59000426013460140414222500400c0605240800d503c84400001002078180080d60040700c0080001070704480400e18903040c6000c1040c02034030700f601c84080780c0010505500e04101524064030070110300900c1c05103465014002181c01c02c5485410199500008040100c0c803003490f00440d0203611441c0810b040071405c83d05111064100510607500e13a414040b011402a000109480d84030150710766450b04804001d25000b40860119407107010004007000308001034020340308091095013220385403851650411107811407600c114230f10000000e001840254411003814030003441000005203038040c41d5481005910800c02d61501070030400381d107404c03190300c04000d4072502c0800d030005089d828800600352300c503c00500410900b80c0c810b400e850702c011415210b0030505a000741113500214031240003420055251106440307070035114484070030000800040324031400c042c600e4245580e0703407541c0a5800d001545040c804501c024 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 370351241 1250 370349991 370350011
    0x6090103030806061b06090a170703140a0903061a010e09090606040b010e0a0e01060912020a0b07140d0f111506010f09080105090601170a020f0402030a0905120a1e09060302030a 78
    0x5003d460300401e203050240502231014100241c035482806000109020700f0001d01d004641c0c001c10415080740c140c40c0e00da0352012030207401c88000189410140a05140c54400d200110414018000700c01c0c0c02c1e2101a1000408010451081d01c21510005143c00117030000d10796103002e41c0b01a41700309050402c0714007211204089000400d149e0028840014040014001c0b581c00c0340c480c0c802407204208000d601d2180e036011a210b03514030311543c03450b907101041030f50070004a00c1d54242e50340c1d080d50427500c6105034a0402003012008000e0140400c0d10189401a0700902003200140e01c42e441128002c26281e601c0111001c40f40480313410100801d001c80403410240c00e0041a00405400c0000d003400e50610501c826203510403641300140360720484500b0300507110350403e000c000c08100c50058407603540014074409001e48501c020494060343c10507403612041c030005025103520039610140e00060303ca4402c02072080710381c07000c004100988402c10070584241c00941d070007403008001251407428 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 370352491 1250 370351241 370351243
    0xc021506040b0a0e0a060311030d05042709030e0f0f0a050f0607051506100f200106090f05100b041d070509040905060601030c0207270b03060403110606090103030806061b 75
    0x152805045c0c65104e0104006005002c03403800400b080c203c0c085c2901501014010703102e8492481031004485d40140c00b410401d402d0034110044104003101440002140c0c50000d2907a13034180c000c075104042020450740c060428404240071024040c00c180145418a010003405440090b0701c181d0080b001c1082f400021004d200100841c2503214440d500c600f800c4082041c041002c901c00d030704015440040e400d05980c4808020300c94140c030303e20350128101e110b40680c003410154024406550030115074091041c4658099807140986e14901d02d9072a48400340b08110344664030071400005030320580ca1020740040d21020307422040e5410214608244c403000b150030b443e40040180c4243c2c1024003041003550b01406540511100b42c40540001400c0400c0c0641c11220342c000044440010386021400750340c6903101e40e40303a00004084612501d404d01d8018403400503106030005a00441010800d02e00b0a6100300703050f2549500c03001e50503600c500501000303030041000d050b01c0c00b8031041d9aa2481c18 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 370353741 1250 370352491 370352519
    0x30c0e0303040501140d1d0607030506011215031415010b090109050913021005071104091e020103020c0609030901171018020714010e070503060c070602130f08010605040c021506040b0a 81
    0x60211f9019900741a240e886820500014034040c00d050814040009aa9000c2d03420408542078480000d0380c00c2944401094031890303500000c0000d00c0c2c1e50046000340400081c000103440080c9080805c0d40c0e00c171140104140501d400391408520131440034031187ca0311690441d40b10f816005107582c00c019a400040e11083e607280c0000200310b00242c407a0610440882100c510501078a0038030540482d40d540d00c054803105540b5111000040018500b1680b180e012a841050828200c038582d040c8812902d8a070b92100c40110b020401e000f00100a800b41401007a1150141c880b02c101c3e81450107202d041e4a6245104641a60394200f00e10000038110502c1049254001c100008000d10601003041c82d06035983c218501c01d9200908006c0712080e41c800300c0307480b907074080400350310b03001210410b1141016980002a447d961103801094030141540490300b1900d08540500000e204000166140c070302459540b0002c0168000081c55410b041c1c005890f034240c05000300c1c4c2159a02c01404520070 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 370354991 1250 370353741 370353761
    0xe180a0f03031a040e100b06070206030f07020706080108150414060f01090f0e060a2301151409091b0c01060b0c06010b0a170a1416030c0e0303040501140d 68
    0x10ba42c030b01d075030307100f1040c0c02c1e201150b05003090720204503880907000810b80c0d441c0981c841502081d1142e00c119803584410096503d240d90290040e03403a400c1c4840c1700005964200c40c071100520900c40c001440c107200303d12007412680444041d0800140d090311340080c11100400075101000540107103c240e0008021140c8210303c1c40e142695194108501c54081e51540c0c0d0340c4006c1981410341400354000082a2a9004011208001000c04900c00d035004440010045c4440810010000240c004900007803002603034010355600e42080003c850218040c01000301e45c1360844100e6000500c4419009885111014802ca40c182480219a41c45094801c3c40c1c00c507210003080403d003003219000030000e1601400480304010705100f544003008090f68005070006107280740e0b401c0421aa01c80c0c5503c02c401144400344950990310b021880303c00c501e0303814180000041d2034001d0480c9003d10608010041d280300401031403400f49401c004651210700c540350956101410405a0341d0012107100703c000383c3d = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 370356241 1250 370354991 370354997
    0x40302060403150c090f060302090f090103030f0f0206010e07230406031a03071a0310080303010303050c10050c0306060a1b030309150b0f04021c14011a040e180a0f03 73
    0x900f4240001e0007903039041152101030050100052283c220034640c10820b440300c6180040e1181500e01c00141060210400380381c016040000110070301d0b41c8808500798003d0a40c44406a031800301100300c4c0d90308824842c0d500408040004280d84500c0b4120140c014501c00401100e10759100005000c694071036804000800e6541175100e640c011014211b40c0300c404120060102c4a00e8149113074180c420007000c7c9c0c0840c02c000400184400116080b47c00900080000c8949947e100d02e8050070070340c007044010030303d445481d082c00d04a1106004243c45035681e03080050030f50b2540f038140aa07580017a90f580e402d0141040b8941c01c44421b43d0150300042d402998041240261401c0402c01200711076071a840c0f640c00e000766a4540d4544408440070b640b003c2c1c2d801681c41c050070701d51110603400301485948030360400320142c100c0f042202115058a003600302801c1456619040ba80c05e6114920030385100d0a094800218142d41c4071411205940316041074850010f40f56454a000c0900e000e0110b001c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 370357491 1250 370356241 370356263
    0xc080106020c03150f041401060b070b0604150303030b0303090d1a0117070b130302090f0f06011b060c0216091a01112a060d0504020f090408070b0c040302060403 71
    0x3280358100326800c80c0782820383c040d01e807600c10800001401480188403540d44c854000210302002910b5860f074030f001d010000204541510b0740b440710544d5001d548152070031400c25000c83d03641e14162080000c4050405d95451041c0d10355902500680700000855034140028000410a41c8400e0203c0088a00c50041c0c151080d11910a000300610180c1007425000c02003151000c041c00700103041d4041d2140340e01c10079100d0b1080307545402c0144280d04000d4200c40b002c0c0521221224440400d40036100c0480501c049070344800045442034140d0f55072100b0088061407203004100a54841041201c070b906c140d034908002820400a142030383e03400005100d6840c00724041103c8c0d2949030b158406000d08e07001d02c02980b5080140d030380705102d41c0b01e10503241e0686c220031002c0b01d400090f03044510010703000340e4444640c503111500601c022103083c0d0103010f0101d1440007030b240400102d03104941c0000124103040c056290810200d0000300300c018445810400800940d5400010f00002c51042d8a0408 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 370358741 1250 370357491 370357499
    0x9040c0e100c03081f030602040e0a0e01050702031e0f07030f0f17060405190515150f07080703050909040f02011107030308150102030405040e01051f03080d05190c0801 74
    0x30000c0c60501610341000816120040080e0740031440039000000c40e420070801c050100481010745809500080047e4400500000c0c00b65040f080d951144685031020420156074413903150994508694020040e0010000c1d0780300009440c1c0300c40440d2641d440d101e410480032080710020707540030700381c1680480c00407032142c184035901c0420180b03c00310030f00e001e03040362248c0314854550398030191034603104a46a01c0001c1c605410034403085e02000c03068006205504144039900c074a00348824905008442d1010b0302440309200508690b10440f9001030345140c41920b4a03119120b410001040381000020003d400c4035641e0340400c1c038011409801c02c82c0000c0c40c41d100251030410404000304040c3c00c00482000825009812a50b00c0300090042151007140c50340104e0071440b8582000da8090700d0302c2c40d80d45420708158080d80c8030701c00401180050211240c2000e2541030701c2d03c0300500c0c4410030404440845103079001305411069800080c0442140c00109a00740c41640c0f0440c8001070350080104 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 370359991 1250 370358741 370358749
    0x804021f08040305070f0f0b0106020d0212090f0d0c0b36040e0a080f07170403051b0105040905091c17040209070c0818040606030606020c040b040209040c0e 69
    0x1500a64003604840d50104100c20081c180000080010b800d102d000704112050080d02e8180322170310b56104a07407030b554403524944010014000c0c0120401407140040030380c001b6000044c0e804441441515040c20502c400c002c02c50800c100310b0340d10350001601c00c821030008400d151400042c00c9039444d901d440b400e40c5544201c18411002e160442c0c0040569030f11008101507807001c100c1041540c0104a840b41602076500d81021b1802c002c144100c00520080c4414044025115491103101ca1881100146c480d00016005a000203006900403611141d18072100142c480d0000506040041c1080d40e00c0c1001021148100d0720900c987d0031801c010405070103c0d00c600b0f4043ea120741025460501032984c07585551200a0000b8041c01c42c01000c540b145000300c41110800d5485030040e40d8a240c241c2c009078010b20a007213418003450030094080760190007400f0309010740f2003550003000355001d000d0400c170117002c016440a40241d420070201ca03d0340c4442c014542d4144c03083d2501d07409000341400b48 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 370361241 1250 370359991 370360009
    0xc0a02010b06030105010f121b120b01081603021809180d23070f0803090f06070c02010c060b040f020f040509060904120c1518051903020d051e040303080402 69
    0x510b01c00e1800300700601583c0e80000c0c000d03201045501c5c2c80307201900c408000320010705141e144103626501c3d4920019030544c0c03245002d118504509400e100b84040c1c1001510400401c1d0350003083c0c41e41428520203018483c0c5c1c0035002000c440d064541c003000104d400308402c1d01e030503a8280610a0880c05104814408208202c80d2445c00c0c5032500041d10703120700c0626076850746c1280c1c0e6100903001035540c0c14882000f91149005410010441e80c0c1d040c00703480300d640c1d403004100c0b425082c00741d0000075100c54041c80d007482404c0d030103071504001c00005549a03402004200c44840e8002e42c0c64266000103000c91010b030024030300303d810b02ea54440c1072000701300707428a005000324491844d0004110000d440340301d049140c04c1c5182040ca505000a20782208102107419007d00a0b80c584000008600074071080760446602581c252060100481005548120885400b030051b0780612404110300344071b200140b69002c040440d140812900c0400500140e0150f031003500020070100c1448198600a503003 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 370362491 1250 370361241 370361261
    0x9031205122401030c02011b0503061f0c020120060c0a09090213090203041502130302040b06131a070b090c091608130c03020d060c0f020106050d080904140c0a0201 72
    0x6091036011000419250403402c81e410360405031200ca6011509000750880002400890007104510300300750f60040051700304a407020b11a508001080c042001da28000c004401c2a540d24039046e2103140d001983c40314410341d091043c80624000020050906001d400c3c05000101072241ea00e11029000030304125045c0c00c02c60089104000f1a07070f40340c00c9207020780e0443d58880405602d0f0340c2c560400301d811340111119090340600014014410b00c11070440082078070f100302c40412030100091b060000c1d50049000900c0c2101280c0d800b0701911058a1902c5040d4400c003074864600b0070390b03a6030b170061000f094400919960001600c003101d0701d0030b0280075502014031510500031380425200140b103004090120348200034180115010700c560a2200400385801030090912080d0307602d406c41c01001c0d0301201e4000110000340d56a4900d01c10b000d580308072030b4001e003600582c01d01600d501c2a107030f0000581c180d0140d600d0201000e1000784050700c030311502c1000c01003600c910400001900b13459811369 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 370363741 1250 370362491 370362511
    0x30510050f030c12010209060f0a02012007060b031905061b19050306011e020c040b0616080c0c0a0f0e01050103151e08120a1101060e160903120512 65
    0x254500094030001540549003d08a454000001c1e50194150080c854411460781000001407003c0c44c0015080081034260b921740d000f00a02e102413520021000e85100e0a0400040c0400a44000c2116500101c2000b0f02c01801d5488000e6484080300175882c00000c1191a5040701c01007000e0301d030540000914490a0680c10b0380f90104001d2051003004602080006000b00400868000c2c1d105100d1240705403440c0b0142c005401c0111400f81d03903a003d2441c114030550411310240c5203070410100f80c81004100c034101189514040d0303503c00e07040c0c00585050003544644500c4550950320609020010a09801d04441907030a10702e01e101e07a181d058201c0d9041c075007007030498440042d202c510340c0c089442900310031580a00404400300c5041840e40990402d00c9032043d4042c60704140c0e001080740a080d0f40707a0000e44e001440002e802d03580d903489251101e00c114030000e240071080581c90708440141e8a0300f200000e0702c070b680d11920310200c2048200000c00109960310290000d500140d009510710ba = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 370364991 1250 370363741 370363759
    0xf0901060206040201050703032d1a031009030309150c02070806160c08160606050a050406080616090e040f021c110613090501090c0215010609050d17030703051005 72
    0x20001950750b00010300002d040100000b8000181031290b8401c041c44202c0c071420103911100603e980705903d500b0a40940034034541107501d80240d03507800301c010030182c0c080d02030300c0c43e80e005000c040020326000509905060b08e400d07403a00050384442c0a400c0210035442c2c0001c40400302e00009103000781e0740c0c01904075a8480d50034403429074116200f8842031130803032409403000652868092620301450030325441c0043e00015210801826810042c240c4e2001e5070524102030361072080006440c024440e100d01500031401007041101d6044c3d4164510505003441a29995140314408425000715405d03200000139a07241030031031800d1001142c004a80c000c0101c140034154846e0032100310303014217103403080400007032018030320247c61840001015a400f08211543c1d4a00405d000390004d50088001030040002080340741d1481c2907018166005ea645400354281040c0600a0384482d0b500e040d542c0342c491025072007002c40f55034015480f0707140c6580d02184904000c2d150a40c1c84040350000d40c031956000d = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 370366241 1250 370364991 370364999
    0x1606080408030103020d110607050a0215040302010504181d030406080109020c030a0f0e04180b01120b010b07020402040504110702180c0904090c1e060206010e01180c021002040f03020f0901 83
    0x580c02d03641925011034609842003164940f8020f01a21003070f485801403804103646090140205030b6041c840d00954002c1d0031b135a003410244509205501000303001c500c1c00d10050200040c00400b0800c200b0100ca00010340c1002030b0381e5083c001a0b15000c4082d250300c0003800f803000c1c560208400d8010030701c141c0c06504014103244041e0301da0042ca501c050810680745078107034002d44164070704180103001410402902d41c44034610500d480c2801030a6503c001c0550001803403101d10036500d40800c4c0c0111910315182d00303003107255100740d0100e201030380c0c0940c082c000495240e52301d106002e44080d6420b80b0596400c8188103019031206144c100d002000d8401d4200550b180c803200844000c000d086030300060021040c6030000c0c28078680d400c49000c0384400401e00c040d0b104100a444d003600d4640d0212519030780e070390340004c034452000d024100d072148200c00800c12000da0354019428907002c40c010b443d071301441030090604980250384040206031980c881001035003415407a5941408058502e14a15818 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 370367491 1250 370366241 370366253
    0x11040e0726070f03020909010b040213080606190e1b0406050a32130902040305030a020f0105090a0803092b1101090804121a0c092b0210030204090501030516060804 72
    0xd10005c3e0180c2c2c28003000402c500320a50000c0c0d0000b800420031901d41e02d01c0b080c0c414205100b03010344412445100e0119181e4945128900b10000d15091103000d01c600b4400f500c41c44903c0980341310f545120100c00b0121022001c000ba00141240d0f41d195922207502d80343c01480c00041600505004009106036161a020a10708101c3d091030380c1d203426981c00304408001c0001c10941d00000c3c60340d00c085004010080c010000340800140360b422221008485041c150032181c00352364100095110000500000c1c3d03c1c0c20245922003080780588140e0181c2c00d000b02d00c548426000d0041702021036a00700d400d030350031211000c1c02500110003000714509540c1d80f001030780315500942d00d20341740e4094503408000a40c16503100040400d0540542c604008001c02d100c0d800480e513a0388500343d0001100c44110800b0880360001c0001c502040e004007081c0c085c4a0403020041c085401c05800f040080b403030b0a480c2c0103503402103125400902400034408440c41c056030a603041001000403080512002c1a0 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 370368741 1250 370367491 370367519
    0x61503130809010905131b1e0e01050702090a1401080f0304170106150306051804020f010e19080a15020f03071b12080a0506011b11040e072607 63
    0xe480860740303980c1c520030390041c2c454501940c0566488161554845072840303450300444038179440915559045120f41400340c1c0c0e100442d28a000244000448040280e8820700317202e0002603042c1003aa00d031400d9038001c03419002c0119070001d5500d07200c032121104c00d840310010b40d004054a002925902e51405055503c905c00d0f8030a40007680d6006400c10380604080d40310000810540703401e04890f900810000c2c02406240c03090520894103100a031148104801d50503118a500414042145451500558042050361078098111050803400e00036070001000c200c2c060140e14009110400c003e152082400034542051000540107015600c10340000100392038005a4606003d880d07a0003409601c9103924105070040c04040101232224070309904220518095440c03c801488940d84803401982c0034207001c4030011101c1c04c0010054042410702c0c4200b6079040c0000d0000c02d05904e0742c10450321300002c9030410018950071003c403600b201040071134131400002c0800509400740c42d00e990301c10120 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 370369991 1250 370368741 370368743
    0x70c0f030f021002120a1421070f1701060813050105070e0310020a140304050f100e1b061602040603020306010801020c07060905060712050d090602090132071703040b06150313 77
    0x129903101f4900180c3ea0313016904010440341145848075192100b03000d11501c20b80308100820138818842c079031644603070300c1810850900c000d01c4520386d01c0c140c02144e0481d4001c000341400011356003080700040c1d003802018002c2c20180c3d5419000403090b01058140044815240c02142c0704220900500307401c842184c0032035480031580c0ba26940c0b02c1c00c0c00c0d170074200e00004410740b40c020300740806440146030b4003865444808608540000340c0c0808064104560060b05c264800000d01201f081c52130b41d00070000d00a0f20140003c202603503284d0120b880d1100a03080752078140d40125050810810400c4100c1c001c02252901d4494030b4a82000b040c018030a078000a84000103050ba80003425014204951003419072640c00c104440b51424110000d4000b1401180010b18604010784030240580200600c0d12501882c4088407050b0000118154843d08048452881035148100200000405184654000c2841c1c61440c0780c103c007001880030814400c81e16004003801403021140300031148032081 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 370371241 1250 370369991 370369997
    0x209010608090a05032a06100902090418120e100903120c0b071107090b06040b09010e0607060f0f050405100b0307080f0a140303060d08070c0f030f021002120a 70
    0x94884085280c00d0203031103c40940700e488002604400600c1510722503807810130914202400d2041c4031081a1144020f60300c43e00c0645440328240107820f100e50003800705540041c800103640001e040c0003503400300c60b40001d844015070b000d6800b05064109032920f04008044594840c0c50f45c00d500d010f04000030b24040505800340102c24a0200d0303006a03041e052050300309a07024214548480020300c902d080716103c82c003d025400d0300158041c214090008005c100030070f403508160800722400c48076000942501e04019109174004040d4658200600348a401108080745841165080e03000ba1892040ba60a01d00e20380020000450b40204041603001c103608000300c0c1464901c030000c3e2a11690350024520b0307000e001041d00c0804030000d034284001d4403419440f00188034000d445038880c00120703455900401500c00110019150310014900d0a1046a000c4407854850780d602042c00e4403a0000c0ba00e207135020101c0790a6103052000310750705c0480c030301c01021350b00d080c100f00d0151801094a12414 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 370372491 1250 370371241 370371257
    0x1a03061009090c110c03123c0702010f08090d080603150903040312020a021e0a0510030f0f0902010e0909100518011a0a05060c1239030a110f0f070f090902090106 71
    0x4c21701d403100545441646010402485408c0c1c608441e08640c08403500700d012408880744501c00700d0044001e00e200d200c6980240061070701d001000c0e00c0002d4000d004540c1070040c60400b02c1501054140030307006111046c011500d072411464404441012080c081e8259072003081920011703507400d81c074181e01103449440480c10204000102d43c003050315410659001e506034041481465241e8420081010311340814030400b0800c000d060111a03103000e001e03000841b050319251490911600c03d5410607010011195441d8455089108035081034554507203011000049020062007405012802c40000440c510a2030130500024100d010ba8800c0300d010340c1d00811072101280080c8000080d01c40745511850f80c5002d4144800306201c0310307646507061200c990b24420380c0445070318604000d4521a500640c41c02d955078100742e80c1045500d203000194442d110154448040c14007401580301c2d0705800808089007403880300c0182c102c468104e2aa9640741098050150303641107940d9045406d14108615 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 370373741 1250 370372491 370372537
    0x1e060902040906050a11130b030705300f090606010e06090415030611030405032d0a0305010e090316021c14030a0305011a03061009090c110c0312 64
    0x14149a44019601c50b1030a00300c507050103542e0304050700c00c8407910713420020f803120b80f804044c0381e00502c1d80004031240c0d034200c28130003846504000c581080c2241001401c4c846445400407015098840b41011000108120003000c90546e41c0c0741d0304400c2c04850b4540034501181c110f90b40b00c2008000301c0c1040443e5480c442181c8640e02158900300c8003400c140003018403800e5015171a070092100b20345191900d038080c4105c00224047d031b030046520070701031171404a0410204141d000a10000a000341511400b102006800002400140341c2510081290762401c80e0310900c4002c020a405059041000000d4101d42c500ca1420300c0d095045915410b480b2601124407040c2450a00041843d407030b400c211800f01d46c0020186c96031584a41c0e05002da03a0301c50004411006054152040e9400e007407000c00e56914004030b0444156019141c103c6034030b039603000c0c0c2505540c1d05210380340210310010790300081d11380e0610032081c07082402d030014071942c1442031000c000c0c9e02c43e070038a00400b8580030902003 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 370374991 1250 370373741 370373753
    0x816061d040e0d09170303070f0c060213030b0601080a06060504030b090c0a0b0d05090c0f060702011713060509161e0503160914010806010506070807020a09090506131e 74
    0x80b0010008021203d0244500d00c0182c24500b445c0a4000c400301c0145207250300309800400c491107110f1030380e40d11002514011041c2c800445903101100c03080d409103c0c2c3c80c03101d000c0000703090085020b00da000c8a030b8180f0b0310014041440c040c20243e07a5904110b014030519810004840403a40e000002420b1562007050503418400c961000d150302a044070300001d031740d03d90070780505906038100004102c6070316a17081095448002040aa800076020702c0066801c0c5403400140038900d0040c1804c0d8182420002c11240011040310740780801e0100020b15407e0000710701c50503034403000303841c0245000225500c40c6c039010710b41d0388210504642c4050303040c101078028003045401004007804442e0001d600c042c00c404442c42c0c0b0301a052242d450400c54510043c0014191812905240050003c69082500f802941d03400040103980e50b100400000e0016100c3c40301100043c4035540c000201001645486030814201510f10a482c041c1c541000d40440c0300007000d01a16007010700e00d2441e00040d45492 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 370376241 1250 370374991 370375001
    0x150904150308030c1b061305100b0f01050d0f060609091815090507031401050103030305150a0b09010903230106230405041103030304050c030709140f041e0c0816061d04 74
    0xa201716003d403200f4441c402c08205100142644184140e800000c003004d800c03c100c0d88801d00441e400600140640c02c254014401454544206100811500f294051700d034240e440301c3d482240015200a0101b2041c009407250041040780300c041040303851a161501088d090900300a2000c46a071042110100281045620011079000382c00c40d001d01c0705182081d0090400344401da0200f4107040c0054440940407d0360f100076400100403242443c180040041e02c3d8000e40006c038148884c040002c004503407500c030b0f00441e500300d0015005d905210881c0080c00c1d5500c0c0d1b4041c840c699184100c0d180b80580d4a03694800c4034005550000712641c0d5400c01d0302074450814000398160000205200070b0000114406200303910030380441c0c011a60300c0c2107507812203483d601d041d813800d601000420b1002ca4030b05d0b882500300d80a140034101e50703c00c02c1601c2c0c0710b01c10300d604100c2d0603948188042001c40400d100080035030b46400034070789400e454188068844030f424029a540549900b40780c00065441d9440 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 370377491 1250 370376241 370376287
    0x4061d100e1018060f0f111305040902060715020712030902090702120f0d020c031605061e0103030503070c050102030109060e090a032c150904150308030c 68
    0x4031000004400e4654000302032031071485203107004030144034110510038001c418252614071030500c0058880c2d01c07103000a16445c4081102c003605c40300540002c40722406410300031b00d000182141d0303c190303041d444800509103512050040d424414000003696464081c0c41040303802c104200403400c1e8040482000340706611004048680c1058400c0460b0707032592012201da44203644001003621010070590703484004402500c0060400c00c03040801d40001006054448042030700941010f040d60303d014215082413400054032100c0c441c5070030600030204810b1f600306801035020858901d0101040b08581c005000c05018400000003081c105445042c002c0c1425030400001c540340d5849052440c003824851142c004e1090012010854104012802c440d80c540e0544482d007192410313618405144200b048001c200310011210b000940d1108800410072030380e81262942c1c3c90440e4010041111075100c150b40c00203601340e8050000503012400c883d0030115411100307488075003246003100d0700b80fa43e0f45 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 370378741 1250 370377491 370377493
    0x120309090406020403021003270c05060706050712020310090c05091908010b03030c0307030c03110706020309010f02030a0e130b0d150e1501120f05010e0604141504061d 74
    0x4200400d002c02d41e0701034020389101f250302504086100800704c00fa9007040180100c580e80414440d48885501400007002921441c20558515035031070004800e900b055100762901030710b4104202c0c84aa00010072103500002d0902141981015101103002d4142c0b4004c1c0c184241c0d0310544501028011000e540503800010400111503441000c403480e1802c1d24801d240d46e80d801c016920409141c040180ca0130400d00d000190b0801d10180c0382200c813031105240135428002d4007030031868240700601c40b11001d0003031500150b07035a6030381100040189041d410140e00319041030080075881c0b54820040900320714100d50060ba4a00c04040810080191008d0b00b5404080f6881d501c003007201d00e00e10100b02d41c414a0007002400303449006180ca0784078111151940e0610b90f40103020b0700c075100040000305030040c09906002042c503034a081c01c40b00c081c1250040350b80300b48100030821041d101c411748008590300241154112040294800300800b520003440151507003e031801181071112031809546082e0 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 370379991 1250 370378741 370378759
    0x10503181c030e0102160206090409080a031a06030105091602010e01060303020a1203020301051302031b0c0615040606020d030b03030c060708040615030206090409050a050d0216081506120309 84
    0x110100c1211000c0618001082c03d00d10120f1400781c040c825200c041403c140a01c2001c0302a90801011ba4061203803254099618004007010904c0d800c05480031084503100041c0c0b911082008000c0c0e4400091a00e01c9107070701300b0040c801a00d441104540250300340d441c03540072405d5103400783d000d894041c1003c2c1d015803074048000207050340081d1201030300d40595000d02c3d082020750b000b10140c2c8030034080c1c0b40e00400100b401c1892940968021036001c6222034800f000f41e244800308802651103206903440702e901c44024029603030016141a5034800d000c075400c2204602e080350180d190f444c0080c2d04428150703103400ca402d954505104841208006405a462601c0c1000d400b405907131003913401346e5206140c080345c02c2e80440c00190751002e03290014552401d00c505801008040c01514800301c480d400b42000040014400f000001d900000503009420070031110043c0e2043e028181d8040c070b04030f030b01114208a038010100041038024070255111030704a082e090500e86140f141d0001160060019 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 370381241 1250 370379991 370380013
    0xf03042117010506070f020907020a17030a0b0f0906040e1903051b0a0c14040e0f06070e030105240d1203090213290414010e0a1b02030901050318 64
    0x1c012800c1d1a407411690400780d90340c039801884241d010b500c0004014084000380d0001524007106c0702c650103020b910455183c05031a5540d0700c01c0c00b0200c502607000c00004401e0011028003400750240462081c3ea140303218a80c507034001480644060b0006018507940ca0980440300e4040c400702c0400700e41098170182200321890014801d92010409041d00208192280c88250010580d104070541180d070307600c0311600740000542202c800c00207007076000e69904a0b14400c40000d1181c400207240040c040c0c04113181500c40505075400d2080310714403e902d010704105138000c681170000040e403100d540d05402c0c101c0080c0441c04d200b0f04084050b108500c000d042c01c4105d40e1580024544034800e552401250000410b00700555103000308903140d070400145c40c0d5120403201c565000c2c13000c0c80101b001c207003a07030840e8a4180244007a0004596001e030071003044081e5555000d100700b00c501000000c1c1101d1f140840094503401001c96081c1000b03000001309154602c08a086042e007800340068078481400 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 370382491 1250 370381241 370381247
    0x1903050f0f18030f1210050306010b030712020405030a0507030c050114030c250f020a060c240b220b060a0f030c030b0a08060402011107050a03020d14060106110c090c0f030421 77
    0xc071b94100900e806d44d00049640e060103d0141c1c120780c40e031540b0b503045031601c20b01030310310409002034004059070900000a4070741d01000110314050051000d45512821410103486415203900454140f0140d0304e41c1d40c101241d42c0c0c0c216540000045074140c0c40f6001c1c0d2107483c01c0c692817803803034001e00002c41120f007003406000c050999003a8400c50764021415076402080e0743c0307074086075400740442c0309124810440840c0740e5000e00c1682103060000900c1014200003c00c0000901303251409490046e0f00780c0080c1c1150720480180c0ba004480303e500348036a4400040c00408203400a508054031520080c400c18002d802c074804c0c0303503070080c902601d090f110000b89a0742d0a0031182a40054444512103400135400b25005050ba80d001d84501092401e503000d200b407929042030110b03064580c460000203442d400303218681c041c114940c0c138000e101461507d0a80380110210070148035001c81800d1010b00b0041c50104d511205030704041945a60320740c100854000e070040c02c03481000c424409041e6a0f50342c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 370383741 1250 370382491 370382527
    0x3020a0315051b04060c0201020f030d0e100b1f12020304030f02010c1e11030712090305070b120f0c070f050c01031409120c121903050f0f18030f 64
    0x100706041203142e441429007a841242c0201d4803001c4401000f0501005118600500b4114010300403940b01050303c1101615541c00031071034110481d0344190340840c0b14003d1180580070720b1250410310071005504000b032803a06118190820410722802c6440c0c84900446800080321362036502151030b4986401c1c013401d00001d5516040041d46840b401c44989402030011881c3d09404108103050021005030664500002c00c6071407200703100c01c1c0300313140000340da100e040b1681b0b80880c5c0d0f50310001c030315503c2d041c3c3c9080ca49070403e420341d06040c80400c3d501a4806080c1e644461400c801c9003090b02c1d0500da6010781e228000b03003d01150725208030b800a01400041d0703102e0041c800e80c0c040003034210030160903506450540d20b107161a000300042c0c1440050000180070080012826106a8604085c00404541c003c60b18849802c0c4483d9a4101550b058410241e02c440c020040304014a8282c20000180100400950301a681a211000041c20401c240c2d030f0401a425102d59450b100b0700d1050804034 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 370384991 1250 370383741 370383773
    0x130c1b030c02012606090901020919030201020c180a0c0504051207061d0306181c0f1e051b030409020d0603020a060903170c12030106030f1514010507060603020a03 72
    0x30103207200b000c8030282c4c120b0f100080c0d4084080409803621108200480e008020f03004182075902400103210702c0d82c1c0d8602014031960007440d030800d035914510002e82800f4440c81c01031311403052100042c441c2c0180100700c2e6402915040300260186400105481d01c0c012900702c543c01c0349602846420711480000c4940503507555841c0d080140440800400d48410a98581d68154110602140140860b203e00280041c0744400350b80051118089504c100d0304c0c050700d9500020024207900904541100d402807010414039000c0900c0c940409000e0010b105181504912902400100e000030409205840c00f41c00c4c900829540c80c052001071f2000ba080502040e4072407030000400140803405034be101d4088a42c031000f500c043c00480001340710584c02854052aa6020742041500c4414101c1c00a40c040e00c080d880c0020345814240159044406501d01004880c210900620186d01102d0710070303154210034a02236a0700c3d00380c2e20f0b045011b080c1c99400290010862070340441000041d4241c04010 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 370386241 1250 370384991 370384997
    0x3030a051b120f0a080a0209030d12090b09030717072001090e1321020d080a0204050901030b0702010b0f01141c0513150903050d0b12060c0904110702130c1b030c0201 73
    0x254641031b14001c1207116200302154907520003840b030004035001e514108080e1030380c5200041e50b1149512450203041c0c0482c1c810b409078000051010410030f42d000c064080b09120b040c0c00d402c1a88964075031040000b004c2d54580001d0080c41501d0321070384100c034510081d114041c28152942055000441c2e840a10300341207502c40c102c14840066283c202850118080150f4001c10740c0e90b0000c0c03000e40d403001015000d42c0e406c0380c00f00004281ca454101c0114000d40c4500c9030480c0c58503203448003e08441103001c01501c5014501c0c14980c81c1d80c1d00110300a1444854810b0030b030307924926138079100f8880c4446543c910b10381c1401c0c100300305200c907140001e03d0f0602078055002c8082100c18181c04071002150000e000c03d6040c0300c0118444056030128401c00c8001e40650202400d03107003c18504042111b07000701040000402091a04142c0a110b6440f4040140e19040c881c988d400504d075071520030802c40e14a55501d01c14030046209118002039440881070071a03000d422418020201c810114080c2c2c04 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 370387491 1250 370386241 370386257
    0x1006080c01180504090c09050f10090e1c02190f05010507020607120f0207061d010c030209031e1212070201060f06050d0b01020c19031103030a051b120f0a 68
    0x45501a040340c04040d650003010241c1c00c0e0500c820400141175500081ea0b112801c000041038101e801d114131801070b103507561090034624242c1076828540880c1e4110312034003400c1c2540f031a1800720000c1c0240990400402e034141c201c405c04012481c005858503081c4d014450944140c2c02c0c000d000c110161680d010340d000b032100c0c4d682c2c11020b0740c0d01d25080d103208002512403124007540502d2607214204806512070094a41780c09030300e40030181d80c0075882040c8580c10103200340402d41403d01c105040e01400d400d084d41444030240c00a40ca4882c03211040750b0000c1503211511940d0b0f0140300710518004070340c08240c0c44d00100301131100d442104484003005507113410004103400280030783c00340c00c9030b601c0c1c1d50f400e140820300e405010207020a441f4140c1503100311070045a0035942d0103c2c4003002e81101241d89125451070038828234900e4080c4444d402900100300c12902d09521100b22640c6d091450706028642c910790079110300d0500510030400110f400801c0001c04400c6000081a91145665031550 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 370388741 1250 370387491 370387513
    0x905060102070e07050306061905030603010608070b0a050304020a0b04152604140c09091b09060a0e091c0306060e150a0e0301090c030b0f010f0b09041a03100608 71
    0x20b41c511041c0202c5060140c50070009070315611920080d640014017500890901000c0c10006003540e840e820140c001c14000f00401c94542001d2281900515100d00240002403805508003600e1207038001180800c90b00200080541d122007804000800100380b60b103640d6a43e400c0405416110180c0c284d00003803040c0d805001c602904070407502c080601580c070148903155555641410700b1040392503116801141d050406640c0d65503111481144000041e000b0084d200e588803d0b001c0c48a52441d2092030101c003030203443e48406c24404103aa00c2d6051011440c1c964442c100c4ca48038a684245200c038061031000a03e159154100e041110090b44640a80100000400024184002e410804040c0912040c440e841c8580702094808001400000c1c6580d20740e08d5282e180c540d1a002600e4441e054010f1000c21040101590f004003921030001424908100c2641218403482d008184200c2c2c0307681200707009045144200d4002000101103910000038109000c1c0940b80b948114201e0b4015411804 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 370389991 1250 370388741 370388743
    0x8270307120b1807050111010f05190f110a03110c060a0218010e100822080a0801051504030f021804240c0c02041a0a140a1403150a0b06070c0905060102 67
    0x1c903e4000c094042c1c450141450011141c240e054041c104966494028240c010a0b00d4421540034601d0031908405c41c40c404488041130b6240036a020109501c1c3c19030440b0600745110070fa92075003403107140210f440d00325052414071390b001d80006a98140250006e20510442d140c0c02002c11841ca0b1241880391403000c401940c800303620020381500300031011403441300c1c01c0c402c0480d9a40490b581e00d08181040281148100d600c2040348201c40320b002c00110ba13920b080c0c01002403401000308840a541006000c0020a414042c5110003040d090141101004654034000140c0c1c005c0c51203031180203d85020700300008150305103000c0c1e80c1c02880c1d207018541004d1050291b0200c3c240700e916007450203e425802c0c44028405890040c800402d1043c1210a0b40d4a1000020013000e10261207070040c000242003008402c0c1c03980c45810700320070051401d0016100400d9201070718a107503490307281c5039444003090800340c0401c11138164800e400094030f50802422030030800642e40c03504010880703035a40c00016 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 370391241 1250 370389991 370390021
    0x81210060e091302030f0706020321010503030409050a021e12070521090a020d080a02010c0203030f0c03060a15030e070506070c0b0705101811040908270307120b 71
    0x2142c01025000004010080038104400441d01c00b80403107044464081c0100e0a241040d0042c800603000002c400c20080c41f8995a8009040c0a400c0000c040d4940b4001aa0b00c0c4100c0c422880001d40300c0c000680184041c0d8165079410f80c000356940510040d0f807028034903c2c1c0c813001003110705003d042c021400252007082500c200d131002c024004000d01100300f1401c1006e900800f510342c9407061241035070058941c408034402d501d1180304551b8484103800006402d44200c40c4882c01103600c144100001d820341b100f4017940090540160702e603240c80c0d40020441801c0c10360409403060640300003c4000b41d40c19403181d090700e0b6900056903543c548400402c0100d10601c04090610400000d050113060b00c0c09005100e4203200f0f101315110301e002c44d1941c400391040d0309060389030140c0c003c0b40903003405000340401031140703400c440c100314501c915070750480c0600404803402c0021030000386244c5240e1051200d11500d8000400329911207903100750400c007506407950b0484480010b0000300b42e060181d1095 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 370392491 1250 370391241 370391267
    0x40e090c030d0c020a051503040c0602060f19090f031d0f1027030f0312090b0103060507020a020a03050708011508060604091119170304051f0c08121006 67
    0x501002c040541c000c5880150700034007030381d00c981844800110b03584c41b51007141c0000c03190b94010740c42c0d14142c03c026445240c954001c6080d50000d404001e04072110802070f65010380c0c40e0040414082540210000078019100001c0c89500c001c0741101c00d040d08407030300c001d0541c104090503a42c035001da814401d40f18441c0b900c6a805c03c1010180b01007a074010381b108039482003003121030500400280d400810503400303a4010744001a2507800c50050680c8002d43c1082e040c200c00051101c1c1d042a62000f200c00814840506065654808254500e209204166503103400400d2584016160300b0701d0f6031541c42c0c0740710f10181e5600c1d2443c281404441a48240c2c2240d2041c2c010708201d0f5108001c0c400942111401282c1d44800d101c0402905d80d19103070048030880740002c90907044c034200303c3d141c0b010200c0d40c40346001c66401400208140e0b03641000f11030f0080240078603100c2480d06c28905490502c04070b840201141004158035481131142204903100b85a803120440116540360402c0d20300040200c1 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 370393741 1250 370392491 370392493
    0xe0a050319030b0915040606141602120d180f05180c040b070f05011a0a2306160b16050d090c0807060f0306090509060601080c040305070b040e090c03 66
    0x803290110403800d10301c1880c4102d00300415100d01d40e40028095682c12558001940d032151492445401e2a11400003d0700a80c100305c1c07951895a03e03042203501948040003d4100e500101504544030802002c2d10301031000201c0d448012190009801580245c00001d08a0203008000851000d2454500200d80024120550303e100e00c000310950340c4c100800ca1511030340704000024109038400024400a806040c42a03000302144c9041030039a0030b1040540700c42460040e044045a5500c1074441c11034001d43c5008505004646c4c41d80c070018402c8904c1d5600803c08078400c22600618010004a84e01c14076100c085a0303a0748000d800c0f200c1008210100264050141c441c40b002c1c0c2c1e40c4602c44490141480306181c40d80c5034001450914150440000100c00503c1e031300c030064050213204040d20081c2424001458901c1e80c440c0c1c0c4802c000c000034100442d25010400356031040c0c0888000e5500007050301c40d03040d1103074400d01041e881441101044110340000079060440803030650f42c50b00c4018 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 370394991 1250 370393741 370393747
    0x61012120201060305101a040902010f18030b13051002270d0506040c08010f020f1801170a0b12010b032d0f0a02040c05040305030a030216020904050f010e0a0503 71
    0x620341003000400031020405640d0703582008000303d10200003080c2c1440d00342c0004a0450b205e00d110326040c1142100d40e90186040040c880c0c0140e8000303d0308241400e0500c3c04c50540c40015030500c064016551016052000000500c8a80021804014409806203049a0021512909e405c08038440d0104001d43d201548441042c200d40da4601a03c81d288010324443d010550303038845c60704010081c0c030202d500c03451140e800c02c003014080c020042d260f80317080e01c2103003016002c2a82903050311a840d51140a2a150104c0402980c05020202428040c1040512541c0f070040003d60041003264036051150303940340d01108040c0014014100c0344500500500b49807202c0101c040008e48a45400055030012545030320400307002048541198139610340108040519401808100e82201655008001c030402c011301c00b18000008942c0b03500c42a1078016501c0d901b49018820705c04590070025401041d2005000520400240300300903004440001c0014020b0b468031959641444040102903330414 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 370396241 1250 370394991 370394993
    0x408030402090a1b080f06010c020102030708030709080a1104050f011511010b12151303050a1d220b060c1213210302010c0315050402132303061012 65
    0x70510b410081820740491300114510340360b400708407801412130020b28600104a8598480341c150780d0030a0080c01e10011400c1c02d85c000035224800c0180c00b500c081c0000001c030f680c2622403031091005243c0c10044e030f4400304a52800c1700c0c1661445c000544541c0c01c1401250f5800850b50025040710098849541e10313130b80c542c030300391860b080403079403803141d55a00c020080a0361110092001c04030203070405049554030302c2c0c0d82c1c564455000f03449105c88114030f4140800082c3c224003114840c842d40e0403c154036070488582c0403100c03034441c000715411191841e00640c4110480181c030018041c280b030203003c103030000014050700e401450007144042c1e01c112080d500c0445410005c000070756110284850103515000c0503003405251081800b040b1081d6071320030f01032542c28459400040b000b171805010b041004610f8007510f13280d03801150300c02c80e4005261100780101030500710080005401c00f4500d90b0f40e83c40201300c00000072003624000d025041c005001c0e22403615402003501c82245a0042540c1e131 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 370397491 1250 370396241 370396249
    0x405040c030902090c0a080a020304121b0c03060605040c0f0806130b060f03071202040f0e090f0f010606020706020111120615040909210807030e0c061b0f060408030402 74
    0x50200201459562140350015886014506201d14005c813806a568140103000400b0782d00000c1c824101c0920502c24880000d28260213010078240e91301d8190705420f0740311449400d04628950040083c1c03004c050000c100106038100c0c0b012030760221410011944106030580e400ad0441802000007032a5a0000740a85000709070310010600c03081e00007410302100c03c0800d1031648030281c8202070204c00700801452607482640c0301480c112078182542800e00c1d20080d203d8000850282c10884074000700043c249503000c00006140080341005c2303070340011102c2d1219009000c03501503031005001c1c0d0b110100321a401402040f100008640a185c44c3c95140c0c000007000600141501d0383c4080c845801007605540300029001500b050f03100010800014608800001124910494903070711101c03d0711030340d43c0c11404042e03008125007000b08420102c03144403802d0030550924076901540104410320000042d00b0801030107280141203070304e07000c40c0040690750741c03404440c0108210340800c00a801810 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 370398741 1250 370397491 370397501
    0x609060a030b0a020f070c140d1a190516090f0609091112072613020d02060d1109130b030a030c050a020901030b09010f0b01050f090a030f12020120040504 68
    0xf01c0b400006080c1600a825054298402c4c1c00642ea030044841c001d01c2640000e07101d503840c0020464446140543d26961900d180340d2006068030418054000200c20440c000542004403050480421082c501801c0c2d01c403654a41070104000111500340c08030300c0b01c1c9110540ca082e94810345807004440d25291031100030b08441c8401c280c995005024156000000c10310031400b4825548417040140c021160050502d0045d091104c03551003e8014465060300f003500013030701c264060300c4640c03440d200e40c0007145e203501c1200c0c51061030603d40300f1a01400c610380740c0681006d0504640e0300003100400106442a515401c1380c0c5c3c1d9142d0010076a4400003401031940c3c0a20a02ca20140c4240d02c000b6000205025000d80c42900d08543c0b03101005161202031252070b207250b02d0000101306080c00440001c2c9a4010090002c1690000150001075541c1d1100e443e070045505c01c02a502d8a81d151602842c00b0140c4048070000d582040031403110009560082a038150039440e030541031910341400c00018203 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 370399991 1250 370398741 370398751
    0x605030c0d0e0a020306010608070f0c0206071209030b07050406111b0111070807090608011407080c070618050f160e0a050705160321060308090f1f0e01080609060a030b 74
    0x44140c3c032010b001601c0c14800303140205410b455020407443d00f014094005841034003048108a039003120070006a03124000e03583d02a400020742007016009600a442c5443c00e03810141500703030210304204049a2000c020f10584072150b540280f40070304010501d6840c004009610b062025540180003917500c00d030040b444440011044a52507691b41e40c0c807a0501c0c0321b03030700b0414916895550030300c10300009001d03000785076044204001062600c501c1c000c0604401801000400c1d00000780304040c00140d400c0b00300c030b49624848800e402100381c80d00d6940c41c1050341c0004501e01411000040d441c1040f25628110f80b0103640a080aa13280d028200007001c0062802050001c10700000044462007080048468443d4950140d6080908c2074403d00300c034680b100100d010b041c1001440001d1007081a40c034180d00903100800305581010005040103801e1480c3c0c040250400ca030032000b1035010704601070122007130325441d03450340b00c260030301c01d0711001110100d421241c1c00e2410000a01816070303450b808 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 370401241 1250 370399991 370399993
    0x3080306060304151a01090503150f1503031909080601060f030f06030f051e1b040c11030a091809050d301505040213030b1506040b070c0605030c0d0e 66
    0x200307100c4c1070000b1111000700c01840a00303414912801960000d80b46005450103d0041640b480e00310075258034020020000340c01c0c2d03541d840100c0c2d50401a6414642e035508020141e030b8039a500b14105015008043e026140003940510b000203040501081c2360341a40c4d5299035100201070480030560182000e181c015500355529040000401c1c4c045240c0c0000b00d1264028001e2884485031030740514400341002c004a4000c000c0800001d803800c05901c042131410303540481c141c454140309a68182c0580c1800344240400504076041940c000d0380d040685080f50203980b11043c18035444c5003159440f04005240390700144850102d02d0061040c500940c416030200301c56070741c2c083d03a5065090800010341e00c0f0301e5111400301c134a01d80c00281c80360142900f510110b04040540154030ac4150f0140300c017030301002d5248085084405c00404001050a006c0e00d40ca40e00c643e0b40c1d28a5104d40d20008003035030b400c0785044010912303c0c428800c0302d00070f0400c9e05900f03003800b40c050170307d0b0001d00032140800a1 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 370402491 1250 370401241 370401263
    0x11203020319200f01050a05070207120512041203110d08010303031e060815011a12040309080102130302040c030903080c090f100e0a0e10060f02100e0c010e0103020403080306060304 80
    0xc8030f054141614145126100902404502458001d080d660040c014000071800e1800700403039140d0000c3d0b00000c07282003070000d51711014107040450070074a104528100c4001c0006d000708085c8a54144450304521a03902c1c0b102525203000d81c1a119a000c90b000b4002400100041021078400e412290b484c02a05100104508030544c0200c11039100ea40980001d800008110402011409046004050f541c205e25040b42d550b55000c1ca40b8454410030400c41d5012401003000d051081c7c0060016203519002155109100390a482c581e15080c4800ca206905040c46118441e210b8043c8103500f660680711824107890340800011313250403251903280c01c0031356040c4620309692844504180078800303840d007517681c8403004d05105501c4c0c62608200b101e0720b1154203201c3c0360803d40501000b1a0014640035251310a02e5108a040100c84d16524021508125000b48011804120012814170903211903525100d030b000107505900444c070002d0050801880001c209082401c01140d02a12070b281c2082 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 370403741 1250 370402491 370402517
    0x50f0d0518060108100e0304050303030103030f050403120e0a092d0e0303040b010e10030807022704031d011d040906090c0305010e0105010b16120e061b06011203020319 74
    0x21500d030099010840903401034122045107840c40c8181c006c584150000345240c035013080c0c0829924813040c0f0008080007607005142c000c1521843c00da4029581c0702203691a281c20410004004070f80d030401082c072842040030f0004105000d80b145400e0b039000e02540f6900c5080030581480141c98205a16043c01e4031400c180e80c1c1003034240011031180d442a06203101c0d075410003c84503070442d401803c0090340000600b0a1002c038160300d06881600d54100c449002d40900600c04000c02d480141c1a42825800e21082c0703c02c05401116541c00784070001440c8518091120046503a40d100c10710891061a40c41c200010340d0400f44c211003001806448042000d02a955418201006550040d50140d540d03020308428000b0070300038203004201e2006e52500384860203488003000110202d00910313010710340b0b038041005070003103c131111000b50040c50316440e4003620000c1d05010741003603035014142c0945400401c59540e4004c44605458040e801541402c041e103401c2046120715180080c01d004001101c0d603 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 370404991 1250 370403741 370403743
    0x10f0207020f220c02010518060403021f060b0406020105070f0e062d040815090d1b03090504020c070303030b03060906011509030804060306180902030c0f040e010c021c050f0d0518 79
    0x119400500e171340002054500301d10003070403d0007454144c4e1515044142440046a80042c82420001c050364500741c0512842100b10020202e42d4459880b42d0000300d00041d40ca501035002c076208030029180d4072040c203c0c005080300c0e601c28000d000c55000c1c0050107004030f040319140340c4544146d40309200c80709800e00c610f60400181c02c1580482d0f15548181e8514003241003400d03d4503040754940c1c0041c45a6000c00d5006800382c90520074050000c9600b00c500000e062080840100600000d04110b55440400708901e07161032043c0000e4000c0f0b400c10341044064100054410f02c034001003c050011a420400c0b0fa00b002015001d2000801072829800b00c00300e41030301300400003480a6240018251714003512111202d2403041d803040701c145400b4401c402f58402043c1c050a0070b10440f00c45492031108000500104140d03954004036620b41200060590b40020f17001020f00b001495007452a981403008079a00c0c411740c41d4101c518101882290503c1c0f0b15504925001502d100004680072050b11003d = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 370406241 1250 370404991 370405001
    0x70f080c01110f030301030609111003020c011a09070804051203091c0203090a050402090604031a061c030c0f080706090b010e06040213140406031704050102010f0207020f22 76
    0x851519008440150001d40c1c10619606a01d0074950207419505010075015440c1d010510000e801c141c2c40d007510b4402c01c0718005c4c031801c000c0740c0117044404640105100800035000700720300c0c030b00d070750700c1c0c00ca450207040203180b184060102c004119201c0c664418404488504d0b01900803130380d40c410284920721000500e00614810f500d58001000c0310194003900381c0041d0502044c80c01507410401103040f154440700c0d07902c1c0030744a0540c2c5c05681c03990510f021540d14440c9504c0a005c5800c00349400050f40c0d84400050f0080008071400c2c544c400007941c5d41c42d204180140700901003014cc0e59548001400902d0004055001e42c0c20203080c1030007a110081541c503d080111004c403450001444000038501c00c698100c0c2c0180c2d400c40c104004900d408c40c90342c03124040c2c0320222000302001e0307601c0d41e2280c01c020080d591001c240e05440c5034160031501c01e90054083d482c00f55081498411914000d442607640c8140c000b0186800540d0010a0241c000c9109414404240040c420201074880e00c3c020 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 370407491 1250 370406241 370406249
    0x70512010e070e130605150d030320030708040b060117090c03150705040b0d020712080a0b010518060702040e01150501080f1b0f1306030b01030f0605150705070f 71
    0x1044818156400c0c1c0d0402c051500403020b0b070840701e014030500980c013405035110243d01800025842e21000100d01e80c400500407000d6101070720307031001d00805505401502644030300c2c222b60355a4204e0052010384901003124807100007401803000401060028045680054041c18546407803040440d40d4403500c8800c071020f91242d4042c85d18044241000c01400d541c10780c904001000d02d00f0320110040082c481c071b1007605100d0401080b045100c8045504031040d07180e200011103404016a28080c0074110226180c0c1d0003103103007114560540d40079100301c1d4070081c814801a00461030031000c000c200c4d0000d6a0036600203070b0302d501c0b41e915480244180500d10140106480c604c40c504400107102007801048800348100c40014803080051110710707c0b88000031500010f07180c2c5407000c208074280c09904c1a00d003600240c8000081d1064050340003d903041801c1e42c0512450b0484c01000e0203450080c490716402015000c0f8103800e10480740b01030403000d4429016124510340c1d64803c0c070000020760308 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 370408741 1250 370407491 370407493
    0xc15060b0307050c06090c030606060703140406030e0f120f072406090b06071101080405160b09040605100f05030c0d0f0507031b080403120e0115090b01110309040e070512 75
    0x30300c1c4241c09002c0150390b80c03000c8900d004011f080d288030086500c88901812250203480301141080030107000b9542d05080f084902202c6880c0c0741d0b120030040161012030200401400f55000d0041403c00105030b58681d84000c1507124a81000c1d100006603a0340000003c0d034039048500024100c100300c0d150b1a0b0070b0071400090100310107080840100c21185a43d035103e1198904009907000035101c01d1001540440c2401d18100640c0d85081a5090220061035209401e83d409030110b1040300c85806001225010740781003050035101e009100154101c6214000850554101e400c405440342c002181d01030005184241842035a010321829282e03641e00c03a4034519100c408005101da030503ca50b1115000d100f4011074030b0b5568440c0170b0503406001e04003904001c0e03805818070b1034450315084100000f04010080201d030410564070000c0c0c4095004440100d4100201c0d40069841018507030750008480c2e01940c949425081000024110b4604070100c0d4014000c000405a840d000d013030454801c288 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 370409991 1250 370408741 370408747
    0x80c0f07030908060c070f08030901020c1014010b0a050d050606160f12030b1c0809090f07140f1803071505041403070605030a0b0f040608030403021e010c15060b030705 74
    0x5001e2a06006000b071020040175428400980803d03004c001303c03400c140c1c004103c69583c0d00c4405291340640b01d440c0c0001344a100c1c80b8501c50300c03000154041441c8c004143c800d000c06036210594039070301c3c2c4112a19000090402e01c00100a04c2550748510b41000000340701d51b103031200619040c042043c0c41001580c5010100ca000b100f801400d92541002c007000d4038040140304121000a0303c056600100307050704407080041102082a890b00700c400c080380080032008180b43c800712142d00c1c0a81141c00e40000307030880400c00d20803805001030303890482d40d030000f55081030718501100040300c150a501d260f1520030044000b44081d40d1003043c440150342c0790754099503030f810541800c0c0d602c1d040800060007035201205c00c201d4554010305a9030010b000060102d0000180e01c000b50364040d00b0854164068501600020f00000020081040303030302c00d6a00452a590341d006064401482c1550304d0b010a26101c2104001a42e29440d82c070710340f480d000d0029000740c5410014085810071105040464000 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 370411241 1250 370409991 370409999
    0x5070221060c0a021002160b0910290d0503030a090302070b04080c010f05040f210210120e03091819020f030105120d210b0303030f040204050105090403020607080c0f070309 76
    0x52142d48000f0a00d000f05600c7c0c420700c8201101c50030aa0080035202c052079101050744040280b0548480711315507030f03007403040d40019002c400b071079041040c24019442c1c1301c28151f81241004610710101c1c9800101031030469440400c84005032108081c00c40c11070285040c041a04d5403540d0203003001d042400d00814a1024100025021004804d1780301d05125085c4010021030b408030640e03400350b402000d10741d018400042a109400024007000031350016107049502d540395403000004c0c03c0b503c01d144007840f80400350f0140d241c40380700d80d58189070000381e411130001c03500240b51a040d80007010308443c000012240c9025104036001b4500e13034400c9081c00070041085140811070f04211526250143c00d1740d45900340f0142c008401601000d00142100c0c480d0251010b0642c40090f042401505481d52841e000008015a44c1d0448040b442a49440e0000c5100d00740361225510613a0701d0f4004228503140d9031800e0750341c10002407980c1256081008074203240d805c8400a065414800c1e11031800042c01c1c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 370412491 1250 370411241 370411243
    0xb040b0a0605120c03152505041211190b071e0b01090509100c021020040303200a0302190c03021c0302060f0c1b032104060606080705070221060c0a02 66
    0x103c6212900354040300280950100002440a001d0318844070101c07d0070400d840c03c0d039503400b4941c0100b009284100c01c01090103019010f80c140b00e0000c407482a120217210000b81e0354034042c1d0040b0400310209020400000d0f910712160818880005a040d0b0208550b036192010b00e0000d030800d0310130b40d440700c0501110b000100003140800002203818084080065802561640080000141e2a0700c0b515001001c10782c44080d98000344030380c0d805c07036901d82d03c03418098141074041788031000405000040d00b2650602040f14415540d25038082d180c07000d82c0d01428900140031583c10303182151486400001640d4501011081c2c500d28004c040d009940f030306002e42003240080480c012420268100030307081c9030410171a5080b000c10032903c125040d0310000245107029035081d41c40c1411140c20600300349401e165860b44160300c20201448210346035481128222403e440d039034089481072007800014502900d00ba0024024551401040c40c100000c8924001050b502d0703960b40c4400044051000344c1c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 370413741 1250 370412491 370412503
    0xc081c0e1c0e09150f15090a050303040501140d0b031507081608070507081c0b030d0318060b03010b0d080910030e030a0f02070e010f051206040b040b0a0605120c03 72
    0x2003603040401031140040b01103400d81100a1019180d00b402e40006543c5039120140d07162200b02c01340200814800e03485500300b02c0d51101c060180300b180340440000c0c10f8640041210203441d8180d4541a8409011084082c150401305002d01d038282c54100824058504014910302050402404070b01030a04a901402c640b9026003079000080e100c803190030700c0399046112150084141d00e4601d42c1c40304e50742400e12050154414020804102c220501403003043e94005010511085054500c0c454100500340e040302d2150180b400c2c529440303c2c04a01280036903111081c9250042c00108040d1408400a040d106840780c04641807000800c05901d281800c80b00e03540360300d101c2c0c00c08116074203c14010603583d024030f908800404c0800002d00a105200b8401a401440f0380d0716000f209584511004105010034016a405241215500000850f00150b158041c54101d20b65a906441d43d403202c0e01071400003080c401d850707500e414001403680c4644410800ca9021100506004d046001c1010705100d = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 370414991 1250 370413741 370413793
    0x60a0302130812130e060a180b0a171603030f0806010504050613060908070b0708070f0b01030809240d0c020304050d060902270f060f0a0909050106080106060c081c0e 73
    0x282814007048016254442820142d800d0231a401e0410042c0340c240102500704134000581200c0941800541104605a902003507a9901d05a42c8800e40c85640b2804400c2d2520001e40060b031440e95444200e40100300c800c2d045038040c5000c614250311240442c015034804503844100b44d510b40d80030841264441390940240c0341c220301600c5407a00c2e015002c1c02c240140310b0040e086c000c0010303040d01040f1501001080c101c0d40017690000301c0d03030b5a04054003190401e03d00e1601411184070090b01d2801d44d07850300400482102d46542c10401d82201480003420301820741001c4d444200f002060503684c80b50304800c4184640b40100e041b800d07074070600ca10044086180250102e4400203003407602d0725a00720b22f0380701c3c1c9092580c0c585a40c80350002a500c40ba54000641c0180071000c0100c1c0c2200503802c0714010038010802801110f81da2300c04642241e40502c2007c00094941c0d529400041b80d801c001d2000b0707604074200c081c0300500354400108603030a021000310250b109024001540b000e10146c51195 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 370416241 1250 370414991 370415009
    0x8160513080309032a1903230c010509102f07080f0102030402090f0a0902090c0a08070c17280507030906030b090a0c030905010c020d17010302060a030213081213 71
    0x700c0100e50b051140c400b400548603101d5903114030001b206c90140c4080f07034021038002403102040854071035030ba0006910350b580750701d80c1c0c0500b403201801940035078101d900e200005842d02565009480b01102c01c507206420f441ca004003104049008101c2070f006603261420200c01030210207280085452070300c9801301118050340d006000300400341e515040d22583c003141c01c0e9078002040d592001008000c0a400d50b0003540444608184000b069415020788544206502c458503a92298001a9181c8a00c418010726020000036055481b80c20303d0b014110480f0f850040100031441c009038111000c54500e001000100081216030034580c1c0018031400508290500300b000300031040214481c0c040c001c010004458a4510031803c140c400e034422031100342c005008102a02c19000000e4540b083c4d0044179000504041804604014503484141241d40c0104050b01e400410b40040c0d020390400b5a6010304000c4c04c0c1c10019500d5000c0c0250040c624503031110399940d000f11044455601000c2c1c000380c07a6 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 370417491 1250 370416241 370416283
    0x13060f0905190501030207022101090b180a14160b0a0216060e0103090f020303120109060801020c03070204051806040b090d0903080a030b0a1d090f0d0816051308030903 74
    0x1281c0721a60b40b40c02501c07020310340542e64181a0010401581d40305c0071100b114441150501c50204c419480b6441aa105810050044e140c1d0505031907400c1c50200764111580101112000041c03e1204025804502000380d030080d041e07075107546440800c69072041d04018000241701ca9815818419008100c1100006900c82414003000a01c603941e41c100e03031812315685034001010300c000f00d42c1007542240c2c020304076560341c00b01d10080d40d0030b90703000e100307010308070f4100100071130200418020f13104a6041803005500303103034407074081202520303010301007561984502041851001042c46994402c601441d43c9029a090031806946882c000c0d00c0d41108002c40c10500b440003424241c00c031007411903646000300d1800c01c0318001940400083e400316122104035404202d40c02c00701514140f003090504140d820300407070490002d4a40e603c1030f0b201000034800710001888504442d4030799800341c50601e860350401c02040013180d1006860380111100740c1c00400c81c21041c1c901000300c69a50300c825002403407 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 370418741 1250 370417491 370417519
    0x1203040812030402060409060b0711030105310501180b0108060c09130b060c010906050109360204020d1d120414010e0316150507021f020313060f0905 66
    0x9150380e41c01480340074861000000c50709540d28001910050011244104641a40c035000480d10342d129070f104503000a24440c04680c1031070b041c1306d0325101d0142c030314401400d48407000c803658040902a100c10000364280580e00d01113078092085c04400b40040194803a80045401c0900c4010f40581c03150166902050400c82401e41100a07101400c5050340c400c203010602404800181045200503a0041c0c80824030307004603081504803100301c9020b0a81000141d803182a40810750303101c100385035940441c440f426082090424804000340c050310303021841d00a84c1d80d00203020b030382c00002c240d60580d0316030504c000300c1c504050004620317a8244004000402e5900500d1103030340501d10500c1c0840207450501d00403640120710003140d000300241034800200900500b600710480310b0145103105d0800c0506030341910300036800c0f5a04681c004049003455454640306c1220071700810f0740b04d01180418407401549003604103000c0041d15494803541500f510b544d400406041c07071680864072801c0d1044000c4 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 370419991 1250 370418741 370418743
    0x309090114030d050904020d05161d0901060c080d0f020717160602030a060e040b09120c0a0809220f24090902010c050a050309040c0c0b061009050406060e12030408 72
    0x2840f0301218140507450350f04a44c0050f0080c0100351040300c155080c44104601e21070804502c540c28009a240c0e218032050340308182401050a0b04520f8102e0005401400024014045008030360300c0342a210b0b181c440419161020350780880400e2011607000301d1484100403e10464030000314140c4016403c19107400c22420b0140c400c00b001400e03d6900002080c3c1c4e03210540c001001a180030440b050740780c24180340241032020105c0d81c15005015020f407468650720302d00200d038050203125005002d54511504c4d580c5e02a84007040080e40032640c03841454240080b20346e229102c0080b81c1d0001509980c001004041e02d090802c050001c58541e00e908101041802400d001d5680c0040c0000780341c010340c8011380c0c15003c4090003404610550f003000e020071038000f000380044030007940d0a02042c9120a000da45d0003400c40700040183c0344003c00109642401d000c0c1211f17034506440c0848449030307103a0120341110b61540121000071800148101c0c0c0303060988140d802c01143c60001c600e0685040d82e05 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 370421241 1250 370419991 370420003
    0xc060f030a0911060f0c0f120d0c0221130f05130f0e030705250e07120f0c02010e0c1f05030415140f060a03050607121409030909011403 60
    0x124001d0781d0b100504188045040107022903840074190a40d1200d040700c1c0c440054104c8912a21544240140303d076050002207088150840403014140c1444410540d0743c2c043d1182000800031031240b614a541c40307440100e0300c4855980646e0245540c0c0040171000c0203440d16607000489150a40c1c02c1c204140d17200c1b089000d95070b1700c09120001c0c1c800c4501c2c05240291040308c542c20582d100104103803050100106840c50a984525074100a84400d00c0746030b0346c0c1131003920444105d904541d00045565001c0c09178141c442700e09840002d007a000c1c00001104441c010641c0c1c20060303644080c07440030000c04100d000b1010b00c0843d180b0b0102d48240d10304040d550b000500a6040120200100e07081181c20340e40c13210001c4000d4420720040d510401c002c50043c0c41151203d0036501550003013065401c2003034801080d01c0d00000540700560341e20000f954104001010500d40544d91000180602c181c002540e018045e44070185075540b07816002c0150b20841070308212202e8142c446061103680d000183c03 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 370422491 1250 370421241 370421251
    0xa171006030c053a0b030c01120b0306040804090b0904050a02040b01180b032e0915080f0d020105011d060f04090618030f030c1b140d030b01020c060f03 67
    0x810002110002110107008640384590316000d101d4844c07000c200420881e004008021100d403651034400d11221066804002c0f5450f050b030030408560400754401c84400610110506001c502c804100c0d0100380341c150200d505440303c41c4040f50034488480507004003c4049070445a44419003055180c083d02c4440050000380310b1303551450350b44101d9014103c0720780c210b4900d01d51506032030354071080b0350a15030044030b0208007030787c544c020810020301919196600703a4200042044550038180804001c0902c40741c00699802e104000045502c020007a14071940c0d0120003404070000d040c080a801d462041c0c0201212903c00d48141c12921107400b4050340c008800c45001032544502000704004058035400074045600305004104012201f4100d1130320603202c3d98849012102c0302c4012000c41c0c19942c07080e4002031941c0c220900b22082000300030705882c0280e1a440810140341c0440b8900340132240c1e91002b08e82c5511140241d5038051140c455070b403009a07019440c10071042c4882c1018400109 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 370423741 1250 370422491 370422497
    0x114041205011805071a042d0810020c0c150d021c02070b060f010e06070308060612090d080a2d0605131d0f1c0c050109080a171006 58
    0x800c000c24000c09410910500182c0242c180c9064030382c0c20420740700c0d042d40c001e0200105141920b01c1e4140c030400c00321070407641003013544101e622200500c5094410000d505010501c81d001c00401c16460030712001c02d19818620005a40f8142e0810090074145060b04403442020707a406412110b000c100d0441740084512500141c0d9081c6c4d20001c40c40340c0c2c00d1204560940c17880800e07840304100c04108814007c00702164202014072801c6d004450070b843c05499140c000d9003c0c010000041e00070316a0680010f0018070709424501c80b1000c51610500032220420343d40e20035101d070802550407802d0203030044005007080c000d0b4a2030b001c0420890000c901001d07000601ca01d900c4101216550000c00541002404200f85410fa1025035003c2c00c44c0344800d0b00810b41c3c5a03030014141e14006820340b100490003015022031075521030906290f00059103260140080ca54113040012828458010210b119040c0707191103820b6954010041c0c81d01c81c800000300d040390000d021680307442c44e880310110303203484c0307 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 370424991 1250 370423741 370423769
    0x10b0d030f27090b09060a12030212130302180c04030b181510051c02100c0c03050a0b090a031d03030408031201150206010b0d1107150506030c011404 66
    0x52021922201c0e1a04092402d24a070384005607030720350125807041116601041800950040b03001c018016506640460b88448204010007220440300c0d0700048850090051b0b0351803440000508926a2250104448801e08000c0034801c6140c1072620f6050b89a28101aa013180307803d500540c0d0912440c00064907029800c00000c515144207011062550485000c2e0341d060200300d05040640b4034151540d940d5030326001808507060401d140c180b80c04403003148441011041c1a000e00c10a55005090081008541c040c42c1c00401d003050000c1004610a000820581c6c200703040102a98002030441303074494204400325008030b50b001c1c04c45042081300e005407089540d203480002e4514030890f0300c600918040410302c0030485d485402e81034101d40c01a00e268291100445040780c40d41c40c24051486546028049280602c8895001e90390590052040902d400100d403a5410401c5401c402054142c5d112010041542024003c0c049011400c1c20140b180606416402d002402203003d05507001d2010 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 370426241 1250 370424991 370425017
    0x705160819080603011b050301091a03070f030b0f01050d020906011214060a090603080d0c0c0b0901290105120903120405060906011e0909020409080a0c05010e010b0d03 74
    0x100e0403506012600801440128000e2002906000003140d40340c0c4603501e00766181038649240c010018222445c0e03684d10303255a007000d603440000c0c003903e102c2c2408c1040c090451900f0307480802208010b03144c06d14406104c20314600c0c00c000300010040460305a4904040104181e0701c03000c00900203198116200f543e5079440310b0040394031080c03852002c00b0643c20617408120000410768041d00901080e540114065210ba9208050390220f00c80200302600402540340d0b0b001c2e8681c0003580d40840c1c9d00e0016582801034070f460341050019205502d29956030544c1003410202c038401c8603040040c02940c211240c4070713107001030001c1c000c22000d0301094140c5030010780e2103003040c003c80b03400d025091086041c0d401d281c10240e80d10703036044980c0c903d20701c1518008508822821082101c024540103110032050600503c3c4000c0c0c0704804040740c1094070b445d1000009294a406481842d51590320495044861704040d4291003048032002901d914100342c4082ca500c0703030b004482009030103042060040006c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 370427491 1250 370426241 370426253
    0x7020d09120510110a12050f1305071a0408160501050d1e0203040311100b09060f04022713060302090705090a09020f090405161e0210110702120303070516 68
    0xb89824842486151101c4e9522030300c411005000c003058680ea50400b030400000313541c3e044501c183c03981c10501c001c040c002640e240c104100b540e0000d104030161400359a039204c000601c010001205080800b000c05c050107202d004100c20a501c0e40c00c9038184424600d03010000e8154071460f402180101d8071a40621818141880c108000d105a403034210754920f007508009218900c0017503c100140220510181903509500030030018010003044c03046d05407110000c0000f45643c00c00740d80c1d0040c1c2c0034821180c0e00075040384011000701e41040c04010054012040285400310b6135100600107103000d03000d0015880700108950320039181d0420950b218a4000041c51a0076550300c842092400001c0300c29541c0d0036131002c0c01e00c445050780c083c40a6141d8281c0c1c0b000341460401000c0002d5046c1c202003403860340c00f401100004415005031200705044006810584125141030340c408440010181d0071801c24084148009440002560650520810081075841208414000c203030500041c03500b4800 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 370428741 1250 370427491 370427503
    0x303031b0307020a0512040f050603090601140d02031e07050301200a02010207020a1401090906031208270f0607080108100e2a030c060f09040203100515030a0507020d091205 76
    0x11700b24080b2007100e00c90914001c140d506c14011000c41c00c014213000149401c000c004d59001d0010040039004c1c50703003011480c00aa82048100e10340c40b0030701c0755005001d42c13030900851500200b071692952405107026a424903200d0303164015030180e03241401100384490084010001000d140702d0040c1d4a080343c0c2802c074068015440041c2d44480340280010320140c0c441e180c0d96061100713032501c00006940c1c034403010455505100c043c1c44428200a03040100784152183e0703074040301e06003201e12070304d100020a10704002d400e0000110b60b844103203100c1942e001040441d17444270603894941c0043d810020043e8071842480300520703005443c2c8044c0c42ca6100140f1051004424003111040a820343c1302080140e44400710105002c0d01502c005800c503402e1100888010354509480d05150003031084c10b0000a40c0004d101040840e00f808012980b5500c050404d0403001c500e2101c1038490502410400072034001030141025944290780c0b00740d00350303001468101160b664680c0702c0e205c628982001c0b0b042803 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 370429991 1250 370428741 370428743
    0x6030c011809020a1206120804031212050907050f03071406031003051f0c0903030e0105070c0503010905030306100903030f031a0306100f0b090f0d14061003030e0303031b0307020a 79
    0x60f001142020040e6480380310501203c00900003405090398a410803483c0040c4404003504010b0108418800b0802d8582e4441410b1000d1805840d60301415842c201110b806031071030122038025480030829450700c1e50f500020001d0403000b07000300c149000403045401c1150a0307424002d04011000070038070308101402100644c1c2050540f0b541642c01c507001c81c50310403003400b54500c2c11300d41002854054070845903401a2581a103450412a041303000540d1203070051a4221031510440f000132078592020b002c1c042c600c40c40344009540300d090401c01c0104a44042c0daa90081207164a41040404c1c0c0c44441c05400c0f0a150034001000c155101c544540312103072815080d0548a84c1d4280a500443d0501900443d0b0031084904261501c510010f16540304105011303901c9142c2c2c00c0d01c020f8a20340100340d00050b0384a43c0407500c2c00000907252a0400c0800c9648140c240c0048000b0401d0507044202035040c1038040700503524600d0810340c2003040c440d29508007000c4600100000e05c02034002c010b1000c00d2 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 370431241 1250 370429991 370430009
    0xa0e01060c03210930110a1a040308221506090c110d0318080a051303030801030b131208150a030f150204150e01020c0d05030910050306030c0118 64
    0x401e84080700c031004d0006000100c40030109451080040a0900c03041a096980120007002d0b04160480440c0d001c202c10030b1095081c000d0060313071000281c09280142040c04074140301c1055141a0402922121000300013080051b44486603d6001300000200055181c0c05280d0424240400c440a0002c1549400a0580c0c51500d00d0907020b00760050607107160300740d0303d00885140e07942240f021029191090000301110496104140c002032202d00984994285413605030304290410700b102c1203191043d8000e40102c0c64110040c42481122110b042d0300c1502142100c00a9a490340d4584610102c0c400c0b110420810201044404c0c402c402c031000c660300b0040444824039141d00b000c40ba03031004200b0840c0d071800712202051400c121402070360211174103030510040103000a107040d9059410420b0007411030103000c2044c0032603901e10703083c8003190340a07900039616014010144001c0d2070030304c5030384d0091080600c2001100da80003f0b0350307105c201c000c3c42d150b14080f120a00440d0070f52191b810290b40d0b = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 370432491 1250 370431241 370431287
    0x30409050c0d1103041b120201050313080301060909240b030a091203150e040c0b0d020405090a0b130504080415140a03050405070e04030f0e010c0501060303080a0b0a0e01060c03 78
    0x72400403080607602860056003404c036a00b81c80300e0028200d54031b03440b038040500c0030684001e01560094000e1030340000c2042e044c0d827000c0c0141e618004298401d030814000b1400c026401d019090300d51144c00e041410200e26a5100062282074940d4500b09209404140800000180c000d14261700041007541c1c0c440809051241118009409000090f94104d1080601c1600042ca034980c2052640100d401a00d14826941018000c8031541e020031100f01450303408000001d081c0c0c4440400f5882000111400100f190b041004c02400e010b106508580c480e0a142c02d110125102d6000c480884888070001c002d400d10500341560799012820209034000c1000c10400c003c079405800a0748030300d11070f800340d5000315104d81c0c0301c801112055502800007030440900c1980d8a00400b80c03410b403400141000140003049958040c01e50320131f50003c60004403200248a07807400c060182e101c0d40c840403140c4a800768203012480c2c5a045051140c0d008015049031820241801030101011820310b049401d00 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 370433741 1250 370432491 370432511
    0x7050a0501060b0901121b0f020703050d020303040308011d0a0b0a05130b03070f0b0a0302072102070e0a022d0f0712260a0c140a08100b0c030409050c0d 67
    0x210303049841e031540485c00080441785030041b5880f81031903030410b02c0c10110407610031442c12104a14442c050700158840c01c1808001719074100200b00701100315a00540d541c1c50540b5004100350b0b0103921034804100012000b41664821025042d400300c49201c0002d4044c4250000881c2c02003a6405079800806074401030354050002d800000c0e40d2081138045401042d40e0b0903001401c0f84580c0b244445d041402e1107180d100b540b00e50000c0918a00441e031103901000300388100c500c1074160300d2486001d40c0c4407210410460800c195610382c000c411a80460074281a9208251000415000380688510030b01a842c409100a81518022002c58900580b11103007460600c7c02d1801407034041d07000c10001c4900707120000c1c100403040c0301070f031986169401d80d45506c2206800703084000400c07814000440c12106c9441079880207400300d00200c0c0e450140034100285003414100d083e030003810860100300309200942e01c0000c216811181c2c0d411001406541d4840300c24404c1c00380b503503400e42041c10444454 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 370434991 1250 370433741 370433759
    0x30204230f2502060a1103010b031b1c0e0f01150b1b07170f06040c030b06031e0705271b0409020a030204031a06030c1e0303040806190504030806040207050a050106 72
    0x51281441800410400d02d806c4460100c40c0400d120390001d8040400008078074071641041007201410420b03886050042c00820b03c40440708c00914002000d40e41e64401e8803050041000a8880403914000c01c50000d400c40003036030f011424082c0049840000038807207009540e400381d521452000d00305403142a0b482c1c240040941c05400d072031a80c5da100340c92922000940105200d4029a030040340c0c8880781c2c2c91640c821854001c010400c5074035006000c0d0700199401589000710308030032250041c081c0982060100410750100b1201245030482c280031080900380100e118542140d076040c0c00312141203000c03503268120300c110703002080c1440c00403a01034061a05030b0040c005880c842c40f0a03680d4842c81480707030840240100d4015904d603005900c0380e0391605107801d803640c5d02861045d10703011015814012900e581d003d903005514541c040030803c51504608065002c204040f00c1c0d00b4040d605103603c00800d10400a00613a1040e980000d5210800c03204006448096501000a1252940e43c0c0740704 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 370436241 1250 370434991 370435003
    0x151503020418120219030c141203060a0807180b0d12020d0e01050a0f030b1504080d0f0203030403021b0d0f230f07030b22060501030204230f2502 64
    0x125408404840e43d042028008249070580d0800521721211400d900d4408850101c40c0d00025241c0040040320140d045c0400c0c4280c00c481c3c034004610a58900f090002d2146001c041c0e8022211342d0001c1e00e0034010b2204c601c0c03111800c2c446140c004904541c0d020001503640d189100c00400340b041c40d01d00140b80527004109507428a24540706c10b5400504100192000d04c01c8504810004200a440c980e0301402a48004004207018000083c89000505c88104daa84950441e0324035070700100c010480d05502c214500000800d80c0702442c2036061030340d07019540f0007040d4040aa0145007001100d0152101c6d51808a11500b007503190092039002c2c2050007201d0001c03a03412082030402502c103103c0090004800000314200001000c40038910707200c8501d42072028200b48507101c00c0c88000d035524040d0300000d0085500603040044c803545944108402c4419800c0404090150812a4420356000001540d807015103032111007650390380e440501e05104d65014a003c0d40c2d6984035000b0940980c006a1 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 370437491 1250 370436241 370436243
    0x4140103031d0a03030507060e03040503100b100f0903110d0213140f07090e0a0f1407030605040603120305070c0c081e01050408030615040503100b01030b0409151503020418 76
    0x80700440700612050203d42402400f0150100f5030401905001541550095400c0381c5880c003070302e0070551210000313400d0400401224207516141c400c16034040c50b251900820004071030801428014042402900c064240d02c40600368512801d041040c0e07445926100f81070301d900601265030503540c0c2403200c00900004980000e40c002c0c60700014a4400500d0045029a0b0184c0390131104614041d90102c0701d500c003d100900103034407200d00c509000e91f1782c001c0d00d2140e0490001e481e85031414410040845a4a03480b05108a040250401c08140d031205140054036551034003080995600805842100c2d500400a10501c04903000103000c82c004190301d40c0300980c5001b400c41c0315000514060aa0310f0596000d81064010008104640341141c484482540b0549810341090b503208002400c022000440080740d80d103c180d4202c40f5a4584510b003e940d100700c1d42080b030a185601c5458180c5420111451526070302c4c142401850400880b0754000c5500401c10b1051340080800c8035158070702418 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 370438741 1250 370437491 370437527
    0x10e07140a0332091b121203010620060c07061109150307030e0604081813051504050901090521090d0f0b09030406021b1203030f0603100b060f07020414010303 70
    0x3c041140c0d94000310310782c01d20f840000c10030306043c00340408101c003000d541000130045200380b0b02005000c04c801c101460081040341ca03220040030382d00c10450381000d10340045041e9034005d002085140040b4106980702c41d6000040040c0c12600e052000d04940306915009900180005625030207082800085225809696040c401c0d82d0468a82596814054a00810f009010700c40a11a0030440100e02038620004140c24010001101c4400845205440c140c44c2406c12802d00c05190400b0f008843c3c204441c40020806c04040744c81e01c0c1c0d2154000d02641114980f000910414070300744d401541e0025100074180e0b280e6190b10710700360540581c6401c0440342060100005000c4c180c001c402d95046400703d8000d03003155040d079070400842045c100116544904605c20410001e0001c002640c811007800b6a4001d550600500305490603448020001c44141001d07030954864481d141500c0030030301d150117041d8413100b0034400107000d00300c4581240e994a00d424000000d041e80180c40034903442c5020 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 370439991 1250 370438741 370438841
    0x20d212904020a0c02040b0f100f02060606070201021b0102010e030d020c06101203050705030f0304240608100207050127030e09040c06050705070317090306010e07140a03 75
    0x1000307000603402101c041202061340242080d0150806400c58074504000a08110007803072240b0004001e450910450b000003a620350450280b140c0400100f130300031800301d500e02d06110a80d40004c0d40ca103a184001400c850040030580e09990003504800141100d04003a80d807a0003503a0f0344030300203400042101d4079078410000030400c2200c05035401410f440515520010300141d03078034152802e60000308110707898803003000f138030503c410900003075801140705403000c40603058034008071000d0305040d40b20100b40c80d142c4038003000700780b60001d02c106845c0000300f000342e101c42d0942072a50040290b009408110124941c4010001592211148845120761101c0c000103800005120b0200000c95001f440c20301c1e18601482424000c01c05025103901c00c5044440507600c0c1d41d100341d00d288492803841c60001003ca4044490316090000074094140a0441039480c5081c400c0201341000012205201c8000050b60802051280e0018607606082c940031400a5601d040c03140740c1680e0038400141da8038141 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 370441241 1250 370439991 370440071
    0x30e0904030c02150913061d0c03011403030c01092105070f08250803060310180b100305030309060a06060c0b06151201120c050907020d21 61
    0x406086402a50503a5034042e0340c0b0801c0d400d01c4011280309000c200710701000d2041554030b03511358009040c00744d009070780480c1840c6001d00440807180f02c0290801d446402900b002419240c220030f607411074112420710103056036403002090462090828015681d401d1421020512085844e891501d881d0006042d1007036046c00305c1101c04d400f8103200140010104181e043c0461400e80240442c007060308500d000384002c82142d680b100c498084100c0d85520084100120751400344000c940145100e0340621198040002c40524903205844c000d103120611004282202e24070001074000e1640101120f0340c2e400e1800807240d440000700c6045a20a05080b0041f501c01c1c4507130540207244d035000300016103a07110300e070030407075405071800d6030b440440000c0c480d1209401d000300500c0c0c02001001c08040b8500810308210706640308981150303018140c1082442401035001032051055580c9142c4000310000c010402e075801030440307200c0c05155040000c48042d400300400360092143c064005004000d0382 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 370442491 1250 370441241 370441249
    0x121b04060212030601120e010903020601141c24141303080610050d0606050403060f02040e011202060405181f060203040512160315060f1208091801080109030e 70
    0x2203015600050300148400d045001d15080039541150050400318140a4582d1211003101e0700401c4954035691200c0f00c460901d601448841d026101409002d4000707407080c40403c01e02145818462000f070a0309101e10144076502003a00048482c0c543c9017000d02100a144501426490005080403c0d0b0301c400f080c2c0b0410030302d0410b2034040d4940c80b5561180c0c0c92408000041e5900c421030400e00c4410852a14180b0082c0700300009002c6644403161540d0460905404441e114040f04d0800d43c4104418000801c0010a1034119003000c1c80800c0b50807150710100b80c1600440d03210a800c580c410f01c1078640e1300c2d00003414034480d0a03121811106400309520300394401c02c052041c40003680081105000070700744241c10b20318101c2440110f8282245603400c80c00002c50300d03403040d079031f404210102103160101c0c2c1c000d1340020280448120252070415002c0300c001d21450b007008004110000c0c240c1c242e40c443d2425010203030010182802603684d00c00340341e4080c0400740c20490000d846241624501e00d8 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 370443741 1250 370442491 370442497
    0xa1b0f05060a05281a0901090c08061806130906051003110a050a1202010903080a0c030f0c020315220809040609051003080c070b0c0d08060906180a090503121b 70
    0x100b2441c0c0c0e40200c1d081c5800c4002e00720b50040c1c141c000d004545c5001d0315100e1159280c001c02c410380c1c001924582c401c2d0002c20288001e00014030804a60450030b180c900140e0780b20350049011030340c00460300404600c0000500361160b000784910f052804100e00034242c6d00c0c0e81003ca9028606400b008001c900c2003040c1c48009019040c0c0c0306182140901c196201030944095861040c146103141c9a101e4a0f408865000410003d0000e1840f01c0c403201056806507000e0010442800c0400c5101da10340e0001e40c6071081940303a0300018204000250060310075a001a804106000d07040340c140c01142880c88860b403000301e041c1d000b9801c04500282018591003414401c2200809034080181140e0302d0381002d5100e044250094800c046011500b640040e00800c051034220008000c601740c015805040a2170041245224000c40400c20640341c45501040c05440ca10b116184082c3d540d903c4002c1c0144a030940c0070700248404661802c9111500324001d00480d4000d03c050600180007030300d180303944 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 370444991 1250 370443741 370443781
    0xa0611070e0702100e061608070206010506071a040501050f0c040305030f070204150b0a02101107022b1103010f09080f0904090b13060e01050106050a1b0f05060a05 72
    0x1034040e440400106040c04492600403550344142c58a005070b01600b03005a580543c07504045411200c184040d15030b04d45a505466041400e00c001c07503150284003e0340303c0c081480303884d015100c0001d11800304030305290720710071365010300340082101e050909080d030003060100c0d00209100802000b00e54046600c01c196000c8035401801035180c68600300d02c075030b095088928103e07002074175101e009021040d0416024040c0240003071140d155044118000d00c0c2516540903506914903080c00c01490403040401c40c1d401d140c05a507003003403012a14200c110102825002c2e212117108a8a01e00100441c1c42e0b0410ba0626044000b030101c8080120124202c0b02d80d040001c0480900b0030004824003a004054514003000070400107000c03e00340c440054242d001c075030752a032000e0100240c1041001e2031003000310401d0900001c001d158100b801c082d2040c07144468070020700400900741c0302526003242c04400703820382c055092022001d40346000380d6600011744030100e0003814400000c410040c0058104080 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 370446241 1250 370444991 370444993
    0x314060117101a030316060c030c0c030c031e0201020408070e090606011202130b0912070e01180b03010627020a080402060702180403050c0f160303030203061c03020109020a0611 78
    0x5042e0240011004192002000c00c0040d00d24140300d00ca9035003171001e031102c011140d0003c0d04480051500c0011a2121301001c0300313041c80c000303041b6a020703404124500d425502d402c0c00c2d801213425090981c1d0100b00307408001014103550411240d401c0c0e06402400403240312408a508454545804007540c2030104c424100302c0d40500005006580305415641c61031001c0c0c1d1005141602c41c2c2003480081e42940c1005102c840700190305505400c1890300280c4c0c4a408c900603160301400c040410401a4040c4180c000001e850403039000749014a0b4848440303400e00a000f00301c8580e40300c0015888003141c24980041c140ca0880100c500059402120311071101a40c0307001aa03a42c660801c5400d4004400036038201e140584901c01103000508d46902840c0691034442c0c4900c00c1400c0b0b0361410346002103200d02c0d501300485010311020210140d20a407035240c20b0140c1c40e03554410201c0c4c2071300031111500e80000c40d040d0300d03041850303019801419080d000392140411a0385030300003a1001c029107440000d01d = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 370447491 1250 370446241 370446253
    0x9010305030307080705041205030310091b200f1501240c2a1a09090a0c021207060203070f0503150409030201060b1305030601090b0a0e040c050a0314060117 69
    0x703d184100e0080c2e60051450501600382600c813440405958007614007210307d5400002400700145c0702c07107a000c000f0a41c40c4030a101c0c41050f21505104800c05451000078811100003c0c5085110a00c115085400210459140324201001035036140d81198074800403107aa0b10020a0030300b81182201507900c01e20658285465074448204c5840c200e100054a1240d6440d840c1120003445155801c0c001c8089103c8002172070901c40c5210300400c0c8850001014070007000003101644402c03075490380c00360300c0000000c2d545030040d6040c2c5c1030024103c08e818180307100158100400c40143e0180d406a681a521514812203401003950207210580e81005860440d130b10600343e900e041e410041c40310f880f900c00030801c907945000312030300364029844010324612049424400c909040102038014060780c0c0c01800303128410310220700d200d50140112450000254001401d10003e030301c0d641c0060801404442082e55681480d00d450200e0320792110480c000c8000000394451b018403000b803500001c00103031007 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 370448741 1250 370447491 370447501
    0x2010605150d0912120e011505040509030d0216030206010509010308030c1e0a0512060d0b1303021c0806190807060509010201110a0e031e0a06050406020c010501090c020c090103050303 81
    0x846904011a400500341d100d050250004501c10040000f01314251101c0c985018512000d4054440d0800001d006078904034454814401031042e4504a80c0c00751400070b0300d912030350000b6041d4458900301d41d069074000143c0c2c04080c00b482e021200c038079000c0d070300f43ca68a90700c44e0304008650342d003807102504421050000c0b504403032034540104101c003401000700b44081c280c511110480d811005c0c810010400129800d100d900d51040b4595000c0000c031484602d58503140d554a040402c0500f03007007400d11300f034101801003500030010400d5410355501c4809030744903110001056150100c420b280078441d018443c01410b60904924019510310070003501005042c103008a4140d0040d615190440d9200e1130005003480c0c0350401010100301d40d07910f02c0098400c55052520f84002c07030200303080030780586046140082010864903245944401c02155a841c0c41c140b1b400a070040880c4240154a0a03000084000295100705181c1169400356840401c4140c1000328100d000d101c040e0540c2c100700b001030 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 370449991 1250 370448741 370448779
    0x408090103150f0f0b0909041b030807110f010e010e040b03070e09030a03062903040807060f1d0c01050301032d0302010209030601050402071a2d01050405060102010605 74
    0x4488014103240000300495602140501c120b4a40e00080c01c0c0008031034203020781010196813a002e02030608400c1e250400705008201c031100c004102400751444510781c46030000d0162112402503800800c09901c41031a42049044c03c9454201e092085100650781c090310350003100b44e1075000c00161140c003019100902800040c099811070325905026041001c82ca10012003046030140d4450402103450300034000004e42299101d42003001c090050942805100f042c0005809401c140301c0e00183e141d0f212868021030600504400500250030010201801440e81e4000a0755490302c0f54280d0102d0b15105d140c0d0384504c0d0a055450002e80100010f101050f141811015400c10015441542c001c90400c030f0f42030315034a410300f207005075000543ea10040c0f0b4104256400340804450441c5440c0c0d259880c0710041c00d804a0004804d0078007c005860b04801540b07141c4c116666041e00c42c00e56910a0700b01e030200c1401d0050900c03581c07070800414880d501c14860042981c8000e000440140c031804480 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 370451241 1250 370449991 370449997
    0x3060d1509081903060807060c06060f06020d08072a050c03030c0304090506030607121802030304090f0f02030f07110f031818150f040209101808010e060408 69
    0x1610040c0401038824694a4984503050400d402003004079183c0c990040d01c101c0308912286104101800d0060601030a140030900e80212017207800d20300080811880e14601611040c0d00541e000524500002840d0b41c0104004c1100e44160780c23050403980d00d180050301c0c1a02c080c0356060313920481080d0100351680c005800c11140c1e003d101121070000032040000d142d603206805000c01b541011400301300b0316903a4050680c1040046000d0941442c1c030038002011941c04078008041103446a100e00110610000c45506058014054964554807085103030082c01c1c84d00f12a41205150660000f040d15552098034040c815410102400c1d4440d40382c100c541d003885000d190713100d001c1c81e1045445040100024002089000b040f544803802c024200000c3e1001d000d48042100d89070000c2028003404103400800c0241d08a81440820566001041c000d0007488205600710005038500d000d542e4004850100b407160405000302d020b0f4071001e001c0d003078a10100540001c2c3d408034000c43d0004101d8009 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 370452491 1250 370451241 370451243
    0x120305040801150810110a0e04150b0307121a012105040b060f1e10020c04090507050f1008060607151d010e0316020f03150a020307030615020303060d 66
    0x1246081949416485086940660340300c00000700c0b80c04208901881400b6801882e07042c9a4100f050411815084405104101001c000c1040b0301c00038082c16940d99108175109420703400090340103920b800c040589548103844410204001c01d5a080da44002030058118140c005106010059020b00054a101d510051440d010908242e0407410460b080c0c41240d11690080c2200c0308541024005c0c46020000c182030307940200e0003000980c00c2c0500f016401c160001d800d844080c0c0c5018003403000c80c101000d40d0344440c0d025051200d050b05011000600b4015a41e0480d0009042d1142d40c040140d0040b07004070150225199600044003890302001400c2d5030b900030f0003110080844810240101c40045100c00395080d40c200c00b0024401091280c1c54800c15444000c41c80c00c00013010707600c101d8221080091080383c121800301d1141c2c0b420710004440299480164000e400e000341024007940003251030b900040c4c42d00e01d0000f426102c6d124050f58814181e0055461278a8182c10b101480c840044 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 370453741 1250 370452491 370452497
    0x90e070b030a15050103140f040302010e0a15060803090d0b060d0804060c0c0b130b0304020f040c0c03020f1b010309050a140703021207060e1c0c0e0f07090806011203 73
    0x1400616448044010751041607001400a10700c1101c501422110b211a040715040500c2c0c5940b00d600c10b0b0b00036407010382101903806030708a180c1d694582240540b0104442a58078083e0003c080708101000c460240304050724003080c4203032a168010107542c0c0c0501c241480e84016900415804601c21100050b00410080c0404824000304c2d142d4030aa40c1c40390380841c00088130310810030280440320203104081c1c100031060b00d140140d101e032550803604643c040c201c0c00400000c04102196103510901401c01c801901c01e200307a03c0b43d100c01034081e0b0502a0190058003e100100d03083d07050106819460690b2202c601030700d000b21000444c02004101001c0711140700e822400e401080c0c46020b05003860204134000c00c0d1850840c4180301c0c10f0a6034003000d00c02a03104402c03d001280c1c00c000001070a12043d07038981c03005410005100c1c00b039605004c0140c641034000c10085640710241000074410260200229100c1d207941400f25400c800511a4440d55001280103005c030180c0000c000c40c40500a04d = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 370454991 1250 370453741 370453753
    0xf0914070c060e03040e07080f0c04090c030216060c1e23130b090a0501090305060c0a05040902040b0a030b0907020703020f120f0109030e03060f070c0804080d0c06150b04090e 77
    0x4403003d4515802a000215070b028120104030b402c0e98862005940044054084001800c190003c2d94071170284d40100c004107611070615242c1c40c3c0c800d0303064a001c8030360600380c10100405802c1c210010617404652000141c451240070310800c01c600a103000d00705040c1e0380c028071509603d050780704510881c1074441c0d50010810039038140702081c50344200a007084401103a690244c0008000340f11071168007460501406540420104001045540e840f50a891501c2c0d0307204154801142c491040d60004441da80c40864042000720070103000c1c1c0813810b0140c07000c0220f070344000c080261101c41143c0440060340702d942c1c1440141402031408184842c007401d8401c00383d440c1e040362820104107040d00c0890f695900c05540034180e00c4110100904000d44c058000b0381020030705a100010018103641c01d021080f4250313010044040d0480d4000c050203010b6894000741410010100811030206640c1141040c580e0040c00f10851304580458151024492900e45401181000385c85524155040c0d80105 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 370456241 1250 370454991 370455011
    0x507060f0615020c10020a03091a16081804020c030703031a040f051609030b070503100b0c0a03090e061315030204051305070b040608041103010b06130f0914070c06 72
    0x90303107403002c40580d4010b0011907000e803080c040440e0452042808540c0441451070200e50402d0f440c50503209040000592205090400302480c490f0380da03501010005440b510f000e001d00100503221103407618103040c1020b100e01007003105074062804200100c0c1c10400c08040028082c1c4e00944d40030000c00c87d40c5643c407450400043c119200180c419001a07150f10400c0b0b04c42c2950f01e4010004401410030300c40c00741c03c3d91242c25101c080205403505029000000c2000789003040e14610050a9a000c01030b80c920450301e517103841e510300413002c030302151002c20089400d2002c0240c0e80c2c030035600030304a4000000e80c04c00000c064402c0c6880912140380d12000400541c9850003203a1145034103090b08580603509191581c9021000c0d4040352012005000030712511b540071400380d80184cbc010f0030010fa07082003078000030f00420810f8003440d4015000107007510868580c1441004642c80402d030038461740d40e03c500b0b0350180c03080961040c03c209407003400038246034090340300e4083c040d0140c0e80010360841a = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 370457491 1250 370456241 370456259
    0x1312031a09042f0102010f14010314070b0a050a0809010c021f0902060703030606170f060108090102121018110f07170a02030315030a0f0818040510090b0904030507060f06 75
    0x72024403410760400c0c3e4010100c9580901070070054210b0000104482a540b0075601c034049018000107003101c2d8141245104a401040248082c0c402c401e5559501c4a1003030020300164020103550000c134100307000003400600c040c03180350592000354010b0a009911449038803210401c861034884001c1d40c8640060151701ea007400b40503414481d4400060650610101070f0402c00014018a00c00001d0010410494803400303665402ca1000e082200c51741d2a10842c071400381c01451403000c450f407494803c110008124185040c00c86403410b404201a21010003500c00303403050054100d1440908100d00d111002103a0024400280940d08844010705c0f050007104582e40001004001640b010080c401b401d038100326417408500f01100100b90041c9030342d80d000d040c0090381d00084d02a400105520001030758602940c032201200900402c01c0d8500068204c00c111002e000b007145051a19035607030103e0800401c1c0d18003132901600c0d0b1508041a030780d2280b024201c100c140c0d00701e454441c0000107107004 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 370458741 1250 370457491 370457543
    0x301020f040b09041401080a0b18030706050708011703030f06011407050604150603120c03020106090606110106080c0102030d0902060d020d050609150f060903151312031a0904 77
    0x21a03941c4140e0f507211075010041039801c0720310700c44140040600108401000051205100c507030080c00e5401c42c2c0c0e14501040b41c0035400c0c2d00c0000e05400001a820108211903101c5841410192030741c00700c2d40d8860311841182801542c1d011610b83c400c1010452200b8044000795001105140a220107501c44812004c660002c210132155030348804240020000c0107580104d1094030054200301b19860364841e024507000203589002406218502038050520030340103040501410030b4280f0250307507074a100901d101890440c5200d40e52070708002013480003001c20f1007800180140c1c0218144204814284c004007840d0104a0b8896402c0100080381d00e8940040e00c06104400c400041d2498240117102040b5401883c5100c0d03100500c601c079655a9410811902d10745007950703129118900d503408a440c4c01c05942000c3c00f803821a5040084808040202e5840a8854a031001c00956004015000c0c0d80303881c40e0103d40755204100c0c0144a080c200c4020368403d02814950003280c21040c0c801801c20 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 370459991 1250 370458741 370458749
    0x6140705030f04180902060f0306010903050f0a150507080103030f0c1703071106060108180102041a0702030f010b01050901050d0f0e16140916020703060e070515070309140301020f04 80
    0xb0b8011608100d443c83d40c2011110380c1c1c48110040c04145c2540c1d00261103481040ca40305143c48011000c07803a982d100d11802ca0107550f0140032211000c02c03441080c4e03030f19601c80d0401c450503a2500034a02844410b805614007444050716290303420303400c40e07400352440243c8010b9802041000992580460384210854218294a5520a03501c0c00c10030001810004506500c28065021009000d400c2c0da220041c036900240c0340145035000120840510b019105e00d03840798079492400c2044440903050cc0300141100b9108a040b84ca41c5d0f0720300c04201d420388110420560104105000f802901d5004e5001412140700403040080d40c806040c00600490b000c0545c4900c1c40d500010000c1d50700c85c1e602400d0400f078200b01c240417100c0c1031110700003441413034001d12130069190090401a055802007200e9030103194040c6c401d00ca024a007038240c50380d54690b486041d1042c0c800d0010070320081800e801316211103805030b494107603582c20082d509440180820744d141e0159402c00003170381e0f80113102000d132001d0 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 370461241 1250 370459991 370460017
    0x203130905070906021c1818060e011e03060b01050c0d120e03040f030f1703011202090604050c030a05060f10030e280b06060d0f0c0201051f0614070503 67
    0x5030412010050183c0301c0c0360440030955100041134100900f41c2912031b82c8030000c6140c1100005081e40440e100740200380d1104038003620030013142140c0300651300b101094030506074020351180e0303036401e291242a21409400401446030042880461000d8002c0d20b0ba6001c1810031600d4018038803030007450302c40c00000343c0c000190000341807046100c040c021540d00714540c50080d800d190030004080c841c103840344401003000e030103007000c0c0c02000048022200542c1c0c03556003080d1030350703504e840c00c00c85584581c00480c030418019001800030318161145501486003020000e055a851500c080003d040103401c031988051310080c1d800c45a0b80c0c030bc0040043c0c013155600484c0140c14a10010302c1c2c40540180310031110445034003040c60702d01d600c2c00c43c2d030f0807601702641e00d000d07484103004101c040c030034503458044003810001c014026107455081520f071141309038000c000d9a5a999000c03070400c18040303409100300018001c100140761107004140b0300010f07410801442c160050b5951840c5a0001b4205d4642e = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 370462491 1250 370461241 370461251
    0xe06131a0c161406060a06020727050c0409110a0504060c0c1a0702040501050301052503060e070905011115011211030a0c060207120302060a021b1f06050103150b070302031309 77
    0x14143c1c0130f00c00107030424400d0701c078840110704008001c2d4a40301ba80c050400b0f0150b40c044405101075482c1143c4042c084080000c011030300b03254031003050f01ea1140c090710380480e0414070320140405074031084410b128607540c0c8031400c4c1420510702300c841c0d4110940c1551080e948100100c0c50000605160054120000901d96201c1c594410301c000d030751059114038441d9250500704020b8250f92011030040428558003a41030031001c05098000700040d4000031030b40011030007044042c40e04202054280c0fa0240c8030200441107031000c070350390b511a0146c4182104155001008a154502c4034113005501c42c4201010903802c00300482e1510b0322851050310b640c03601c603808002c0e01e50144551409000a509a115a0020b0b0b0302c0c0a0743c0d6900c05040791a855500240d031303a0803840c102142c251542c5000e005d40f8143c04080b11030100300c4001d540704624044c0392180c0050a98043d205000c83c4031031084508001510f444d030b43c1c0d8080c0c0c020b9842a41540030800103d4504560b1040002c09005203900000f2 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 370463741 1250 370462491 370462523
    0xd0f030b0f042c0c030a062a050d06080d140a1103070b0103060c140306211020040302030c0f03011104180b04020c0604061d030d0e06131a0c16 63
    0x10fa066501c10b0040c00340e1300254000107860314081500080c598200c0008141402214486843d9449500c1d1300221064100c9460310607076402402000390000b82c2c070301031044c6c5031585280d6440e941e400d402c2102142c1001c10341c0b04e0481d210f9028210203036180c101004241000304459085034080c00003100d1007000c100040c02004464481d4400d01082843d00d0751480f14202c0852000c0d1001074501c41c0304011100c0e16510840c10450035803061203514080d00e04280b02044860081d2920410307042240c9071050f400e0340700e0b40c185020386084070703002401030103802c1c0340c0030a0004140c16044110740554a9041c0c5003a04403800c4010002011200001c10280d00940260320803285c00454540c451401040400c2d14648005801d50b0829006440090400746100d50b6a000360362410603001c4030f0001041d103900d00060366101c2d1100726100070540b5081d43c5c4048101c0b00510b4401001803050041168441c40016480c4907281d10402c0340390802d01d007903070003104404d041c0c0c55090304851070b03498122101 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 370464991 1250 370463741 370463801
    0x21c02090a060f0206180102210f070e0d060e0c0d05150a09150c110f0106090e0c0907050a0212040f050f090c041a0702090103230d0f030b0f04 63
    0x402c0c4a1800c1c1c05a5103980600075205d450203085200c0c00c604102d030000c0c070f10900794100d60050740c000000200059404210f0107034001f0032198174042403258000505101d00940d1501c540500080503840c2c04040c0303075680d40040015008000192041d5161340c400ca0301e94a5022000034003400043c160503880007640005068010200c0b003a035420a0f260600140e4440141d11030b40c4070014012031005018942100c042c0200c81c1d88170070500c0b90400b01050400190702c0b2109444069106100319021124a20f1355000e4180301302d070700407101700000b4030094454000746c02c101a591042e02c00240c0c1d101400340082e0080d070009000c1c6034503003808006510701001031003400b1009072449401450300b0070b00300415002d90b2142804929562601140f955510b00c1120302040e4010b20601d115616810030b8200c040045039200c0040381c1c0e54030750071506803000070841291000c50392055803ca00c0c60038100e010380364204138160401c14850701980a641c1b1409145070b41065051692034401c0445031003 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 370466241 1250 370464991 370465009
    0x50d06030507180e030316030f060b04081207083718060305070e06030703110f03040204200904110702090a0c090f03020612040c0b121608090a020d0204021c0209 71
    0x500f600ca80750030700050340380c1008801d403540100700c01204801c20151042c00da000d0328240c00031040041c03408074042054607214020344203a640907801c03030301806044c804603019403050110207000d510f07003807042d508000e00340b102c55145099040350440140c1c0702d08140410006140c20b9130000300d1114200c100da500c00b404c000340028140c41c601440103050029000e0201c08901c4441401205c0000009819034001e1300304500b80e106600401d580c6002100500307a05420a0b20200c0c441ca04200c0c0403529030003d94001d00421010301e1035280750548540402c4014407000d045080300c18024012040540c0d44e0780b07071036442000b41943c040384a00c0c040400802d078460980082c40d006403100c0c01403001d81c80310340550f50004215842d42d0b040c0c1e12030b428110480200c0780d001404105001070200383c44003e0301101402000002e11134058410744820035070795142d00300d4105403254080526034000d86440700070100700c103001500c01880c21000c12140c0b0050540d201e861501c581e00043c1b01300d4582808030712 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 370467491 1250 370466241 370466279
    0x1203092e0c0912120e0a0b091018090c0c08030a050703110a05040306020d0905031c0506010c1a190c09051c0302070e151003060302011107030203030d0c050d06030507 73
    0x207014094142500c01c801142d00403c0604903020120301c4d104403d0142c200300201d4a0003c002c40d03141e690311034a4070a16071000d80300b640120a04000c2c03201103401607209070724411300303002c2c0742e00703070608005d0342d44020514485000200a0a801541c022843c00e800460040010030b2000c156490300c080b0207800c3d100000c00c84000000104140c40c3d0040d482001e85003945d0b840000035903940711003150080580342c00140981603000c000361114034176049440583e01490011400d1003503585200064400a201e03160140104810901b5009071011348600f5640c421000604003a1200210f8400c2c0c1c00c0b24074804544000c12410b007014806e1703243c0728a040d584041d6110039650600d00d950b6000351034031003510443c5581d100c1400810480e6050048640b148140030306145040040c9180040240a442c4001e80c08218042c3c03240d24459004100c2e10203580d0041d0003145003440c0c035402c1d00003c01d50088883c04002003400002c140341141d0055000660050b030042410170704001c4110050444205 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 370468741 1250 370467491 370467497
    0x12150901080d030c0e090c130b04271e0501082109100c0b1e0c3105030a061d0f0a11060408031b010b121203092e0c 51
    0x801080651400034404900d00c072989400324030114810801c2e04c0b404403940e01554007084079001c000704252024007411028080d261401d0a486d40c9090401c403600c00c0c5d00a00b018a05000e580e110080020b1a0803c040c02112070000b843c02110301503428110707092201c1c807003c1c585a100411121008215808440a84004108950382c1d020421042d502c901190380d8000c02e042001050f1031401035824111040c0c0020020386285003c02480e8818140c444410307045000c0040480e0992980500f2f0b2440d9058031005040312519a00c0d1080d1290420302152100031019400840d40752024840e000b111482500d002c6013540e205801c10341e031042c042441c9101580710309c00c2e6410710340300081c104241035004080107540d040d0200100e000d83c0b003190407000c04d034400003d03030984c0400c560440700507184e4064020007050800204200001e950032810914a51160701e0740709104c0d42402c0295001070f101001c60b2015040721740d8401031b8040c0300082c4000c0c503040441d0082003010394014020310303200740c4c6 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 370469991 1250 370468741 370468759
    0xa031409030a0915031404080304050601060f02060a24030807120e1c060b0409030239010e0d0c0626010506040b0d0608070b040f08070f120f081215 65
    0x903500804010240c03141c44540d140702140e0561305800b981c01010f8204001148414a00c2c1c241001c81e0164001d070f8040b40c40b84151000000c943d032203000a8100405507034060b11040d20341d8103100000d081c0c161000b1416104d072820080c0800381c1040306100542c42021013503150b0180c2d0520001d6158415082d40500c21007840d21051030340c0701d103400e50546603401409040051241071140c02072a4001000382c01515000c0d4540c241900007804030039881041441e00140700e2102590001681c0c0000101710513071f0346016030803a646c0620031020002034058406581c0302002d8031400c8000800358455800725840b101754a0380d190070441103042801136aa49000036515000100340c0311301c950b11488012401c0414120040e0760288c00007801440c0e03080c01c44190607103801c0403810b42d60203440780007100d100400703000030840c0012403124100d41c51055010381030f62600c1ca00400b519000281210b01c030401c50102000a208203001e27000c1314210400141e00361801038448070030303401a5070070241303d19035407 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 370471241 1250 370469991 370470007
    0xe011203090b03130f0501060e1503190c14011101050411010f0507050703150f0c110f060f04030503062d040e03121803040503010905010221010602071a0f0a03140903 73
    0x8000c0400c130180c0c0c80010080070319001d06025004007902c1d00251031034807050080c0200c249409510b01100300c01241903403201c02e540f08094110304003044005002c00ca40180401031810003982c0303a50390b41010b0500040e0340014500007400c4400481c0d08890700740000c0310034195541d015850183c3c8008a0900b285004103a44a0a0742d4540e1440010451040c011601075003815a4100c20700e0040c1460061210803da514040c10a45400e8441c409170304c64112205101d900000310170303020351803800b1b00303002c13503104c50f10100c400717600044ca52508001100000c40b0285080b00098548003001c1c6480c240c8055044104400d50300014101c0c02e8581c01402000d5140044000090700f04410300004c112101d12501c04606500403988055850352034695030506202d010b400520080c02c0307074407903950072159880b16004c0083e000e008003001a8403407001072048200803518010003812880b009403c00f01035071650f0742e444e8440f111070320000740c813540c0e0044141c02c01d0b100d0305d0300428000c01550030700c2d2203 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 370472491 1250 370471241 370471261
    0x3060e010305152d0609060103110304080a0e1305062d0f0f03010c020303010e090601080a03030b010318050c040c021c05130f06090e0f0705180a0e011203090b03 71
    0x35200f458001c1503003040100e040300ca100041501800c000081038040c4061520241015103412550075002d00d050340e0001d4010340c0f00380b0038100b100e2030b00c21031a81107440320388400041c4e03000b4401e110184200c0b01d64004191b81c40b00d0068800014121002c41c01d0300c3c018007031000e003400d4829400d00030f0040c00015002800012041c10300700c10165084410030086d04001814203040820b04c94055207820070320080107501000a40c1a40d1034021094556151420116900c0009210f51843d40e0012410130001a1082e0880c07418600140740100320b2504250050346010315a6000b100e0380c1c1c1c81303003611045a04050280030300c03c40d00c0340007402580000526040d008014806104100a000901c1e084070080e45031001c0c1c00740000c4040b02c071003c0d48540001d40695036900410040040180000d041101d8154840e882010199105030500701c0ca0701c00c01250a0305901404e034802501c078000320b0250105d0348020f001340718950711800d1803d01414042c1108a1b01d070000c0140110400030480c1e402d40c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 370473741 1250 370472491 370472503
    0x20c0d060e120c10050c0405030303011509031208150a050a15021c03050103232107060504032109080712120903030c03060e0709051e060708070303060e010305 70
    0x10300400c0214900038034031401401e00381e4044101148002c0852550700720715000450302454400c0034400c101c00c1d21407145100c4640035a12400d981075004200601c5510100c14070307100c00840078142001c0c12616583c1e041d071060112034000300000d50050400509071603050203808a21826104958401d04000c08180e203003d480c01079500c03c1c041c1c090041c0c1e080c0d00c20804900c2510000403c00303245004002d000b00079000030320058801c00c40f05401000c4111103d84860b2600c03ca060090070501881e030220800b40c888091040305444041c0140d80116205000c0c07103205038486c1d90341d84900400010a401c102e144030340001304c07031494588614001254001280c0031039030030041c1800b4101d60001c1c0dc64070f08402c240c03002d0925080c85201e201705909034000c5550385000b61000c1c0603060b220300e0ba042a01e8002c840440005524000c10011414058822009105a2400030621003244d0f8007088440d40f281c40300701c4401100003400300038103525200311000b600d60490501e269501d90388806036150 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 370474991 1250 370473741 370473743
    0x9051603020f0c06010e01030203070605121303110a03090608010906060e0424030b0103052806110915030103060506090105090c13270b10050a050306061608030405010c020c0d 77
    0x1a07000448074248030040d016991024180001c4500d19a110400c1d803009034020b1008034000c1c49010404982c5502540a031001d500c1d0304544a50b05680b0300c0096081e000f014070040e41888104940400b0150050260807885402903c81660043c07900900400405050340081d40c0c680c6444000d01846600030300108140c00202c8000c610242c44081040705040840c4205a0a1070507078400800c20500482c01c0781287d025400342c0da0260906c86c2e05800d20703204e000c9414a913810408050300059881ea0205000021101c4200e01b040c40b09408140b00c4400040071a1000300007000400400802d40600343d44200d007038543c2c01640d494200410b080c00b201401908414201245124902e681100b80000604040031141c88001228451850321618200640492810087c1225850609207075900151b280d90f95040e18207480c001e4200c965401c050b01b03184e40002c1c01c20400b5410682c00c000040c01c0c038001c903005c698030704040c9040c508503003001da240300944d00440b203459038036650714014451103 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 370476241 1250 370474991 370474997
    0xe061804020d0c1e0503161101060305010204080f1b0f06030c09060d0b01030509070b0d0c0203040b0d02040602060912071e06050408040503070605041503150b0d15090516 75
    0x500428000100a03015440038284003a107445070840100d58001c03003000d040302e48078544200810007508211076501c022a4000c00c1240f4048200980c107111b10800842200010700000e8016125550709003039910592003941c481e40141c40c000000703081030043c000c0301c0480303081d8800d0706545d00d404612002c0d8111020391181c00080002880200000103d50104c00000c181c0d5540d5140b504080c0020310030705140350b0000f49440d00180900e48009400000d4070400d02d401f40c00d280560a51001800c261810001140020b21002806100b002d01038907032256500009a101c40c140040245013032002040c0c240035034030800e542c2c440c080c000400c41c1e40854028017850000c1c40940510310081d4601c1c00c00501032071400d02003200b400400c0000c1c100b5260200d0a6808071030340d8010495aa0040780900302c000745890b02d4159001d4060750000d01c0c00101e140e03c4403003071aa01c09100107940c0001411048071502c8841c0c0c5282c000c11501e504000d4402c66004115070b06014003170901c00c1d25607140314018 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 370477491 1250 370476241 370476277
    0xe100213090b01020a0b010306090303050c340b01080604051213050423041a0115080a0b12070e0f01050a0303021e0313090e060a0e030a0f12060801050609070e06 71
    0x81a442405110007040e00f14400113141d5032360f480c0c130800609c1c10180070b400180c90031010500d000952422241d41c92096242031803101c0b201c0b4048001c100b00d0403081e254000e44420410001011817000034000d02410002d01076910b014284241483c2c0304000c040d00e007032810031025441780002515081604c0c010345000401c0d101c3c02031203412081a81006159090b50382041104003c0d162041c5a4411900c051440840e41d0360200e04418002001c001d20115041c4400102280020341c03200321440001002c0542000c9942c1d001800c15006800c6801c2e00324000c000c0104401d09854914010103080d41c02e8030340140f031500d00a4880d0f4901001500d01680401c0c004001d0348208103170359002c6a405951140386554402d0240104420a045000b5019080004080d050144106c41c844040c107005980742840100c0d080701c02c100c510101c1820300180c51044c4000c130343c0c0b40c40303030202034a000c0000040da418000e04010304480c005240c03030b080012400480005e5181d20017030390400700c000c910b8010 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 370478741 1250 370477491 370477511
    0xb01140103060f030f17040b0901111603080d02070b040b0412080705030a0504030221070311070b090d0503190f0305151e040b0d0602120c03010509040b0603010e07090e10021309 78
    0x7000c4680030b0800c03009001b000c80e000c1900b4801c007000740021070003601c0c0d00300810314038803d00b900c80246003e100c6602030a8072080001c21450320040c13210342100f00d001483c1c561269601e81038003c0a403006c0c3e92600d000c1c41044100607054140c880410107908125006242517080106640700007803101c00844d441c0e0000c181050b0081080c0d40400c62000c070b50303007030700c00042c0c500d000303140c008a0003500080d54628030441300c60320106080081d100451001c61800c0c07001320600c00d41307048d403039812100d900c801c1005080354000c00040c0740d004982c44d65000300030442d000c40102514005820a410030f40307180800b4a00703594100000e040d10f951426081c411070644c00010b00140500d4803801e03001205d0314148000c100c042d40c01000c412090b41c0c07000c20305441f8123480b03003400c1c042402015003058030403008c0740119075414503c41d8801c44c02000460340001d420035403410000da0354440c8000030380342c0b510300004105c14810315151003141c80c011030030244502e4650260709054804d4440407543c0c2e4903004 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 370479991 1250 370478741 370478753
    0xb07050a08090d0b04050610060302040b07020f1504062f0d0807030b0901030506102408040804120c03060b0102010b0607021207150f0207090b240d090b01140103060f030f 75
    0x401c5030300030181c07001360315103402c2441c3c88200854610510280c00704020030454000d10a88041d6880c8d4130030b09040441980c203011300c4c41d03030341040e107603100d455248400b039039800036030040018102030395860020110541c0078502000103403070f204c44980d6107480300d0070482c2c1c0700041d0300c0c07644110751030f1040007900c03503a0040d0700505101c0c41403038100b00210000b109002c40020b016025070520036001075016035545591b0149561100611000080a0001c000941c03140901640180c0924000c0d0310302690340000c1e07082c1b22400f800c112140c159561003001408498444c42c001040207000030f0202040b00800104103104001c1e000340b00e00044103d0440800d01009200040c0000c40402400c0c4810084081d000c50300204002e001481820030104940c200e6002c0c10000c040c01901c0c1d6910100050401100a04903c103041d0400600f80949c1e1a21401070090140803801400c40408650400d0030700001c880c0308900f03050516040820410040900e8030202c4c4c120303504100e480740c01100d5840d00b4 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 370481241 1250 370479991 370480009
    0x5010c03080a0b13050f0106360e070f110606061209010f05071206080a020108010b0307180f030b0f010803030c070f0218090c04090312020c070306050c040501090b07050a0809 77
    0x40c2e501314001c0d03926014904e40c0ca40c8881e000c1ea510010024040c0c2e65030780111100341c981c10700c040059084112506110300000c150711800b0742c0e002000c003411078940c0341d04c0308003035412212007001440f082c00328042a50004400d42140c03e00101070b25072490403602003a0b052140a500e448010304010000e041c2003400c0d480303028000741074a410300050400301401005140c0c045002040c0c145000c000288100c400542e06c06c04c154180c555201d0b42c0c0ca001c0d401c0c21540c200030182000c3c803494146800c0032000303000b00f14000e070000100c13130f01b2914103606150700c44078001410510707030118841c018000c640001040e40d41c00101100c100d6a141c005150095000c104020300130341041140d074900348e070040400381440c4500074420440341001480400c02041d541113140150100703120000c490382403e5182c0050507a000c091041b2003000707681355568011a0000c40c1d990404c2007000c40e0500503580c1c000040c0c0c0003400c505e48244e041030402d844080d15140311000040910000042c0d0b0099a240c600c00 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 370482491 1250 370481241 370481261
    0x30c0d140303070314010602011416020a0203070f080c0a0f15020712111302031005091b1b0115030302120304021c050c10050c0613061401080c1905010c03080a 70
    0x5980e143d00301008058050700e1202c4013107524240c0a00003040d0140b0500c140e2014000e900c80d00c1056446200e08081403106201000003140910002040581c50400c198001408280e01c0054414a450703d951700f400740380c52901d8482c000700c0004100324800062a0810b440d605041103605400701c1400b41d181644651080294124144030402840080d2100f2080041e00381c0300340ca120316190344e400d0b007244402c580d50705020516280a0020781407000d540c0d54010300b0140c108038920103810725500107802c284100e1454460280c0350308400c50b0300303010340c2078400d090f05a1215024110359020b511034015100540c040070740840000c007550f44808074075900480d44982d10503030f0f01a40c18001e071542c4d8503041e1640244412414100410300c0b841c2111103000b000300c09881c80d42c0b9040c40510000800f00c005540058940c401c0030f881c61001c845050003005200020042c0000303600034042c5c2060201884059014540420000c50b40c00c581514540e503498070b0289941d90720122000010101842 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 370483741 1250 370482491 370482493
    0x2030c04080718050a06240e1c1a060303030412180608040303062c09010b04021306080708150105090312031006090f050f37061805030c0d14 62
    0x6000603003455069140042401c103c1c0140f00702e949101c035010594003c0d100300d03e002c0c14005040035503841c0405ca081c101c005540760103028603040c1c00000d52101140c00000c1c801030250900e500070050560404425000d25150300c851a241040c00241c482c0801000581203450126101401c0e51285e9043c43c0d00b18842400d0524060b15039400411804044808034080784c034101c001310711082d04a07803d4400c241840d005943c0c06500401c41c071034146002d80721a080c1e42d290401c16000d980c07103002801c2040304003ca562812791400400402c0e42d00050106014000240c05111003007441c80821007041c242803c05580da002850007207840c004100014000c460300210a0205103082d0204800c101d801d2581d40c1c61039251907200c59141004030f480b80c5980501405556900c600708562b502250107030401c02e0300140007101004104982d480d210488145440d14010b018058028100c00c042ca140da241484503d810303e008656502c0c0141d5140e84070b0201c031180e10701081b000300d40e81240302d80044 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 370484991 1250 370483741 370483753
    0x2120a12031a040501140d2d210207121a190b01090b090121020408030702040f0e0d05092805120a0302060106080402040e1b040501090606021002030c0408 68
    0x410040c01080600e402d038501541c0700c045007040e8a042c2c0540d5050351443c0c0c0c0b801d80d64004c2c40d0b003004520402a0001c40301170b01055030300d40400b0402d05490040c0143c4607030111060388107107021000d85481800c00b400c0f4006482401107441e034005901c030280d0302020040800c2034194248224a49170360201c6103240c4014600b08000850480244101020ba2000911114a920005460300b003010301565040300300030b02441e41c8561040f05043c45061041c0641c98200010203145002e9900035003200010380d10009060302181032610900c100c40618135020055001c1c0310341d00549a842e461401c60402002140c10716aaa85040c0c1e0460b40c080a00900000c5000a026901d210051032141600c00d481c16010005080004100f140c40c0d5941603001d042240c1c02d0510075a04e40e0400740099800607903e200702101c1c103508020745005004001206080c1c02504001c11081d42d40580003106450b00f00311080205940000b800042618105005600c0c0d5442c1044052240142c0e840500b84c0d104035 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 370486241 1250 370484991 370485023
    0x7020306091605030a05100c140a02030903070e09030a0e010e0301091b0905100e04050307020d20060f040603052203051308010b0a12020103110a0e0306060d020d02120a 74
    0x6504450040c2c0c44680c02035042c0d0703400c00c15444400581000c1d16030341102c8920a6100d24a5206203040780d2a800c0070044241000700c101c0d0503401c038500d81405a1300008465086103010002c00004204e126083e1000e86411000d540d22401401c3c0284140b16200040001ca07038010701c0c40c000140320140c020001e00780300d410148175903020407151000140310000f002c81c40c9607290103018419920f95505410103480c284203203070154402041910540018011100140d0707819101e149194000e07012095100c40303440151140c0030b194880795220b80b03000c00842c0c0d60400b03100180d4080f0382403400c1c0021107a4900055528010700c44102c034180309031192210b0101a0440c0203000c078015080002c81c40b007915070001a080311806061264003074807854041080c0402000700c6206644113140200c1d265200e05c91600c20b03a0842200704020440c940e0300314082e070400700310103030348840c4c11152000001c001e600445c5890a400d030780640681503041ca50040400c0400800e88465809514806c0704208 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 370487491 1250 370486241 370486243
    0x10e120304090b0f030d0c08040b0406110d230d0617030a0f030902010806090703091211010b010e1809030403140309040506030a030225091b03050603060c07060b060702030609 77
    0x400e018890701c8900c0c03c0006241410182403140e034481015000b0120307110024002c0d5901d81c2103180c200c1e1500801c00010030a145054054030047c603041d1a540305802c801c00001742800c240f48006010403d414400d400c2c1d070507404080c0d0301244508103905558100201268020f00320582049842d030781c400039103441109000005000e074424071782e210100d1107001c01044064071911600a400518014042046441c00541701e0b9004109802c00160145080d80c3c3c68144520300115840032591069404685503401e01440841ca842441c0c036001160815000031214100c3c2940542e403501d0800000701045800c108890155802490800d01d108007070303145039030781d07480010f800d0f02030f40c1050f0208540f400c0c0040c00b84422503154010b000346101418000341d82035443c007002d91000c816804000b03202015881610982c51006020406807003070a54041d09482c0080c000e02d020364400001c20590b490b10310203031154260302036404540c010680001800ca402400340296050003400240690080 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 370488741 1250 370487491 370487497
    0x90c2f010b040603111507050d051b100c0e04020f12040507034b02010c1b030503030103060c0906090b090310020a05070506180307020f0a080a05060405060a060b0d0b010e1203 77
    0x84c08980c2954011400046d10500340a01040107003944e003c0c100c0c5092241c010006000d008241002c1840d46100034804945024100c00b58585100e60300c0002684181d031280c000c40710031006a5040d494250542e9240000e4403801c4401040c50303c07a1800706007085014003500000b980c21159401b01c5000e2043d09248040161038110340c115003402003d1418490b000c84403003400c9a460181403020103a030015108921421011103c0f03007072a0000702c8801089041050182d07004a00445d229811464034008a42403040c94009214000308100b144603484219081910642c40d00c20341c0352052000800e2600c4844941e138000c140c000310f210815254418041e00141d4058800c8402c1c40c1c44241d01d103211015140444809030700100604030240c01c222060642150001c1c00c0380c0d1920755204060341c10507141e508211420341181042c4801c0c4282000415040008854108081407400f154129a4410080d69213116903d5640802c00341c0e000f18420002410090603501041c03440d24420368580d8 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 370489991 1250 370488741 370488773
    0x1112120a270b04170a0206040501030902040603080301080a06050907450c2601090e0a0606030305091305060904150e06040516091814071806090c2f010b040603 70
    0x100446607130380c0f00244000354422031142c0107044a403a040c2000c00440181138001c000340d0304a40c46840010002d88040e00070b40c0207200c50000380070070420034981a01513072000390145040ea880038100340a400001c0084554140b1981d008001c15042c1e03040140130070039004410190b104044c160301c01c900101d038102c00202d80381c59030b03541d5950035001c0c81e8080c03181440000068101c030244c0180b101c25a151301403100980a00c0446a20300419a51941642d4660700110009580440d61705114200b1b081241d0039103d801005020510b40000803401c0034200510181c800300c419152605407104580c0300c0c404500c0c000c0b090340c00f1071a25060440c0e80742034110036880007051720200003d03d40030300d2051242d80d0020b602254160746c150788030320101c99a0485038401e01d001d401d20000c3c2048289030342024081c0c3d1810045011440c00b0b41203011903903400055814400c071403140110f00e481c121612400b50341084c608004c500e000b10000c81c010007010b41000d42051600341c0c00b0003030000141c0e150483c4 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 370491241 1250 370489991 370490009
    0xb0316060e0f040c020c091b0c0309150c0607050304020a03051605031b03030306130623040b01050c0604121e0804050d02010b03030f0a020a0605041112120a270b04 72
    0x902c0c204824007080b591130021080068201d10380c2682c0324907000c2c1c8001e4009a01c60203101c0e18a031003a800415035488014140001d030310001e0020011700340300c140c1d40c030b02501418040707003803c0940343d025448080041c030309020084000002400c655070426a20051a000400c441121142640010035040c8600890307201c1c1c0314030b215940b01c0e508a14030110100c007001d0055421a22524140a41305c4042c141e120075141d01c0d80808200710040c8075048a42012409400508801500034081128920300c102410032100f04201d4500680025049400c16070002886c8440c0101a40c102c1c2c240d001403003c4850305000030302d0300f03419640c012034450182c0d000700c0030303160440006003081e82200c1503100a1a0180c109200080c015004d8101078200301d030746401034511520840c1e507072a044031402c8508462005408001d190305003881812912441e8454000f4030051f625401452040c0c02010503503c208250710074a00b01c103100406030845440b20742402200700075124010405250401c0c01140d8103 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 370492491 1250 370491241 370491259
    0xc0e06011206081509030f0309070f05030601050f01080402031c030903030b09010e0103032a06061e030c0b280305010e09120a12020910050c12071101030b0316060e 72
    0x100384842c402c110880d00c1d031078010300b5541c0011400e1140b211004000c20590b00007803101d601c10344901380c02540705014460207094100c2c246452800c00401581085010341d100320018001600d03130481000081d00c090806090b603948510002e0310380a2001c00084c84210601426030a06406405c46900544a5201441220b100c40140075042909216480c0640f09203801000807034002c400c0c8069042203400c03d40c44001540341030120700046c8803401c0303d2040da15281009280d07580003c040740340030508040f0055614540300c40c0300104050095110211001420400c101ca4200d2040d030000c002c0700505c0c0103d210850068010324003440740800004440c40010150a0040340b80388084146030616400c02c0001c103030450341041c5124062807101d13030170004143e840d51002c1c1d4000e04d10900b030f85c03000e58448844403420b041030100c4480d000642410300c4100300090100440c0346c8065420b10b00015071000120009103001c03100d0221341902c1e01c2c461404955180d2001e000f200c0c001d801e0f108404 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 370493741 1250 370492491 370492517
    0x70f06140601111b04020c071205060402210d030c0908010501090219080403080f040201030605061b12090a1703070c090b04140c1209030c0f1617031905070c0e0601 72
    0x144854004000310070524800032032100711700d001e0303010301041c4c20190220751031107840e102004c06601c126a0180c0c0d042e4020020041145441d600000c1e01006001242c5d020f018241044d41da10050085010281526481e20340c06a074030501d812402000000f0090185581d500d031300c08029030104140000300d10310340000080e014000d00320039000304c1e45551404501c0d580c03944185416000036000300e0400d51624000161540c1e264081c00b0f444e0280ca4031441ca200c90000040e181003090b600300001c03070700c1c14001030401d5540c5101c0b5800300c41d0011540324280c0301781c13940356041d071051400c003c10500d92980040342c881440da010710100c40e4291001c0007460040b1864900300d40040310300c40c0c1100f404006d501c0d0022400464507400005140443c0e051407207000c40309040200c0c0d003601502c00d6010000301c2c109000d519041100500040784a45049844078804944034410800002848030a2446011800344034030708403041517401024650b80342d500e44580852000017541c40d0f0780091968030b6004 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 370494991 1250 370493741 370493743
    0xa03021306030606020a03110a0b01080606030c030708030d0905033a021602040c122f0a0f08071103070b07080f090c040c030b03030406031d06040506060105070f0614060111 76
    0x2007604c005800030510100d0913030701201c0b8505c4440946174140a003003410320000f91108070181c064070301c0300090072a40c43c04100f494900000005541d11036480001d0402c6004404002c907a000e0342d100201241c25000740c100b50745180f094980300c114a0b10411015001440c070380040c10550780400402c0c07100469490500c0301640103183d0510550014480e0305030062519034000e070045805418107049a0729010386d14022501c0d411440881c02d0222142040031520340c2c03034900d9115400014403410003542440080c901c02c08041010b0a208401380403802c400e0160060090000c0b0100480340d64101c0303032421a412803010356010011401410108407046180d00034140318030380341001031407102030003010000604213010019080c16901d40f960317202901c06000030f0014142c1ca4402017004440107111141c402c9805020004c40e802950500002643c04580035400003800d19200707840d01540c0c00c01d22041185008000d1100346000da922501d180c2d6410203520802090700d030501d000984191003 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 370496241 1250 370494991 370495001
    0x50d080709061409040906091a061c11190803040b1207020604390801090b0c120a2a030f0e031206060a0e220c0905100e04110a0302130603 61
    0x5143c0c40003448800164101070740024030f043d00a490108002a15440301e0072200c4854800481c2c8001c01d00810509040c0390403030400c1021048041780ca80a200c0d01c681c1040030380d9081c113070b1084501c0041c09152000304204980030300306280581e9961640c5441c8032030242e2000c035565200d1807010b4001942d450020651a203e203800c8000910307100000b5641c8120b1006261400c0350807101010040c88185110340f01c00c000d40704a60000880d581d41c1e0401031001c000051840c0e10011040203800400b4031081d81d40ca801000d18400441c06d041103220902c00c0045100b501303000c0b89140ea501003020b6505030005820107244030303020860301c4100101c040e100d1294a829464007000c4501143c0a410000018034202c2030a24080700b60b8500080040c0480303900c051a015120000d9aa041850500e80b146c0d20700307003006003030071000e180c5880c2c08035200078400403066050018101d05101140c41e180c0082c0c0182d012030501c1076072803094032406002904480d480011446505401240f43d0b4042d01c11 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 370497491 1250 370496241 370496267
    0x803030402040c0e03030a320d0e010917090609060708090f0616030e060405030712030f03150509090a05060a14010e010b0f030a0603020915013e0703050d08070906 72
    0x142d0302d4030200b49000c0d640009823207070590380b031a20a4503140d1188544d4101c0e800c1c2c08098040d00d0f42d15030f1040c42150a681605d0035038006030745040146000900860250511101006925070302c542007000052840c0c0250390b01507411850000300c000c01c1046d039800420204004985880c900c40403402440034601602c641100c0707650300840c5500201c0d000392200c070300d8180000c004a141688503000300f0700b0940c00d544024644210603141c00e04064100702d0201507000765103401c200ba801420001c40440741c5520440e40148109030224102420600481c5056500308080390b1150920300c0403c07000b001c0907010704c4d00c40003080002142c440303071030000343e4102c0d02e401c04881c0c103101e003880343c0d0306295101403e0b01c5045640c0d404000f005803a10704410784908042d50041892107444000549020986c0301e42d03210152131b90441602e07603014404540c40c1011401120140c1c5c1d03407200207241c9010760682000d4050310400c05003410141d408607900f4843ca81d20303a145814685d98601c04c0c1d4000c4984a0 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 370498741 1250 370497491 370497493
    0x203030a02130506070501020a0908010b013516020c1203040918060e2a0a0b0901030e010504051c0c2a09050906040323091c020a0803030402040c0e03 66
    0x82514203003160050540c0c21084012000741599500002e10b0940c4a0f5604541c9650040f4003031f16a603422108242c010641c04000340804e10446000900d10350b440002c2c000004100740f940680c10845000101114840e400200180d050001c03030315900c00c2003c81034000500c80c1020710040b600704a5107440807068103c009504050902d00c050010b0642890f1f00115070303050485050110b0000d0040341a00c0300e0410141136003000b035400080700d9182503c443c02c1c99032020b000f180200d45403c0c49a100304c40881c0300c42c5896401d943c0040f8090034040c5040c161540c00d1030140028010081103052003240c1020401008055130300060710203504010000d080003101039140d41c20b448891408901001000504015450b210440079088840580c0c009445600c56802c200c201a041840029460010b440c401e03618800c0c5400b0300f850748240700441d8040c0302540400200c0c1d0b542c5442ca2910560300802a40c00d658580883c00d0781c82d001107500f13902c10b0341445d22350046103020b55440c4070f40e20800340c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 370499991 1250 370498741 370498747
    0x100b0402210402010519030905010501060f0c06050907050414150a05130f0f050406090506010509010f0909050a05190c0f1508190c0e0102012304020d05030c070e1807060203 76
    0x409081500014810b034140b100c00c10120100d41b08280f040c1d2109001c58030f00250342c03002d50038050700711030050b08034070140302d10700c402d01d4600c1b5004180800320307691003400031404da655581401d0500e041c0c0d41c00720b074000e4203100c2100414001c103030640748a001c2014001400c85011010805d00010303d10800760403c1c10040c40001400840d00801d050895110380440c02c0f0482c074036507404442c000c5034241c03609a41c035891742e801c029051003050b0050204075112402d55042013419810382c040752140e17600139650303100d52000f00310042c800e028803950001c00380c4800c040c0c1282c011807401118181160340000700080810030700700581c4a20150d8002c0c6030030880504000d1401c1d0340e0a04043c000321402c2c880a0300c1560405031500442890340001d03030310304800714081400a800e4880703001e074801481d0a03000000caa044510003040d0b80c4541c0440d41e10404000c6401c15500b94803c1c5a0303440d071140075a22001c602c887c2d041072140e00a005500040c000906e1007041161500070b140034240c0142c000b0 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 370501241 1250 370499991 370500037
    0x18010b0f0d080d090206030c0415020c0109091e06170609030c0303070e011205090714030304080d0f0c0b0c03011a070f06050a0e030d050703060e010e06091e0405100b0402 75
    0x10b070003510060142e00b10020b0160540e03000500369030812aa07480c25900005018070020302e480c070002c0d1401d100350001789211007082001034031018850007000e043e10f5440219443c500585210282880741c80d09081045944820002c085d0700d44061a40800344034403c0810481240082100d2800e081180030b941552104402121494080d501540c10407001d08050140c140c240c1c072501e4060b407040070087c11000e00d0b140c20b405c0120242590a803203604244010000c01c03c1c045160a0200d0440c6031100070320504000c151101c803031445014090139161170400ca44044101d0056041c2c640c2ca40c04405c9994124150074901e00c56160b0080550026052030400200791b6081503801c200314940c0400e9141032009424a56080900241c0840d9281d07024450611303014031409001d03111741c039141142503052a0550612500192035140601080800079519480340500201d15480c141100c48180c2441d042c100c1d41d84540e00700364800070340381840c3e105180c40c240c4205c8482094641e0b8284e110441 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 370502491 1250 370501241 370501253
    0x50403030903032d0306030b0a09021302070f0c03050a1b0b0901140f0a020c09010801140c0901120c020a050607110c040209280e01090b3618010b0f0d 66
    0x8513a8544078500d0044115580c1e8550903252000d20405a0340c00007040e03461424002a000c801504800d101c03442d220a500158581000d2482a041144809039941302ca80c03400d4050360b60203010160550074515008000c0020210345884594003496111819001c5100302c8940f0000d01c1c0300789607400c14200090400355003d4000600004104403159003044182c1d03100781c85542c4485030300001600f0100320880e49281062a45002d0510030008002d901165507041d50307452000b414100b90880c012442104c16071107501e05043c6520032040c2400540c400e00030195560000034021285802541c00003055580306101e00300c02c840b4400c00416680003000c0610000390320140a407504075a520f03506482c00240306401d0648126800c0b201c52180303241005c0d1044004060700010802800d03c044403000350742e01c5221041240c0ca0440003151400c0c5040c0a92245a00410a40014441d01c3c100329150700c0c1c2d02403500d443c024080c024000e8003040010401c13000c42d840301541c0d00c100600041d07004079503 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 370503597 1106 370502491 370502507
    0x605031c080403080c040b0703030e0d0e010e12030c011d0d020c010e1e0405040b1519150210110913020324130207050d080705040303090303 62
    0x944040001c20095001c0d1000e02004500d001040002102604940c0140840034107642da4030311525000c0c1c003a251307840307083d0071034010300905248140c001c400408100c50b050352110030140102d000c0202c04400e03081c030541148410300c200200b4441c24414440914000b03000c410302085081105807600100e44041d03421900540e4404156907003100042e02e489104603850b441210303200c4031411030007000904243e8090b00f06424003060065032003500c4c1c021410006403100140c451805d0000c11901a041c024890403060010840b50f42880b4821084208910680b0454400301d280ba00c140c1e411a0b0030141c00d0440000c00d01018608400c00400c2004112010f50840c9080004604254080031032000d11107000814821079a0f00c20a42c4070b02860b0398a002c40d100c840071b0608540e24603041081e4000700d803d040c08540424011307002e95040b40e40c5965040065401c1d5a021180c0305c0b = true := by decide +kernel

theorem cover : BRFrame.Cov 370323741 370503597 := by
  have h0 := BRFrame.cov_init 370323741
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370323741 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370323741 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370323741 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370323741 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370323741 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370323741 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370323741 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370323741 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370323741 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370323741 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370323741 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370323741 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370323741 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370323741 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370323741 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370323741 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370323741 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370323741 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370323741 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370323741 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370323741 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370323741 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370323741 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370323741 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370323741 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370323741 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370323741 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370323741 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370323741 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370323741 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370323741 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370323741 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370323741 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370323741 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370323741 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370323741 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370323741 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370323741 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370323741 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370323741 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370323741 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370323741 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370323741 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370323741 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370323741 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370323741 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370323741 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370323741 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370323741 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370323741 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370323741 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370323741 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370323741 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370323741 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370323741 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370323741 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370323741 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370323741 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370323741 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370323741 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370323741 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370323741 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370323741 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370323741 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370323741 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370323741 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370323741 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370323741 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370323741 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370323741 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370323741 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370323741 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370323741 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370323741 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370323741 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370323741 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370323741 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370323741 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370323741 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370323741 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370323741 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370323741 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370323741 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370323741 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370323741 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370323741 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370323741 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370323741 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370323741 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370323741 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370323741 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370323741 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370323741 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370323741 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370323741 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370323741 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370323741 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370323741 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370323741 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370323741 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370323741 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370323741 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370323741 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370323741 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370323741 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370323741 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370323741 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370323741 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370323741 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370323741 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370323741 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370323741 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370323741 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370323741 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370323741 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370323741 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370323741 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370323741 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370323741 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370323741 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370323741 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370323741 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370323741 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370323741 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370323741 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370323741 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370323741 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370323741 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370323741 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370323741 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370323741 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370323741 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370323741 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370323741 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370323741 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370323741 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370323741 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370323741 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370323741 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370323741 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370323741 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370323741 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370323741 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370323741 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 370323741 ≤ n) (h2 : n < 370503597) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
