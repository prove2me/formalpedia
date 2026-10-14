-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2199
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:57:55.736772+00:00
-- url     : https://prove2.me/submissions/faf8250b-df58-441e-937f-53c3ce570040

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 395323741 ≤ n < 395503597 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 395324991 1250 395323741 395323751
    0x301080a03090905101403250905010504090c05091806070e0306090607020a151506050a0f170109110f0301031b0906050a090218120f190f0204020a020304080303070f03 74
    0x401c048116601076640f5000003170300c180100140d1070495140d0030b4103c0e00400ba80c10038030b03040b181002080c068034124090780c0381c901c0f03042000e105144102401044c05840c1070201303003001d0740c851100190310b01823584a00740f050040340c01c03840117201152040d15080101c0d1028104401c0141c11a02c805402d14443d10502c0e0010315148404105540501d1042d00140301040c819134070781e044e03545454004030b10035a481c3c8110760550440903052001b000f0540b1402d940e03000700e52000b0a0041410031034800d001c0d6102e401200107480a8500341111255000000c00d40c0800c00300b2101480f074501003039038281011001100f03201e482030000caa004c07506001500c1035590781e101c1c141503038501c0c0b10391a0301c002c8a25040049036419001441d1303003e00039114500b0202c4040014a1b201045880c1d0301180c0e01c82c01c8042e6069804218000e501e881d844030181045c40c0c03960320070f01ca50f00480d400030301442d00441c03d01b20301402001541c004d4540a0150398603403030210001401182c3e2030b0006000a4102 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 395326241 1250 395324991 395324999
    0x171f020c010b01110a061d0303100501171504181709090603070807030b04020d0f05150a020f07060e0106030203030315090705030402010f0f110f1605010f020a0b06010c080301080a0309 81
    0x2600c0003006040c4d4000c06020b20010544820004180002d1500f00812111640f100b5a040034002184103440c0b525100c40128140000140380c4c803601c14100d00ca903401c5405016a4510414011500c00d808407004079402c0d4403044030b0f03000e50a08450040c09a040c0440c076103004094200645000c490039514105142d40f00300c1059a43c101e544650314103600684130900200f8100c5030035692050010306801020440e598581040940d00d00d8280d60340c0c0c002c0032080324032407100d40301550000604101036003041d41428800c0024464007100805143c0d9a800040d901002900319000441c2c004003907a03200e16050000d01001d1452500c1c551141c04c83c1c070001502180210b069a001d80d80617940c8501010145205594842100000b4420701c13504032450001000108a40d100080d6890003601c3c501c0a10800d035403840d62150401c0b414800700b01a4846401c2d03000890507991a04082c103044540ca134440161240f101811001e450b40380d00000201e400c8100141105a240c030035540c007400346a403 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 395327491 1250 395326241 395326247
    0x60902040e1b04060e04060b0403080901030f1a01120912050c0d0906091217030901090c0e1513060e011706072a03020102091207060f090f171f020c010b01 68
    0x9404440d940140103210612a5620519045e0b99080700a440020820380720610580076802a42c001c540020f400a05041c56503418041c40c040c07142d0000c800e0104100c8050f07903090300b07289240b40d14100440c0381448400301c0c40c5c507080813007042c0d004070600a00d16078885006210358440c0742c004100f1710840c85110402c0344902c00c0320b0704a6485980f049200e506050183c1c0001010170420780303031506892247c60205c207a020003140030303544800002400720b01a2800c0b03404503509030300004112601508100d00c41040400d0b110942100b00c0d801008840186034510040069401c140c3d84090301100110381a243c000c907c12258684004403205903880ca0021100c140b5415020169035001420b010103160310880040f120a10a00016041125800119030010078070700d410079042d40400b008020071a0803112810102c4c1d41c514010900d281010700100d620082032042c08400055035110b58001c001c01d02c0320010550700e40081b0110503000c012000080d41000b401d0070525403030719001e00441e40c0 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 395328741 1250 395327491 395327521
    0x70201030b1c05070626060102150108070f0b1201050f031c08010f081906020a050d050f04060e070b070f0f020d030201060305160807090b030304120f030207120302030d090c0504060902040e 83
    0xb0014881034090003086c454543d4200081e0806040d0b201d40c0311002c2c0d15048880345180a400b0442c003c090540c50b00c40540d2090320160b01c010410f150803c10264185138481100707041d039900f510040651092707200400d00c1c04200041e8101c03418031041641e078a00390b00c00c600d54100c60001026440060b140c2000d00d86034a100400c2c0c1e0080e40c4155100030000d402c0b50050480c02400703007440c0382042500d16980d01990000c448030f40c0d0a2100404102c1000310360b114242c180c00003540104081414070342c40600d9845000c401400303019140501008000d005544885042e81c05018000c1d41c03c550315010f0b0103411640000c441c0b60054020b10303030f00c03010099006002c4a213108014a016803a107840a40140240c0e03000036094001000082a202d80d246034085c20380d4403520398516281c08078100281046000c1d0420702404407045012404241c1c00020754109500c42d140c00110300f1568a4030380d0a0840e030780d1005800500b0034a00240000180d03014104035440445400c6680e0f480e4196510001 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 395329991 1250 395328741 395328767
    0xe0f01060323060f0114040608010305011407170a1808120603011e050907050d0c1401080c070b07030e0f010f060e100b1c1404020103150803090402070201030b1c050706 74
    0x800000c000f40d030b503162407404001d0010040c105942d8007002c4030440395041d0b2281c1c11210220b8001c000400800c40300b445440e20182c0c20f80320403d031034200410003c1100d24510802140d80c52910082030250609902061402040740484004a40e5a28049209400c070102e0306031540c1d503200c0040ca040c103040c01600d098407241c24000030b841840410980091402420303030074880c41846404595600c0c1d400e4045030450081c01804001c41c0360201c03000e082c0b081c041d0345904002c480802d010140d070300e0005443c403d99101c001d48007503582e2660210000d20422191003100e205200310340342000010360081c8840043d45405010050725402c01c41440d00091354000648031203000c0400004203008054003108070015108481c40b4001d000500a84101c811401800520041800700310340c1c1602c94140341c00303400030280380002d00d44103001352640142e8559078083c9400103140021a817003035101210b190002091410f00140850349505c0580b07083d13408890511070310038003013071560080300480021 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 395331241 1250 395329991 395330051
    0x3110703020a0504020c330c0a052a01061710050c03060d1b030503120105091510050d05040b06010311070519030c12020c092a0703090e0f010603 64
    0x10707902d0f241c01c0c80025845444001811b00810408550038160061544250548030042c1d40c031000a1040c420640b410181c80e00c000c0e55401c001e60030f03145030800181c07540c82098102003410480500030707001d00c2c24601c1c88020000e520305040401c403000c10124125003000e01e0411600300c1c0e00a041608112242950104401e0700c00b8800a89149415000c400c1035a226010100f03100d544003400c240808000c1e0411204ca03040840c8640140408075140384c0100710440341c6c60100d040015424000c204105100ca0007204141d4040214034095412281c038070411404c1000300745000c0c00c100307444407801c0d0707552800603003805080040c84640c401513641c2075801c032000e040042c0d40f00107603150007101d1080c210244140420943c02048840d24640d2000f10a03401414000850034200140c0c032500400c007002c2c0152440002c514459000d12982c03851030004501e0380d55031100c0c1000d898003041c603800044260700d0b000407c0754803880891028106c42460700c0034000e1104e600943c84032032541007018901 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 395332491 1250 395331241 395331259
    0xd0201020705090a06321c060f0b100504050a093e0a0302070203010e1f0209060c0d0504090b06090d200402031e0901111c020d06120311070302 63
    0x10325003407121642014138070500050051740d800c800b0082540940144405040310020300d050382e04110118040450115840ca1002c3d0700b005412017132034429600500141d0b034034a1072103040342c01540003002902004024080b203600c0c1490040c842e50041c0190b83c01001425000030f0300c02003d0140144414403500401c10326010300780d045101882d80500d82649aa103030700d01c6005e5000200003442031945a603805a03442d00d40e80103050a43c0c0c07100b503140d5542d60000e0480a14a0361302c2c03072070410301c1c0040d00c00540e54440400001c0c40e54001d480d5000c83c07038010050508a52900003004200b1516500700500040f141e0108014280c010071881941100654030a580010b110003200b082c6620740b084424451401b00b000301d4120b130030488100741d419281e001d50b070200b0381c100400c95911008000c000d000e1511241000011805800007901d08100460307805a0142903d030140c65549248101c100a0a550751903119115100d01d5001c0c5c0102c0c40500050100a101140240c20380340c0203009150 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 395333741 1250 395332491 395332499
    0x3101b0c030909020d02090405100b0a1d27070305040c030303181502040f120c05010807020f01020c010f0b01030b0d030e0406180606080606070506010302060304142a0d02010207 78
    0x14580d050080220100901c1440209034015188050181c29040c160010703241c86200c0b0521040f02c001034030511031003a00d054108040d69850f41100c81c0f60b542c0c1d1800c1001900c0c03100d000010340e0786003101d50742c6c0994441500c0b04111703403032400042c40d450911049a5503445404080d01154000d0341c0250107101000010b10201c2e0094112110381c6013442e121045020164540c4000380c2c091860807062150002410000c0f88481c1e900480038094a490103507214030b0f556111070798051188609811720101c10000b8400301d00034803400d0b41c0ca01e030500c001d559078500c045036a4002c0280171407001c0c0480c544403a2880c10752013803098000040b005841d0701104000d54905559500b03054127011b910030b481d19400f040c00042e1500042060044003000700b4800c0c103003d0040c140da10024034540c0240300c203000344d5000c134500041981c1180e405990301980c80d1100d09203290301d1094442148560306c10012a05845000c601080c000040390080c01044440d4401c2081891495240c019005a208030801c0c0 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 395334991 1250 395333741 395333747
    0x7090f15050c0d020f0c030c090f06030c09130515090a06050603030c070906180203090a0f0f230708012919120c0e01031a3303101b 58
    0x80100c9905100d8288490324107983d241c0383d4030250f0200140c000c2c2404044000c01040801900c10040300603124400b14040403a4550000501442e0514503240101d01a42c40621010030880780c05089500c0500c3e14982d80e14810009030b0f002c450741d108419100303980440081c001030062010300702411610800d42c550760b018000150840d0f40c94001001402c02c40e03002000140020084d965020070030078503081c60112100400d00610003c180104100320b503070440450291096036000100451000f8242040c2d080c48448903401040030900c00a2000882d560641c2c010518108100704c420481d01c0d207071102d09840c51075003940100140102450f1000003603076007003103401c10b02404000c18200001c60468512915034480c00f00086442e50320b80a0040003496070b0054100b04418006d19459580d5001103012294064200e90741048042001005045031400c502d0220750003080400301c1102d0303911440300c0003400c120700c24419111030b00c0d03803c5614007a20f015880c3e440c0840721001c00b000030135 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 395336241 1250 395334991 395335019
    0x8070e06090a050306070c030215040c1a0d1d06060d021c14010c050306011209020a06030b0d020310020306011101060f030b040503070506090106090c03090c170c0405010803070201030507090f 84
    0x40d030340441c80b02c502045540302005214420003c5545451819906050103814a0105e802d07400d22601c9042c108400b24401c0c4039418115034400444c01c2201d41c546001c0c55480c020b00c0e00c1c02002c141002c00c0303140927400302c0e90304180020500003079074400e840d180d0030080b0704802d406000750040c044030549400000350100c05002c490242d05010034111206046c41c0c01c4a1444a218000c220080103101495a01c150941c0080c1c01710181000001100e40000710081114401c0c0030400d915140c10595584030613100100303250307000d811143c110102c0502007010390011914540042c40c520a4441d50102c14082c010844400400c200700c0c0d6419612262600c4d00c00400c00d980e6840101303e008002002045120701c01c43c0c0300c400025210f400d147c0d0749000c0c3c5140d120703460201030400d81350b24082800034400004440d1416045070b2a8900d10007080c0c00c007241d0188141d03201e0314200c000501d8800101c020300c0314038400d07a0104034555645000b9907504440d0300030383c410090243c806000094880d61a = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 395337491 1250 395336241 395336257
    0x60f020a0e1509360405030d0209040b0607060f0b0a030f0807080c060f0106140c0c0d0606051012140f131a01061205011401020a06020d06121a060108070e06 69
    0x40d2440d00c2060f00c0800c2d2644040d010559200d2a642d00c802882c168400300301d03048a4040581e804103081c2174071000d0382e90188101e10300300945d0006007900655207550010044403406801140c5032180c0b42040c0300140103040c021195a41040b05003105441e111224000f503079841603040007124500d8030f602095402c032a000300e40c498003c00028042078010001c0d10710541d41000401c500307605107500100089900094010480400e20200f000c0c540b0100e00d5442038142a00d80078401e000700d05288000e040c49511440c0c01600344001e101a56070b0104c3c2c050709034407401c402070000303900e03508200301501c1e800c0b24241d0619601c1c5000c181001c071342050341c1d0b1070316008242c0e55030b10f496204000d80c1c6800080c0e12040115030340382000f0032780901c02d029480c01814001e44000c60300c01c007800082d4903902c00400003014158001041d0f046402aa070001025000102d4400809000742c90b0202000307a201002a6025a02d04005155580b00d022458840c001954500d59400c5103038047c4400c075004161 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 395338741 1250 395337491 395337529
    0x303051501090803120a15030c090e03070b04110112020c0c011d030c010c03052703010513120e0604090606030605120a0503250b040b100f0803090d03090803030a0603060f020a0e 78
    0xc42c00c1c40d521131f82002800b840c00307004100182807400308003804840c801c005840d0b01c0e40041c4008404102100341d90fa50060304060004be400a0901c0100ca0b104e11307900c4542e200e03500c041403041d8056800214601000020780768500c80b0110f41c03402240601050700d0960745680725041c04403040d446075022520b41ca200e41016030600c201c407000107582154009c903600c0810340101030036086107403d010346504010b004d103580b0045904d607291000030104c80c440e540c041c0204480e41a02c07680341e62080710024002410200300a5403258802005400581304207481000b034151000235100c00851142c0c0c4482d4403034011407420001254103200c42540d54117000065440382404000f1404440c1681c0c0b0a0b031240c1204140c40c85d2244400c0040860f68014208500040300140031801b00003084a00209044882c0c0d070401d66180f40441d00e03001c494001c2940c5010200601041c01c08603000303001035911510091100c2071402114008a000e030b600304c10005040c8910001003418800e1010001d986045 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 395339991 1250 395338741 395338751
    0xb03030f19051b0c0405060402120a36050c19060806121005060411040609090e010b1c0203120f16030909060e0f0c030106050304032601030303051501090803120a 71
    0x4a46a6083d490401d40351519420185180440e07180a206440d404801103c045007402c2c51501514250307c2c00400404010742d0703402079003003015124041c00070321140b60207000303404076100c80421001040d144003c85441c072822204440a10303101001045903060301d0300380480316280c072000312240000a03001580024002d00017036184681445a0348050241190100709410200140000ca0703080c6205900380f02414003080c00140c1e4041007450883d091014007041c1548101e840a0040c0318441d4019481007002820003031a203141000c404400b8000c8055421600700f045801c58180300314680c4001c800c80420110200e81c00031400032010034020f24250b020300783c88022920490b041600140c500c03007050000c1011503103504481c03544c070410818800d070865240000151060201600003818881c100403524250040c0500b02c0080701d040710500d02d20355a4a0138050002c04054800c1006405c18400c07500041d4002e504070b0045840070380065141c081c03c0e5100070b0340e200002c0c000c21a455110 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 395341241 1250 395339991 395340007
    0x72d0f0b3102180c2805090603100504021902010b01021b06032e090b1005070215190809060f010b03060409030201291207140d0f05060c0a030b03030f1905 68
    0x40c10901c601c6084820f65501c0401d000440210640d58400031060561840414020b940c400251000ca07d810f946d1646c581c0c4401c00d048900d450260000e0741c01c18400328444640926640516154542a800801a003072400004984550348040454230302035211503840c0803030525a0040d54802c205040046039110700d03030181e0710341000d070490b0840c1420440b1420700c200d06c00c81c4a01d0a03070307034001c44041c04030101520010b04540511680079100b90030440d44902000c861074115132203500454506c400c404003295018140d03050a450003c050b02c00e410002d042461658a01c038140c400e0400c0190460f42d0310340c1004040d114041c4200d00f15500c0d43c00a01c544040c0c41c1040040100d51132011181d075420205010070117502001d07020241d40510400c10841c052140c0340f10a4440a0f038500104c080e290070410015044402d00038640d1080700e0030007903002840c2000d1f05202d0030f43ea4062000e9118982056038038000c0c41e0074054541c4041069214200c21280c2c07070686402c41d400c003541445a2 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 395342491 1250 395341241 395341279
    0x1050d050c040c1e08010e0109052d010f08013c05010b21010e0a0b04020712030906060510021c03090203030d05090601090908072d0f0b3102 62
    0x142c00c070700c800320303141d44c9020342c007001108407080d4806128a031140c0ca66141440902000308180300311403006070f07508040b50340c0d007400c40e24003000d080c13149490a050002c2c00400f000b4602092003010818641000040350041d01801940c11003034604030118203203001954002070010040c072444522600503250b5110716601c070b028560081610390182c6885881152036030060220b406000c1e5a856140f000502090f412411410b4008103902400150b84a400010400911071200054000220044042030003030707240c1c0059800e103116401c1403020541c0d807400e018034040031041307950158201c040340c4030740304480e134403410001e07601f5180c017055026954000c03e0542d400820440c1c502c0d503c4500b009800302c010004140102420300040080340d0080c0c0302c440e124003404a004000c24541214031f41e40798602d8070305504034080c007a03a2a503087d9042c81c203003407007030750115048a68002c000c0c002003800c0083c105540c82010322196075111400c00b1410b0241d401c4c0d6200080740e0082940000040000c1c07 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 395343741 1250 395342491 395342501
    0x60414010f03020912010f1b1e03020f0d0b010f020f1e12030f0a1506200c0901150305060604030314070f050102120106110c0604060e0f0301020705031c05090601050d050c04 76
    0x14100001850503c000810b609070b070b402002d00340c045001c40702c01c4441c1c190702c008909d400e146041954007ca440800048010740701b001e181d940101408601e0140d400c9495101c0b2255030000d803070f503001140c8001010790300c641900c1c80c4042140c1004040b00c10403202c004100140710017040585800f01000c3d00203008903001540d10610314000341c010030026040611035140800d2281d0740c0500c007640b8104004280000301c200d085000c3c540401c10491403801044505294040206042559070312451154804101041c180e80002d040c00c011803401d0900704101c81c141d079010303901ca0540e01c000400681040d400080b0403141c01c4440003c05020030400c0c0f014064004010f0305120041d4904100100107950420419100380c1219211014564072403049504441e000c0c200f15107111190750000300c0d0103400306511034255000080302c104014003c002400e001036110700502e110400ca082010403140212a480c2265014000511040c50400c4101c940c4510403000c651103d1944001306040d54 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 395344991 1250 395343741 395343769
    0xe07020f0a030525321207021e031f060e1b0f071208040606080f0604020906030703050a1208090f0c01051e13090606110307060b032b030506060414010f030209 70
    0x6052450040c0584409405c21640c18000c1c400600c4c0e903007041050b420380c0d0f00c140c0600038494410002c4407030050817047c0d40d0b100001c0004050310310481010440a0020000710400451181f400d140411203a85040303200303010f06040040340f007840e00011043c0c0841e070b0103100081203409092080400107000c110000902554580d00c1003801e00f05882c0c610250384042d040802c10340c0020046000c401c00c0000c40c0c0b5031042d01240c901d00d0688642d40880d043c00f109070005030160154002003800c0c4000c0b44c81d0301c102c174411581c64148555882e031140d03448072403034181049590002c007420911584190064103c03a610700301040100c4a06662683e00d90f41700d000c8003441d41034100e10030814811144104801401e240c00e10b140c4038500310090030b4881c0710b45680142981d5071070350b20f002940c0b02040202c1161100e01040318490b400c000481c80c000790100b0040c000a030030280010380c90b04103002520110780c02e10455200c3c0c07450120064445001030044081016428040040240ea499032081696 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 395346241 1250 395344991 395345033
    0xb031305251a072a0801020c0c0108090a20040c030902090a020a05041806030501021201080610030f110301110a090317390102040e07020f0a030525 65
    0x10141e580205600c0c0c0d4101c1d44003002c80090790504950803803003181100e040650101644107822504803400a034500b04102400340701c40c050300d000c50845015801820928043d1040390390396807101f40110f60040044504140540014020130300194034650905140c90703146440c1c40e02040000045030854004c032a180001a03290300c0d4113410340c00d11000b095048000d8600c15407400160040280c000d110360b1084590a10002510050300320461380040c01955202009541c0c8248007103500348156001c0c00f4ae45041d0051102190000341600490811240d10500e003101c4840c0c681c6502d9000107150802a4065407900742d11615150208002c026004581d02c481d0354050850402560200701c003207071180c0e8100c04106840c1d141d0b020100f141c0c580d0f0700c0d540000712150420303405454081c42c0744103109429800820003181c90150b0714103480c031a40469080310400740c050303e01241d90722445a8050041502042003000170200d0002448c81845921800c0040310700395500c51082c0c140d401803c00035 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 395347491 1250 395346241 395346283
    0xf090c0d05130209070207080606010c060204080304090e06282c061e060d060905070b030103210e0a23061b0705030a05060f0601030e0105070306050f030114010b031305 74
    0x1140340140f10140c01000c0c1b44000c06a0700c1c2003a10f016075404003e80554140030b80320141e4410400950111409800503e068907140d42d550807001001e400d001e820051503004480001e01d40300c0304a2001040301090306980d00340407403140ca03c60002c007000c0c1031803200107c0e800c501c448510b224004020051003604002d003481d182c08040c107942000100540d00107003c010381400000d9440304030320b91019400580008030300a0030714010f4038012140d880f155803060048000010322000c0211040703025803001e6a90020101140d01301c0e59220300c441c00a038802d040d0071060015403010a41c0c204440060303650103100400c0350002454941000e1803044000e00c0206001c41001024002d0b0401080180c004281c82c031810782c2c0e01601c0320001000071040c0a42c440004090740e03ca03400015251206400801160410b140002c1c09050300c5c3c0201405801c51400c0720140c0d090510502111000b2100b080401e07900b450510400c66002810100c224111200c0c5003010480500282e4601004503031740b050 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 395348741 1250 395347491 395347493
    0x220209180616020c0603180604030e03160509150f1203130605040302090106080c0f040e0f060a0506070b090c04060e10080715031e050109020403030e0303090f090c0d0513 75
    0x3151240050150000841c44000880d40da600044c009140002c1141c000381c0782d50b40c06c20800c0407680520b0154403103100d0001804245500078141611420f400c0d001e841d500c00d0b101201383c00156142c89001c1d00000c1036400121205004e0007106203000b80100480301d42c0c00e00c0000203129151540030007800d41c0000555100c2502d2403600c40d00102100d0610a04061031900094000c050500c00d03c014032040e040018580c016080444201d0640145050348903511803140341c00340202185c180501c100c40c0c04c082041498074500c03000c204d8a009010a251031076903070703501407402005410005940f040348098807036035403640a050003403c3d4181c44800c1c1d5141403103140000280b0b59001742c101c1d8100140a0003080081001c0f01600000ca040100c1c612a5203511102810a080040198103162a00200e9904041e40042c030442c0c1c040d5460101e0b941043c030415403a13202e450f034540d40c0f200c8600442d20546c03c015a8441d03120305108000c9003448110030250701038480480f000e14031244e00d002444 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 395349991 1250 395348741 395348743
    0x905100f0609060f0b031303271d101403100603050f1c02281b17030f03220c0303050a081806010605030606070515040c15020622020918 60
    0x4001000000e65541c000b501c5d01004205900c4003500e070543ca100b241c0c00b01024075014018988030781d04003c3c40043c80c405000c80c00104007540b40103c0d0908552400781001004004060600522401e421749000c1480c103039410240c03006000345107405006820300c001484a1600c00c6c5001503010f0400303040c60000f2001c440313047c01644010040503400f1101d54862555001900346202c2d8615950240840e010400c01c008441241c80018401c3d81c6034011044084118a984801c64101d5508256450a18403600c0e803a07000c3c0d500c1e40d0459407010320009030340700c036010565482d5040013601e210361907070152a184219a0650405e40108600103002234115921205560b440030401e10380304100c0c100d0349501e580303075a4180b00d40300402c0404004281190341d450100c0f01d4495000080f129407a05c1385010a003001e2048034140ca200706000300c0040c801c681444050302c4e8030307225405460325a980c03246459214034403880607613850078850810390058449400050240400c0c0600e00d1100440e0b103526 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 395351241 1250 395349991 395350001
    0x2309161404061d0103090f1109130f060c030209060a030b010e0402030c0706200711120a0803010918060903050304020f03030a0e0904080c0a0b100608010e010302040905100f0609 78
    0x904950003080004000e11640249081c0301403240c07800400c0507000c800b004070094840c107403001e000031407034800703005c1000303c0c240e0180320790842038805204690350710700869400320070000003a203035a28989048000070a00d900c10f075090503080c2401804e02c0254004111150814200301012039600c64016410350f0300191060b0428404903005d44c994a001c4013441a02c0c080c80c0d500814068a03500d4181950000310100050019044c240c20f813186028184844a070350503118050040003980320f802c11161010071041940341c0c019001c586103918046043d8018514101c5204000b010f00c1014000190726000e0350381114025641c0d1501c0382424010842c884003505c400d284039a00030080c0c42c0c01584c0105040080201c121022071039a521820f280c01507200d1070525084600500b04c00f401048400c6211901800b28014801c140a840308019500d8030340a0003116203000c01e22004000500e07254104a81491003a4141e42e8001c0e0b4145900e41a03540806410754050f031503c0061003485031510070 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 395352491 1250 395351241 395351267
    0x8070b04050607080903010f0f0b010305090a03020706180510080a1a0306150604080102030f041415011a0d05070503010513091e0807080304230109020307230916 71
    0x100345098a0100050554400c5403402840940049070b80700300e40d9000c0d0321506080d03a9804050095120030400039006000c8070202601103858440400c1c0c08001c001804094554181c004000440c1480c9081c1c400e0030780144100c2c109818001d011826840d80109083c084c945a21514403600b80b0304001400e0381d8001c03c1426104500d000b11030340550700085e003a50401212030960281400f40000b040c00751085404c6400f0303a600020500c00301607410300360300e4461070181070f04541000503490300c5a141c5103070345c1040c203600031401c0061041002c1000d400301e03ca0003641d0380d28075054a8150f01c1c41036403c00c46042000c620302100400c89410700e0160300903001e10714101003008400e103540c0c200010b220000380040210000407104100700084040b1001c254004940c0340c0c0364541450441c040c0000d8144611000000c1da5000c5a40d180500400d4425640107015160442c184008400d5000c42a11045450382c03041803401000d8851500702805850284075003c0e000140303104c050b208500d0303420 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 395353741 1250 395352491 395352509
    0x1b060304030807120b1503040c0e1303050901030b12060103330902012a1a010501081302030c0a03080903010e030c070618031709090f070c0b04061d070807 68
    0x10410001075030050841e0f51041071030030303c0e19001c0c418101c0d0000500c40f200c10182c01c151044a07081917601c0ca0005144924841e104108540d5114811860038240580324408600083ca9810000a000707101501d141c25062400280900302000000c08088122825104542244005009100c611010720030844420000c6410382d1422f403444d5043c03403512252441c0e501c0e54a000120840e031240060700140102211500c1405a4150410581078204101200c00d480c20100c014940e08100040504070b9030140c44201d40356441116607541130402103c107e0381402218540780f1959920920303038001d0b5024284250310382c0020f50502d4210380354114180c28590050050300325860000514509507810b51500c0c1c86d10102c400003065101890703400003814140c102e4001312440840d48003400908508944000040d01c030641c54000101c0165521000210400e00d00c101090181d444150000d100b14000a010008500701c241800d180f106662141d0300301c1e48007008420000c0181501500040e9 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 395354991 1250 395353741 395353747
    0xc0b07060c142710020601060207050102011407181e05090a02030f06012303070c21020327120c1813060507030f111908010b0706091e051b06 62
    0x40c0d800411401440d003ca019020480d45090380003100c0807651034915809015142c01c107003d070790080d444d10310900481005201d040c00000d023640c4140920044490300b2040714040e51200740040391005da280b90441681d903404640019040c12110714881580b070094400510701e81860300700300e0030f40340c0641494038050052081c804da403024440f045401c00424242032800c030142915900060640c69074002c0859004001c0080164100125024143c840c143c0c3d000e40007001c0780322150291849482c2c000603441804159a841031040c100048540001342041c00b4403d01000201003800c40b20301e0034680d4108821080050600410303800000c2601c40d5010f1051606140c0a0f15024504e20302400650b225004607890714043d0303129000b1f040c464a4280032a4192144102a030707400070742444030b41e948070310200484034403d00505042e50105030540b89404c40c1600c07000f014000001040d110383c54141d500d000100380c90280c440c07015228078003906410150b4035072120005580041240104020 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 395356241 1250 395354991 395355017
    0xf06051603090c0e04051f140612060c090f030a060f1b0509010513170a12110a020d140a2604060206060d060e1501080601090b13050903070c0b07060c 66
    0x300c801c074080d078900c08840c513082c1e80d41c0c1c10450b1600f0a2103c034482800801c290050030982c10b60403003c00300031442030380010390301e80c481070102844c80c400901909070000004500880b2046000301108400102500304000302c10f00000d0070041c00800460740e580d41c034000c0319440c102034095440654a008600070714848180700c058040d10801c0e40c8241046400102508035500207094600605044491060080d184000311551000c020034241c0b0a140c81004040301c0d03600c0350044d04a1041c2c40f0010302282c0840e0b5080c05940d0540a0040f100b07540210160002d0540401407190818041d20099182c43c403443c0b40490301d4122040c4002c00403408010620000d50006000d58110301300350340018065910b030400d100203124440c410841384c040e15a00741c00c01180300c075005060364820803d03603600366a00c0030910111101d0071410b40d0000d45401d085158200c0c1e5034001e036404001c00e0203507482d191145c0d8502c4090030454001e54201c1c180030a64000f07200e02ca00c0381602407901d506021880300d10b0 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 395357491 1250 395356241 395356253
    0x20703050a0b06011e03141005010c03050c01110a0804060e030f09010809010b0a090b0102010f060e0103140c10171506031b0d0e030406020f0c090f130f0605160309 72
    0x785100c06444a0310840c04100c4070703482800100300070580488440241c40c40428010085c180b141c00040d0284211804100a2078040440300100d440584a10444004c1170341c003a034040d00004812034080d5a5000c04442d2000e02500500200c1120380c0e9641c206c0c070386031500c94201c40552003083c2040c0d0040c8190030009171900202c070825002420300b00d50650b10301440d18050702002400b40d41045400000182031981d5400124060600340c001b401500328030f00c03203070b012140240b0034402c549500e08010404160080c0034842c1e500091419250361001c1000031032410385402c0c01200c001620159130b5024000303411280354008045001c4100341e200c1c08000124240400341a03418000c500790b400b000e034088030b1011079280c514000c1c0203100400c0c21340510342e00c3e5002803041d00098003c11201e98801600480e4014907202e00810150a50f103400d02c00c0e00d60b425000b01a8020414100781c080c0c04242240415202d0520030500401d40703103010030020503040b604050040070700d0306200030040040c070 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 395358741 1250 395357491 395357503
    0x10203270309120d0e06070c030201031d0f0a0c090c020c040c0302040806180706020a1a040201030902120f070f05221104030c050102011b0e10110d05041502070305 72
    0x40401403040c514a24215031425441007005050348400703642009010b40b40045604a0000690307103612048030900018066144207504004040000c00c5400703100540c000d90000c1801e9000d80081c03445680081e40d0750f1312300300c0d48100b80c040700c0e404401e041e001c00c903a400e00e00010b01500602070203c01080e4502a60340c00200400d140309944800310b005c0081d1090741510010518003003161018146010b00c00700c40800f40940311194020407001090340c0d4000a204145035138407a0031b120400840840230341c04034802500890402d51100d0008001d03076500f820290514503a08040c110444110505a107400030301d6101c0220880003141c104080c0d43c03281420050800d40d0001901401281c00001c0700402c4030481c00e41004401241c04400d100d50711000e007003682c80a8008000295031804119182d0864611450000740c030300640f014a81016886496604c2e01c1d4180038200c03d21004000d17042c00c140400d5240010310100d010803404080b2400d5a040d51554000b40c54414115290720703031201 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 395359991 1250 395358741 395358781
    0x308030403170a06080d0f020f07090e2b03150e09010f14090d030504080904060b0a0f030203040b0114031e0c091518220b0703140105061614010501060e0909010203 72
    0x4900038107540031f40760090050941521008050303035442500d40c4c131654001c1418110b0303101c00d48500e40007100901038428004101c10135400000301010010170084010f0310690041c3c0e401c0304d0b144040010105115201d25004070032134000803542070360421030b10044800c0b42c11010020382c82c2005002391402e0100390103036004154a07000c03480f580d0303900f000509485031291503900070b850010001010350310f201c05400990b44a42e610500e240400030124242c1c003054034080c0510100744010030103105982ea26503400f04003e026145001100d02032190004080f501d4400660041400307a106450300741d001c581d100198241001c3c400002d000401c084061001c005c241520700d1002188078040e40f20b0780d4262000002d0641d895605a82c9800c8001e00001e03105d01001c28248140b00e00d86400d500c941c54182d68020703100381d060640400150101d00f551803002c0d91701c481206000803080b5800c5c003c9a02904250310707900d098214603014014a404000c2180003964818400d005500724100d207035200c05 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 395361241 1250 395359991 395359997
    0xc0f091802100323010e0103030f0203030c3106090518090c04050403021c091404020a120b0a030f0b04141209040b0105040909051f0207030c0602130308030403170a06080d 75
    0x203009084c1c41144001c1000b141440081c454800060f00c001d85480742c9040e64420360710040541090a8140e0f5640015605289000c0050103003c0041d42c0d003442608032200d5076942e5800076500c0e14482c9041c0910b58220320001100c002041c841ca007044040c940000038480540311681c51300e96001e41d118441c2201143c80f95171944040380516108104298549001c1c850084103043c4002000e442c0c107446118900400c103420450742401e140034801e0b0f80c1101141c1c3c07588400b00b2540c540c1880107010030320f4015448403000e1001b00104828a4a0110346803250024039401d08080c141301d2514890245040700c030b41d021600400c0c8040c00c46058070f01182098902244100134000141ca150086812801c1c001e07241030342c00310502000040c03800c00000e4842200d0842056940b0b41c034264451010054082030340b4406850020307801e50300400c5840038215010604c283c0340e90f180c60803039009890607000584a4021084051840e060068106000c0f100401c0928901268035403902c07200c0b040b542c14 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 395362491 1250 395361241 395361251
    0xb091203090303040b180406030503030610031d0a11030c1e0f04050a0507081005101107030f12080f040b070c06110423150f03130c0f0918021003 64
    0x540001002601c060241c0201507035216500d0341c070313454440c0d0043c0c66000e0005401e0101c402690030f252040c032094030f0300b12001e946590368401c1413046c4d034208107080310100f542c0c0b4241c0015402c1c0c0d90102440443c14180034040b410890700304404038400c0301c09600d00c250012042c4070160f5990b41030304481c0c10543c0c1d4240701013424200015a100b400c6140e100c1d003040c105800c001a0780c506078000e5108401c0c94990304c4040d101c030382180550494601034950032604002c100d00391103010300c4003111038548003805c441d40980c50790345805400e5003600085984107400c502000411b900540c006270301c0801219900c00380c1c50941c07111005e444000d0002414415418500740034040290800b1407c810305441c01e035515540c4251302c0780d0741c40303400503038180b2840031070b403911581d151a41c0b0003008941103d6a50f030500205081c82c483d43da001500704860070306207090980c0050040c894001c005c2144031242c0f98414a01105542030303c00c040703690b004241310b070810b810041c0c0c0c0b40c10400d4200f5540c0d00e00052 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 395363741 1250 395362491 395362519
    0x314010209040203070306081c020622080406030501060807020a0807030f02100e03040f0b09090126010608150a0b09040803070c080706020903190b01030b04020604090203090d0306050a0b09 83
    0x20081c4584066607800c14000010484403e130550000c800300d80400c422155020800d41c00fa02041f01207008607401600070001180d04000766901407054154842c04031024106107a464990950081c0e120a000c60340758001003041c1c68000b2a12544681382b8000341a1000c450781d00d90401d07100d0f102000f8148007a8204a040262080251850820701d803401004200007610007140d03260010700c0b07a0100c0b000300300b001294003282c582c1514a48a00a80303007100c680d00f4400c4150215020f4410014129151f400558000209010304001000c624010f0000e0340c900380c035241d0129000814241003141403141d41002600c41510300c0e60712a4000d0a001c2d202e88481004550400980801402d200070100d00c1c0d01c00d110156004221110046044903200d0f40b0b42d10020301d04070022078016100c40320381c2c00100041002250640e078481e00c018174031454107840300e5000040f070b001070f40c2980480c2c0c003100140c08440c0c0c00d4414100600421a04039035020b10b088145000d51140c03100940c00384805003811a = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 395364991 1250 395363741 395363743
    0x403050310150306080106080d05040b03070314070c02030d05090607030f02190507090b0a030f0b0402042903121c0b242101030317070c060e2a0a0314 66
    0x10040c0075441c03062020b045002c41c004010b00510b026000c9154030300035001542d4032001601d40280c0c00343c0c0c0c0714942010314107001c1901c540c000820344000e00d500e40358400707400c541c803010783c6100b664251100300461039680145450160f020104c48140300080144240559039403040d41d448a0741031520b4014481291001ca060400314903942864450f02c003500010400d000c54500d0558400000070000e0355169001c101941c661840f0152038134003080030750000310b05e00f00340503a8803900160000c10200c4013608da02c406190301030200e460780b10400e400850700c1e18042c002c0e003480300a0603440508016042815051a80c03140031105a19656144030324045d03110030082c50440010000b1115003440c42d5005409260b0110921900c0f4000800d001d8210b01504141b003416a40c0685e9544d07419000301200300c10b84500903018030b09110443d91224006402e03802000d01e800c1140300a030050580440216459104200b0990f039261320001e002c03c03e540721a118081200c0d088504500004a13000302a = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 395366241 1250 395364991 395365021
    0xd0905030a09090b030102131203090b0316120c0813110a0305031224060d020d06060518010207081506013e010902030606061305031e01051e04030503 66
    0x90240c040460784810903900084124100d030100b040a028025403401018202d10401d500c0d1a011423600005016505081c03080740e450600c607080000c540ca840321544200754004680305080c041d160340b4824501c80d484019040c01d000052018000003400301409440e90390001c200c3c0b2410400e0b00351070340034030100c04070220000b507001d1704624490392682030203502d0394400548522104100c0e0003184c0c0c007002d2050401c21940c01000c6544040f510a400c0204650050070100e803841d4080c02034160030104c074450790004051503140d0643e16100b801e00f006841520b140d82c28150741105200b0880c03074001140482d6072a030320010800b49550f511005032038444002100c0b141003d642e0644009104020b02e141c5041501403441c00d21075111040c98078282c6001120003901604070902140c09814040f0180c5520500701c0204051191a0b0000c40d02d41032002e42c0c21100b1038203c0e4410620f0b203d0a10446400800f098800741c00c81c0740b120703000701404401a1000b400c00c23100200080100b007940c880c03 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 395367491 1250 395366241 395366243
    0xf0206040b15130e0703140f03030708131e1e321b130c0e0103050402060d02070813050621040c0504050c0c16062a02090c03040c0f060e04020d09 64
    0x200300c20300904e10391030b82d078041c507000840d101c1a08402c0360030344520004120010317001c94002140f640d911807030115003614020306012032a842500c00c29000420000042c400c4034100000c010307402903d03080a503841d01e2204107108611204102203804159414009440b551500c42c1800713400c40320001c10000c0800b446001c04103405503105d26002081c80305a41030140c4001c6844506908540c0c0d41c0d00103c500900c003031808200300302c03000403065000e90825640a400148030034104140300314044141d070302046048510300c000041000040c030890107080007401c0103072182403c1505810440041011118406180302540c40c0094200300841d100100a000050424032490070b10300021a0150059240f01c0414080c00c000c0078900d04001032840304076076482e0b540315104000d401c8400c82c001c035003814080380302c09030b10440400350705c451429600607007001000a80e00c1c50581800d100451a640060b024100d04e504200f02d1254400740300c418183e011100103075143c8603403038030741300502850f10 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 395368741 1250 395367491 395367529
    0x2309070509091006060305060603070c0512041e1401140708070609061406012d14030106080711070503070b090d05010c02010209040f0501030f0318080a080403030f0206040b15 77
    0xc200032590b08041030341c0d031158280f4181481655141c281c19400da50341200c1c030f0740d004a024000034440310300c03501e03074640703500d0117003060b07542e41d850010302d0403003e51094010303009841c2051042c003100400f03100780c880240303202450450b00044010000b024929010300801c0048000704014045c00f405a048072606540300e10100315580041c90440041c1020350344840c400c96040c0b0001d01154001c0d862150012203941c17000d0b402d074005442e40100e03214000f482ea020032a15290060448446100440c0a0300031390312500c0c514500090000c00c40c0301d1081d480003064210641c108065200020401305403031000c042a03443e903003100040b4800a140d8580070f0029820008402101601940101102030381980c1c240710401c0302c00c0e2001e082d95820310000b40900d80140301030003c40c0c8518440c1801201c0380c1c0d0341c4100c1c266a034503074904e04100d9141c2a00e40900005041003015040f4030b80301907015060001d060541b409440e24050890020130460354184070841c0c524255a42e444000600d201e194 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 395369991 1250 395368741 395368759
    0x51c021f02120d270f02090703180b09070501020a17070609020405040b0103020f0301020c1e190c1806081e01020d060b041e0302031c030902090c0310050423090705 72
    0x1240c41809040903016085044911035212203900c0650074586030450717001300081d80c022200f41c3c00d1040c02403008044008142d5603600e00048405014038143d180c60103411100990b00b40791883d141094801d5100358195130103642c0b04030010340303103155058983e10510003135900d450713060600d08082c4c9401c14000351701c00d2030310040008200a00d00c007203040c0c0f40250f840c003400074040010b1500302e00c00e40403680f5041d80402000564202d031100c1c20065a603044d82075800c0740c180d4840808170050210022039101c000b010003400899150101c00c4c00103034134a401803000a14016031640c40302e21000f0701204c46845010403000c00d490940480b0104040301804005c0f840e910a000d85041c1c00a0065800100110b06091040b43d118842503046c0c03034005014142c0000601c1c0100d4585202c6103407802415240c03484070016954400d0090b01c6541003a0f0010b50b60b26120605100c86403841d00503a06c10703480c02200c2c508203220700b0402c1d1419100302000c0362aa440d0b241d440341c0303030001c1548a0355018445c8 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 395371241 1250 395369991 395370007
    0xd091412162d120f110c2205070203031e070e0f03160b0703120207032f0303160809070e13031b050a121b0204021605060907051c021f0212 61
    0x1071030083c3c00041d8a5540c07011900c4a0030b07000c44e6180c071500e0806903568000c0c1803521a81c03801030074590010519044080c6201c0640782c405065400454030750300907800c088200b11005d00c4020b40b8000640358030094159038034120901600c040400280a80110303207001004565440802502e5440f05243e41e44030003444c0c1c0c1386201c5020380d20545044002a40c207030044028203889000380c940c020341c144c442070007405000081445d1443d2500d00c0003000000e2030b20240040405200a6016056034510254410215040034145000c00b615019195000e0b1208000b12114131407201d80003c200c1c2c0040884040b40c0c103044460010076a8104800940c4485850800130001018a00e0900c0307040b400c43c00c0612801e003940c11070b2400c00300100302c504000c00b900042ca03056009021410008100249038150f030380b00c0ea840c3c05812116411150301503007051105140c0b1420030f14007420405003201850080c2d0340440d0340000400340741d10722161004070703502d0074500078050031001302418200b680c0c076581d02c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 395372491 1250 395371241 395371253
    0x120510060e010302041a0702030316080d0b100c031d18010e07140307052b0608010509010911100e03060408070605010b030411010807050d091412162d 66
    0x5900c10344021504500500e50103500074000d81c0c00310380240d40c0004200362500030000150340000c03422a80760000f0019542d0740704c000b03099000a01c2c024031900361120840300b0000304440b00e80700d1141c820b090101500001c150720003001c52543d645482c22030440c090504440807009401c024460380403142406084070310f846018001d040703c001d00b040e4811515400c03015100c0025103070769070241c82e900b00002001540a44001e06401d0848003600410b080c8403c1008940718a420303290600300c0d11a40c042112031024001c164208210100801600c011555000d80b2084003152081c002c00c1c9000c5050300c00c2d80a0000c01c0388051010301500d9107071606203403056079603028070011a4441c0ca000004a5001180b41c15031348200e5120314010040c1551400543d58008010305c0242042003c02035000700c2c02c01c50007001141803080020f1a0407103125164942042d050018441c80b0302c070b06001210004c22401c1608030110781126030648440c01e800000303c44200e400d5100c150700d01e1550110420040 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 395373741 1250 395372491 395372521
    0x31805010f0c050a080f09120d02090307080d210204092d200d0f0e0706021b010804081b0a0c1e06090b0901090302031006030302060c030c040e06011205 67
    0x607440a00300420300c0807003030070368503401000300101c00155a072000401500545072034541201d049000c440c020042820700b031510350b1000a03040b5110b44c0214013440281010001400600706071405894483c4002c0c1c00145400e4040080c500500c86400c43d042903841c29504a4014100e030a000f841a00c3d111620a0f94020000310000803881099203024000401849801890640d2402c50ba041040001210070f031a00058000b0b13014542e2a01c0c0f8050910040c402c1554105458005e44009442c1070400707800d150191800c1c40d080030100c00308540d16a40600c180c0d5125511003402901c41e140b0400030030300c0383c0301046452400d00c1503415030740078001920082800c9581c0b4800380401b440036907a0010803440a80300d07000c0400e0140c142031043d4002813000d400e440c1c1d4189032804505980342c0000e0b00d090040382007042c0040c0c0e101c40074018554107001d15940081054180c61460901d000b5189191149118105a980c02440401d905070310903000c210b0410071000060106082003c0748075202d00c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 395374991 1250 395373741 395373761
    0x903070e072d0509060c010903080106091e0306110409111206062703150a1505030319030507170f06010219020612040f021002030301080c040605030309010c0303180501 74
    0x2a602102c10340200c10380c500281c0310031100c66003420007031500305019141a0008a00070354010000e00c070000c0d106400f40325580e40540240d40700b031155490100c0141814030035402180054900340c846080350706a41c0102000c072503005400054119600c06513104038091034108240301410043d40311400c5400074007900540c41e1004000607980ca8480c20085c841c402c040d034120b1a4413040803800e0075090108464210600d001d0256120300d00c0751800181c0c010400c8500c0d446099488050396080d840800450300604403d5000714a4503e6038032903030b00c6102407010800d0030180c0380d4000581c4144a0403480c00c00c1800c00564007128140000104a90581203404174018814004505128000082500600b503005032000d440c0070000e080780e8140c144020310690703258902d481000016200c140e12600500c1d85ca9001e151a035040c0010b0a0821401c4081c0a11071804c040b001d0100365404001c46407140c009081c11045280c942c0b074250042c2c00c140e4520082c41d45030307411810a220064019035500 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 395376241 1250 395374991 395374997
    0xb070201052206120e300d0f0c030501080a0605090c060c010b0118050a0314070b03070c0302190206030f0a09020a140102060a050c0f0a021005010f0e1e15060903070e07 74
    0x140e550842404446001e0071003d495070210746c100c0200141c030b41c603200d07203070756204a802c07000080310030200c030346602c40291184007503a1444131060022040c454039010448928061000d949003184655640e540c45102501c550740e1031002c00c0c2c6a00d000c001411003a000038010719210094254454002d11042c1c154030302080d4078040c07280350045401800d105660000301038145080c11a00c605018208042c1c001030303203105030803011a040e050342d006144280c0e00c69840c817084030000c0c42e0080c00c2060203402140540c000500c05030042ea2800700f529071180804490500316034a01c8031940c0a402040340280d045804844089001d0703b410309000e00f00310082c1c088903140c0d181c01460303c00303c40b411200340391405810f002181400b00c4c03110041890030824811a07007240c0c4c4002c907034001c13a00288d201c13007440c50481c0360800c0400d5010400719401342c98454503074140c510042c410420400b0081c60740c0728504006241010694030101a40e003030201c05011206041e45400715520b41c50030a031051004 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 395377491 1250 395376241 395376257
    0x52101060612050a0e1b0f04021218061510031d010e16031a0c07140d0306080303070207271508120403030212161b06030509070e010b070201052206 65
    0x251124044d43c407204405c0001008a00c1c40c042c90406400040941140e0200e4085801c150700e03502c900180c2003510011801000504000220395131380b00d080140d81c03079a03030421010051840e6540c608070203c0e00d81507078103400108000f40d04a00420141604103c40d540c072102c2405c0bc0c400560206682c82c8403c001c541000b242c25221300c40110446c8002041214200c0441e1845108440221341101500e4400c42c1801c0c211390798411008110a15605540c0c40100d403d01340c45d500d4002c0d10010410702c40a1859800c2034a00251104d00fa40542e6200485c101b1004442c41c010503003560b51243c013100c1c03c1044001490307640c2d005118038891b04c081c80c865441003007800f041520841c3c0450758150001e0005140c402040b054680094662822100300c103201140800c00d449400740501d015001e0403400e00d0700381baa004c0c00700d580191110030a0350100000340b0940c80500031407030540f980f001c40c0a40300e000f18030040b10b9a101c2c2645150310240c1c10180e0220b40038916051400b40d80e495250a15 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 395378741 1250 395377491 395377501
    0x6120708091e071701140106050d0f0605060306040507050c030c03040302040c0f0f0f0509130e060709052101020f12190c05030a020a090f0b090909010603080405210106061205 77
    0x12050360999014058020f44000c100704c1c60a9004211040b8000d400850b20b000d401d12200b00144090780210003140000450005404040c8922009200b11103c01c200ca130342800003051017400002c0000c1c1c0241d50354400b00c1c5d419801107050b5030030308801d6821a6900c184800220303440ea0010710040f8015801d0010b4130008901032307003020f04805150380c1d4480e05c1c1024400b007181d00e04e00f500030000c1805005c014040d034640b1005001c02c003128604d140890b1140d0502c1c600c500c0c041000b04108204461204140300d95a51071030107a03862001c000303031a441c60700c00d00c440078020302c81c00c110940590310000f60b224149145414a9200d03000060128444106e0f8098030801e554000042e1800154200f0024136100160b6000d0700c00303041940791a111140d01c0715403505240c0b0300c40d00215903400700441c002d8038929020400c01c1d84111504003d01006185545d81c44d644e0241c1d000303951140d0088008041e00700500700c1040c411b401d01e40000d00c140766a4640261040500b45400a1410304040006d4 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 395379991 1250 395378741 395378773
    0x115090608060702030f160209010b1804060305071701061206050402090a020903060f0403180305030c07090b0307140111060421030b01140d061a0a020706080705070f020612070809 79
    0x14410b0321560017071407800c0005e0070340351301340d078032485810f070b2404110342141000d82c0384c0d0341042d80642092400700d0350740d9a001722440d076124a92070354103200741e08110041c0005a400b151010032950304c42803580b01c100c88295813601610301c0b500308500c0b50046401d0300c0280b10042e040b440c003c40c001c1d140ca41e41e40d15200020303802c0e481520403c640503400b00000c81c2d2002440c8240325841802490005042c2c1901a00c40d0314030340d00da03442a50282e1000c24500c00000050201200800020104200d41d9540d00042a202c800f1882080c0e1505012741340d4400a0340529218050155284152000340c80c1c5454445142440207141140c803140e0080035106950180c42005460342050b162001d103164090a604c019600c1110b003084140e848110000350204100b09c0d800181c031001d140e150712020720000007840c080e030703503407000041102420030f208105400c4401c803030580d90406501ea844400e2030021030000e22502024035030354036007072041014266004c081c1f01d002c1e08849041d01c1d40c100c0750070311390 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 395381241 1250 395379991 395380003
    0x20102040e131a0c031f080d080f010b2106060415020607030f023a02070b040b06060703050f0f04030b01060e010e040509150a060f030503040602010e1903180302030115090608 77
    0x150b040d0b44002c0000c5a401c0034011071004c807100744c4586c1c2030061074441d030140e8140b14441900c1404522181c0034400c0d1809000c07000741c0940b51040b941410a607031912a144159810202d81465000805c046400c9484080889002d007080c070b100c520107140c000c0c000a6036000c0c00c0300c650000a1070304044113001e800500849094210070701c01c201d0044082d054112000b41d034522200461152000381c45010071a0780040e080c02d40c0110122001ca10b0503040200405034021319541c4103030410802c95001a41000c20703070340d40c1c46804103025180c0d41c0300b00c542d5640740b041d600080c10200800c000011199130003035900c01200000c0c0c0c1c0b1004074640c23205c01d0009403003050369010320a070848204081521401c40169a1200041e0408203a0598a000e8282640c615410a55a036000007405016140d02401401344141c0c020004050b60307814034220f4190184d00d03110003070410007004007442060800c08000ba0103142c004000300302c0e904d400307400c52a01030414403c1c4020107080c200001041c40c004a21 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 395382491 1250 395381241 395381251
    0x1115041701020301050607031d1909060503031201030320070f080c0301270c090c0903021801061403091e06220809090c0f031302040608190303020a020102040e131a 72
    0x1e07290400c40c0700c1d601500c801d0100b0b41d610580d418211502e100560320ac015982030083e0f204c89421505040100b240160740c40c54200318003d9008006824901001000e0141102d80520300a240f05240004c500d01103d000c5242180c2c5104680000c00d090700043c4e4102c0c21603440e101146c0d034031540403050500f43e5210003049800218014a9803061820402100b18014814401da030501c070345a2241000700c84807520700d0750020b184140d040c02182071018241203500c0c40c0452040e02d541c0b5007440201072080810b42d0130340940740800440d207040300030401c00c2f8020f0032103c0d42800092169400c5566007a013103c200d10518030f8108840121010101e08030301240c4c001c4c0d2010301d007440780380c14481181c2020f804890701c00d90400410004540362400b4601a0b0101241c07a2135110007401000180c0c4c0c0c06030089403554214012500e213640b8042c0800d6640d60789410056210550090306a00a0003668003400388182c40308200a03024172030750642c1741058400d910010005000908100211400b107030 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 395383741 1250 395382491 395382499
    0x60306060919020405040603050607030c0c080403020d0204141608160203031501170a0f06050a0b0d0f020d2a02030306090106030e0a021e03060604180f111504170102030105 76
    0x1010502940401816145490b44010054a49981c94020030100c911960003900c880d0002000d1240c03441d41405202c0d94007000e071401f084912215124240f051185200003846407081900304021502c03560490003003249078010781d80b214a02140c0700d074098440c4000501c00a203540f800903040d2050089481f0f948440c41e401142140e8841f060005400546070450707060001000c1d90800803102c003c1c00610924040714003040b107169540d115000c0e40c3c000d402c05407041111907014022103010b20107a44010031100008950545420f0721600248100300d00d0903145070400c2c40d8001200c288031540b007140c05481141008100040c103089840e400305494495120a03500010400315129401440366403100005a40c1600d2043d070002d9549000541d03945801480c60380c003209245001e000c400c0d1310450035102808888070040e001030401442400040503032030149117440c148003031500b06d1201c00d64060f100401d010013035040246141c000d03110301501c082044d00010401c2c05c0c18000d407412100c01174 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 395384991 1250 395383741 395383759
    0x9350a0e060706020a0504060e040c080705090d02040e0f1204060c0803090f010218120c030337020f060703150e0403110604121803170307050d0c051206030606 70
    0x90800c5401004460300c1a03803000007404a0800f00360070f40300a203110b0086446030b6544a1500c0c1c00070b81030304001e030b86031485a45040040c6603501d81000740954071104900c0c00c9982e49400c0d000007880c0c0c210014020b500039242141458506030000794039103155508004a0740000001660300805102c0d60041c00002180044408001000b210244d074102c42840261941c10f90f070144900c2c00c9030031100d407a80d0a44e4050804100d00d080901c41440607400d158050180c142d6050082a503034802d080d590903038094906a41100b00c0010750842030041c3c905005807030a032221080081d80c0d50074608030606140520401704000e50f00a01c01c031007647d8440e84d42407140902d407149014045000404c00d4091000c42c0d1004504801c0130b01106120381d1144451031100204040028075210101d044c808500007000070510104081c540c02455000020580c65540d41e100f407001c444074000c81103078080060a0a00e4800b050b0b8022000e0b04012070a540f400300903a9410007010756030441a5030071340c1c20110319 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 395386241 1250 395384991 395385007
    0x6150f0d0c0c0f0308070801050301500103060510030f0215070b090609011b05041a0c07141305331003060e07030b1e130935 55
    0x107070401d442103142420100300e9070500d6154500484484103044000035803a40400541e540c02c443e460b40940300c1034008120680a0314280303100d02d004400316600c04400400d21102e40407251400c141505031050707a48400300c14158032010f0b104d03020700040f41e000303013403d00085483c6049500842200c0e0032130700c03a40000540740c0900001c80024860035022203810007400d000300d03050150581c01131070048010049442c113050341c60700710750a210502103510f0840130301f881c0c0d00303500005907020341d51811135940329591640d8010665102e05000750a150003003007400110f410215184010b010b005850620202d2102c48d92001200d00c2140c2c0200c10021820140559040890303180f038880c000d03020101c3c0324102c1e4800280002c4405452800029106e610500403000b00c0714029030000b8580c1024031007140420002450f400840452580503411603000076030b250f032a8180030f40340c82c0caa8401005402920f05282c0100c65064404800c0603ca00c0f1001c614840014024900f08214101d0242044c0c48 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 395387491 1250 395386241 395386267
    0x613150f0b03010c0e03030d0917040b12070219031b0b011e0605121302190b0703090f0302090402010c05120304080a0e030a110d0f060222060905090711010e1506150f 73
    0x1449e102a6102420607190402e10400c600060010306902501c8540b00c00601100c4002c245004100d81c0441d0052000e8100700c81c01c180c45a28125414103001c1011044400003083c0d20318400c1015180351000300c0001407203a000590b0707880c42d1440011084102e5183d03402902c841c8a0704004884d0840042d00290a00318070728000305540744020240c0005680c2039400d0210700302c142e088101d00c00c2001402900701500038200780c1c02046402079009065145400107001d21784002c10280c1405071040710b020800509001c060388808215140e19100c1c1041d007040c3c0c5841d0094140c5c00c020501d2403030030703401610b0300041103800e1035406840760900e010082d0500144910015080358000d03402e024000c0001e5840c0090221104600000081244c03a61002c544405450348039409201010205002c5a1544842240e22080074204104255125442c3d40c1c0107003640c40e10085c1600600344507800d40e103800a42c0c0c2d0302442045035820103004911096060b43d00c241042c1428400f403c000107100009 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 395388741 1250 395387491 395387501
    0x1006080706030515091536100e070503181615020307020402040b3a15031506092004030b060a050d0f030306090903020613150f0b03010c0e03030d 64
    0x895442c04412840b4000d001c66461101034440c100002e01b004240d8085080074103c26024441c014080b04403091080e4a6410b1810005608043e6040c54000690160040580103009141c050304441c01c0b03103840040201183c10a80d84d03103000ca1601c0c40c0c20360b6528000203640c0b40340340d020031440403481d00e07081081c1220141d582024041d4002401103102680c1c8610241005000d40c1c007101c0d0795200ba40208610301049001454150324800907031981440440b02c2c8401803034202c26002907001c04403840d46c0f0140080b54401000c480d048008150100b0440c3c00031000c403002d088007446846004000380f4001c48200e60749080383c4030240b01c00c10105200850003500040b001d0054500c3c15220f074089102500c203088161040f14088e02c1d807104040e4903218800c01000f8100c410040984640d500a450b9403000e400c0c1c1c405d54110038440307801e1040d221304c00914a104000204100c11829600d00041d0068148540c8070f5480c284146030143e0113440003003a0420014080e52a140380100d0560080c4 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 395389991 1250 395388741 395388751
    0x31107141006051c02030f0318040b120307030305040203030f0a0309050c10020d081015021b0a03110f13020c0c1504030807120908070e0115090305060601050a020a0f031110060807060305 82
    0x11084051461a8240c01d00045c006c252746410320281e0500a44188820b1324101d40406015030b45881184004090100560311020b0b418a40031500d51100e00001e4030310b01070001c800d40c042c4d0b00002d0b10400c141d01a1702c01210302d4070940a03900c8049013402046482e00f45601c81c035001d03801008110040f140702c0e429031640722603003061081c5440d440e07410007035000d00681140000340e803041c00200a05488031002020601d0300301e40c1509518119522701c3d0149070001100c60050741c40b0b62918032140d139a58011403407504102411921101c4140030701340da07103281ca2091800340400e480495180107404003250103407a00b2500062400d1555030741da00c64582e00740c1404041103440b98011514020901010f0f009007840c3c4031401e981e50502c5000b00c1900a02c40c210010701c01518800c100007840031441a62214013400c0c202d445440422040e1300b4030007105001024801c03860700c20801c0541003603c941c110160401141c14040c02c3d95007140448100e4050040c0d1540400d1080000502c00d402070382e402 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 395391241 1250 395389991 395389993
    0x310021308010e0c280504020a030f0c12060501091401051b0303011d07050306100e0a0b03090a03030506011412070509040509010c0f0203090609040507031107141006051c0203 77
    0x2203964a00d41c50071203030141c4440a0130340020003941e525142006032000045009110007010150400c8441c0005c0158815180160b8003c90040c0c42c49029030700111004080f104180701008003420014169a205100e4503461441d001001c41d0a5111b44900b80a80c1c840c180031800c00016036006491030b400c0540c0340503600720041d480c4c09070003000388059402026150306040318460581c4081503105001031034901007220034400c12601d559406c403130301b54040d07032800c00003e60751000c1c010922145140e0001141000700000307001000c000060403483c1e003030084c1d400700059222040111002d0a1034100301395220340a11240004000d844140341e00030360035081c02494101c940e004181079071811110488665500c4800c1c010454102d00f0004003450144095032030100e0420004400f070003090f07501c50259548400207480c45000740d000010350300c0ca01d000c1390384441c4030703280200358801018032949885c081c104100303044602500920080c0c1d07034002c086040c80d40c03849142c280c10720000390050741e06d = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 395392491 1250 395391241 395391277
    0xc0f0d111e0a0507030f02180601020309040908160c0503161802030a14040f030e030d050a0302030603030c01110c01060518010b09040b04020c07060809030a0819110f0702011d031002 80
    0x120100b002100551250116081001c1ca80c01082082300d2004520300d25801494100300c0f50360390100448081d190201c0380040c0d56281400e01c61581e001d091500260121340b102d0010511165900c0780089450450448000714a5400c0c3c0001d0010213208150000c09040d03000c140c60303080c0750095640210240f00014103c81254484101c044043c2c40c152005030318102c07034009042e405480042402d07030030760007406942d01c0014001c2c0740e0701c80d90500d0401c056010022900550b03041c4101c07004080303604020f0291041c200c100441c03070390088418030019841c01e140010a03003805c000180c01905d0f070350b40c1d52020782c1c41d041c849083c40d031221080950041e03581d040c0001036500d51015100b2a41444010b000741410302c0c5c0e0280403048083c0409803207a2003404207e40841d070240350310b0b85c81b01500010504010b40c516181004d00066841ca0072101d401091900e010002c3c1c40203455024000d1380d80c421000c1200e0444d503018202d801d81550181c1025464240581c3e058005245500c035402403481 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 395393741 1250 395392491 395392493
    0x70f08072601020f0a1d03061b070c03020a32010e011202070c270209100309050f060a2012040b060f030303040b010816060801050d0609080c0f0d111e0a 67
    0xca9900c0f005d401c03c041240103210500c008851050740102410030750040249041074010088505110400e01100d079100013413860400154469441c005d5602500204e155611200f041c001500e42c1000d001c071503040a02078030b800c20400c0c2803580403c2c3d4180c54140c0d81d4507220303004403400c3d44500320801c4c80326002c201d2403001840360b0403110010120441b039040d003045c41d0b0046d5140144034044402e0850300510812b00310b5642c0c054030f24000c0c0c680342000589805c040c0340050408400c0700030406640116420082e0f00741c4150010042a100c2051091041f03005115032401401340100c1a41d42126400003e800a620303604803542000006101e03540300d03504440001c2ca142e01c2120103d5075015003500400000d4030802c00d042849141d1194a004075080c101c000300074081c140715044c410044500310509004049c1c1c0f244021a0b00892102da4512410000380c0e07540e0b0f02926441001e214110950446520030b8800d00702182c44080a0140c0c20100312240b0400d4850134129941c6000d81d1410304 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 395394991 1250 395393741 395393767
    0x9370b091503010b010504050109090b01030612030804050d050403050d08100816030501051b0307120209040516081f05150c0327040204050a031e1202070f0807260102 73
    0x240306a4010010000700814482807600b51508500043e0600000b4071061100741e030442004029a14421000159592040f004801800d1140c3c003810038900750582603401d2603031000010b80320320b000350704403000a00040004c07a11032080d4880600607070080482101c0c0640b00c0c00d24150807880701100300e4142a12441602d0400034001850f42200900420030405c201e020700805911400c24808031045080c00e2640d8a00f6220080c804000c21500790241d002510b040e50642c0d064003405001001703180b90003900034030a42c00b800000c1011980d16000100719080540310203102c2810400c02c04941e514100078441c9840b80310401e089002818012400c0003a4204080e240210320680a07540446039070605010319008441400d024500410080c0306c103845a038850b50480e5407004400d8a50ba0780e0740c1c01c0c004061812400142a40030381050300e2021640090b102d0140c500703030391000741c1807580e80007136a960305c005102e2114030760b02603000d12501c00070000004d4200490380300090300e08103403101d1030 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 395396241 1250 395394991 395395009
    0x810150806120a02061c06081b0d081c0f0e0607020d030e03160305040e010807050f130e0703050105090d020c0a03110a0b0406020a060c08040302060f0a0b180609370b 73
    0x1b0712405c1080410b015142c0c000383c00b84000030104100900840004107140c520100000b142c407901403500d03000c442040100800449100648601c5000000444240c01501401c102c3e030310b4280c514140780c00c82c8003540020819074042d00142d001003c80100099060f0042c11f14110a0700d050b00003405001e01c4410300840740a8500c1c4240c1e201540c0d54105540e2031020001a04035009948c0070314001d1016440d44180807501040445032151240c03d08032540c005825541201361017070040020000030010305420260203020300c1ca094880901105d0000c81c0e668030be440d4030340e50254420700104041400c002ca51011401c020300118100d548501105010b51301960002006900202d0395509200642c4650114042a4a08201c2a00300768030001d5a89001038440010884c04801280c65221650701c0140d507040054101c0c030840301601c00508a1000864047e40114030444c00034040d04a88011183d5040a0403910f40340004120100c00001c0c00380314070020381c0c80e503840c00c2d03030055030b690891 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 395397491 1250 395396241 395396257
    0x20c01020c0f0f07091505060a0e21030d2004060c030801050108070e01030e0f07030303050103140303011203030c020106230103060605090f040b1903030810150806120a0206 76
    0x3503034480e2004056071030007018080c240c0298100410003103555034045004003c40315442d2000c01d405502d204060f80316210b942c800e85d07002c00c0006550021540005420900762800c4030b040e02d0901a00342100b4000842c48501051a0405c001404402c059a0b00c02c0d2021010801d108050543d9854410101c1d03219400c244081038400c286071080507131018540e40904000e1038100100c0c01c06d040090000c0481100b150b06054a680d612a200c1100f00a608085c81d6880300f250702c05a907a0070302400401d0280000c0c1e4080401c0410711007003000010849040714503005c803a000c1411107403001c60050560400e40300c1155241c036000211206c0b8080c0d400200100c0e40c0542d41d003100c0d0500090110f56042d40401c1c2070000c2481301d5620f940c0c440041c81a148000c2e240403500304140300002c0e014100100c0001980384406202000781544a60030078440d5001410180900791180c0140300c2250340c88c19108000342c12a03000400c2420041c032046070841c665022070f8141c800d00d90008141d40c002f186 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 395398741 1250 395397491 395397493
    0x602040905250f0c23100c0e0d05030909150d0804050112060f0b0c030c060f1006090302060a031815150512060c071a0702010207060c020d08060f0102010e01020c 71
    0x244125810005040c0812154070904124110100d022000b40c0280946200641104940e20034242000b03684c0c20004109038400040e905450141050031009101403024100041e00c20380c950300f40c0c1c1c01c1c244449d80145401000a5081000c440308003c00703030f5001403814088150354000060240c40d8028084086072151103111748035800c00c0300042c4008910410030702c2c1a800c007070080001c48680300b0301c0d070300703441c85003040301d540312800c50801c2d18520454400086ca441000d040003a50040101d100380560400380c16242d04a039103143c12030b00d1401500010754002c600b003114400b040d000781d20501d030214500c50071303240c0d400d446c0d00e680c50000301182d851480e45454094034080802c050303505001400040f41c98540e104d80504109559020041030111400000550b445c140a5030014403440d100c2e1121201c02180b6141308000d01035007114000f00c0300241883c2e03111207500d00224140800041da41d848889603a200020002070030301c1c100d07500b419035503076803079481421380280000c20094070000 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 395399991 1250 395398741 395398771
    0x130c020f01020a090e13020901030b13080c0105060a170309040c110607080403082404110403020916091d04030f03061a0403020f040b060d0510050a090e010f050c070206070602040905 80
    0x300344101d0040000b4082541b01188810280050b40c1c2e4070b9800b03054030780010103a0619540da0820070030b2100e40703c102400d0300d1808110003850700d005402452017203409943c25000150b41c3d9400b082c2c8140002c8103081e0541003481140002c0c20190b0001e901a805032902ca40464501002641465016a00c00000603601780802c400e05802162458001c0c2c05400c0320303044250042e03548804040074203000e512036901c605120700000f009006071001303190010100b00c683d003400b141d1540c08103a01540100400c0c0510310025144e491000c0c8140c01c401488084086680c0b1036500b2220090300d00385010500d90b8480001ca001c010101c00398007400d410014083d541d500314010041d0420b02c5002c0b0324800c6003082640d514584403281510a21900820082501d0301e801841603012201500300e1900440d0754100026142415048075226055003002040030030741000d0b207401030320000c990300244444c080140300010305100b00100308060041c100181082c0d115103c100c1035075026a09100660fa4030 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 395401241 1250 395399991 395399999
    0xc1801020a2306090705032112161403040c17100609020408010e0102041a03100b0d1a040902060307050a1404141302130b0c0c0d050d030e0c130c020f01020a09 70
    0x8101c880d804c60311000040245a01d0500041d540c0c1c008070042c803011310000318800f06a0b510100580390984240020110b4920b041c0d610100840c64404034000020702e128024408140c0200441c0d0180c3d40201d034001000d81130052b11781c0c01c0024482e003c055845264a0f240c00c3d40d00c0c5100303810280c0032032000581d8075850940121300f90b8007218001e080f01d9204000802800200d9403800c0403140c80b1101e0b498590f40d0700c0c46100303010516584841d002540008031402c03004900d905c4482c250900c03444903281082d031070003403200b165008007001b0742000080000c00c54840c012400382048080d40c0c6000f94682c00b00d011100c0391504154481a1554580c1c2c18a9109203880312140c030b15103c0f500c1c401c60901d6040c60b80780c10928402d02c00c9584440c40042e141404000074070843c0c101c0c0c00d0190502e502d00324145032583d80c81150790030719400a85084601c40824001042d1807a0040b40245917460b43c80e1244500705c01051605040030541c401c41c0c501c5120602d0070300240003400e0003034589142e12841c0c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 395402491 1250 395401241 395401243
    0x1060503240109110d1406040f021e030a060503190201092102060a090815041203060e06090907030212030301060315081b0102010b0d0f1103060c1801020a23 69
    0x88608003007480c4400c5980000741401031149941100c20443c1c0c04038121020348003900d942d1141c0301c114407041d41440d4189403c5481c41407641c3c0151401d840400041d4140540402207000d01c0207070b90819840410518010728800300a190000c00001c00050304030340d1440001d1800d10301507101418003000f10600c0c0c0540da08200208007d00748034020507400309000c4d0407144140102c1d00001d128840115042042c2840341c4201009440450110740001c041c00c0c040060010044404561403050f4040300c0107024860301a107011a60f840f40d00c48565100e030402c00c100494020321140d080d2284c0c41c40000941c5e11202d0f4215420700240c0516030300e5045c1400201501c8c2c540c04100704113100444104500d03c40024490b90301700114001d02c90104c10303540100d025003140f842050b804086c5e54154000c0c4850034800400c6c040c41104080740425150091540750b0034129040d400c071040030b2216500b1620f00341280407403180c0c1481514040e604e0b82e6a1811200a016542e4234008040d00e20300c110b07520 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 395403741 1250 395402491 395402503
    0x509040213140603091905011409010b030f011a0f240a03240303080709080618010510060e091015030f0c2d03021b0a230703140f0a030201060503 64
    0x10040c3d841d5440c40c6040c0002caa9208100703940ea000d82031466001509100082d806464590040020400703103040c080411406000082c112074402d0050602c0d02d4980d0070144644210f0078058940300e6440c203e01c004000c500203460300406c0e004020019824403803c00c0301c41c640b4a110a802d000c6071240d4101c0401012100116029201c03112203103080c184400701a403006040f47d5041c5480c030695902c40104a441d000f1543c00790201d4450380083c040c032803402001c2407005c00ea07000020000b42e900e03041844100102c51180c04003081c011401105103040805e602a0f00c08004800c940c02c1694030111810380641c0e100041000030341d01c510700e80d2a4066405004600790091400c01000c0040305101881014104884440c804684101c6075186004e0b405070740080c0340c2103012080103040020456200e0030440b50803030b11410182c00c0e090702c5801d4a98002808444500101400380c00c507074410020256441c42c103619446106450a0904000c002c00c1000e070b803003a0b00200c4d4207464041130501d0310f5 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 395404991 1250 395403741 395403779
    0x609080601030b190e0717010c0302040b221d15010e280f080312090f12030403030b0d061406010201090b0609040212060a0b031207120804030509040213 67
    0x40c0204004102095501042c5134004444150b4181d030925030f07240b840002c2010b8000e40ca464090003000080b41061044544024180d00c0e000b0b00165008101c120704a00c2940100c0784082d85c02d0006040d5102420b8840c0c4000d20401c0c3c00380d49803a29a01c0c90b5104000c0750f880e1041049610081201c00200c1c028848a041001e0900c0704000740f4003400a034440c8181254601441d4003c0076603038503115400001401080030360684e0300159100c0210940303d0740580d1002c00550203650200d64840c00000c2d160401d60ba400d006400f2004852481c2c5040c0d0b40b0291040d01010349070106410b40b90344030160420746c00d00c280d20000314041540c03900880d44400412503815a450072042d03002003503041300081d511080131a00c1840681d181e10000340079072903a50b51a080d6100b401c0803c0032080842d800f01190050444c103c8501d4400c882c640d04040c401c2120080082a80c03a40e0b100140d070140004a810520900309a820407030382c2c502040c00c0342c00c030345e4001454400f410010001c2200903148a0030324 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 395406241 1250 395404991 395404993
    0x717040f09060302101103040b0412061a0603010308070501020d06060f0809071d13170a0e03031e1317010207060f09050d120b03030a0c11220b011704080301060908 72
    0x2542c915000218250070303c9076241705011802c00c2640f2036440c10300407207000e0f0442c006070944a1351100062402e220012401f101c141e840d102c0c0300c403401e00301c1e40d4500d00d40a5005004500e56801c56503a402c282d001954215219902480028035000c000d000c1c42c8080c01c015552041203070018507000b0003040c0702601030f00c00c42e001442d09000c480e10400302c82c20300c0c0041d100004290f4a07901040c000420740e91202401642c82200c0d5207086206000c01820400010f84d60f5003691070b8902c00f01612031041ea014002c43c0a4072140e241d2a219024001c0c020454544103141c108580e0b84406040d8605424050005a580043c00e07200300035584c401c9421200310004100884c2e1345e15070b0740d95605c00c0f8600d2030308148918003103003036041036954101d1141d416007e01902c0d12146401e001410b0040029000c035640c584c6100e0841260512030101029000c80a0401003e0fa00385d51715040202400030005041101c10112544c1d0000d02414260283d40702d42d1503180e1700c3d0f02d00f0b0401448203155800004031 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 395407491 1250 395406241 395406251
    0x30a0f0224040b0a11070b070203071539060f060f0b1b1014060a05220506061b0c010206090d080a020f0910090602010b04090b0414030717040f09 64
    0x454480d00082e1070a955941c030450307079a00720442d400e55000f00d01d007900c1401440343c1040803440d01c140300064415035200f5030440b0501900c0d15801c0050382e407803d4041001561460302d00318080b4902c800c81480740e000400b40010305224600003128607880840a80384141c03a80038054201241c0e210b040000d1008104a280080c01e06070300014030f01c0344040c2c207168404400421420300c4014095080e40072066002002902f44444180c014064101d48180c8102d4511100003080d00344110b04142c40c400074942e9142400710707205441c00800001e404180c102e50184402404e140030900c64024010003640100303800a800c1c00021320b820001403d0500035080130014503100c94100c000c1a8006448050168881c8801541f080890242015186d0b01140100610702140e8000c000d010903118554020301500b60303442e00380010364082a0b00103060f04040c0d40060041b0340c21946040d0200d420a0a0300d26001ca04d03194004403000040007035220746d41c0054108080354841546000a02100b001448 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 395408741 1250 395407491 395407549
    0x609031806110c041d030c010605090114010c3206040b0c09090115120f0b0f060405030a030c0f1b0f051503010b0304030c080307020109060b0303190c060b030a0f02 72
    0xa103c0e2000080f0501464072a44040c02505054402d40611102401103039118007114001030702a20280c0320b1280607154100c0007007645840d102d0200b4405a041e10307118a5880d556580d0300028070600d4507490482c1d5a15850010001d2010440000541c00c00050500c0c2c02c1c5802d10b04e0399444080e00310001004d04119040950316512000b5044801c0303c2d03020714003182c007a613040e00c1e07038180082d081c0c2031203180803202d503640090f035480388072601c4044d1031040c0c442800130b050012500c1140103040e8154490b0b81c1d2000000d10a00307074040440d100d42c1d120405040c2a80c2c440b0b241c84100b8645589140c6200c805010001604180c08020b00b02220042c88c840400103c25449200c1030140d44101d2100100003410705009040720348400c5e0b44440c0030b564070b180c85074000780204402d080444415013070110031100c9103030000c02c1d0340c1c1c5100400502c2c01c80c90000310003920248010783d0b00b00e445030f032201c425000d9a80d040c810400e015000d003801d02e1032000b4610400401c4101201559510803a40410503 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 395409991 1250 395408741 395408743
    0x30c1a071215140105030a0e03041d0a0c0e06090105040b1209060a02032a09030f1609020903070501050307110609060414030711100306030c0f03050d080103120c0807060903180611 79
    0x1a40e100c0d0f0a08080ba603d468807080c01c4040c0045249401007840001000103812143c40c00c0906040041d4000e41c06d10340303171419258143c43c1041c10700300004002502507121490400010015181d050421a141070350715034413915103401c241c141c40c030001d44030810028101d0060040c95844030349044118598500480d0010711200903004800030300407940c1c0c0340c8510f0b003141000c4944400d40201103541e90206c680324a0b0f0703182082560344000c04040e02001801c401580296020600001c01502c00c690500d80112042c1c2c0005219208024201c200300000c00d000380810350140444070060a450b2500f4200050911401c4403624041e91040110781c000c1007100c070407070740030403011104024203400d640c0040f03010340050381002d00307502234100780019904000b869490850384954140d442d01c04001c0f170140c504200c2440060407002e260b05032005010301c11118844064440c122041c00c10000ba01d409044a85924088011880d0850075081003510085001700504e03841c47d08a2100740c48100d15 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 395411241 1250 395409991 395410019
    0x3071824030b04030c1a0907080a0201020709020c1e030915090f0f01020309060a0806030c0409080a0c021f020a0c0504050705071e020d0308071d010507030c1a071215 73
    0x14000c020b5000106080500c00c1d6280418650800c03015003054a2010282945001c2600c59144a101e94140042c60200104089110b207030145c000d1300b0308520b8001110007070742c001600514130f4007501c4080c05a98809500480c04110468000c4d80c680500c0300c00d110700341c10101401a04070f0001e01c2070707122a6440010802c61075000741c0305c02d00364120183c010703882c601501c03155941c8030341c020407814025035005240f584180022011900e550000200707200440d0340795180500000030800100500350b0040c000d030b80d8560301c0600500a2803a817008001c18002d03440c2000e030016000f182600e0144114145803130080e0104841c20070017803c002001414510071124000c107d03000d8481083c0e2410711594a00860030b40103407800c1084040c03807800402c01030007114802c010800880d200e00211801d95102d40c40d180068446601e0001c003910281c0d400700c5418401c6651001d41c42d821a0080882d05510340250040d448000401e00500d42c58804d036071200b010540d111048800400203c0705d20010 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 395412491 1250 395411241 395411243
    0xa1a1801080121030c08031503010b100203121b04030606140406211506120b310f14030318030304080304020402070c0b180a090e07030611090307182403 67
    0x40d22000c00f10b8601074070f803c56642c00242203181d010080002d902520000103c50341401c4001300300c2e40303240381c04004007020000c0c010b40041e4014020359820000305400303190000f01c0120240110400d62014102c164050380040340c0b01c60300c42d42c041008034500460f40e0400310085a042c401c06040040044c80007603c40700722032007240e680403032005020b07034041c0310030803e00c0d684401d000f0103442d44184c3c0350001d0b40ca4012605072400000103161040007800d2041c041c0600071801d8402161190208105100d0520580b600d1000071034080c0051180e130314107805906400065522440d01d0880610480c01e901d0f4401e03d5a0401c004000025031000103da6100790704a500603140d4040d801d008060512a0308581e002030800a40c00303103132640301c00c07141d01d10312070855a45800035103800c503140079116180c58001d0641d01c900002c5c40024641d400401d0a510110000d07402c00c4c2c205e000003440e045143e442801c090121005d45584d00d00c581c0a031404024200d0500166015681c0340140380e0034642c0701c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 395413741 1250 395412491 395412539
    0x6160506090c040506031c031e090807020306100b0406120e01020c06040c08012318030703030603060515010804030305071e12050906010501020a030f0309020406140f0306240a1a18010801 82
    0x4a8050300105d005034001c0c0209c03400c2d500f0080340005207480c80485d800010281c3c0300c0d100320030000c0c0f0801c0d6644106816110541002801c0c17610388a0140d44585181e0407131210540c072804052a490000d1019048074500034000306003504050134246170700610f68120b0441e0703074102300c41c0300c1080718076401c0c0c07901c207140c0b840d1440700c50b0351000400585a10b60f401001ca01d070100060300428580e050300140b040d070b4010401044543c0b01c1039000c103048045043c0c8030303012035584400500070034041d900082c1d005105090155a8064400d46c4141600c0d04c0707014080850451800c2c49100035a47c850319a000078200c000b04480d505040010f5950713001c4e004014200421020303080d100510940100c00d0040d40988240300968440070304405507440000e1089c0291070030542d00049140003d8913501840c3c0e110003010031003861040525201b40b6038038a40d40c101240d40b000180c059070b01c1c9005000802d407202e4058403001c40c0b40300c0d850305420181049040044000041c000c40c901c10030203031481c503c070107 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 395414991 1250 395413741 395413751
    0x712050a17060d02120d0306091a041812030914190209090f060c0702012d030b040b0307060513120b010902030702011503060608010c020a080906160506090c040506031c03 75
    0x3000200c1c2c0c202e0004000750804074001c169094400001a416109410f031f4806004542d103540808080704d10040c2440d000740490011181d050070700d50300c03025680524080316007044456441d400300e40d554444003400040e5549180505024417800e603040c1100c2d40c58090706442d070151100e004541001640640308581c0761001c0b50056204002201d40d8001d004c055030f1161415001032182c41c2c001160580c0800c99409816544040d2111500d0860304500241e010150080004400603c480240140c003d507940031101c0e0503943c1041110010301751555030b2980c883c49400800c200f015a40c0c05170400e458003080301c1d0300003011401205d064a41c50000161a0307599420200d000d809010b0071181c407082806008000d121503604404c05032074203d03000340042c0c00e100c0c1e4105e13525650f600b07010b44010f109001d042514034013103005001c0c001c0d2640c5290403076a907949880d4100941501c4800741684903040d841094241401a50303400281100501000d800c010383d00c1c6c0101245121481c05c2503520 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 395416241 1250 395414991 395415001
    0x1b0206150a12110d140706120903080109020a090f0b0a2303040318050409050d081812070822030b06040c0f030c1b0b0f0108010e0a06020307030617030712050a17 71
    0x314441031307901504002c1c5558000709000d1415100d120a02804c1c002032240e1900c192240c000d40958100d080d41980c59444a07840e0400643c029040b003100e030010048241000180b0f582d01d00729680c082e248040350250b4450315000060410103900302c100c504848000c1c00050221004000c1e203512a42600b41100001035109042104002941040c0d1f4010710742800c410502c400003e108030081d0268480c00141e4803542244042d013100300380040036a600941c0031080d0900c01c0300140410500c0785074007904007003110758200010307951084211841c0118840030405d002d42c205145810000c00d940800404035070700801050302200800385d6045c1034450b0440032a041c4191001008180071202e100e41d0900185415440050241c0b0103048100c020800403510100c18071868826030512401046290304503a05c00c80a900000c2c0f240e414140d44400004e032440b8146030741003d0103001000b441e5102e9843c5444030300034034960361800030403400b0f03c00741c01119005803146404100d01d01d01500c0703c0d650 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 395417491 1250 395416241 395416249
    0xe071208090d05030d0c0518011419080405011b05070b0907090c0203070b010e15130b03060c04081507091e0909140d14120603011b0206150a1211 64
    0x76007180c0c941c100e48990000d81c140300b00807015080c00c0d40c0c8450b0a100310300321902c0885d840d00400304e24510001c4002102e0344c1660240e0510f001840351154498185220020103510036200d580980d0081851442013004110b0288119024450400183c0c00e14074803900e4000c00c50300442a0041950b0341160124400e5007080000100401c460207040c001c9038203001000352242c000902c1109c500d06450004039050400d03410503031058600005064007440da00e020860a200c00a1510414075a00d4031005920303107003030081e9807040d0010326041d40c0c2c0c0d610b0850350500d0300860203012080482d6520a00650070f6224016404840080840c49901c02501e0b035100900c13411070307024141076464444848200252031401080c00c0c403480341504d08002640406440d48001c1400b040c4500701c041144005000c01c807600395400c004040c00004000b112030000b4502d20b0025524407016078040e00400c05c5219441a180015140c1070f60241041403400d10502e030304d02a400002004200a50039420250326 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 395418741 1250 395417491 395417497
    0xd090f0b18040b3705100503041a1006090b03090d11120706050411060f0702010c0c050d03021006060504120206301905040f02010f0e0406030303021b010e071208 71
    0x400801307614980c1416141d14182c0e01c3e4a40d449840344130403003030f440c0ba001c2c0d42101120071103101a241c1098040c0b02c1c2403c846a0384018811254219800c0340d2604d14070f04850403900c00e4104807071040c0d299090400150020074507034000e601b010810130070000901c5000c80c00305c42e00940c41c1085006070310141e0381c0a08080140c5900f03901d000d004511042400400e40006024a01550001c40b41e040d45009000310b91103101e1554440340d1040080e480194443d89442d80e03454060004050b115071a44000303030312000c000d0030940051b40080030740501e04c1103920a03140103004508080c1c2c0f0382807415017404c040d168000c502903c035000100c1c3c0c0700c01c0106c04c480340000d5210000d000000d141001c00204445000940b02220b00108a10901c0481d0f00c0b2846403501860300816502c0180540b03900444109040b0000b000400001120901c210b0711140139900280d44a07032000351b141c000c031400b8030204000010207030210fa8140002030f504500c01250140541b0306403007160211407014100221244 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 395419991 1250 395418741 395418761
    0x1a09071a03060a0b0405011407020a12050604060608010510090e030c060118060501080606030a0c03090b0a0f110307080403050a020115180b011d0409030c0209090d090f0b1804 77
    0x2140101500003101103600110b00c01d41003100c03100036840d00c4070701c68001d42c050782c00350714082002c030342c0d19065007c03070707000501000ca100500109aa5481d02414505100c030000122881d40c401802d0000700503490064401805901e00204400d01c1c2855400144054600c9035104055403000c62606400042c0b01711281075441904461a030b50b541c1d12142c802101410320418110314000001c14a0740c0700301703d0a03000c0d0f00020b10b03003070560322070b0450f030710081c50400b81d84e8040c55a03410070000010f0030700c0c0f151849100b40d8003000511260702600c150603280300f8003411002c04000c004020603581c0007110b0036002038140c0b0f4007646a28085006a00604600d40c20501e844d480c4040000c52a100803c0490f255030400740500030110180b005452102c41e031841401424900080400541080d902c800c040a00900c2c000c2086851500881e43c1050300b85c42d41c481c03c3c1c000c5000c0c044510780242540004013941c0d0012540c46103882c1d07102c02d190050600d0b003280d0300b015080c1f03405180d5607601310352404 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 395421241 1250 395419991 395420009
    0x605280e01020c0d0f140a08042405010b030115050c06070e1503090a03090801150506091503040b010824060f120d21020901020309041508070e0915041a0907 69
    0x1038050380301424154420410348001411001007280110f46c04095422148140d01d4aa00307940b580c2e51507004100d5400c1003010b06001d40c00751a80201443d01810b8001c2440b0060140c1d6541031040c400e11150402d002d950902c00d0030000741101880c002070705540000725140c42d80d10b03800400005416440c1c3d0055021078141c0c00f00900c0349404010400d5040588241c850300000ca5a03291101d0a0702d024030046502441d1a0741c041020f410b01500402c85440300518844000c403006102d524150004c1d1429280429980012301400c2c1041005400c007562000d443e0b2135001054145604011009003101d000d9075000341c010000344c841c007034006003104541066410036400c02000034880080c181d4420b4501442804130803051a191084a101040c181e001c0c5240560420502010b081000340c80e0b18101800c160000d00c1110500c2603001401820f40c08010900b000200e092800d09010003c070b016810308000d01001403100f1604400da402c0c00c50020f50786944040c009804c03c91150701801d10 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 395422491 1250 395421241 395421253
    0x40c050607050313050d02060d200c1e03031015051c29031e0304030c0b0a080105220507200d080c0711010c0501020c03070804030605280e01020c 64
    0x304240400604185008044904401036803801000021703204c0c85400b03900b080027040041072000d216001584106620a41c0e02c018031042844800198040d41d4002050b401c050b4020001742d408481ca40d0001004c030300250f00f0360925008030840d504003407180313500b80e070380301d001c042c55990194056401000741c80340c00744228025000b40c0d0018100d00104029401e4005010840303130201c800b0343e9880700c47c0c050002c20a6131800064050140750050010b05648018040040019030785072400002c1c120081005844000d0f0140c041c2c0007001c1a00224454500d00610010b0400101e160010503140b00a0100307843d01d9130b41094070900f0440c03a104000f04825640c1504030000052004004072203a610060309680d80e540000050207a000028a094004802c088041d03200344074800200380a10001850410900c071200c1c515030220004584580c4003290801c2813140b07910809038001003c81d265010000312000b2007110401130441c40903526640c1e030791424103801c00d506842e2106091021112 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 395423741 1250 395422491 395422493
    0x14040303030f0e0109080a111f02120a020306030307120e09010f0515130509220507090507110c0103050705090904050c12070f061407081218011a09040c050607 70
    0x3001c0c10b00c162906102e28140381071012180014400c18440b43e8000458038140210300e2400c03201030844840c90349083c4291910008214641005c503407030708284140060341d07407001d00b0802145a90042c2003041407071052081080c1514040100c509031544003844001044823000151890780b0038031038194004180c00c0011136a8400e81040b801561021600c1c0306201e040041901034500c40d418160600100342d08040040c2c0c01e03c0c0c0203064100d5111000e41c0004604402c3c0128407000e070841c2910941d0080600308a1040c09215480e044641850031340b00c1c0d00105000c295882c045010302c40c1c10507a6402c00182102d00c5101070310204040208080c1942c1840e09005555810311202d030b521410f000c001040c159840004d9410464a005107030b00c810758034064082e03c1107001d07450307032183c2120200816070010324400c1c0104500e484041c41c0c40750300d09011502c00c03510041c0c55142c441e0341c0e02d000c00d48000e4120340b2000d400c140104895210300d43d0f44500d0310016940326030f0f001c0c68004d000451008 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 395424991 1250 395423741 395423747
    0x923010603030206060307060c080a03091506060f0908030304110321030a0f05040f06020c16230109061d030a0c0b120a0504020907030203090f12040e010b0a02071514040303 76
    0x408482c080e03402c03aa280e440c0d0701c08040d2515450300c120408940410350b4a0700081800010300301403600d905000661704010380b56a1604091000301d02c40c950398440c01444203e0304801540c81e040071902c0d00b01e07540c0d81402c038516035920000d4401b40c440f45990002c2c40446d50200944e0703100d58041907005940b134001e1085011650020344000c0161410001c0c034038000030451180e00d118035000010070b0040c044c41d49407100258441c4440c20801d0090850001b00940080d103104000d003080000c1c0a00704d1f440c512040684440020410704108002c0c000b0000654090083c62a00308010781c2142c070180c249001925040715004000d082d0031503004002440128600075002c0b0010052100e9102d035034012a500c200c83c000ca800a510003215000f1902e080d1196028545c0400048200c0c0e481c3c2000b0180c007840d0030701e403d140400103c8001014440c0c001c04e51120380c01422a00c1d241e40c00d01585100107511102503000e5800c1100310650a00710b200e1060605000000129a02d2a03540341c89007401 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 395426241 1250 395424991 395425001
    0x60d0204030b01050303031012052404111509010f02030d0609021c1103220c0905060f0103020c12030c22050f0906150c0102040e090a030f020d080703092301 69
    0xb901d400c80b070000000382038200801100e200b10070780f1200f50074150070820403403240a0305203800d403194450740000d030703007038810f0480110007000b10a41059094034141c6403040600c1d081c0b4604034041e10b84101400014008a4151603102409081c41c600140004c10100d01e14022900b6042059080071750009041d800d40d402000390fa588415080301c1c1c0c104804414090b5081602c1200b07aa0008000240e40511807000704034142c50300c0301316000001c3c081e880c0c24034110342c56004950380c1a40c0d641030000e03520300311003103003181c2100b800d0a41c282400f18040725207986000049064207400040040da00613040011200344110700c1350300c604400383d42c034200400540280141030160341311000018180c5000110140718140003003040041c50f00310301c7c4032000d0750400780c0c948000b59005d02c8049170080e08505000e2140700e01400030001c0007841d06008010f0201c0901c2a010364204401d03115900e0f038002ca5440d40324109007404180d01500e0b00e0700c150603150904080d0b0407880141020344207414103404c0 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 395427491 1250 395426241 395426243
    0x150b0c19081e0f0d0209121507020115050609120109051005100501110309100908010c02010207021c0c090c02031b0303070f02010c0f0c0503040f0b071502070308070e0d02060d020403 80
    0x6400c03128401140000b01a106601c802c1101100500c6010607402c0c19400821040d000603020701c14603010640ea10307252810a400b06402d002c010020400e6103030342440360900c240185030070f0204143c0f17420041800b520074621018042d1801030309040d80d160094101408240e4030500b1a1180d40645030341500410042d900e138103103070b040c40c40000b0701584101c500d110403500ea00051894415200304010241e403180980c0310a20005000c0000c00d0384081c860750030f5152040d000541e441e0414410030911036610000401031120340e2031120302081003034100c039080d10a02c050000702040d47c040140d00d1030007480c40b000c88864442d01000d080500100256020f15807a4840380310000018005078282d540c812884000141040307946c0a560303102d120044084ca002da02500d00d05501c1d80310105003642290407141c10b1380c1d030004440c410040da005089100ba09460411030800d490b07a5002040140013420220402000d101484075944d50740164211299008116550303414034490800065045440 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 395428741 1250 395427491 395427517
    0xc030303060e060f0103090f12030b011803030906120923010506010908190309030510020c0d0201050402130b0402160308090d030612121101020304030203040e0a150b0c1908 76
    0x2000090b500b841a5419000701c200030f0030100c0160050340110000c001143c01510303241c0540a02c900411030040740341c4010540396070046203140300400054003000048009508440e00d14a0810100364014909001d66080d4a000249180f50300903820240880940181050710700b43d5100b600501c030101d180780035081e00002400b069980034015500603880d40b00e220704940100c99002c030880c06a440950b00580710703042912441d034894481e107241c610b0300840b10381c0080e070000f07a1704018241003100481c50042c0340f000344480d20b0b10790302003060072031081048a03410381c4400551016603034a40668082e0034000c61400541c01d0a402c005050303d1080c2c0e041c08039400b924044201181c428000c0005032100000008030001c52507459580f0050304410b4401040403110700c40d0030105003030005600544c0070354015174980d820170540003030b00303040a889141c031070341b619001c070781c5428410424400301d0781c039050381d1078440e103e1124560420301000c02c0a480f80564001000030000400050005a41c0c008 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 395429991 1250 395428741 395428751
    0x417060610030b150a050c030c060f09120901032003070804020a0b0c03180d0b01030c08010c03051315180b191e0209030c060f0703080c09060406050309190c030303 72
    0x3001602103603003c5444940180d240710142d00210403a00003001a542e0a01d0854509088100340350b046800442e82403003a500f02d0014420400d4000d440d0310380080761100a000020031b0301010794418421032013010f040c542c84040c1545980d074500c2150082403203503400e043e035030701d0600002000032a04940c128030801500c60085180030420007954912600100110710f0b2868203262410034031044003406503c16420f13420703c00040e600280d07050080d846101d003242c603103081415031030a645004006400701881c0c6000c118041030820620120f182c0c002d00d420030090490482180540294913681c00441c0786084a0000c001310104c50b2481903142c1d0b60b00d01c544101018692094400d210764407100c85401900400200700d036540248075200b401411a400910201c3c0400c02d150000344504408400c003013400d50905400200096010741842204d510300411500011501e02a500815040210220008008142c200b00c10b86d400d660400e4103602c0e00b020307490841d44c0c00c003c5002c1280064205 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 395431241 1250 395429991 395430019
    0x120201020a091505040e06040b12030409050c27030f010501060e0a091a0108090a050d0518010212030109271b0603050606091e1206010504060f2904170606 68
    0x207243c5040c00d24040c0d0b00d0600d411300d4540c0c03499010401078403880d44183c0d40e88564030035540300b4040104040d0700102440e00c1d14545100350044900040418042c1d5204000b0000e4416801a981d03502000705084400c9030049407001c81e14009007409205e11039031810b00041031181e0803440b960004c810450741c4051041c0c4a14010095842c01c1c450485407600c00e02c5c880580750702035400550320010610071985181d559448040c90300d01c01645180100340b00141d1038081d070034007142d1910000c0e0301303000400720802c40d5907903500d8501c81403081000c1d180c1c0daa8454240d04181070011080f41004444404112581c0e0815500e0881400120b0b00542c00c0c6203400900740d13000b4020544901001445c0c1410b104681c800c0c0711030301000101050556003034412220059440b0314007001807466010040c801981403505200c01c45089070004d80030008a01d2003001041032140080d01ca001c0007404bd18450111001c03001118080d64000400c7c041e618086d800c40c0440010b00c00d403080c101228040a202d1007 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 395432491 1250 395431241 395431259
    0x907110c1f05070215040e01030c0b030402030c0418020a0e2e0303050d0912110106091e0213030c0801051e011202040b190f0302040b1203180d120201020a09 69
    0x101e00520700c0555000e0608401a0140001c1c00d41a400913020301520f8581c080b00082a601c25000400c0142130440144103200e81c07aa0710b00050205411028a1401e050300041c0d52920200b580c03e100780d48501d90344905456410707400e00c410394041e00c00c0800503180c240102409100720350355090408031405c1c220b1054400c01e903320803a0300251995600a003140c1b000c03035031584814141120035171224407000024069601200500860b6038440007000c019003074041c2500c005074401c900711410241c0740090b036084a000038180d2500d91800680ea02012010a4005000381e0700190410604510004031540190030142c4103180c690f0b840c0000b592110b46006409a0078007400284042a885c101c0c0182000d0340f0444481c030300200342c0180301018042c0c40d021950950090150400201e6042085060601904d07400a204549034030952019601e0180d581c0202c07861104040c0c0150111003454a482148101c0c82e03821209014060b046400c0c0a8041d51007124454009200e02c0000103140701 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 395433741 1250 395432491 395432509
    0x8040209040803090a08040e0a0c02161413050f041101030912080709050306070f1107030f12090504050a02040e0603150115031122140a03080703020c0907110c 70
    0x64018082506500c8540315500c003600020700380001441140d00350070219010380b002e08000e00312400540200d00e08a603083c0c0c00e540b0003209040a44d401121105014028291083c040d00e0400d1000420000002c001500f1000c3d6800005c900c03e240c2030030301040c1105403a095120303074020141c40e48841c1c0c400004400700c50001e500078042000150420b00828461143d580d0442d6151900d0840c070780d01d0701c00003070821106075582c1000c155000c18501e1819005408400744404600c00b42111600d162611010010400002458068141c19103141c881c012020040030300700c050310030889441d1100c04100254401d025100411003990001120391a000800741c003940c4c56003d42c0d89160f4a02080072120003001182d40050580f03c818001711020301202034410549030150040400c0b801c10200c08801005800603d070b013903d20f1640780c8082e141c1d01c108104880c1c1c003240355a5628120b050490030000d1400282d035103d00303c00d090110aa0b800244626a445100300355040c05514104104840ca = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 395434991 1250 395433741 395433743
    0x1e0703021c020604060e0d0b07110f16030f08070f060b0a0504090f0204050604062411070807060c0f02040203091b040e061308120c03011e051c0602040b0a020703060b010804 76
    0x907400c0006001c0c2c144250f01400201c24054861249070b890b942c0c404030908e004503120400542c461040341c8000a0070000c1d0075041c0007aa002d084001480d81495010f0341c0e00b030102601a4044044c080104860801201c62090300300d50b1410140d000c500e003d0740500030380c0103c54802c0d0503940000c280d030701e49441501103250b40300e0010b003010781c0e05a081c4000342800600c801d41c03103582e564000a110302d000110750215071550380841c8001503441d10242c15818030a440348007550044005111040c1d00188040c2550700c4c1b03042004180c020b626003202060b10126009411074000f009000401d900054010300d0850354641c4509200f540c001403004849403600d64110715807100340403a08801c0c0c0390543c0001107028045072494140d0036a0991000901500e05961074000000104441c1d420502c1a03e0030034a0310761490402441c00001803440c1100280c20b0048032030141c808810402654100d800900748400499298051240083e46a100b0351005440041c03d2070f2030900a584107145551050b = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 395436241 1250 395434991 395434999
    0x910050906061e03070e0f010e19020d0b0616021f0c0602090303070614010f08070f03110307090c0e090609100e0c07060603061b0f020c040207051e0703021c02 70
    0xd6480104205000030b9586501400842c1c1c03d0140b400b07a1402e101c602e002e8035415140162a041c00040a08030300d105030f0104502000d4141407012a009485540c2c441d048000005621000807158036030040c50b0490b0043c2d40a03100084000c0c108074481c0c1d00305000d6008881120080c007001e107011504041c426240f40c0000d840d005010006145c690180401c50409800c136070a00e00141c1c0d0702c00865044000c0036106035103010042013030410786200100503044210140c544d4915203200003041d0203143c0402890094001040301c0c05450800c110300007032088040c00d0041810b012000303010204a420910b0044036080d0025030b041c20701140303550141210400314640107140070769812001901522008400004000c400701007400e5020b0400514029000000c502c12080c2c110b140c074030015606c1d402070082010200c0d44850b0049103540303001c041035070003503910259031800c2401d11400d000f00b19036001880da40c2600c865000902042541c2c0700b9503103144114441500801101075101000f580 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 395437491 1250 395436241 395436253
    0xf0e07180221040b070e03030f03070c02030601091d030702130902010522060905030c01020a1103070503060a0506010906140313020406030b0405150a020c06040b0c13060809100509 79
    0x900d6419480c59100054840060a085202501e00740100a104030000c05401c4441840180200c01c003402d50055640c1c1001c034024000600425240e01801103103040303c07403001c0b0014500901034400804032640c014151640382da190030510b0020400f8070180000c054041034001441ca10004c01c072040302c1d40003801c0184601e011540c0c600541880101241003207014084000207035030b508015400d011a5540c0300018a08214004010038001e91003039100b41d10258240714180d030041800b601c020f4000c48400c0c44400018080b0380751040319400ba80d054420441004880c0d05541d100c0c1d40105026640c001c0742903030752141103d03807444803208202440c0d020008220129200300c90300d15082c1c4090000320380541d490300d0b16045100e0880702a86d00b40c011882c050840ba11114803d544080c020404605090b030360100d080d550503008100501c10070b104800b003241a0721a406071181c035800d0000308640c05c2d44481c0c0c0140907103005c0d61000c0040c480c00c42a100f4210035401030520404d005002050 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 395438741 1250 395437491 395437499
    0xd0b0412090e370b1f0503040b1b0705010605030c1f210207050309101e03051302030d021c092709020907030902120a03080c03070e0901030f05010f0e07 67
    0x5011018403e40704540c1079104002c1c0190f51100d940541c0c0c0d81e140d00c0000d448404034140102520886120301d800c2031114501c1d54480d4004050300e820640144d1039400c1541e40400d900000c000a000d00b4543c201c0c04203158007001815080301e42603403002d80956517203403040000c1c002821901c00000081117201c080202030703d88200c691710204154014030410790f400c5030085030300703c0c1e0200006031840d4100140855040c18400d601c82021081860036a0001d55032400c0c00c075413582016446010036403110046200c0d012902854490640c00034103541507094110400780d912000d00412006103940780006000d1a0f009019003070440701145030b0582180b802d51303013041c41d202400310440c0540c0c0d42d54040e0307000b41e160072100340d2044181d6100051112400c0c010072403080c400c024403100c42e6105101000000741e002031026004180e0b95260358807604c8104d420b507004511a1404c907001a4410b00000900294452903800c26018030000c02c2225015a4404140c604050080200d0f50240800300 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 395439991 1250 395438741 395438761
    0xa0c0b0702070f0609030b060d080a300212010801110405120f07090209030c240306060715060918020a1e170307031b0c050603040c050d0b0412090e 65
    0x69100c0d005105480b21540c4070741000104a5240c1c0040f0002501000c051013000003070051190803c1c0d04941d0a000c011040e40c51554511883c02c1410030031140754400c41c070721036258800000064800202416103a13500302c2100081d00001c0308007144203d0320700002020801032042161014035805480d1a0500701003c3c030032003115000c1e1321005807003039030408009140c017401343c1d10280c4400720003da615081c1004040c81d00301c0204400348112507611030070400d841da0300c54000101c4d14601810341c8a0b40c403800021901e000380701d0080d003451500864100240b2141d030000003640c1203050700300141403480889500c4c9803070418009411180c040418401400e0180c404190084200343d583d1079151034202403030100c02040c034894442d0380081203490415400031f1020002001d018054040340d804c03034a414004c5441071103841d0243c0c2c0008042028000e6030304400c03003c0d01c0007801c0300f81908620b1403e40c440501c226802d8403181c201c103044850781c1c0d2243d05280c003103a032075100290a030b0311440589 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 395441241 1250 395439991 395440013
    0xa061809020f0f030a09050c030d170a060b1c050f011503050a0239011407030b04110a0507031e120f020c0f0304030606060e060409020c2e110a0c 64
    0x2040a1010901003e102101c000c801544034419000c400f0440c2c100902d052460f100400c1007071407103074100d501921060380e4408110380300e401c000c40c3c4484084e1280200c600040000360092040044006101905551807014070b0f82e6100c90114108159602e80260b00c1c130001c03003800340e040790701c10b805141e10f48a4401e07005190821680d035001840c0605013070001c04140c031020080c0708501e1040030254029000704ca140c2c100094130400034804000f40700d04500072420018003140c00d02d5a2510326111a8a541c0e00140440343c0d00640e03a996948250009800c40d003207030740c1c02c03000200c03803c80940411620040c00c00050281c3e4581a80c80100340424402800e500204055034503800e00c803c0d64060701c200002e840300d030811405559190700703600308a0140c3d946900501d0034021103400e40308068a82c981141d046070302484005840d00a82a141400d044e8512802205624525000180800b040c1d01451021000c5c410810165002c2440000c03a40504051400400c00d9501d200c03021500205c41 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 395442491 1250 395441241 395441257
    0xd02120a08041a0901060303020f0f0607081302060a030609050709380d09021306050f090403050d050106090f0f0305030307141e09041410051201060812090a06180902 73
    0x1e080404940540000032800c411100044c1a0391a88020800c0c0354051040c00102c003180d802070f00044481c0301080b5130350b40f0040c00507420003c4010000d040c580700d0704040418281e0040849035074600701031004000d407030700f030140d90822850000494541801035004e0000c9030108400101c6408030000c1600190380140200100c0d9142050503400c0346c011080103200c00400400c00154944840c010700c00d02c07a002440308407099143c210203000b0381d0f440001404900308201e501704202d5840d03240840340e50107420200300f50182450004220540c1081d0503400361041007405902040d0f9511400095009500c0042d040740c100300041041c0d54441c0c1d60f143d4220305080c2c40c6a01c4c00320380311004224805004003d0410010104801803249014041c1c10003d8070316800b000300c03a0510b01d6044400d00f0381813181e81d1003014110070f4500c00c4003080d00108000c00d103a0341540c0c140b00580340c82c8512507000301522480703403c141c030010950314001c200b05820102c140da184400a070900c00481c0c02580200130b = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 395443741 1250 395442491 395442503
    0xc040e0f04022407080c030a08010e0f0c0f091009050310020724020c1204030303050a05010b0a0c020415081518060a0209010c020d03050711060301060c0303150f0312020d02120a0804 80
    0x100b50080b03440817006024803054000250341c0c51040c02d800403c4c1b0b00041c2c110032900c89400d000d001041d04192030840d0000c80700726400380c1d16590b00e42070841030b1081c54903258201c542c110744908500e801181c034004032030b000e40c140c8140c2004440420124032034000c000302224600d230400d030040a446881c922102441c0c03007005161529049032545000c040c5940300f03246150001d014803c040e454001c5542103203034254103000300e50410030310050364001d12207481d042240c001d403404103550b2039800c6582124030240440401035240c0c508543c43e4800300e0000f08851101d0340200d1064946025541e4000c0819005000c0580f940200d10703005e54881401c882c1001100d0304a580540d0721900c8640c0080e10a499050f9178003501c3c68042c0c0c80401034030f50075100b54820310041003103c0d04030003d400c0c0b01e07900d0f00e00020b20001c2c04807044403240598012410b50700c142d280c040f04006020f010030340b40312010303022141c21803417928040ba0b03140d000030501010600c0500211091a000b010500c1e00244914 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 395444991 1250 395443741 395443747
    0x42301180f1406090610080a0305070b0601031b030204061e1e0909020a0806130c02121b060408030f01080d0207090f0b040e071802070b011202060c03030c040e0f040224 74
    0x904020301d800d0060704c805149810500902a0499005141e00010900c00d800340c9250301141e10041c1642c0142140500200c0140001812580c170030341c081a14030041c2e134400c101c0300c005540d009000350001e01030350012404100c0b11680310052244a140300502d103036542840000c040c8140c401d4004503129030400d10944c1c54000c210090f15001821084031a5501c01c05240750481c10070440640e5910402a50317894034191411039980490038038a0240ca07415190303620108500c0c022002403003030b40840218011a02403004200400d0300542c01060118000803a9980324054151030340740c0150f100c000350303101100070403901410384c125400c01c40d01c4c10000244002c1c44030202d0b058440c40a0031100907045098248120510b401d035140400080142c21401e000c41c0c0e0380c55a030f074400c040c003801a850700d181501004542e1140d040b1040d08404400707a988070f0901d000c803450180c02c940546195800d00400140e404248814031520841e002040c1c41d02c891203410344400d1000d41c61280c02802d050070 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 395446241 1250 395444991 395445023
    0x60903101a1e1002100222091b080916080607140c0d0c0812160315060c17042309070305070c02010c2303070510050606120903070605042301180f 64
    0x52000c0e124001900122a0011f1080c0d1200314113131130f10b0b40280c18034610b01001c5c8015440d840943c0c0000320014100942e02e0340711000b40c0351905140103001c9a08403d10b104c00300300c0200100d0101e00455098940a940242c0c02d443e040060290b00702a11940e40a408424200e501c00c00440617440e000c2c8030020b00d04800b6120032054100c044a91400c0d26000c1e54946071030742d626102d985011110001480e0b00349050020080c803910103045d000e0802c564811841c013111038038404036401895013440c4008071201029107800c1050340780704294414001c12000801c030318080e0140c503110f940b03142d40d82040490705a0055804076001170f0151110769005030810a147c03180f07126000900c00d09001151590643d00d4610728040c0141800c102440c14841444901d840769000e0711100c42003d5240941507a400381c0440c554000c103640a4800c904020030302c0140600381003002c007540c0d840701002d5004c40381c0e81000390913245c10801030403100b03103030884000110710000d803400c00c0b09124111414180942e = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 395447491 1250 395446241 395446273
    0x60c1707030c120506030d0e060408030301080a120906050409020c01321e160e03070924050604050d020a0902030403050a020d0905090a0209060903101a1e1002 70
    0x1044548201103665007807690b20340c1e41c01c11101c206260220100b4800c070b15144010a4680d0401d48000d01440740512a00d459640c8007001d0740d01138036921040300d8a81da500c1c82c2c0d0694442c0c015106441c0c000e040d0441141d1148a014143c043c1da9982d01d4440c80c00b0314181c0d60070000d5019600c00c0005550f40c042c0e82c4102030301e000d01e003a651100a44034804480c100040c190900300041e140c0b8101180445800b44800c6000381d13126808181d400c0001503d0074840015102c6c0003e405200c8c0d454000d204010035054501e87c00100080c2d10b0b41000520b00908203100d0b540c0b03c41c10702615500940a000401861611101241469201421198040d0740d10051003050b82c000703540032001b080c1c01291003030030a0707030400141c1d00540b418035140c010140b0789004941c1c1410050007200130190001a080b207a5282c0d0340c11100d0f44100901101c0568200b0441d02e801800c442504c41050300c0000d5070350101d0301d00081122001c0584c5212180c1c00301c004020080e08401c450650310640c01040b80c0c001c18801 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 395448741 1250 395447491 395447537
    0x2011506020c0109090203010806040f05100c02100f05090a060f1116050118080d02030a091a090c0109081b03120d020a0e060309101505190806150102030304060c 71
    0x120340d00148004046030002500e945000d801034110503105100400c01500009070043e013050700f0005413142550241002801e0814441c4000011030800942081d0a940011100300c035030302140302006a034100340c401c48103030f81c030690301030000e54000c008074004983e450340300348142c2e10b1004002520040016010072a80c04c150200005041c041c0072030020f001d001c8c0100c010340440181c2049500d00c2c1a9105076490040c1c00c01a84066800700020384900801d900480640d504000e00340c034402601060012200c03400c45003013109020705100003074154010300b40e0000380c3d4070302005030411034111810080078031140c80456905202d03940104c101281c0310001050200000340025076251629440503091100e828030050292204004100c0842d802050318403407442c030001c021910b420340004e44403050701c05806c95a03202405a04502601504080a1044a00c107509480d4031359951240341c446000c80f03c5c030290250304200005030002c2c110b50300c26980b00c00c050800c0d402070001600c10912a50f = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 395449991 1250 395448741 395448749
    0x204050f0f3402011a1f0c02060d0f0c0905011d04020f12070512100e2212020709060b13170a08040306140a0e07050f04020d0513120507050c060a020115 67
    0x703590707401c0c0085003030071805410780c0061099516546c45403c0e9441104034180c000300000401007a40240401c42d82c6500c101e50b8050107006041c80b01c00c15400f2920001c2c9a1680414045012030400141c1540141f030841183d04407001c021604c49180400e00010358424404a41384c1c4000300041100b00c546000c8050095210b40e845544500d507651031030702d050601403c83c820400070603104101c80703400400c40540c45070600b8203e1030740302118050703002e98504d15000140300388104071242511640c0002c1100480707140d01c50500a00c0e5640a41d03400c80c2c42001801c42c40d5400a6506004246912249451130300b2148202c850040e402e48074005d654119800131204913456a1581c0504500780c4d5200341c00418000080004151811240340c0c5d0380e01c00d20880d03014a003000400c2c2c080c0d40d541d9041d105c5c250224502031089140110008a0001a825040303400c0d1190039500c1800318451400c0d2000320b0750100052803281c0200040003416003111000b60210740d00c0d84000340f102602080c003c4014 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 395451241 1250 395449991 395449993
    0x1902090406060801030c06080f01030f241b050702031c17070302130501030b0d12090b040305070302090c0c0a030804020a05030a140106060e010c021003020c0f07030204050f0f3402 79
    0x44d41140341111070109168171280800c20f02005000a44c1002a0200e04481d80110a2900c1c070141d464610036907404280800008014007000c0c210480460700074242c100010006001c1e10f000110080c2c416026079030005e0340640c08103140e000190f107800d54001c620046c60034190100d032901d2540c3d00301d148040340e04000081c2c02184031900a20006440c00281c50242002d0140303950600115035890000e62001d40032419880c0b040740f44600407109403000d080c103001c4050340c171500d80c10025901d030030074031049010b80800000502182e03050016905040c2c80600075100500c40b03500d0440c0c03210f5028000b6603100030009000941a0340411003150820310610005101c514191640f0303003110000d901a4081c0700624076118140e81e4003181150082d581154003034110f01c0281d40c220000e00a0240c040c1a03449a0a13010361041400604ea0303085074421501031201d075403005814a022403082d034000724402c1031b143c0400c1c001d410440080c1d100410305890b03010b0a50a00780c58009403181528180c000d = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 395452491 1250 395451241 395451257
    0xa2102030114090c0a050906240c0706020304080601060302030709030b0919140601050901080a06050a0f140103050c0a0510030518060709050108010f080309060703050903150a1b08190209040606 85
    0x4107050010085d03006080484082c1007d28003000030074110401100340e5001c9a1020b44219800c1c0200305c03d442c1d0321207143c003c81d10f4541d101c02d00a9600e074090300810302984102c50001130810700c40e00880b8420602580c80442843c5195114994404090400c40c89400740825520703c0001c0c244000c0d10080c01001c82c46402032103030141600b8184181c00460151045400600180400241040940c9c1d130000001030b669480e03440f40001000f001d403021302c51504040f0144444100803103024140c030700400c2901c03010700c1248108284080c40b8400e17142c00140c3c182c0c02c3d482143c02640b0036513110f405614a0701400342c000840c13504003441201c83c82e002c075940807001d100550784441c000d800340c25401035902501b41410025541d03405a80c19a0340300703590004201e42054400c20a5802c0080041c0481d6400e400c91300c101c441d00c1d030084030140c808520307080c140101e200c0d41c0e66509000b000b841e290f908207900e400c1c003416201103048030078080e001c0d0204100c0c2019122440b59800800070f0b07642d00d01d0 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 395453741 1250 395452491 395452513
    0x4020307090e070c1707030215010303020105010303110105070e09060609191805040c03060506012705011b0f06050a0603020a080102030a1847070e0a210203011409 72
    0x2d402c0c80a8505030800604d0342e4004c3c00241ca102e1108024030000020030307180c2d007141c9402c81c58044200750021040b2080383c000400c054054100078145e0380309440c0c05101c82e4051604a0803034400310794413000a141010002c416017030405603650080c1000c0c010f10b1a040800b0082018018000045802089111006c10000f80007000c01c154280c8904024081801d0036125400005c1c500d010290400e030f07030380c00403c4e0182e02035524481a580d08804c3c0c440113907401d40c54600040024407840b40420404288803802c0c55054101542d038961101600f051608030703450310320061400814240d1055070f60003020016035178411b00b0500421101c3c00240c0d480c075180600c071702650001c034041d40c2d00c40001c221500000b85600480c46031410300ea0450342e503001200c035424998007602c00d031110b0001d07030940c0d0400c144084400d07503500c180025105d5100003c0d04200b8411000700520034080d440314000085406075402e40d50030465640001c00118140540040084c40100141c81000882c1d03c481030580c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 395454991 1250 395453741 395453759
    0x20d0210020f0d380a0512070312110c09010302010c0308090102041a03190509070e330102060c0a17041403030f04060e0d050304030f17150a08071202060f090402030709 74
    0x542e0604600c00038402c8113481a020a4a0515a0007520300c00d0480020303c0c14400c01c10000100150f0b044005510f10003007a20700602155040d00d041007882c094000490740714203054410a040380e906030340c0c458500c1c140c0d0301d003111045405009030b640d65408000000d040403500040b9010014102105640e904284403c50307000380003006083e0b1404c0c10300007042408032012481e80b08513407140c0c00c034117000da9440d5815501404001c072000c803c0345600b62a050004c08603030202c8540e00c2c0a800704c50755511902880c1e07680d40641d881c3c03940018110500c0e280483d8102e6007558006102e10703252250740104a546a003150001c0303604000c019103090800c000d0210301c5c0a402c0d08030310b80e04054180c0280c030603002482844010070241c140071024082c07045403449954020008940028540050b0902a640703d20400003c00014420700725904c021038035401c0404c0300411140e04d0b1489080f4946c0c194284201c98101080f800075058052011112a8540340002e40c8140002c0c0d481c90301e4107080c02c60030 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 395456241 1250 395454991 395455061
    0xe060309071e08070909050c150418050105090a050609072109030f090b04030305070f0311070b03060f120703020d140d020102040302042409020d0f1103070f020d0210020f0d 76
    0x6403c049041c407041c3c81c0421300c00318605d074041400303440c118021003032404480000d22542d44040bd0416140c1140480c000b02d0343e028030b042e40c0d41240e180304642c03901124681070310010b0301c3c000d600c000c0c00404180c3d090b0040c13000c00d9000700b40b10460300304d20000c06564012035a40e40419000f0600c3c0c2d0f424254410303400107481000d044080465410641903490060850060a1000f08006800041502414014035041c800c000170b145c04c98000581b2408440400d030000d4510360702845c0400c503200428540403201008100300388008100756403440d001c01640228101041c1d820790040344990740020403d2014106110b403d4001594840c83c6105000407200250900e80304c1c403000b581d08100c0c0d000e0210916040b100e00038405600d45036008200c0008041e40d000b030b12072040c540034040c445030403048080e604c5401c55807074601c400e88000c0001e90f243c07410410458016000240e140024052540c00303020504480305401c0c2c24440200d5101040362005803000a000c041e0303000c0030010010260030 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 395457491 1250 395456241 395456249
    0x207031e120f0f1d040c02070806241311070b06031903050901110c030f16120b180c04140402030d02030a0905060702030c1009150f0e060309071e0807 66
    0x104841030301c1c4110005141c2c88210141400b01302e00c103100075940c1c006100c403460f0840d400400c100074020580202940c3c0301d560b40300b105818062040050607415901001801c0c00300301c01401d000d036628602c2003104652060300602c5100d96121090005020f2a4014100e9180310341e0400d080c40c01c1c8201010b140a0302000050700045440c5075510003c5c0c1c0c03100030f84035501800c0c01c2000d40c200d04100c0030760501c2c0540c2c640b19010f106051001e40b00000c0050b00c41280b225030b1100034985038685082040428a0120107031544050001192209000b03a010712a5100c440c01510821802d070b200003002d40d4542c2510b03881400034407060006500c0c090003840304124241c002185000001000039041c095184141881000c011400e0b5056460901501d10815001881c06c0c1c0d141d00011000341c40c1c5d002c02e025203840110010695030100d8018269120744400545624000c46080810440710754002400d50410340941080001d2002a2240c0d100c031019001d45c0c812116420b0080d0180f403d665580 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 395458741 1250 395457491 395457497
    0x307080a0507121802030f150603010e030301120c090617010b030703031b020402070b16090e0903031b070b0108031c050f1602070b1306080603150c03070207031e12 72
    0x3081c41001a0001002e015541103d0008154100100c8828814981c610000fa41500540503400040c0202003405a0540200908039125807a040701f450300700c03070009001c030f40c15a000700018005140c1841c8a0500d00d0302c030b10030880c02140c0340c14543c010750b895075205042d61f002c40f0038154510352081c0955000100158024400365207941c074010a1182641c99840b00661450f0b02d04056407110f40417550400d400101010050402e0b5840302070004c030071140d210008014050100d001ca150400701405410008015800c6440316011200408200510f01c158400208840000101d5030124603000384400d0018585a418080303030307001980c40e007401c0c0000c054070306000c0102c603070140b209198002e0044010002d9451401000f6885e01d019600002c2c0c04e0000801d204031a458402c0f4104162040c03071b43c600103c1d894503020705680341c80821030b400b52580ba620004000120f1b042c003441d80900b142c412510301a99070340b15890384000c80440c14154054040c0060140401202840c0c81414185 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 395459991 1250 395458741 395458751
    0x70c060210060b0c12031b040f06080105010c0c090c0504080607080f01050f0604090f14090303190203071d041104090902190612021809010e1603020a02100e10060b0307080a 76
    0x2496845800300c500b180d070010404801301f40c0c81d0f8101c2100d50907000c0c445c20001d691310741340c1c2c811903190f4805104010004800d20300109040d4424464000b41e40d500804181501d42000d0402c005020341d001c5200800a052000241c1a08108000c83c0142c0b802d444071880780c00d00341200a58168141c010714000c06034860036100340c1d2500011142100c00b070340c4001481401040c40840038000c9132001c40c416000036014000102d10220045000341500040061100c00038242c01e016400111540740c003040b600540003803088000c610301c02007103800500010b4982002da50008441d042038001d601041d513502421011428500128088405d040811075541d03850981c000f00300010000008000c0358010a8282e00e0101480c4134103c5024002e007140e44541c0c460b5002c440700c410840d80d501d02c0c00c4102c0c1140d403086019208079810319459130702418508040c0c403002d40c05403030200c040c881c4910414501d09407070031240c0b091001070600e020401d070b902d00300300c0d1008140040151070301c00c00714681 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 395461241 1250 395459991 395460007
    0x901032003190803060a030204020703110114100e0a110a02010e07081504170f0d09052a1e0d03020309090705120a1805060c030a110f120c070c060210060b 68
    0x805081c1c0102c0760300035503581e6a07640e00d0002c1401d0f010244c3c80290000c1c000329030340c03003010340005081c3c1051034480000c110390074038940040d0150380d0a41d540c6422660700603040c0150560050640e9010906880104400c0381500380c045003a480f21007280d006075501c800421411206210300d5000303140381c5000741140c503140403076030184400281005048000400c0040c2d464100c1105a441c1a0030385500980c4030074125152101414034014106ea4034060340c0c09095490380002c0100321a8540c000300200000600010b0000524640d04842903c101176014441240d48180e180305040d44070f94003441e102c00600d414400f40a4000d80180700b80f050511045840345000c8000a5001a80c4003002c20180d0440c4940144001c0e07446000c0d1050141c10200840454032900460191518900402a45400103030901241c02014145441d400c0c00b0800c0c401d48100a611f001e400c10002020076280c01c142d81c4d545100250309a01800141c2c020307544090400c002c1d4030070031004104180c4040e14002034 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 395462491 1250 395461241 395461273
    0x1b0f15171015020f030405061b010e0c18090a03080702010213080c091b09010309030c0503031014010e060306101e020f01060e1909030e0a030c05090109020a020307030f05090901032003 81
    0x5071f00405000381804601e201000031621104070368090341030006c06c0814400e02095854600b0041400e02803103600302c0201c188603c03031466030b1107091022f01400b244202950111034030000038000724115902848440b440c0d54021110f44020300094006010074400002401441407004040045959104500803400ca10900403150480030034680000c041100e80b4050f10108a400303400740c498400402001600181c0c20b10040648030f0040818201420200c01181d405404128031600241c052000c20074a04240c4e80c421603004a034103103c140c00c8010f049a44001135a0703411000140d02100c0706000047e001c0c4580c0b80a001c601641180525100d004514410302c201c60b102c2c04e843d0b0703508004040c903101e414403001e03001004244080700c9560342041c01000c00d1602400f4418038176400000342c80e54840c0300720341c4115020b4000e1401d0801d40d440a07030382d0310303400d5050b4001d1100400000c0c1480e0340703582049018511400583c0e000b5080e110501d4130b16040312144a0113030f800f54091440b5124 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 395463741 1250 395462491 395462497
    0xc0a121d1203011a07031b170c03030403030605030712061d062d060a030201050d0b19091a01170907270c0e21070807080a1b0f15171015020f03 63
    0x14030280b03445081d0315241103502c0c2000e288c4001705500000c51070f60b2500a020000b540514041c6e03800340700f99903e40701015101c2046102e603096001140400c50005401d079006541100115015940008000c941740c0d400d21008640c0d0341030203140104400078503140305050810619520f4084280782c80c011001c10b1580341c50740000b905011000c1a074081440322a048400850800f4220f0072040e50326941c14400301034540100d90260341015003449400844040d0034035038507016920425182c840d00040b50010700080c18024080c0901d420100300081040303404074407007404014107030180c00b05030068030032a040c0305074070400c0101000729840700c4c0ea2071480400d036450150040b8003154180140d9140752402030f03400b1081030b008241c000168550040380103403d0b24041c1d207941d0045124040c9085000e2003a02504050445c5607100317220390140f044400d1502081c0b403c2000c8a545481aa010b40840468007004411080c041c180314030101001641d940d00301034002040c0161a500c05ea6403680 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 395464991 1250 395463741 395463767
    0x901061d040204021902070f140f0402070218010b1306020d020a110f090f09120a1d04110c060103110d0b1503120715050c0a121d1203011a0703 63
    0x240d030041029952180d04403000c0072105194807004030820603020b5125070320b91050503c21801040b0000e40c0d0004102c200e00803040091400c00204280c0c801c003c02034005400c180d80000d403c01d0356403c03203150f4a55a50103010070301440794441b8030620000280c1c203101d40114003150003c0c8001400240c000402003050355209025031150104100462102060b1840342c0c2d52006101061101103110301980c81d0080d41450103542c0c0340c00e001503180f0018402c000304080050310b0000f0200c0ca0070404a03c17000c20403401040455800200900800150441c00a01896804c804010800c001c040500700c003081030b0507100d06036a0749041e02d444481c5500241005c80c140315560703403401d881c0c0c1e0a00210080200c5030208030f48881e840c0c1010300c00301c0301e407090b0342207281d14010201e19648000b174251007200c01e459540d5940c4448003000712002d8520b01c204a200c0b5502c0c9821400407000501c9288003100754441e01949940c07600100c0907100c03a8640d0003500340c0b013042201c000420750100c8072540704 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 395466241 1250 395464991 395465039
    0x20705122704020d09030302090f010806060a0f02150712050f1504020913110714120a050a0207180e0c0603090304150c050102030403030e0d020616031a0a060215090106 74
    0x30306210202c0d0103032203422003503000c4500d000c45003402c15030180d000c0c143c4c4041c10345600414544200055482140c01c2e202194002c000b84400007042c3d10400c20901d42100d148141c411903840903500501040099681c54007103902c0e0030810880c0d044030300c84c05500a007008031041c6207087c501400881ca9520041140c01a9000030f14403a90341c4a004002d444c1e405028800c000f40c034044802901c05030401c04007140c42000240710000f0f01c04000a018000c3c2c2ca0000a952610140743c030181c038a6401200c10340154007030303a68001440200f604089504200d000d00c04200844180f0120341010501c000321440b0716810300030311003008800001e8070140c400c1c03e20f80407641441c242050342c80c000f0f18000100a503000100704000c0650641010220361030000c1141c03800104800103a844610842d81d07010300c840f188541e0030311584a43c0144000c05180e2060240305109100031654042c615081100540d001260000360b0082220b03006520450b0880208440b5040c011260300764546001e0704511 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 395467491 1250 395466241 395466307
    0x504090b01170117060c1206040f23071b0c0303030b06070c03050a021c02031b1311120601260705160501060e0709030c1806081002070512 61
    0x240e6401160880504003000c02e51a1180da034500703c0102c0c0c240328095040c40c9008081c08603100c4000320066411042814082c000c4c40da54140500000703250340604c12000903200c80d000740007030401c00e0a040c8980d4170752450548900e859000a42000a40304614003100c00002c1d0300004100307111440780c02d49601d0300e00030421a00d4280022404d005408000c1e203004803e5030000200b01c3e00041000c4c14038400d9481a1200001d50148890404030301c80194041d080744070300101d001c00e80d0244a680000003822030710f5403004a6032007030403242c0350a00000580340018245074504541700c40107034065000d2800039070300702211562591003051041102480d031511030114803498010350940318105010166903040d8402403c02c180604500e2195400c09082c84011508940c8202040c80a0b280c106130840000d03880d04c02c60401e403404840e0047c02207903803480c0126400b03c051101d100792480010026031a00480d04000e414002c0400c1d9080d2011390400c0141d40d50405960380e641004c0080040c601d03 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 395468741 1250 395467491 395467511
    0x5041d01150f231e1906120c030e0d0c0519050a08030903210a060f050a180b0a0f0f0501050310092d0f0b060403030503040b19110a12050106050409 65
    0x94408108450304d9001e0003a500264440e6259003511a21040498102c80f000c480440314071801100c80c042c40000440041107080030380016007190440307a407285000656a0030694149082244003240040082c10a1446000303100c002c01c00e0b0f5050400b1054400c480e01e8103645c41960b1000c0c40c0d01c0007091010040b0024002e10814425a883d135031007032941109032200d1010707a040d454801ca5801d120b41d40740107004102200c43c800901d0941c0d43c0a4030307140c10f55080c0480054894182c0c40b95024086e1610311085141e1103e04c03446000300981c1c90402c401c1410540261420b048030340115042010a204201e44070203500e51040448040d9900010b541d24040d0140031fa1140060088079462240c0d1005814480aa0710225518a00250030000e40d1103403410080b10380b046200150000300b091010074080340c00c2c2c6034507540000094620b000902542442c4d802a0b03114095808a0311301d001c2142c2c4042d94201d0449041c02080003400c02440d2306001001d0114001c03805001402d41e0364520410f = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 395469991 1250 395468741 395468789
    0xd06170a0201081e0c0d1a1e040902180105011e02030909091005100f0b19081008070e0a1103090a030e130509010615050c0a0209040c05041d01150f 65
    0x2104c800c42c121481c0403a01d0702801c0c10045a01c00040c00440b0391800346804d4010071400c1c01e41d60003490090280e083c155002c40041000d04901303200d0f81d8483d6450240c00700507614161040d41240300011001c2c107961610b400035084401c4840b00c1000c0303992401d80b9903001035010044503009030084903800c8036a110030084500d0100003802c60200d1034680b506100c400c0c0c1e51411410102e03120161191102e41e140c0b1031080441c0a0345070303100d810004000d182c42c504c6006008107a0700240040c035070303210103642d028140d10b09011035001e801d5000c1c02006000031000e15020b882540100d4031411807441c24014005a0b5130000360703001030200701c5903011170517a40c1e0706c4415030000180c618800740014180880c0c450300130a401e10941c807446c1e2100e03114485031802030302130301c01c02e00e1510064607039000740b5024402d1820008104031107400070a00082185d68541c450240c0740503840204a0312203800c1d036500303400c55400100d4003942a030b0b0003038200a4a116000c03000c0075140101c920708681c8050400070 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 395471241 1250 395469991 395470021
    0x210090302060d0501090c02150406180203070f050108180c0906130606080f0a0c20010f06030f0b0612190c0909031205161209020f060a050d06170a020108 68
    0x390302c0000002c44200b5404280c1115040c1d403030803602009140c02c1c0d40c4080c2c4e511211909a600c2d00c1c544500064003003030713640d40030240d8070341c05010f101c4040e03515074002401c003842600503500c1c3c0350000b071081c05956844144142d020080c40f40002c2c94800c03581c0380a0381e84410040760f84c42841c4080002d035030394440307004c801c07642d1201e00d909101c0f15423681d0010b050003100700d80c028031080d21030001450300504c1740100d200e00d03c9103885601da1884140c00c61103e0101d1498258103541d21030036182c3c0d1103401d91044c04015800343d904c00821280c9494005500c1d1405404c05115207107402d0800895000071481005401c00080b0342c8403180241c0c944480b513421103620410440c0e2425144105064001e80341030303032007005484208000d035a20b0800c2208090f880212500040b980080003140c496158000b0302100e00080402902c8014500010802d40c083d503400300000f80003240035203070041140a0040940700d03104660141d100301d40c0040365600d0050310701a04008076403000c100c0800751210b130 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 395472491 1250 395471241 395471243
    0x40b0a03150f051e01051203040b03010311031011030c07020f100306080f01020c0601030b0717070e012d0302130e0a0218030d02070515090d14010b030607080402100903 74
    0x16001e091404806030400401900050303001c250f007888001448802d2480450041c1c8860b92240080360b400c0400b44107803840c44400c00904c901c0100f00c04225902408065802144141c5a44a4660b954400c0c182841d00c1d0681c0c04001c070381400b0a00c41c07101c0405054036802000d00003c01e48444140c00001c0804580c5064140c12881c0d00e456880a19819005901030b118064121814081e00c1e0314007900b00c0c4076a031000b14483c1c100c50300500c00241d4156002d50800a540390990050f5489000101107200644101c0c021175104c083c103420f0b43d41c0000c0c0320700707003081c16003100c0100b40e01624908090028242ca04000c0590019501955100710500d1401030481d200001d0388518004840b10000d42c40154504102e030400b01c003a5400e8900010300c0b08004070250301504016140805008086944d10103200144509006443c140d4444c00d86d003803400360040d0100c18041300030081c29400c4030000b03c0b885000c1c1c0c214904202c890368020400942066064480310046050242c0c00c6441000c04d0300 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 395473741 1250 395472491 395472503
    0x10050307180b2508070b04020f12010b03070602240a110a180f030302210c0a03090302090c0a1407030c08070f201c0f05070b0d0b0a060c02040b0a03 65
    0x4004182040b4002c05801c40807004040b080320110900d8410b02c1001024a0080121408010600000b94440040380d0010702c0030b03080311000300c2e2031000a4100c4035001920900c0307a655649605540ca400c000c50f90040c0303c580094250740307407181c580c260b03400c07000c10b40e1035240034134030f408540a1100341d40100807552080ca40c0341d07124100d4550040400600036000c0c1e0600d0712500011507901040700d11003084a81c16001484030004621111040c0080401d07031403d504414041184250130a001d0030074102c1c0f082d0b82e0780c200d03070f8150f01c10440010406407941024090a0007040030340b0b5000082c1c1c03080a003020140369155031803441c040300c0d00b10745040c00606580d00071074401c007000001c01349009082e1042c403079040501e21408424030070000c030201c4507910610b49002c5100c08000d40d004049464050030032070702e28600c0c0340c645070b2402007907500c000300c0b4031400a500640102584109a210481156000c0c031039032070024000c0c00180401000380c81a076a4410074402551380428080085501c00 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 395474991 1250 395473741 395473787
    0x903030e151308010b15030f15130e060c0a0c020613030c061d1f030e120c0d0f02010b0303040312110a0804050117061c030c0f06230610050307 63
    0x10030352485582a00c150080c135800c0c44d2890b0040d1429010f1402014010301c1003c0c01c0d95603000e100d01e00040007814041d51480d103180280001c2c0c40d0f041c644da011260307010300401c200d100010624078145d0024607030340201c502480811035440e803140305c000c801d0742c0481d0001c0d1181c07460040c40e004400d655100405546030b031040007035441e81041ca22442407003051003a003a1080d501c0c080c0f109183c44400880150402203050f000c2d0a03002c0da025050320100c91040303c07500318406252032002e0b4000039194856512402105221039846144106010300300d01c024840c910b140e50100742c0e2400b0700e01000b0100c0c03600ba40d40d504200d105c2d4240c030719000028070859000a00c0c0e82400400340d4894004d103400113440e41c02d803516000c1d0416405026200103000100c10a52101580c083e088180d20100c08000c038169075a408500261004810a030207507100240c60102030f0404840007090b40501240c6282034400c000555950b0040203114049904140d6966568000100d850340030b00c1c1d010340c1e8020540 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 395476241 1250 395474991 395475007
    0x12100509061801050915090a0203013611040f09050a0c060906020309030a1103030f04091e09080304030e15130e010b071e0206040f0e06010f050a0903030e15 69
    0x506501807102402c052880007030880280e82600c0c811070f2012400c2d403045150300c031403641c18404c0070b40c0004800141c803500ea580364006800d41d00b4408081c02c070030141a08281c504042c244c00c20b04101803a12201e00194102e17980e0071420f14001c1040c074800c40d5150003054405034950081e034146540001641d003005d100b850000c240c1c0115000320340000d0456580803a100740000211801048024000d0422a00b250785031f140e052620201560180414090010035140f0000500080c0c181610089403221413000413065203141d101c6100309080c1410555400b285049040ba9003040d00740c41c200d0903261100300411f41c61180e0000d54124030b14001002000340780c141d1622800c0d608180210103440e60303924003c043301d000d904400b0309041000111005c171218006614100700748082d2940341000d91b00d06050700160001d50140c00310809800c204001380da8440c0d00c00c1d040e0522401e00c5418401c12920007011040e85001c0103081c000084030b114003960b00e94450305100441c0f82012595a208 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 395477491 1250 395476241 395476243
    0x10302090603090f1606090509060a0f06021c0311070803090a02030706020d0809153904031e080f07060b042f030f1918050d0f09080c12100509 63
    0x13a5500440c0e50003428078a005d408000141c0e1004c0350030640d50610550b085c902000130301840500816404080c2d4280043c0044441e440003000300b4181d0054044001d848a84040d80c02024461500b01072a004842c0069100c1c3c0066030030442e007040b07a00340c891303a074508882e10b0b080c070118010707516100d002c00c0000c056a0010b1910f01002e016510042c030f13030300c51002c0f96540e50f1403600d1040b02a043e00300050b4803a011030742ea920912800b18004c040051001114a4035182181c14640d01c3c19400202401800b40229100c40440554844060840380d580c81e20600c60003070901050500c80000750010900204d81c1104410500040081141c4401080c990f00c01d09003445451007007080840d80d141d004504182a80d114642403410000c80703640b5811850b1805903000a82c810301c0b0303920f101038000c4c213030300300c84001455108400070300f040c841e004000781c120400042c107502041180300081c4803444010641292158050310807441e42c140c0989202d0820641c1030302084294640400c124030400 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 395478741 1250 395477491 395477503
    0xf0f0c0105012c0412050a0210060b131d0403030e01020702040204091a06030f06042703030606030f090203150405120d050402010e0402090904020906012106081608150601030209060309 81
    0x385503d0325203002c444400c1d001403400021100541880d054a0006080b14000c1008003811480c134819600810440c030007aa007240c466400a4080a00210b064200042a8110040a4030310902c0842d01c2c10045141c034804204006d0004041503101c000c0004540003d405030341078a91300030029910b407602da04501c0d00078290001480d0032101c8981c440003860074840c088a0181c0f04420140f44159501001d000191082c0500c0010000d80d800c0c50007640703201e4120040745c80384241c0c1c010910b40e00d0110010107551520401c1c640c62132800c0891b00059a00188114044c0410003030125030f9030b2103040c0607082480c210320382c0d0011240050300f80d0400c039066002501c51031003600c0e6050142251018801240205650190054110000315001d450441242d175413004c0c1c14500880b1189070790034503044659000c0201300c0301c19224503046c00302107014800d841b010718018240d0007200749000300d09652024035400c42c202544288011035081d134440e40485d1031040024107481d0b07890804a80380e40e80e03a0 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 395479991 1250 395478741 395478779
    0x621100f0b060a0801060c020d020405010e09010b220905030c1f0609090206040b070c0512010e07080c030a120509061207170609060f22060312090b0f0f0c010501 71
    0x241c6010110052031038414143c1d041d400680d070341c40d109603003808420754941e030b031306a000d0741c1c001d462040305001640c1c0c0d400b5145c084d11400c4000034440c10090340440c00d59241c100914030038510144000021200381010b194416203144021404507224240507045210301d080010340d90144d0382028129030110300f5500749102c411801040481d64a490f12401c03038403404070003580588100300170001d100740000075181c0140285205030a49980d032000480204020314a80004d94491581c03014000041c0000c00040044c4405000e07080580c03000070b0313103072243c0c1c20004052017128001c2e0002544200141d80e030b401000390510b035580031380c100301c8001014101c5002000032601a103440100c54210750550044501422a0820b500c0d010104200101a05515074004200c4c03050071132008143c0c1d290700700e41030f001c20000440078194280082c0b40002031605105102c4005c80802c07111404038103c48002050041d40e0fa15581900c28451042c071540340118920360070200085002c2031103004032060b603 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 395481241 1250 395479991 395480021
    0x90612021008100b0a020102131811040b0f0c1f050a29121f1b081e060d0501020a021b040b13200f0712030b09062110 52
    0x90080401c01c0b41d880508403030740424810038290070401000c601014000d0901640005401e00d16080c03282541c44038a94040052003502c2c1d03200c0084030102c1d01c9074128000846030b08a15040c00d003007500e25a403080d803620340007040d4000345400d00007100b8483c0308000c0c1842c203c0c03c42440750b8111040f024103401e894481020749040200401c201c212202c0c148401100107903005004440c8003004000465000c00c803403d0700681c4c4040742d00c401d411301d00c14607001c40a00e0000b101c10045070a001c00c0302d030001c400d2082c400c480b4140020302001d0100d0201841a150807490140d9610740890080140501d004010303600104640c1e032400c0c0c0200d00700560003a15500460501c100808102c01e03a0010041180c205042c101d06104180498000d5030000a000c5070710343c180c07900500900074030b6000611001f52007801191200c10040446118000a10030349800c0c0320004804c000180605c03005000b9a03c100e402c0c01d140082e069002229030400d88081c42a901c0302d03010303044010050001800c0041d98 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 395482491 1250 395481241 395481259
    0xe01060c02010e0904030f140c03280f08011403010912031a0a0b070303020f0421030912080d09050c030f0c010e03060c09090411190905090a03020d0e040609061202 72
    0xf041c204042414421a0907942e18400448041c00a9440d00700720005144203031410400c226513014108010401c023080c040002b55041000d0200d2881401d41e0500380c000c00c040b5100c1c11041e21f60000d141c906441c44100350703c64044007800002d0040110050040602440650102180b40c166004141d81411101d04200e48004102081540c083d1800303105001c040922201c008207100358080c14040d00c01155003464142c40f040780c00c2419200403006800207529086900405a025030030034010070a028804440b00e42075070b0f40c010340d0b0042503100d00d0701c250744154903803c0c000100800f0003030520140654405910fa000403070b444050301ca02440c00710300c1802c1100410f050000d20340d840380743c000300418204005201007001c0210301620582c0c480034400b88002150341c0714404002c44c10300500d00503011034a00b45c05081a100000c0c00041c07507420088609001c241c011403a02480c00961134040403122030180003900408180c1c1204104601d40400402c00e03001c91405600c0d603900856100130 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 395483741 1250 395482491 395482517
    0x711010903080d020c0a05070305010c110d020a3207090e06040503030406110c010e030a09081b0f0d06020c0f060c0a14070f140c01030f0c09050d0204060e01060c0201 73
    0x80d036032019100080814104102100890101d40e0141c801d01c8208404d642d502480c0b03031903207464040b240e0401c0d64142d64070141400115000500510400c40c0c1c10042d2414010010010f904c94444000c05003401a050040c62030006103a41c06409078103601c110340c4030110301c02c54219a90702c018064180704901e0001120b11503080003400a1261b030b4044007d41c40c5644960342c8802511058503400040340090210f814080ea0a00404058424840c025a02c0e0359544c40000c1401d225640040d1103a00111000088540d10b111010a000026a40e0508680c048004140340000301d24025100340d1020031003036009540814004c0f05104030340200c81c61610b4403510f540540c880c0181c0d59020a114030b002c2d80902040d0390181400d14050800700c1210401a02e8500300c400300c55100a81d15082290320205560305413107480319611000700f040081803846000039040c00b440e0702580e44a540c82900e000c1c110b50300d80d005400070b030090306101c07151960b58050103801607081100807800b082d017107440c42c2 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 395484991 1250 395483741 395483747
    0xc03090206040315021204030f0e010c0201050a0810080703060b1e06030a050403030902100f02070905091e070b040308071109100b13090c0207090e060105010e060a020c09040305071101 81
    0x6051503001403005182c6031850b9110700d61181030039900c00d840f5400f400030800005004646d107120380e000e904e07015034080400d08003c4c4810100300b20181885189188900940da010f0f050300c4c038050082c200705825440d0000122903a0b000c40e446540c0521896402008105060300036441104007510b2200480110421402c155070440e42000e41001d0180300141088070540c00c015040760080c10700140058540e0007141c0d0913031746004004040b40075910360320003950341040301c0c0c0002d001c1c1d100d08000c00d042224155444081100c80c02c03030245400183c401034480188243c500400040321300e655035a40e80d01c0d00111035080035605844000c62045603020320304002c03044e035102d60ac040c2c1000400038101120300320540c201006020303d20110440100d01c080082c8070f98031140c03c070780d0024001c1a180080007001e4400103900b80039030f074024400420082e6004202e00e1860301c41150301d103031252044a8200e2921100790300f16940310440c90244000d040e00302008000b800d00880703000b09060121070044d = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 395486241 1250 395484991 395485001
    0x12420070f0e16020a03210f021207030e073005070e09030c07210203011104090e071a07030519050301090b091b0c0c0d0b0a321b030709090c03 63
    0x14026030010017100d00003c1c407a01d2821030142d0140005d08400380d0418910b000c59040d0900c9400050740001c04ca2542e02e5003c0d18a81c2c00100b5107018400d4041d55a001c84d102c21080c8a6000b1040314860000300041e4400c4001c040c0b100714080d154440549802e0482d9600d190f441042a516003690124040c00c0001c000c035000184400000e00106142c6150541807150b0020030494201d5881460f40060b582805010001e0324802251a200c0e0b0812030341c00c048035203540d60314540707620000e001c1100d5200070281441c29076488241c00d41303034040d40c141070300c0c54071881100e00d699042c3d655031030a5131504100603505841540703a08214000320034050040e0b40105885c07607100a039588000101188050004007502d2060300255404900628086981400c10000c00c03030300301d07603135100300b2044015511403500140c034000d2003400403000010a00729401f03204101070511106240000b1685840b610210b8090054403800c599240b400840080c4809010b004204146041c0614030003ca0320074003075 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 395487491 1250 395486241 395486281
    0xc06030608060708271609050601030216020603150a0305150c0c100902041e02181504060c050114090f010608010519090c030209010617012420070f0e 66
    0xb501c0d601740c540c44644070310001c0c1540301c9041c8081031400321141e0403043c03000e0020082c07050800e503540c0342032001c1e0314142d40e0020034490405106024a440540d91503400716000342d0140c1384190307662241d11441d81740c450380500c050b81103005e8030400410050002880300c1004403480b481c0310780e40c40d400610b51252003007114041d500d034880780080000ca20650301ca039400c02e10080002900f0a040254400701040200c0c01d0f101c9264042401080242c00c1007424142e40d00c102c0d0000414140090344100070701480c040d54040001e9825039904000c030035408030110a071001c10a0000c0c3c500095815aa032994102c0040c5650800c035000541c103205000d01402a100d101c09006108291205200200500c501c1a560110030350380c004050303100c1c5240b00e4080c240316910840c044101401da044488010307401114a8602240740d404e00c02d0344003849941060091030b106402c000348117100d02c01d107484079080b070200f40150140014410078181803c0211141e07010741f0800c5e0b03030ba0700a005901040c5801 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 395488741 1250 395487491 395487497
    0x102061e190c050409061a0a0f090801020f0705150103020a061101110c0705030712020607140307020a0902090102010606090510080912030411011b33090c060306080607 74
    0x3404660001186066030044000c40342908000300c0c0300350750066680a00001000c500000303010b0119018500031a8042d0032020194113605440c0c1c15a101280328250740c00e82003000c540680001d542c4158038000080c00c0340002376403100c20417009100d4550007014115131a2280b07031203820200c00701c84180c07030403070383c0080400f041c0616089040c0c0e400b50740303c00c025105550b0369404003807508810002c0c10542c0030460060400d40e0512060502e00800ea03082200003403085561400141c2d200412200f240360300680141c030414206258a05d94044c004000b5030003100b45030041088074540d0301800100500368001d00a00b80e50305400d4031259110301880d40c004096900159506000c2c4d038000d60829074400403203121107881209440c80742c02c140d404035140b00c10120101915a4407460b03401515200007841c0520342c290b41e440011400c00a20b0130032400c1500d00c400039621031001e47c00c0280b8550f220013840306600500e480032481c001405020003003440c00c180410640800030300d0354440c100340c2d1 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 395489991 1250 395488741 395488771
    0x60e0a05010903091d250c140f0c03160b0d0605040515040b0406030302030d0b1c0308040b0f130314090604060503010f0902030601050a050c010908040305150c13031b0e09030a0e010206 81
    0x50810015041c044100c00902030042014000580031040540320740f604000278000f0314070102030b40c0382000480101c85100350f003c0864142140e00903500d40d41182d00c3e021145940d1210302045002034881640103c1c1e02924180030807200c6000d07000e280360032910480d41003040309a00e10400c01114880e01019005034018812030703c11070301c664401c02003203070002e2600c903601c01810400003580400100440000f01c041050004001024111f6a00035150b034000702f1180c5082900481003000d00900a01005181e49500e540c0362201011122801405054550358544941c4040c0c0594401e2040c0c5050740c141000019800726944241d90241034169121850600300d000102c1c0c07903401461518105541c3c1d08681c0b000035013070800030301c000d500c2803001d021000c1842c000800036660041262090540c200445400701d103200c40b03e4010740741d02c00f14000f1540c0581e0140200c03c0b030250408090507051800b48101d0b01c0d0000064858040d00e6943e140100c0020001240ca900041c3c44048800d5921 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 395491241 1250 395489991 395490031
    0x114041e0306020a0c03020d09051008100b16020a12030e09090c040516030c02010c0e1002010b060301060c1401060b040306051e07030c17060607060e0a05010903091d 73
    0x80286411900095203403041859120b440748001c9911098414001c1801004c2d66030030141c06111000d85044203003400f03c00c00d031411000c00c211080244220742000110000260700c1d450841d0301102500b07d00705c8803621007800540c9141e03070100580003070348a0710311644009020862868460800c0e9810382d600303040300c440b00b400d112540b0301c0900a030f0458020700d003002d91131380c8641c400d00744908103026070700c0c1c0312440951307001d0f040307900702c80703d0303004590510b10007191381c3c2e030010f4504407034450a5904420304800d8110880c01030441d101c0e810f500001c008000a0351980c030420070800d281c020580c0308082c4030388004203403c03180a8440d40b00140ba05100800108420707912507035205031055009600c4225a04940381241011a520808640e07540380c2c8100d01940041c1e040142140300740c515000e81031400004115000311600100100e4480b11028403504062250083d4554084002d0140a01d54940a411034110f80100c00d4042100700b8ae102825450003140742c001c00c40505940c99000300c0b = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 395492491 1250 395491241 395491259
    0x170303010b090f1c1214090d1e1b05010f050a08160302071211061005150d090203030417060703021606092f031908031302030c0603180c011404 63
    0x14502e41c082513030584800440c1440700e101c5000743c0324a200c41ca14100034900680f4141103201e6000180a06000d461602d495802d41100c0464003c180003180c20070505062440503440c0c1001400008608000304180120070350030800d03150262a4060b04c00f5040d07100f00c03240c0c003d010b8880c000075080e40204039000c006814183d0259200e1a001d0310300111038480c42d4207c40c0351100c5400040401501c083e58a1042c4111078000ca01038202d8425503103081f00013580c00b102c200f120b200c1101d0004071440168540d50002e4096079001d0140ca4035507684d06404028ac0c0340c030002801c41c2e4060140080c001c0d600c0780c4200c4400729103617200c401c468074031038a1b000000e00c01480c04845160705030318803800106502003c00001510710a00041d9000050245400c0c045050700d86030005120012190014406030242d030340c051012400c2d108044c03928000203141080c00c5591540101e8000240280400d1381d698440b07452445008480c0c10b404590300450b041303100b0030200c07800c00005010601c80891 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 395493741 1250 395492491 395492509
    0x3041a0c04030c1212030516030f0b10020d0210090308040b100504020d0605040e010c090315180605041406101511070e100b0f040905180d0306170303010b09 69
    0x41441001070515490f03030380700c0c4040c008070742190f01d80c2c0074529000000c210580081140311181e0340750a2005061800c1601d6815404891140901d502c840031180a481503a000050015005045051405280703c019482c2e030200c1030004c0040c01140443c9010584a0141c903500551503550280c40d031b038550320b4038440c000b4003800520481701d4090340050180d60f180007170481d040141e0000256145444200012503806220b4038101d43d0504044050298100c5662003c40c1d4100260403400c040d100c5814004141014408445480c91540e0b40c003031000a900c030b940b050b8810043c2500d00450500c40c035540d490200c1d20000308000398001030100080e00d1b604180c0c4c11302c03070b0b042c0b0400200462100c2801c01e2004d8200314044503400041114561030145004000c0010780c030428038050880e550798030f80380324900510251644600120f10140d07400c0766000841090803080d16800820420b00034080d210900c214220360004620105404d00c000c0110381c1243c000200c0103141078030202c04e001500d0703 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 395494991 1250 395493741 395493751
    0x206010b070615080c040f06080606040903111b040b010c170c0a020a170d110d05181f030614090402040c020a0b070807030f020a05030a0504170a020609060a0203041a 73
    0x98445601c0c0c042c00c3c10101281d80070301000c00140c508108450300784000c540321714040c440914105541000342d418041061900600251808a601304036420f040c3d038000500b4894054500c00c2c680340c8404912039640d01030784c0b11f50445050060030401001114035510345000546050303099440034040c41c1c1c102c4028100c1c44110822341d0740400707007600010103c600b55400f40035202a810010343c9001c00911010f80440c655041c41030190800604803a601d00d81c40c1c103060f05200380002d0b072040c0381c801440c07102c1805000805413030401c8180c019100d01e00c111262070801007410114041910040c160303111408503030103001902559101d808000c0a081e019460038207500a03071841102080c0000a214800c46182e1600012401d22110040c11104003c4100c072180d0310511000030003581c400c040740c1d0032480e059804140758440b03041c070406c16032818214005008001034060003098000c600a84104d4000050350310651701c80b03074648168842160b0080010b4404081c410740d1410341b03190300d5081 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 395496241 1250 395494991 395495003
    0x5030a0b031c020606030c0102070b031b1306050901080a0204120b04110405040f0507050d030801090e070b130e060d0b07050706150306050103020306250f03181a0a0c0206010b07 78
    0x42c1e8110b50405070554407008400580050f004c018840c1001c11406007200c000b88020409640340600d005000d00010300b0200490b103014012141c3c240c0d140c070a44092040248000c960707659100d41c050000d80c414841540442d11031000121120060f2003521f0480348200308140181c86d480e0f48240c44150004c000301d500e0040c00d69072541d541c54074892144924850752035036140d0354460520928040c5544c3c4103030f104242c030200d02e1002a62084505045401502010540e44c0140c00c505090140e0390300315142091001c0b038280c5180c080a1120811078084005070f241036150710f002d010021015150190020b00e45030003003148240300d0b03001003480e14081e800002e5100f0b0301c46903561107014940c3c801e444642c1c032003005006519061000c90f8001101d160341140f01e0608503015942c49030b41c04089020304c0b4651001c0281d460094008020311420039442c0400070030107107440407100d600486400030204c83d40000401c00ca450340f00b894502c00041d001420b01d81c1c600403003611035901c4018100c0b40 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 395497491 1250 395496241 395496253
    0xc06020409141e0405150402040b09190b091314032104030e0d11010e0f04020318061f030f02010e0301020703020601031b23031f0203060f0a050105030a0b03 69
    0x501c00c560700c40d40c491070406259000c2d039410803625515a90445000d11020b1280d81c0c024440096000116504185503100e01c5e8140d5694500009000344800480e107504144020108040b1041d52a8440c141c1c102010041103904007120500c252104116030916802c071100e1034000c003142d003a02c454411150f045089a1800a401040d610220361590000b40c41c0b11100b07050004258000007111910107003514802c42d500c3e0913803900f2050000004803d0f041c0110186440030310b448424400248c014060001c4d55a4101035140800b840c000184040060081e030307020400510001041e00380c50354949101c0d640007825038441c5521a80c1d001012410700c6540c01818903a51800c0c0040d0040900a0f005880903600d103042141e0000c000a10203040c0203183c04052000441c1000c40340712080300d0300e2080600c084680017183c0780c1010442ca903141d030540a50070f010760b8940c030b400951007400c080d140300380d0411618003840300014050096074003141c001d00000302025900d0340a4590444000c0403584 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 395498741 1250 395497491 395497499
    0xd090b0f072402090913020d0b0720030909010b030603060c13030c060c0203010f1e0f3e04300228080303040c0312111207030315050603070c060204 65
    0x4190405058080b00716a00401c442d0000e00d02091200d40c041559106000c012415500042c460050b00c1d100400c0620658081040f9500c10408024820b8410015100550148054a94079004950450304c038416601c008503841401c80b06176800303410060300801c0c1c503484020001d002030f040700e812901781c3c0341c401d5400000306000390f032034000425240c0c071540707807102003030062600f03489610300508526420030005281811043c102e42c03000395001d500010b0400d802e020050050000000c0021015070350000d4215610030341c16010b20400344e001c6408901000d00c0c0c070074101e103000c4d9101d016441d1801d440740c40c1c41124032004032042802685480c0005946950000d1111400030f5045022125001c03017804900420480080c0940260300095045280036901d611000780345010084c400d04008860f0181d05010312404074030114090141e0701d68039120400013503190040c0800b540001e04001440000f0540c1c0030742c0c402a5980034160616540e9030a1060f07500602805080f14480c1d400c000c001 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 395499991 1250 395498741 395498783
    0xa0908040303080f0f040c06050a03060306090b1006020105073905010b031213050103151203080f070512010605031b0d020301030201090e07050405011404050402030f04050d090b0f07 80
    0x200c0a503200e511143d0450900070264081c1c3c0c4002014070010680ca1403d220200d01000d10300d900300ca419180c080c0c2d07544580758046001d89115800145003d0416048608000d01c07418114400c5002105890607281c2d1414128240d40c810b84512003c41c401c20715426841c0d41100c011807000544805803d1040190041c501000340c00306400e1f21070740d640d511030445a15007032150040350407040e4081c60800084d40342c4848001d0403441042e05143da500c0c041d2113500300d440090700040040c64ac0540d1010030904003d40809011501c90894142e0300c400100090300540640d03c441204061182d00c44e0700307010080c1c0311035002901805050050048a0400f0010640203184116201c0405078032545188009065000d082d00030301c15503480e000802c9200c0d680328050700c0455109203001042a10100c101400c9840b9940005410a00000821240c1c04a4042030313030149201301c040b1080031100b51012105007429000c2e0310540c1c03034100130959542d01408d01405640703014485560306411805045 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 395501241 1250 395499991 395499997
    0xe0114090d0201032301030b0105060a200a0f051b0a14131805161d0a020702010306030b1303110f0703020103021c150303081015050c12040f0314030c060f0a0908 71
    0x8800d11700e410000520412803150301450060a05480c854246030700c454019081000003410b1141d810405504240c224070704000082c58290030034110030a010880c00c2c107544903840040390220104040d220b0350114105264240300300c4450b00280c1c45c030746800b101000080c21240000c5105030341c172804014040104601d84800c40c0d0b01c1540144070003843d81d0a0361200342c80c242e0103903420b403d0520915103c101c9005080e5072140304ca0600594880b19440103070003e206940000e045d026042003000018030340d554403992a9800ba841c1c00410034000107149544258803903940480317400501c0100015402030b000303003940d940b011621484c9800204001c908940044404001c2d0071100f0408000f40740e04050307a0380d0040b8490b00045040e904050140e14101c100c200344004001e00010803140f071107400e001c5160341c04c400310a240c0d507843d41c44800710b4030103a55001c291040350403c1d03118003108400204880002030302e0710141050b980c03600f42e101d114100091a2642003a114100c600020b4444001 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 395502491 1250 395501241 395501291
    0x1060f0503150418150207080301050d05030705031b0115050f130b03060a0b10020105040f020904030c05101d060103121b12050310062102030a060b04080d0e0114090d020103 76
    0xc03041c00c09503542480d8251404030940c00d4103003841000302c480868202c8d0101d078103440c01175030201c10f038281614050f4510300c80c900010703000d404003041c2010b01580d05800c281014291708020300c010303c804650b14038000103a00c900c070351081d21242502c03001d0920444004075030b1f2000c003000540743c1000010a00b0407034201c800210482c0d43d0342215203075103032445c0b040400408501c001c00091420b59103c112440c601c0344042e200700c00b450001010580300b4804028110f034803e01351030606c0075204d050809031030509405592110403040f1949075040000e901c60480c1e41111004071f13a51040001510032601c042c003a0020030f4407416039007022503503225190b00300c03011983e6100ea0f20310741007078000c0c1e004403d81c201c04100854182081807102043d003030400c0f110300c0310324016a00d40b5003500c610000d0035a540881402c105c00300d800540d4510104540d1100c080310b895410320800d806004603034040005110028001061046807564242a685503074118070604000403c2c0c121148031021110701030007 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 395503597 1106 395502491 395502521
    0x31221021b010c1d100504050f0301021e040e180a0209070e0a030c03021207080d11032a0d050903030f0c1507020a12020601060f05031504 61
    0xa200044580071402040556003940010300f00c04040c0395240f40400d1407481031300103810304014032449400743d035580c0307460300c1e06000400004a02ca000600c0c1c1542d42403201040d80241f1900925182404020b81c94030340e450aa10b1310303603c0d1401400020b2868821001000455001400c910419030444031143c090380c900ba0304aa07500001c141701c650192010800009003e0341d046200140c1c3c0c000da0304020381f120400300c2641c3da080f4a2240e0340c1070760f010030078185425110b030185410307040c82c04068a152903042400c2c650f8134040340c003400d45c44040c1c9075944580c00f50100107041c24090941007040c04d110b06580029141e025483c9121081c000018801003440c405020f01c0da507011070059503080d181483c7c42c000b55a00090030307040350000c00ba0784800d0401e40c000600035040720456502c000585d81c1c1c44004580c02d40010300030202d010b00c800c00b041616a0389004902c20462010 = true := by decide +kernel

theorem cover : BRFrame.Cov 395323741 395503597 := by
  have h0 := BRFrame.cov_init 395323741
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395323741 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395323741 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395323741 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395323741 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395323741 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395323741 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395323741 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395323741 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395323741 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395323741 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395323741 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395323741 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395323741 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395323741 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395323741 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395323741 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395323741 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395323741 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395323741 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395323741 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395323741 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395323741 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395323741 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395323741 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395323741 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395323741 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395323741 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395323741 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395323741 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395323741 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395323741 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395323741 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395323741 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395323741 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395323741 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395323741 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395323741 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395323741 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395323741 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395323741 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395323741 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395323741 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395323741 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395323741 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395323741 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395323741 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395323741 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395323741 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395323741 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395323741 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395323741 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395323741 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395323741 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395323741 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395323741 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395323741 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395323741 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395323741 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395323741 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395323741 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395323741 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395323741 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395323741 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395323741 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395323741 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395323741 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395323741 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395323741 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395323741 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395323741 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395323741 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395323741 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395323741 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395323741 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395323741 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395323741 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395323741 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395323741 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395323741 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395323741 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395323741 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395323741 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395323741 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395323741 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395323741 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395323741 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395323741 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395323741 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395323741 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395323741 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395323741 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395323741 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395323741 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395323741 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395323741 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395323741 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395323741 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395323741 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395323741 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395323741 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395323741 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395323741 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395323741 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395323741 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395323741 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395323741 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395323741 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395323741 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395323741 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395323741 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395323741 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395323741 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395323741 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395323741 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395323741 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395323741 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395323741 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395323741 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395323741 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395323741 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395323741 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395323741 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395323741 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395323741 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395323741 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395323741 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395323741 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395323741 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395323741 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395323741 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395323741 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395323741 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395323741 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395323741 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395323741 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395323741 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395323741 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395323741 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395323741 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395323741 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395323741 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395323741 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395323741 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395323741 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 395323741 ≤ n) (h2 : n < 395503597) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
